#!/usr/bin/env python3
"""A compact pure-Python implementation of PAGE.

The C implementation in page.c is tuned for large searches, parallel start
branches, and several specialized bounds. This file keeps the same central
algorithm but aims to be readable:

1. Generate candidate facial walks, length by length.
2. Treat an embedding as an exact cover of the directed edges by those walks.
3. Backtrack on the most constrained uncovered directed edge.
4. Require the face transitions at each vertex to form a single cyclic order.

Input defaults match page.c's environment variables:
    S=0 DEG=3 ADJ=adjacency_lists/k3-3.txt python3 page.py

Copyright (C) 2026 Alexander Metzger

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc.,
59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
"""

from __future__ import annotations

import argparse
import multiprocessing as mp
import os
import sys
from dataclasses import dataclass
from time import perf_counter

MAX_VERTEX = 65535  # padding in an adjacency file
START_BRANCH_PROCESS_CAP = 8
PARALLEL_MIN_STARTS = 8


@dataclass
class Graph:
    adjacency: list[list[int]]
    start_index: int
    directed_edges: list[tuple[int, int]]
    outgoing: list[list[int]]
    reverse: list[int]

    @property
    def vertex_count(self) -> int:
        return len(self.adjacency)

    @property
    def directed_edge_count(self) -> int:
        return len(self.directed_edges)

    @property
    def edge_count(self) -> int:
        return self.directed_edge_count // 2


@dataclass(frozen=True)
class Cycle:
    vertices: tuple[int, ...]  # closed boundary; K1 has a single vertex and zero darts
    edges: tuple[int, ...]
    edge_mask: int
    turns: tuple[tuple[int, int], ...]  # outgoing darts at the same vertex

    @property
    def length(self) -> int:
        return len(self.edges)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Pure-Python PAGE implementation")
    parser.add_argument("--adj", default=os.environ.get("ADJ"))
    parser.add_argument("--degree", "-d", type=int, default=os.environ.get("DEG"))
    parser.add_argument("--start", "-s", type=int, default=os.environ.get("S"))
    parser.add_argument("--out", default=os.environ.get("OUT", "page_py.out"))
    parser.add_argument(
        "--jobs",
        "-j",
        type=int,
        default=int(
            os.environ.get(
                "PAGE_JOBS", str(min(os.cpu_count() or 1, START_BRANCH_PROCESS_CAP))
            )
        ),
        help="parallel start branches to try; set PAGE_JOBS=1 for deterministic sequential search",
    )
    parser.add_argument("--quiet", action="store_true")
    return parser.parse_args()


def load_graph(path: str, degree: int | None, start_index: int | None) -> Graph:
    if not path:
        raise SystemExit("No adjacency list supplied. Use --adj or ADJ=...")
    with open(path, encoding="utf-8") as handle:
        try:
            n, edge_count = map(int, handle.readline().split())
            rows = [
                [v for v in map(int, line.split()) if v != MAX_VERTEX]
                for line in handle
            ]
        except ValueError as exc:
            raise SystemExit(f"{path}: invalid graph size or neighbor label") from exc
    if n == 1 and edge_count == 0 and not rows:
        rows = [[]]
    if n < 1 or len(rows) != n:
        raise SystemExit(f"{path}: expected {n} adjacency rows")
    if degree is not None and any(len(row) > degree for row in rows):
        raise SystemExit(f"{path}: adjacency row exceeds the given maximum degree")
    if start_index is None:
        start_index = min((v for row in rows for v in row), default=0)

    adjacency = []
    directed_edges = []
    outgoing = []
    for u, labels in enumerate(rows):
        row = [v - start_index for v in labels]
        if any(v < 0 or v >= n or v == u for v in row) or len(set(row)) != len(row):
            raise SystemExit(
                f"{path}: invalid neighbor or duplicate at vertex {u + start_index}"
            )
        outgoing.append(
            list(range(len(directed_edges), len(directed_edges) + len(row)))
        )
        directed_edges.extend((u, v) for v in row)
        adjacency.append(row)

    index = {dart: i for i, dart in enumerate(directed_edges)}
    if len(index) != 2 * edge_count or any(
        (v, u) not in index for u, v in directed_edges
    ):
        raise SystemExit(f"{path}: edge count or reverse adjacency does not match")
    seen = {0}
    stack = [0]
    while stack:
        for v in adjacency[stack.pop()]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    if len(seen) != n:
        raise SystemExit(f"{path}: the input graph must be connected")
    return Graph(
        adjacency,
        start_index,
        directed_edges,
        outgoing,
        [index[v, u] for u, v in directed_edges],
    )


def make_cycle(graph: Graph, darts: tuple[int, ...]) -> Cycle:
    if not darts:
        return Cycle((0,), (), 0, ())
    vertices = tuple(graph.directed_edges[d][0] for d in darts)
    turns = tuple((graph.reverse[darts[i - 1]], d) for i, d in enumerate(darts))
    return Cycle(vertices + vertices[:1], darts, sum(1 << d for d in darts), turns)


def input_rotation(graph: Graph) -> list[Cycle]:
    """Trace the given adjacency order to obtain a witness and an upper genus bound."""
    if not graph.directed_edges:
        return [make_cycle(graph, ())]
    successor = [0] * graph.directed_edge_count
    for row in graph.outgoing:
        for i, dart in enumerate(row):
            successor[graph.reverse[row[i - 1]]] = dart
    faces = []
    seen = set()
    for root in range(graph.directed_edge_count):
        if root in seen:
            continue
        darts = []
        dart = root
        while dart not in seen:
            seen.add(dart)
            darts.append(dart)
            dart = successor[dart]
        faces.append(make_cycle(graph, tuple(darts)))
    return faces


def generate_cycles(graph: Graph, length: int) -> list[Cycle]:
    """List closed dart-simple walks once, rooted at their least dart.

    Vertices may repeat. Reversal is forced at a leaf and forbidden elsewhere,
    including at the join between the last dart and the first one.
    """
    cycles = []
    for root, (start, _) in enumerate(graph.directed_edges):
        stack = [((root,), 1 << root)]
        while stack:
            path, mask = stack.pop()
            last = path[-1]
            v = graph.directed_edges[last][1]
            options = graph.outgoing[v]
            back = graph.reverse[last]
            if len(path) == length:
                if v == start and (root != back or len(options) == 1):
                    cycles.append(make_cycle(graph, path))
                continue
            for dart in options:
                if dart <= root or mask & (1 << dart):
                    continue
                if dart == back and len(options) > 1:
                    continue
                stack.append((path + (dart,), mask | (1 << dart)))
    return cycles


class CoverSearch:
    """Exact cover of the darts by the requested number of oriented facial walks."""

    def __init__(self, graph: Graph, cycles: list[Cycle], target: int):
        self.graph = graph
        self.cycles = cycles
        self.target = target
        self.by_dart = [[] for _ in graph.directed_edges]
        for i, cycle in enumerate(cycles):
            for dart in cycle.edges:
                self.by_dart[dart].append(i)
        self.min_length = min(c.length for c in cycles)
        self.max_length = max(c.length for c in cycles)
        self.full_mask = (1 << graph.directed_edge_count) - 1
        self.remaining = graph.directed_edge_count
        self.used = 0
        self.successor = [-1] * graph.directed_edge_count

    def candidates(self, slots: int) -> list[int]:
        """Branch on the uncovered dart having the fewest usable faces."""
        uncovered = self.full_mask ^ self.used
        remaining = self.remaining
        shortest = remaining - (slots - 1) * self.max_length
        longest = remaining - (slots - 1) * self.min_length
        best = None
        while uncovered:
            bit = uncovered & -uncovered
            uncovered ^= bit
            row = []
            for i in self.by_dart[bit.bit_length() - 1]:
                face = self.cycles[i]
                if (
                    shortest <= face.length <= longest
                    and not self.used & face.edge_mask
                ):
                    row.append(i)
                    if best is not None and len(row) >= len(best):
                        break
            if not row:
                return []
            if best is None or len(row) < len(best):
                best = row
        return best or []

    def add(self, face: Cycle) -> bool:
        # Disjoint dart sets guarantee distinct sources and distinct targets.
        # A partial injective map extends to one rotation iff it has no proper cycle.
        for i, (source, target) in enumerate(face.turns):
            cursor = target
            size = 1
            while cursor != source and self.successor[cursor] != -1:
                cursor = self.successor[cursor]
                size += 1
            vertex = self.graph.directed_edges[source][0]
            if cursor == source and size < len(self.graph.outgoing[vertex]):
                for previous, _ in face.turns[:i]:
                    self.successor[previous] = -1
                return False
            self.successor[source] = target
        self.remaining -= face.length
        self.used |= face.edge_mask
        return True

    def remove(self, face: Cycle) -> None:
        for source, _ in face.turns:
            self.successor[source] = -1
        self.remaining += face.length
        self.used ^= face.edge_mask

    def solve(self, starts: list[int]) -> tuple[list[int] | None, int]:
        # Each frame tries possible faces for one uncovered dart. Explicit frames
        # also allow embeddings with more faces than Python's recursion limit.
        frames = [iter(starts)]
        chosen = []
        calls = 0
        while frames:
            for i in frames[-1]:
                calls += 1
                if not self.add(self.cycles[i]):
                    continue
                chosen.append(i)
                if len(chosen) == self.target and self.used == self.full_mask:
                    for index in reversed(chosen):
                        self.remove(self.cycles[index])
                    return chosen, calls
                frames.append(iter(self.candidates(self.target - len(chosen))))
                break
            else:
                frames.pop()
                if chosen:
                    self.remove(self.cycles[chosen.pop()])
        return None, calls


_worker_search = None


def _init_worker(graph, cycles, target):
    global _worker_search
    _worker_search = CoverSearch(graph, cycles, target)


def _solve_start(i):
    assert _worker_search is not None
    return _worker_search.solve([i])


def solve_cover(
    graph: Graph, cycles: list[Cycle], target: int, jobs: int
) -> tuple[list[int] | None, int]:
    search = CoverSearch(graph, cycles, target)
    starts = search.candidates(target)
    if jobs <= 1 or len(starts) < PARALLEL_MIN_STARTS:
        return search.solve(starts)
    context = mp.get_context("fork" if hasattr(os, "fork") else "spawn")
    calls = 0
    with context.Pool(
        min(jobs, len(starts)),
        initializer=_init_worker,
        initargs=(graph, cycles, target),
    ) as pool:
        for solution, branch_calls in pool.imap_unordered(_solve_start, starts):
            calls += branch_calls
            if solution is not None:
                return solution, calls
    return None, calls


def find_embedding(
    graph: Graph, quiet: bool = False, jobs: int = 1
) -> tuple[int, list[Cycle], list[int], int]:
    """Find a minimum-genus rotation and return its face indices and search count."""
    seed = input_rotation(graph)
    euler = 2 + graph.edge_count - graph.vertex_count  # F + 2g
    upper = (euler - len(seed)) // 2
    # Trees, including K1 and K2, already have an optimal input rotation.
    if upper == 0:
        return 0, seed, list(range(len(seed))), 0

    # In a connected simple graph containing a cycle, a 2-dart face would
    # require a degree-one vertex at both endpoints; a 3-dart face is a triangle.
    neighbors = [set(row) for row in graph.adjacency]
    has_triangle = any(
        neighbors[u] & neighbors[v] for u, v in graph.directed_edges if u < v
    )
    shortest = 3 if has_triangle else 4
    darts = graph.directed_edge_count
    lower = max(0, (euler - darts // shortest + 1) // 2)
    generated = shortest - 1
    cycles = []
    calls = 0
    for genus in range(lower, upper):
        target = euler - 2 * genus
        # Each other face needs at least 'shortest' darts. Generate shorter
        # lengths first so a witness can finish the search before reaching this cap.
        cap = darts - (target - 1) * shortest
        for length in range(max(shortest, generated), cap + 1):
            if length > generated:
                batch = generate_cycles(graph, length)
                generated = length
                if not batch:
                    continue
                cycles.extend(batch)
                if not quiet:
                    print(
                        f"Found {len(batch)} cycles of length {length}.",
                        file=sys.stderr,
                    )
            if cycles and target * cycles[-1].length >= darts:
                if not quiet:
                    print(
                        f"Starting search for {target} faces (genus {genus}, "
                        f"max cycle length {length})...",
                        file=sys.stderr,
                    )
                solution, branch_calls = solve_cover(graph, cycles, target, jobs)
                calls += branch_calls
                if solution is not None:
                    return genus, cycles, solution, calls
    return upper, seed, list(range(len(seed))), calls


def write_solution(path, graph, genus, cycles, solution, calls):
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(
            f"Solution with {len(solution)} cycles (genus {genus}) "
            f"found in {calls} iterations:\n"
        )
        for i in solution:
            print(*(v + graph.start_index for v in cycles[i].vertices), file=handle)


def main() -> int:
    args = parse_args()
    start = perf_counter()
    graph = load_graph(args.adj, args.degree, args.start)
    if not args.quiet:
        print(
            f"Read {args.adj}: {graph.vertex_count} vertices, {graph.edge_count} edges.",
            file=sys.stderr,
        )
    genus, cycles, solution, calls = find_embedding(
        graph, quiet=args.quiet, jobs=args.jobs
    )
    write_solution(args.out, graph, genus, cycles, solution, calls)
    print(f"Found a solution! The genus is {genus}.")
    print(f"Wrote {len(solution)} cycles to {args.out}.")
    print(f"Iterations: {calls}. Runtime: {perf_counter() - start:.3f}s.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
