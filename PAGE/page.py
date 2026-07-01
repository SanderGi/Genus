#!/usr/bin/env python3
"""A compact pure-Python implementation of PAGE.

The C implementation in page.c is tuned for large searches, parallel start
branches, and several specialized bounds.  This file keeps the same central
algorithm but aims to be readable:

1. Generate candidate facial walks, length by length.
2. Treat an embedding as an exact cover of the directed edges by those walks.
3. Backtrack on the most constrained uncovered directed edge.
4. Enforce orientability by forbidding both directions of a local transition.

Input defaults match page.c's environment variables:
    S=0 DEG=3 ADJ=adjacency_lists/k3-3.txt python3 page.py
"""

from __future__ import annotations

import argparse
import math
import multiprocessing as mp
import os
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from functools import lru_cache
from time import perf_counter

MAX_VERTEX = 65535
START_CYCLE_LENGTH = 3
START_BRANCH_PROCESS_CAP = 8
PARALLEL_MIN_STARTS = 8

_PARALLEL_STATE = None


@dataclass
class Graph:
    adjacency: list[list[int]]
    start_index: int
    degree: int
    edge_count: int
    vertex_degrees: list[int]
    directed_edges: list[tuple[int, int]]
    directed_edge_id: dict[tuple[int, int], int]
    neighbor_index: dict[tuple[int, int], int]

    @property
    def vertex_count(self) -> int:
        return len(self.adjacency)

    @property
    def directed_edge_count(self) -> int:
        return len(self.directed_edges)


@dataclass(frozen=True)
class Cycle:
    vertices: tuple[int, ...]  # closed: vertices[-1] == vertices[0]
    edges: tuple[int, ...]
    edge_mask: int
    vertex_counts: tuple[tuple[int, int], ...]
    transitions: tuple[tuple[int, int, int], ...]
    reverse_transitions: tuple[tuple[int, int, int], ...]
    transition_mask: int
    reverse_transition_mask: int

    @property
    def length(self) -> int:
        return len(self.edges)


@dataclass
class SearchStats:
    calls: int = 0
    best_fit: int = 0


@dataclass
class PageSearch:
    graph: Graph
    cycles: list[Cycle]
    cycles_by_edge: dict[int, list[int]]
    available_lengths: set[int]
    target_faces: int
    shortest_length: int
    max_length: int
    required_length: int
    cubic_exact_cover: bool
    used_cycles: list[bool] = field(init=False)
    used_edge_mask: int = field(init=False)
    vertex_uses: list[int] = field(init=False)
    used_transition_mask: int = field(init=False)
    rotation_next: list[int] = field(init=False)
    rotation_prev: list[int] = field(init=False)
    rotation_pair_count: list[int] = field(init=False)
    num_edges_remaining: int = field(init=False)
    required_remaining: int = field(init=False)
    stats: SearchStats = field(default_factory=SearchStats)
    solution: list[int] | None = None
    _ordered_lengths: tuple[int, ...] = field(init=False, repr=False)
    _length_cache: dict[tuple[int, int, int], bool] = field(init=False, repr=False)

    def __post_init__(self) -> None:
        self.used_cycles = [False] * len(self.cycles)
        self.used_edge_mask = 0
        self.vertex_uses = [0] * self.graph.vertex_count
        self.used_transition_mask = 0
        rotation_slots = self.graph.vertex_count * self.graph.degree
        self.rotation_next = [MAX_VERTEX] * rotation_slots
        self.rotation_prev = [MAX_VERTEX] * rotation_slots
        self.rotation_pair_count = [0] * self.graph.vertex_count
        self.num_edges_remaining = self.graph.directed_edge_count
        self.required_remaining = 1 if self.required_length else 0
        self._ordered_lengths = tuple(sorted(self.available_lengths))
        self._length_cache = {}

    def length_possible(
        self, total_length: int, cycles_left: int, required_left: int = 0
    ) -> bool:
        key = (total_length, cycles_left, required_left)
        cached = self._length_cache.get(key)
        if cached is not None:
            return cached
        if cycles_left == 0:
            possible = total_length == 0 and required_left == 0
        elif required_left > cycles_left:
            possible = False
        elif total_length < cycles_left * self.shortest_length:
            possible = False
        elif total_length > cycles_left * self.max_length:
            possible = False
        else:
            possible = False
            for length in self._ordered_lengths:
                if length > total_length:
                    break
                next_required = required_left
                if next_required and length == self.required_length:
                    next_required -= 1
                if self.length_possible(
                    total_length - length, cycles_left - 1, next_required
                ):
                    possible = True
                    break
        self._length_cache[key] = possible
        return possible

    def candidate_length_possible(self, cycle: Cycle, cycles_left: int) -> bool:
        remaining = self.num_edges_remaining - cycle.length
        if remaining < 0:
            return False
        required_left = max(0, self.required_remaining)
        if required_left and cycle.length == self.required_length:
            required_left -= 1
        if cycles_left == 1:
            return remaining == 0 and required_left == 0
        return self.length_possible(remaining, cycles_left - 1, required_left)

    def cycle_vertex_uses_fit(self, cycle: Cycle) -> bool:
        for vertex, count in cycle.vertex_counts:
            if self.vertex_uses[vertex] + count > self.graph.vertex_degrees[vertex]:
                return False
        return True

    def cycle_transitions_good(self, cycle: Cycle) -> bool:
        return (cycle.reverse_transition_mask & self.used_transition_mask) == 0

    def add_rotation_transition(
        self, center: int, prev_index: int, next_index: int
    ) -> bool:
        if self.graph.degree <= 5:
            return True
        source = center * self.graph.degree + prev_index
        target = center * self.graph.degree + next_index
        if (
            prev_index == next_index
            or self.rotation_next[source] != MAX_VERTEX
            or self.rotation_prev[target] != MAX_VERTEX
        ):
            return False

        component_size = 1
        closes_component = False
        cursor = next_index
        while self.rotation_next[center * self.graph.degree + cursor] != MAX_VERTEX:
            cursor = self.rotation_next[center * self.graph.degree + cursor]
            component_size += 1
            if cursor == prev_index:
                closes_component = True
                break
            if component_size > self.graph.vertex_degrees[center]:
                return False

        if closes_component and component_size < self.graph.vertex_degrees[center]:
            return False
        if (
            not closes_component
            and self.rotation_pair_count[center] + 1
            == self.graph.vertex_degrees[center]
        ):
            return False

        self.rotation_next[source] = next_index
        self.rotation_prev[target] = prev_index
        self.rotation_pair_count[center] += 1
        return True

    def remove_rotation_transition(
        self, center: int, prev_index: int, next_index: int
    ) -> None:
        if self.graph.degree <= 5:
            return
        source = center * self.graph.degree + prev_index
        target = center * self.graph.degree + next_index
        self.rotation_next[source] = MAX_VERTEX
        self.rotation_prev[target] = MAX_VERTEX
        self.rotation_pair_count[center] -= 1

    def try_add_rotation_system(self, cycle: Cycle) -> bool:
        if self.graph.degree <= 5:
            return True
        added: list[tuple[int, int, int]] = []
        for transition in cycle.transitions:
            if not self.add_rotation_transition(*transition):
                for undo in reversed(added):
                    self.remove_rotation_transition(*undo)
                return False
            added.append(transition)
        return True

    def remove_rotation_system(self, cycle: Cycle) -> None:
        if self.graph.degree <= 5:
            return
        for transition in cycle.transitions:
            self.remove_rotation_transition(*transition)

    def candidate_usable(self, cycle_index: int, cycles_left: int) -> bool:
        if self.used_cycles[cycle_index]:
            return False
        cycle = self.cycles[cycle_index]
        if cycle.edge_mask & self.used_edge_mask:
            return False
        if not self.candidate_length_possible(cycle, cycles_left):
            return False
        if not self.cubic_exact_cover and not self.cycle_vertex_uses_fit(cycle):
            return False
        return self.cycle_transitions_good(cycle)

    def choose_edge_column(self, cycles_left: int) -> tuple[int, list[int]] | None:
        best_edge = -1
        best_options = math.inf
        best_pressure = -1

        for edge_id in range(self.graph.directed_edge_count):
            if self.used_edge_mask & (1 << edge_id):
                continue
            candidates = []
            u, v = self.graph.directed_edges[edge_id]
            pressure = self.vertex_uses[u] + self.vertex_uses[v]
            for cycle_index in self.cycles_by_edge.get(edge_id, ()):
                if self.candidate_usable(cycle_index, cycles_left):
                    candidates.append(cycle_index)
                    if len(candidates) > best_options:
                        break
            options = len(candidates)
            if options < best_options or (
                options == best_options and pressure > best_pressure
            ):
                best_edge = edge_id
                best_options = options
                best_pressure = pressure
                if best_options == 0:
                    break

        if best_edge < 0:
            return None
        best_candidates = [
            cycle_index
            for cycle_index in self.cycles_by_edge.get(best_edge, ())
            if self.candidate_usable(cycle_index, cycles_left)
        ]
        best_candidates.sort(key=lambda i: self.cycles[i].length, reverse=True)
        return best_edge, best_candidates

    def choose_start_cycles(self) -> list[int]:
        best: list[int] | None = None
        for edge_id in range(self.graph.directed_edge_count):
            row = self.cycles_by_edge.get(edge_id, [])
            if best is None or len(row) < len(best):
                best = row
                if not best:
                    break
        if best is None:
            return []

        if self.required_length:
            required_starts = [
                index
                for index, cycle in enumerate(self.cycles)
                if cycle.length == self.required_length
            ]
            if required_starts and len(required_starts) <= len(best):
                best = required_starts

        def cycle_key(cycle_index: int) -> tuple[int, int]:
            cycle = self.cycles[cycle_index]
            scarcity = sum(
                len(self.cycles_by_edge.get(edge_id, ())) for edge_id in cycle.edges
            )
            return (scarcity, cycle.length)

        return sorted(best, key=cycle_key)

    def solve(self) -> bool:
        for cycle_index in self.choose_start_cycles():
            if self.solve_from_start(cycle_index):
                return True
        return False

    def solve_from_start(self, cycle_index: int) -> bool:
        if not self.candidate_usable(cycle_index, self.target_faces):
            return False
        if not self.add_cycle(cycle_index):
            return False
        if self.target_faces == 1:
            if self.final_state_valid():
                self.solution = [cycle_index]
                return True
        elif self.search(self.target_faces - 1):
            return True
        self.remove_cycle(cycle_index)
        return False

    def add_cycle(self, cycle_index: int) -> bool:
        cycle = self.cycles[cycle_index]
        if not self.try_add_rotation_system(cycle):
            return False
        self.used_cycles[cycle_index] = True
        self.used_edge_mask |= cycle.edge_mask
        self.num_edges_remaining -= cycle.length
        for vertex, count in cycle.vertex_counts:
            self.vertex_uses[vertex] += count
        self.used_transition_mask |= cycle.transition_mask
        if self.required_length and cycle.length == self.required_length:
            self.required_remaining -= 1
        return True

    def remove_cycle(self, cycle_index: int) -> None:
        cycle = self.cycles[cycle_index]
        if self.required_length and cycle.length == self.required_length:
            self.required_remaining += 1
        self.used_transition_mask &= ~cycle.transition_mask
        for vertex, count in cycle.vertex_counts:
            self.vertex_uses[vertex] -= count
        self.used_edge_mask &= ~cycle.edge_mask
        self.num_edges_remaining += cycle.length
        self.used_cycles[cycle_index] = False
        self.remove_rotation_system(cycle)

    def final_state_valid(self) -> bool:
        if self.num_edges_remaining != 0:
            return False
        if self.required_remaining > 0:
            return False
        if self.cubic_exact_cover:
            return True
        return all(
            self.vertex_uses[v] == self.graph.vertex_degrees[v]
            for v in range(self.graph.vertex_count)
        )

    def search(self, cycles_left: int) -> bool:
        self.stats.calls += 1
        used_count = self.target_faces - cycles_left
        if used_count > self.stats.best_fit and self.final_state_valid():
            self.stats.best_fit = used_count

        column = self.choose_edge_column(cycles_left)
        if column is None:
            return False
        _, candidates = column
        if not candidates:
            return False

        for cycle_index in candidates:
            if not self.add_cycle(cycle_index):
                continue
            if cycles_left == 1:
                if self.final_state_valid():
                    self.solution = [
                        i for i, used in enumerate(self.used_cycles) if used
                    ]
                    return True
            elif self.search(cycles_left - 1):
                return True
            self.remove_cycle(cycle_index)
        return False


def _new_search(
    graph: Graph,
    cycles: list[Cycle],
    cycles_by_edge: dict[int, list[int]],
    available_lengths: set[int],
    target_faces: int,
    shortest_length: int,
    max_length: int,
    required_length: int,
    cubic_exact_cover: bool,
) -> PageSearch:
    return PageSearch(
        graph=graph,
        cycles=cycles,
        cycles_by_edge=cycles_by_edge,
        available_lengths=set(available_lengths),
        target_faces=target_faces,
        shortest_length=shortest_length,
        max_length=max_length,
        required_length=required_length,
        cubic_exact_cover=cubic_exact_cover,
    )


def _parallel_init(
    graph: Graph,
    cycles: list[Cycle],
    cycles_by_edge: dict[int, list[int]],
    available_lengths: set[int],
    target_faces: int,
    shortest_length: int,
    max_length: int,
    required_length: int,
    cubic_exact_cover: bool,
) -> None:
    global _PARALLEL_STATE
    _PARALLEL_STATE = (
        graph,
        cycles,
        cycles_by_edge,
        available_lengths,
        target_faces,
        shortest_length,
        max_length,
        required_length,
        cubic_exact_cover,
    )


def _parallel_solve_start(cycle_index: int) -> tuple[list[int] | None, int]:
    if _PARALLEL_STATE is None:
        raise RuntimeError("parallel PAGE worker was not initialized")
    search = _new_search(*_PARALLEL_STATE)
    if search.solve_from_start(cycle_index):
        assert search.solution is not None
        return search.solution, search.stats.calls
    return None, search.stats.calls


def solve_search(
    graph: Graph,
    cycles: list[Cycle],
    cycles_by_edge: dict[int, list[int]],
    available_lengths: set[int],
    target_faces: int,
    shortest_length: int,
    max_length: int,
    required_length: int,
    cubic_exact_cover: bool,
    jobs: int,
) -> tuple[list[int] | None, int]:
    search = _new_search(
        graph,
        cycles,
        cycles_by_edge,
        available_lengths,
        target_faces,
        shortest_length,
        max_length,
        required_length,
        cubic_exact_cover,
    )
    start_cycles = search.choose_start_cycles()
    if jobs <= 1 or len(start_cycles) < PARALLEL_MIN_STARTS:
        return (
            (search.solution, search.stats.calls)
            if search.solve()
            else (None, search.stats.calls)
        )

    context_name = "fork" if hasattr(os, "fork") else "spawn"
    context = mp.get_context(context_name)
    total_calls = 0
    with context.Pool(
        processes=max(1, min(jobs, len(start_cycles))),
        initializer=_parallel_init,
        initargs=(
            graph,
            cycles,
            cycles_by_edge,
            available_lengths,
            target_faces,
            shortest_length,
            max_length,
            required_length,
            cubic_exact_cover,
        ),
    ) as pool:
        for solution, calls in pool.imap_unordered(
            _parallel_solve_start, start_cycles, chunksize=1
        ):
            total_calls += calls
            if solution is not None:
                pool.terminate()
                return solution, total_calls
    return None, total_calls


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Pure-Python PAGE implementation")
    parser.add_argument("--adj", default=os.environ.get("ADJ"))
    parser.add_argument(
        "--degree", "-d", type=int, default=int(os.environ.get("DEG", "3"))
    )
    parser.add_argument(
        "--start", "-s", type=int, default=int(os.environ.get("S", "0"))
    )
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


def load_graph(path: str, degree: int, start_index: int) -> Graph:
    if not path:
        raise SystemExit("No adjacency list supplied. Use --adj or ADJ=...")
    with open(path, "r", encoding="utf-8") as handle:
        values = [int(x) for x in handle.read().split()]
    if len(values) < 2:
        raise SystemExit(f"{path}: expected vertex and edge counts")
    n, edge_count = values[0], values[1]
    raw = values[2:]
    expected = n * degree
    if len(raw) < expected:
        raise SystemExit(
            f"{path}: expected {expected} adjacency entries, found {len(raw)}"
        )

    adjacency: list[list[int]] = []
    vertex_degrees: list[int] = []
    for vertex in range(n):
        row = []
        for value in raw[vertex * degree : (vertex + 1) * degree]:
            neighbor = MAX_VERTEX if value == MAX_VERTEX else value - start_index
            row.append(neighbor)
        adjacency.append(row)
        vertex_degrees.append(sum(1 for neighbor in row if neighbor != MAX_VERTEX))

    directed_edges: list[tuple[int, int]] = []
    directed_edge_id: dict[tuple[int, int], int] = {}
    neighbor_index: dict[tuple[int, int], int] = {}
    for u, row in enumerate(adjacency):
        for slot, v in enumerate(row):
            if v == MAX_VERTEX:
                continue
            directed_edge_id[(u, v)] = len(directed_edges)
            neighbor_index[(u, v)] = slot
            directed_edges.append((u, v))

    if len(directed_edges) != 2 * edge_count:
        raise SystemExit(
            f"{path}: found {len(directed_edges)} directed edges, expected {2 * edge_count}"
        )

    return Graph(
        adjacency=adjacency,
        start_index=start_index,
        degree=degree,
        edge_count=edge_count,
        vertex_degrees=vertex_degrees,
        directed_edges=directed_edges,
        directed_edge_id=directed_edge_id,
        neighbor_index=neighbor_index,
    )


def path_has_reverse_transition(
    graph: Graph,
    path: tuple[int, ...],
    prev_vertex: int,
    center_vertex: int,
    next_vertex: int,
) -> bool:
    if graph.vertex_degrees[center_vertex] <= 2:
        return False
    for i in range(1, len(path) - 1):
        if (
            path[i - 1] == next_vertex
            and path[i] == center_vertex
            and path[i + 1] == prev_vertex
        ):
            return True
    return False


def make_cycle(graph: Graph, path: tuple[int, ...]) -> Cycle:
    closed = path + (path[0],)
    edges = tuple(
        graph.directed_edge_id[(closed[i], closed[i + 1])] for i in range(len(path))
    )
    edge_mask = 0
    for edge_id in edges:
        edge_mask |= 1 << edge_id
    counts = tuple(sorted(Counter(path).items()))
    transitions = []
    for i, center in enumerate(path):
        if graph.vertex_degrees[center] <= 2:
            continue
        prev_vertex = path[i - 1]
        next_vertex = path[(i + 1) % len(path)]
        transitions.append(
            (
                center,
                graph.neighbor_index[(center, prev_vertex)],
                graph.neighbor_index[(center, next_vertex)],
            )
        )
    reverse_transitions = tuple(
        (center, next_index, prev_index)
        for center, prev_index, next_index in transitions
    )
    transition_mask = 0
    reverse_transition_mask = 0
    for center, prev_index, next_index in transitions:
        transition_id = (center * graph.degree + prev_index) * graph.degree + next_index
        reverse_id = (center * graph.degree + next_index) * graph.degree + prev_index
        transition_mask |= 1 << transition_id
        reverse_transition_mask |= 1 << reverse_id
    return Cycle(
        closed,
        edges,
        edge_mask,
        counts,
        tuple(transitions),
        reverse_transitions,
        transition_mask,
        reverse_transition_mask,
    )


def generate_cycles(graph: Graph, cycle_length: int) -> list[Cycle]:
    cycles: list[Cycle] = []
    queue: list[tuple[int, ...]] = [(v,) for v in range(graph.vertex_count)]
    head = 0
    while head < len(queue):
        path = queue[head]
        head += 1
        last = path[-1]
        if len(path) == cycle_length:
            if path[0] not in graph.adjacency[last]:
                continue
            if path[1] == path[-1] or path[-2] == path[0]:
                continue
            if any(
                path[j] == path[-1] and path[j + 1] == path[0]
                for j in range(len(path) - 1)
            ):
                continue
            if path_has_reverse_transition(graph, path, path[-2], path[-1], path[0]):
                continue
            if path_has_reverse_transition(graph, path, path[-1], path[0], path[1]):
                continue
            cycles.append(make_cycle(graph, path))
            continue

        for neighbor in graph.adjacency[last]:
            if neighbor == MAX_VERTEX or neighbor < path[0]:  # type: ignore
                continue
            if len(path) >= 2 and neighbor == path[-2]:
                continue
            if any(
                path[j] == last and path[j + 1] == neighbor
                for j in range(len(path) - 1)
            ):
                continue
            if len(path) >= 2 and path_has_reverse_transition(
                graph, path, path[-2], last, neighbor
            ):
                continue
            queue.append(path + (neighbor,))
    return cycles


def index_cycles(cycles: list[Cycle]) -> dict[int, list[int]]:
    by_edge: dict[int, list[int]] = defaultdict(list)
    for index, cycle in enumerate(cycles):
        for edge_id in cycle.edges:
            by_edge[edge_id].append(index)
    return by_edge


def implied_faces_for_genus(genus: int, graph: Graph) -> int:
    return graph.edge_count - graph.vertex_count + 2 - 2 * genus


def genus_from_faces(faces: int, graph: Graph) -> int:
    return max(0, 1 - (faces - graph.edge_count + graph.vertex_count) // 2)


def genus_lower_bound_from_face_upper_bound(face_upper_bound: int, graph: Graph) -> int:
    numerator = graph.edge_count - graph.vertex_count + 2 - face_upper_bound
    return 0 if numerator <= 0 else (numerator + 1) // 2


def length_composition_info(
    total: int,
    count: int,
    lengths: set[int],
    shortest_length: int,
    required_length: int = 0,
) -> tuple[bool, int]:
    ordered = tuple(sorted(lengths))
    if not ordered:
        return False, 0
    if required_length and required_length not in lengths:
        return False, 0

    @lru_cache(maxsize=None)
    def dp(remaining_total: int, remaining_count: int, required: int) -> int | None:
        if remaining_count == 0:
            return 0 if remaining_total == 0 and required == 0 else None
        if required > remaining_count:
            return None
        if remaining_total < remaining_count * ordered[0]:
            return None
        if remaining_total > remaining_count * ordered[-1]:
            return None
        best: int | None = None
        for length in ordered:
            if length > remaining_total:
                break
            next_required = required
            if next_required and length == required_length:
                next_required -= 1
            suffix = dp(remaining_total - length, remaining_count - 1, next_required)
            if suffix is None:
                continue
            shortest_count = suffix + (1 if length == shortest_length else 0)
            if best is None or shortest_count < best:
                best = shortest_count
        return best

    result = dp(total, count, 1 if required_length else 0)
    return (result is not None, result or 0)


def length_composition_possible(
    total: int, count: int, lengths: set[int], required_length: int = 0
) -> bool:
    shortest = min(lengths) if lengths else 0
    return length_composition_info(total, count, lengths, shortest, required_length)[0]


def max_possible_fit_with_shortest_bound(
    edge_count: int,
    shortest_length: int,
    second_shortest_length: int,
    max_shortest_cycles: int,
    required_length: int,
) -> int:
    total_length = 2 * edge_count
    if shortest_length == 0 or required_length > total_length:
        return 0
    non_shortest_length = second_shortest_length
    if non_shortest_length == 0 or required_length < non_shortest_length:
        non_shortest_length = required_length
    remaining_length = total_length - required_length
    shortest_cycles_to_use = remaining_length // shortest_length
    shortest_cycles_to_use = min(shortest_cycles_to_use, max_shortest_cycles)
    remaining_length -= shortest_cycles_to_use * shortest_length
    return 1 + shortest_cycles_to_use + remaining_length // non_shortest_length


def find_embedding(
    graph: Graph, quiet: bool = False, jobs: int = 1
) -> tuple[int, list[Cycle], list[int], int]:
    cycles: list[Cycle] = []
    available_lengths: set[int] = set()
    shortest_length = 0
    second_shortest_length = 0
    num_shortest_cycles = 0
    max_shortest_cycles = 0
    genus_lower = genus_lower_bound_from_face_upper_bound(
        2 * graph.edge_count // 3, graph
    )
    genus_upper = genus_from_faces(1, graph)
    max_generated_length = START_CYCLE_LENGTH - 1
    last_searched_faces: int | None = None

    genus = genus_lower
    while genus <= genus_upper:
        target_faces = implied_faces_for_genus(genus, graph)
        if target_faces <= 0:
            genus += 1
            continue
        if (graph.edge_count - graph.vertex_count + 2 - target_faces) % 2 != 0:
            genus += 1
            continue

        while True:
            if shortest_length:
                max_needed = 2 * graph.edge_count - shortest_length * (target_faces - 1)
            else:
                max_needed = 2 * graph.edge_count
            if available_lengths:
                required_length = (
                    max_generated_length if last_searched_faces == target_faces else 0
                )
                length_possible, min_shortest_cycles = length_composition_info(
                    2 * graph.edge_count,
                    target_faces,
                    available_lengths,
                    shortest_length,
                    required_length,
                )
                if length_possible and min_shortest_cycles > max_shortest_cycles:
                    length_possible = False

                if length_possible:
                    cycles_by_edge = index_cycles(cycles)
                    if not quiet:
                        print(
                            f"Starting search for {target_faces} faces "
                            f"(genus {genus}, max cycle length {max_generated_length})...",
                            file=sys.stderr,
                        )
                    solution, calls = solve_search(
                        graph=graph,
                        cycles=cycles,
                        cycles_by_edge=cycles_by_edge,
                        available_lengths=available_lengths,
                        target_faces=target_faces,
                        shortest_length=shortest_length,
                        max_length=max_generated_length,
                        required_length=required_length,
                        cubic_exact_cover=all(d == 3 for d in graph.vertex_degrees),
                        jobs=jobs,
                    )
                    if solution is not None:
                        return genus, cycles, solution, calls

                last_searched_faces = target_faces
                future_fit_upper_bound = max_possible_fit_with_shortest_bound(
                    graph.edge_count,
                    shortest_length,
                    second_shortest_length,
                    max_shortest_cycles,
                    max_generated_length + 1,
                )
                future_genus_lower = genus_lower_bound_from_face_upper_bound(
                    future_fit_upper_bound, graph
                )
                if future_genus_lower > genus_lower:
                    genus_lower = future_genus_lower
                    if genus < genus_lower:
                        break

            if max_generated_length >= max_needed:
                break
            max_generated_length += 1
            new_cycles = generate_cycles(graph, max_generated_length)
            if not quiet:
                if new_cycles:
                    print(
                        f"Found {len(new_cycles)} cycles of length {max_generated_length}.",
                        file=sys.stderr,
                    )
                else:
                    print(
                        f"No cycles of length {max_generated_length} found. Skipping.",
                        file=sys.stderr,
                    )
            if not new_cycles:
                continue
            cycles.extend(new_cycles)
            available_lengths.add(max_generated_length)
            if shortest_length == 0:
                shortest_length = max_generated_length
                num_shortest_cycles = len(new_cycles)
                max_shortest_cycles = min(
                    num_shortest_cycles,
                    2 * graph.edge_count // shortest_length,
                )
                girth_face_bound = 2 * graph.edge_count // shortest_length
                genus_lower = max(
                    genus_lower,
                    genus_lower_bound_from_face_upper_bound(girth_face_bound, graph),
                )
                if genus < genus_lower:
                    break
            elif second_shortest_length == 0:
                second_shortest_length = max_generated_length

        if genus < genus_lower:
            genus = genus_lower
            continue
        genus += 1
    raise RuntimeError("No embedding found")


def write_solution(
    path: str,
    graph: Graph,
    genus: int,
    cycles: list[Cycle],
    solution: list[int],
    calls: int,
) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(
            f"Solution with {len(solution)} cycles (genus {genus}) found in {calls} iterations:\n"
        )
        for cycle_index in solution:
            handle.write(
                " ".join(
                    str(v + graph.start_index) for v in cycles[cycle_index].vertices
                )
            )
            handle.write("\n")


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
    elapsed = perf_counter() - start
    print(f"Found a solution! The genus is {genus}.")
    print(f"Wrote {len(solution)} cycles to {args.out}.")
    print(f"Iterations: {calls}. Runtime: {elapsed:.3f}s.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
