#!/usr/bin/env python3
"""Regressions for the pure-Python PAGE search and its vertex-walk certificates."""

import itertools
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from collections import Counter
from unittest.mock import patch

if __package__:
    from . import page
else:
    import page


def rows_for(n, edges):
    rows = [[] for _ in range(n)]
    for u, v in edges:
        rows[u].append(v)
        rows[v].append(u)
    return rows


def write_input(path, rows, start=0):
    width = max(map(len, rows))
    with path.open("w") as handle:
        print(len(rows), sum(map(len, rows)) // 2, file=handle)
        for row in rows:
            print(
                *([v + start for v in row] + [65535] * (width - len(row))), file=handle
            )
    return width


def connected(rows):
    seen = {0}
    for _ in rows:
        seen.update(v for u in tuple(seen) for v in rows[u])
    return len(seen) == len(rows)


def exhaustive_genus(rows):
    """Independent oracle: enumerate cyclic orders, fixing the first neighbor in each row."""
    if len(rows) == 1:
        return 0
    orders = [
        [(row[0],) + tail for tail in itertools.permutations(row[1:])] for row in rows
    ]
    max_faces = 0
    for rotation in itertools.product(*orders):
        next_dart = {
            (v, u): (u, row[(i + 1) % len(row)])
            for u, row in enumerate(rotation)
            for i, v in enumerate(row)
        }
        count = 0
        while next_dart:
            dart = next(iter(next_dart))
            count += 1
            while dart in next_dart:
                dart = next_dart.pop(dart)
        max_faces = max(max_faces, count)
    return (2 - len(rows) + sum(map(len, rows)) // 2 - max_faces) // 2


def check_witness(test, rows, walks, genus):
    if len(rows) == 1:
        test.assertEqual((walks, genus), ([(0,)], 0))
        return
    darts = Counter((u, v) for u, row in enumerate(rows) for v in row)
    used = Counter()
    rotation = [{} for _ in rows]
    for walk in walks:
        test.assertGreaterEqual(len(walk), 3)
        test.assertEqual(walk[-1], walk[0])
        used.update(zip(walk, walk[1:]))
        for i, u in enumerate(walk[:-1]):
            before, after = walk[i - 1] if i else walk[-2], walk[i + 1]
            rotation[u][before] = after
    test.assertEqual(used, darts)
    for row, successor in zip(rows, rotation):
        v = row[0]
        visited = set()
        while v not in visited:
            visited.add(v)
            v = successor[v]
        test.assertEqual((v, visited), (row[0], set(row)))
    test.assertEqual(len(rows) - len(darts) // 2 + len(walks), 2 - 2 * genus)


class PagePythonTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.path = Path(directory.name) / "graph.txt"

    def graph(self, rows):
        width = write_input(self.path, rows)
        return page.load_graph(str(self.path), width, 0)

    def solve(self, rows, expected, jobs=1):
        genus, cycles, chosen, calls = page.find_embedding(
            self.graph(rows), quiet=True, jobs=jobs
        )
        self.assertEqual(genus, expected)
        walks = [cycles[i].vertices for i in chosen]
        check_witness(self, rows, walks, genus)
        return walks, calls

    def test_low_degrees_and_cut_edges(self):
        self.solve([[]], 0)
        self.solve([[1], [0]], 0)
        path = rows_for(1050, [(v, v + 1) for v in range(1049)])
        faces, _ = self.solve(path, 0)
        self.assertEqual(len(faces[0]) - 1, 2098)
        tetrahedron = list(itertools.combinations(range(4), 2))
        for n, extra in [
            (5, [(0, 4)]),
            (6, [(0, 4), (4, 5), (0, 5)]),
            (8, [(a + 4, b + 4) for a, b in tetrahedron] + [(0, 4)]),
        ]:
            with self.subTest(n=n):
                faces, calls = self.solve(rows_for(n, tetrahedron + extra), 0)
                self.assertGreater(calls, 0)
                self.assertTrue(any(len(set(w[:-1])) < len(w) - 1 for w in faces))
                if n != 6:
                    # The two orientations of the bridge occur in the same facial walk.
                    self.assertTrue(
                        any({(0, 4), (4, 0)} <= set(zip(w, w[1:])) for w in faces)
                    )

    def test_positive_genus(self):
        for rows in [
            rows_for(5, itertools.combinations(range(5), 2)),
            rows_for(6, itertools.product(range(3), range(3, 6))),
            rows_for(7, itertools.combinations(range(7), 2)),
        ]:
            with self.subTest(n=len(rows)):
                self.solve(rows, 1)

    def test_shortest_walk_bounds_face_target(self):
        path = Path(__file__).with_name("adjacency_lists") / "3-7-cage.txt"
        graph = page.load_graph(str(path), 3, 0)
        solve_cover = page.solve_cover

        def bounded_search(graph, cycles, target, jobs):
            # 72 darts and girth seven allow at most ten faces. Fail before
            # searching if a weaker bound admits the impossible genus 0 or 1.
            self.assertLessEqual(target, 10)
            return solve_cover(graph, cycles, target, jobs)

        with patch.object(page, "solve_cover", bounded_search):
            genus, cycles, chosen, _ = page.find_embedding(graph, quiet=True)
        self.assertEqual(genus, 2)
        check_witness(
            self, graph.adjacency, [cycles[i].vertices for i in chosen], genus
        )

    def test_failed_lower_genus_and_bridged_nonplanar_core(self):
        # The seed has genus two. One genus-zero attempt must fail before
        # PAGE finds a genus-one cover with a turn at the pendant vertex.
        edges = list(itertools.combinations(range(5), 2)) + [(0, 5)]
        rows = rows_for(6, edges)
        self.assertEqual(len(page.input_rotation(self.graph(rows))), 3)
        faces, calls = self.solve(rows, 1)
        self.assertGreater(calls, 0)
        self.assertTrue(any({(0, 5), (5, 0)} <= set(zip(w, w[1:])) for w in faces))
        self.solve(rows_for(10, itertools.product(range(3), range(3, 10))), 2)

    def test_no_split_rotation(self):
        # The facial triangles of two separate tetrahedra cover every dart after
        # identifying vertex 0. Their two disjoint rotations at 0 cannot be glued.
        blocks = [(0, 1, 2, 3), (0, 4, 5, 6)]
        graph = self.graph(
            rows_for(
                7, [e for block in blocks for e in itertools.combinations(block, 2)]
            )
        )
        candidates = page.generate_cycles(graph, 3)
        solution, _ = page.solve_cover(graph, candidates, 8, 1)
        self.assertIsNone(solution)

    def test_parallel_search(self):
        rows = rows_for(4, itertools.combinations(range(4), 2))
        with patch.object(page, "PARALLEL_MIN_STARTS", 1):
            _, calls = self.solve(rows, 0, jobs=2)
        self.assertGreater(calls, 0)

    def test_against_all_rotations(self):
        # Every connected labelled graph through order five, including all ties.
        for n in range(1, 6):
            pairs = list(itertools.combinations(range(n), 2))
            for mask in range(1 << len(pairs)):
                rows = rows_for(n, (e for j, e in enumerate(pairs) if mask & (1 << j)))
                if connected(rows):
                    with self.subTest(n=n, mask=mask):
                        self.solve(rows, exhaustive_genus(rows))

    def test_cli_and_output(self):
        rows = rows_for(4, itertools.combinations(range(4), 2))
        width = write_input(self.path, rows, start=1)
        out = self.path.with_suffix(".out")
        env = dict(
            os.environ,
            S="1",
            DEG=str(width),
            ADJ=str(self.path),
            OUT=str(out),
            PAGE_JOBS="1",
        )
        script = Path(__file__).with_name("page.py")
        run = subprocess.run(
            [sys.executable, str(script), "--quiet"],
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("The genus is 0.", run.stdout)
        self.assertEqual(run.stderr, "")
        header, *lines = out.read_text().splitlines()
        self.assertRegex(
            header, r"^Solution with 4 cycles \(genus 0\) found in \d+ iterations:$"
        )
        check_witness(
            self, rows, [tuple(int(v) - 1 for v in line.split()) for line in lines], 0
        )
        self.path.write_text("1 0\n")
        subprocess.run(
            [
                sys.executable,
                str(script),
                "--adj",
                str(self.path),
                "-s",
                "0",
                "-d",
                "0",
                "-j",
                "1",
                "--out",
                str(out),
                "--quiet",
            ],
            capture_output=True,
            check=True,
        )
        self.assertEqual(out.read_text().splitlines()[1:], ["0"])

    def test_reject_malformed_graphs(self):
        for data, width in [
            ("2 1\n1\n1\n", 1),
            ("2 2\n1 1\n0 0\n", 2),
            ("4 2\n1\n0\n3\n2\n", 1),
            ("2 1\n2\n0\n", 1),
            ("3 2\n1 2\n2 65535\n0 65535\n", 2),
        ]:
            with self.subTest(data=data):
                self.path.write_text(data)
                with self.assertRaises(SystemExit):
                    page.load_graph(str(self.path), width, 0)


if __name__ == "__main__":
    unittest.main()
