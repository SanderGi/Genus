#!/usr/bin/env python3
"""Resource regressions for the native streaming facial-walk search."""

import itertools
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import unittest

if os.name == "posix":
    import resource


class LowMemResourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        cls.work = Path(tmp.name)
        cls.binary = cls.work / (
            "page_low_mem.exe" if os.name == "nt" else "page_low_mem"
        )
        source = Path(__file__).with_name("page_low_mem.c")
        subprocess.run(
            [
                *shlex.split(os.environ.get("CC", "cc")),
                "-O2",
                "-std=c17",
                str(source),
                "-o",
                str(cls.binary),
            ],
            check=True,
        )

    def solve(self, n, edges, limits=None):
        rows = [[] for _ in range(n)]
        for u, v in edges:
            rows[u].append(v)
            rows[v].append(u)
        path = self.work / "graph.txt"
        with path.open("w") as stream:
            print(n, len(edges), file=stream)
            for row in rows:
                print(*sorted(row), file=stream)
        env = dict(os.environ, ADJ=str(path), QUIET="1", STDOUT="1")
        for key in ("DEG", "S", "GLB"):
            env.pop(key, None)
        result = subprocess.run(
            [str(self.binary)],
            env=env,
            capture_output=True,
            text=True,
            preexec_fn=limits,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        header, *lines = result.stdout.splitlines()
        match = re.fullmatch(
            r"Solution with (\d+) cycles \(genus 0\) found in (\d+) iterations:", header
        )
        self.assertIsNotNone(match, header)
        self.assertEqual(int(match[1]), len(lines))
        expected = {(u, v) for u, row in enumerate(rows) for v in row}
        for line in lines:
            walk = [int(label) for label in line.split()]
            self.assertEqual(walk[0], walk[-1])
            for dart in zip(walk, walk[1:]):
                expected.remove(dart)
        self.assertFalse(expected)
        return len(lines), int(match[2])

    def test_sparse_high_degree_tree_with_long_path(self):
        # Both the degree and the diameter grow, but a tree has only 2(n-1) darts.
        n = 16001
        edges = [(0, v) for v in range(1, 8001)] + [
            (v, v + 1) for v in range(8000, n - 1)
        ]

        def limit_memory():
            soft, hard = resource.getrlimit(resource.RLIMIT_AS)
            limit = 128 * 1024 * 1024
            if soft != resource.RLIM_INFINITY:
                limit = min(limit, soft)
            resource.setrlimit(resource.RLIMIT_AS, (limit, hard))

        self.assertEqual(
            self.solve(n, edges, limit_memory if sys.platform == "linux" else None),
            (1, 0),
        )

    @unittest.skipUnless(os.name == "posix", "requires POSIX stack resource limits")
    def test_deep_face_search_with_small_stack(self):
        # Sorted K4 has positive genus in its input order. Subdivide one edge so finding
        # the planar certificate actually enters the search and follows a long facial path.
        n = 1603
        edges = [e for e in itertools.combinations(range(4), 2) if e != (0, 1)]
        path = [0, *range(4, n), 1]
        edges.extend(zip(path, path[1:]))

        def small_stack():
            _, hard = resource.getrlimit(resource.RLIMIT_STACK)
            resource.setrlimit(resource.RLIMIT_STACK, (256 * 1024, hard))

        faces, calls = self.solve(n, edges, small_stack)
        self.assertEqual(faces, 4)
        self.assertGreater(calls, 0)


if __name__ == "__main__":
    unittest.main()
