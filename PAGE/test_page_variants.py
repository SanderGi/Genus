#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Genus contributors
# SPDX-License-Identifier: GPL-2.0-only
"""Compare both Lean and both native searches with exhaustive rotation enumeration."""

import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from test_page_python import (
    check_witness,
    connected,
    exhaustive_genus,
    rows_for,
    write_input,
)


ROOT = Path(__file__).resolve().parent


class PageVariants(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run(["make", "page", "page_low_mem"], cwd=ROOT, check=True)

    def test_adjacency_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "graph.txt"
            env = dict(os.environ, ADJ=str(path), STDOUT="1", QUIET="1")
            for option in ("S", "DEG", "GLB"):
                env.pop(option, None)
            for binary in ("page", "page_low_mem"):
                path.write_text("3 2\n11\n10 12\n11\n")
                run = subprocess.run(
                    [ROOT / binary], env=env, text=True, capture_output=True, check=True
                )
                header, walk = run.stdout.splitlines()
                self.assertIn("1 cycles (genus 0)", header)
                check_witness(
                    self,
                    [[1], [0, 2], [1]],
                    [tuple(int(v) - 10 for v in walk.split())],
                    0,
                )
                for malformed in (
                    "3 2\n1 1\n0\n0\n",  # duplicate
                    "3 2\n1 2\n2\n1\n",  # asymmetric
                    "3 1\n1\n0\n\n",  # disconnected
                    "2 1\n1 0\n",  # missing row boundary
                ):
                    with self.subTest(binary=binary, graph=malformed):
                        path.write_text(malformed)
                        run = subprocess.run(
                            [ROOT / binary], env=env, capture_output=True
                        )
                        self.assertNotEqual(run.returncode, 0)
                        self.assertEqual(run.stdout, b"")

    def test_certificates(self):
        graphs = []
        for n in range(1, 5):
            edges = list(itertools.combinations(range(n), 2))
            for mask in range(1 << len(edges)):
                rows = rows_for(n, [e for i, e in enumerate(edges) if mask & (1 << i)])
                if connected(rows):
                    graphs.append(rows)
        graphs.extend(
            [
                rows_for(5, list(itertools.combinations(range(5), 2))),
                rows_for(6, list(itertools.product(range(3), range(3, 6)))),
                rows_for(6, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)]),
                # A planar K4 with a five-edge tail needs a 13-dart face on 11 edges.
                rows_for(
                    9,
                    [
                        *itertools.combinations(range(4), 2),
                        *zip(range(3, 8), range(4, 9)),
                    ],
                ),
                rows_for(6, [*itertools.combinations(range(5), 2), (4, 5)]),
            ]
        )
        genera = [exhaustive_genus(rows) for rows in graphs]
        with tempfile.TemporaryDirectory() as tmp:
            files = [Path(tmp) / f"graph-{i}.txt" for i in range(len(graphs))]
            for rows, path in zip(graphs, files):
                write_input(path, rows)
            for mode, binary in [
                ("materialized", "page"),
                ("low-memory", "page_low_mem"),
            ]:
                command = [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    "lean/RunPage.lean",
                    mode,
                    *files,
                ]
                run = subprocess.run(
                    command, cwd=ROOT, text=True, capture_output=True, check=True
                )
                records = [json.loads(line) for line in run.stdout.splitlines()]
                self.assertEqual(len(records), len(files))
                env = dict(os.environ, STDOUT="1", S="0", QUIET="1", PAGE_JOBS="1")
                for option in ("GLB", "DEG"):
                    env.pop(option, None)
                for rows, genus, path, record in zip(graphs, genera, files, records):
                    with self.subTest(mode=mode, graph=path.name):
                        self.assertEqual(record["genus"], genus)
                        check_witness(
                            self, rows, list(map(tuple, record["faces"])), genus
                        )
                        run = subprocess.run(
                            [ROOT / binary],
                            env=dict(env, ADJ=str(path)),
                            text=True,
                            capture_output=True,
                            check=True,
                        )
                        header, *walks = run.stdout.strip().splitlines()
                        match = re.fullmatch(
                            r"Solution with (\d+) cycles \(genus (\d+)\).*", header
                        )
                        self.assertIsNotNone(match, header)
                        self.assertEqual(
                            (len(walks), genus), tuple(map(int, match.groups()))
                        )
                        check_witness(
                            self,
                            rows,
                            [tuple(map(int, w.split())) for w in walks],
                            genus,
                        )


if __name__ == "__main__":
    unittest.main()
