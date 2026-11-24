"""Compare both native solvers with the Lean solver on the same multicode stream."""

import json
import os
from itertools import combinations
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_c_solvers import K33, ROOT, check_embedding, multicode


class LeanComparison(unittest.TestCase):
    def test_witnesses(self):
        graphs = [
            (1, [], 0),
            (2, [(1, 2)], 0),
            (4, [(1, 2), (2, 3), (1, 3), (3, 4)], 0),
            (4, list(combinations(range(1, 5), 2)), 0),
            (6, K33, 1),
            (5, list(combinations(range(1, 6), 2)), 1),
        ]
        data = b"".join(multicode(n, edges) for n, edges, _ in graphs)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "graphs.mc"
            path.write_bytes(data)
            result = subprocess.run(
                ["lake", "env", "lean", "--run", "lean/RunMultiGenus.lean", str(path)],
                cwd=ROOT, capture_output=True, text=True, check=True,
            )
        answers = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(answers), len(graphs))
        for (n, edges, expected), answer in zip(graphs, answers):
            self.assertEqual(answer["genus"], expected)
            self.assertEqual(len(answer["rotation"]), n)
            rows = bytes([n]) + b"".join(bytes([v + 1 for v in row] + [0])
                                          for row in answer["rotation"])
            self.assertEqual(check_embedding(self, rows, n, edges, expected), b"")

        subprocess.run(["make", "multi_genus", "multi_genus_parallel"], cwd=ROOT, check=True)
        for name in ["multi_genus", "multi_genus_parallel"]:
            with self.subTest(solver=name):
                binary = subprocess.run(
                    [ROOT / name, "w"], input=data, capture_output=True, check=True,
                    env=dict(os.environ, MULTI_GENUS_THREADS="2", MULTI_GENUS_SPLIT_DEPTH="1"),
                )
                rotations = binary.stdout
                for (n, edges, _), answer in zip(graphs, answers):
                    rotations = check_embedding(self, rotations, n, edges, answer["genus"])
                self.assertEqual(rotations, b"")


if __name__ == "__main__":
    unittest.main()
