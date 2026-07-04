# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

import unittest

import graph_genus as gg

import re
from pathlib import Path

K4 = [[1, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 2]]
K33 = [[3, 4, 5], [3, 4, 5], [3, 4, 5], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
K8 = [
    [1, 2, 3, 4, 5, 6, 7],
    [0, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 4, 5, 6, 7],
    [0, 1, 2, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 6, 7],
    [0, 1, 2, 3, 4, 6, 7],
    [0, 1, 2, 3, 4, 5, 7],
    [0, 1, 2, 3, 4, 5, 6],
]


class GraphGenusPackageTests(unittest.TestCase):
    def test_page_embedding(self):
        genus, rotation = gg.embed(K33)
        self.assertEqual(genus, 1)
        self.assertEqual([sorted(neighbors) for neighbors in rotation], K33)

    def test_multi_genus_embedding(self):
        genus, rotation = gg.embed(K33, algorithm="multi_genus")
        self.assertEqual(genus, 1)
        self.assertEqual([sorted(neighbors) for neighbors in rotation], K33)

    def test_none_computes_rotation_system_genus(self):
        genus, rotation = gg.embed(
            [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]],
            algorithm="none",
        )
        self.assertEqual(genus, 0)
        self.assertEqual(len(rotation), 4)

    def test_drawing_and_obj_outputs(self):
        self.assertIn("\\begin{tikzpicture}", gg.embed(K4, output_format="drawing")[1])
        self.assertTrue(gg.embed(K33, output_format="3D")[1].startswith("#"))  # type: ignore

    def test_3d_output_guard_for_higher_genus(self):
        with self.assertRaises(gg.GraphGenusError):
            gg.embed(K8, output_format="3D")

    def test_citations(self):
        self.assertEqual(gg.cite("multi_genus", "drawing").count("@"), 3)
        self.assertEqual(gg.cite("page", "rotation_system").count("@"), 1)

    def test_page_documented_performance_graphs(self):
        repo = Path(__file__).resolve().parents[1]
        docs_path = repo / "docs" / "practical_performance.md"

        rows = []
        for line in docs_path.read_text(encoding="utf-8").splitlines():
            match = re.search(r"\((\.\./PAGE/adjacency_lists/[^)]+)\)", line)
            if match is None:
                continue

            cells = [cell.strip() for cell in line.split("|")]
            if len(cells) >= 10:
                genus, page_time = cells[-4], cells[-3]
            elif len(cells) >= 6:
                genus, page_time = cells[-3], cells[-2]
            else:
                continue

            if not re.fullmatch(r"\d+", genus):
                continue
            if not re.fullmatch(r"\d+(?:\.\d+)?", page_time):
                continue

            graph_path = repo / match.group(1).replace("../", "")
            rows.append((graph_path, int(genus)))

        self.assertGreater(len(rows), 0)

        for graph_path, expected_genus in rows:
            with self.subTest(graph=graph_path.name):
                adjacency_list = self._read_page_adjacency_list(graph_path)
                genus, rotation = gg.embed(adjacency_list, algorithm="page")
                self.assertEqual(genus, expected_genus)
                self.assertEqual(
                    [sorted(neighbors) for neighbors in rotation],
                    [sorted(neighbors) for neighbors in adjacency_list],
                )

    @staticmethod
    def _read_page_adjacency_list(path):
        lines = path.read_text(encoding="utf-8").splitlines()
        n = int(lines[0].split()[0])
        raw_rows = [
            [int(value) for value in line.split() if int(value) != 65535]
            for line in lines[1 : n + 1]
        ]
        start = min((neighbor for row in raw_rows for neighbor in row), default=0)
        return [[neighbor - start for neighbor in row] for row in raw_rows]


if __name__ == "__main__":
    unittest.main()
