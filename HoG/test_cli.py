#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Focused command-line regression tests for HoG/genus."""

import subprocess
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
BINARY = HERE / "genus"


def graph6(num_vertices, edges):
    edges = {tuple(sorted(edge)) for edge in edges}
    bits = [
        int((left, right) in edges)
        for right in range(1, num_vertices)
        for left in range(right)
    ]
    bits.extend([0] * (-len(bits) % 6))
    if num_vertices <= 62:
        header = chr(num_vertices + 63)
    elif num_vertices <= 258047:
        header = "~" + "".join(
            chr(value + 63)
            for value in (
                num_vertices >> 12,
                (num_vertices >> 6) & 63,
                num_vertices & 63,
            )
        )
    else:
        raise ValueError("graph is too large for this test encoder")
    payload = "".join(
        chr(sum(bits[offset + bit] << (5 - bit) for bit in range(6)) + 63)
        for offset in range(0, len(bits), 6)
    )
    return (header + payload + "\n").encode()


def multicode(num_vertices, edges):
    neighbors = [[] for _ in range(num_vertices)]
    for left, right in edges:
        left, right = sorted((left, right))
        neighbors[left].append(right)
    result = bytearray([num_vertices])
    for vertex in range(num_vertices - 1):
        result.extend(neighbor + 1 for neighbor in sorted(neighbors[vertex]))
        result.append(0)
    return bytes(result)


def complete_edges(num_vertices):
    return {
        (left, right)
        for left in range(num_vertices)
        for right in range(left + 1, num_vertices)
    }


def complete_edges_on(vertices):
    return {
        (vertices[left], vertices[right])
        for left in range(len(vertices))
        for right in range(left + 1, len(vertices))
    }


def complete_bipartite_edges(left_vertices, right_vertices):
    return {
        (left, right)
        for left in left_vertices
        for right in right_vertices
    }


class GenusCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run(["make", "genus"], cwd=HERE, check=True)

    def run_genus(self, data, *arguments):
        return subprocess.run(
            [str(BINARY), *arguments],
            input=data,
            capture_output=True,
            timeout=15,
            check=False,
        )

    def test_graph6_stream_has_labeled_results_and_summary(self):
        data = graph6(4, complete_edges(4)) + graph6(5, complete_edges(5))
        result = self.run_genus(data, "-j", "2")
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 0\n", result.stdout.decode())
        self.assertIn("Graph 2 has genus 1\n", result.stdout.decode())
        self.assertRegex(
            result.stdout.decode(),
            r"Processed 2 graphs: 2 succeeded, 0 failed in \d+\.\d{3} seconds\.\n$",
        )

    def test_multicode_input(self):
        result = self.run_genus(
            multicode(5, complete_edges(5)),
            "--multicode",
            "--multi_genus-only",
            "-j",
            "1",
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 1", result.stdout.decode())

    def test_disconnected_graph_reports_error_and_stream_continues(self):
        disconnected = graph6(7, complete_edges(5))
        connected = graph6(5, complete_edges(5))
        result = self.run_genus(
            disconnected + connected, "--page-only", "-j", "1"
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn(
            "Graph 1 error: disconnected graphs are not supported.",
            result.stderr.decode(),
        )
        self.assertIn("Graph 2 has genus 1", result.stdout.decode())
        self.assertIn(
            "Processed 2 graphs: 1 succeeded, 1 failed", result.stdout.decode()
        )

    def test_only_flags_select_different_algorithms(self):
        cycle_edges = {(vertex, (vertex + 1) % 129) for vertex in range(129)}
        data = graph6(129, cycle_edges)
        page = self.run_genus(data, "--page-only", "-j", "1")
        multi_genus = self.run_genus(data, "--multi_genus-only", "-j", "1")
        self.assertEqual(page.returncode, 0, page.stderr.decode())
        self.assertIn("Graph 1 has genus 0", page.stdout.decode())
        self.assertEqual(multi_genus.returncode, 1)
        self.assertIn("exceeds MultiGenus", multi_genus.stderr.decode())

    def test_page_supports_bridge_blocks(self):
        pendant_k5 = complete_edges(5) | {(0, 5)}
        bridged_triangles = {
            (0, 1),
            (1, 2),
            (0, 2),
            (3, 4),
            (4, 5),
            (3, 5),
            (2, 3),
        }
        first_k5 = complete_edges(5)
        second_k5 = {(left + 5, right + 5) for left, right in complete_edges(5)}
        bridged_k5s = first_k5 | second_k5 | {(0, 5)}
        path = {(vertex, vertex + 1) for vertex in range(7)}
        data = b"".join(
            (
                graph6(6, pendant_k5),
                graph6(6, bridged_triangles),
                graph6(10, bridged_k5s),
                graph6(8, path),
            )
        )

        for arguments in (("--page-only", "-j", "1"), ("-j", "2")):
            with self.subTest(arguments=arguments):
                result = self.run_genus(data, *arguments)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                self.assertIn("Graph 1 has genus 1", result.stdout.decode())
                self.assertIn("Graph 2 has genus 0", result.stdout.decode())
                self.assertIn("Graph 3 has genus 2", result.stdout.decode())
                self.assertIn("Graph 4 has genus 0", result.stdout.decode())

    def test_page_bridge_supports_multicode(self):
        edges = complete_edges(5) | {(0, 5)}
        result = self.run_genus(
            multicode(6, edges), "--multicode", "--page-only", "-j", "1"
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 1", result.stdout.decode())

    def test_mixed_block_tree_has_additive_genus(self):
        edges = complete_edges(8)  # K8, genus 2
        edges |= complete_edges_on((0, 8, 9, 10, 11))  # K5, genus 1
        edges |= complete_bipartite_edges(range(12, 16), range(16, 21))  # K4,5, genus 2
        edges |= complete_bipartite_edges(range(21, 24), range(24, 27))  # K3,3, genus 1
        edges |= {(7, 12), (20, 21)}

        # Attach an asymmetric branching tree to several different blocks.
        edges |= {(9, 27), (27, 28), (27, 29), (29, 30), (30, 31)}
        edges |= {(18, 32), (32, 33), (32, 34), (34, 35), (34, 36)}
        edges |= {(25, 37), (37, 38), (38, 39), (38, 40)}

        result = self.run_genus(graph6(41, edges), "--page-only", "-j", "1")
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 6", result.stdout.decode())

    def test_many_blocks_can_exceed_whole_graph_degree_limit(self):
        block_count = 64
        edges = set()
        next_vertex = 1
        for _ in range(block_count):
            block_vertices = (0, next_vertex, next_vertex + 1,
                              next_vertex + 2, next_vertex + 3)
            edges |= complete_edges_on(block_vertices)
            next_vertex += 4

        # This bridge forces decomposition. Vertex 0 has degree 257 in the
        # original graph, while every PAGE block has maximum degree 4.
        edges.add((0, next_vertex))
        num_vertices = next_vertex + 1
        data = graph6(num_vertices, edges)

        for arguments in (("--page-only", "-j", "1"), ("-j", "2")):
            with self.subTest(arguments=arguments):
                result = self.run_genus(data, *arguments)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                self.assertIn("Graph 1 has genus 64", result.stdout.decode())

    def test_deep_bridge_tree_uses_iterative_decomposition(self):
        num_vertices = 2048
        edges = complete_edges(5)
        edges.add((4, 5))
        edges |= {(vertex, vertex + 1) for vertex in range(5, num_vertices - 1)}

        result = self.run_genus(
            graph6(num_vertices, edges), "--page-only", "-j", "1"
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 1", result.stdout.decode())

    def test_invalid_input_and_conflicting_flags_fail(self):
        malformed = self.run_genus(b"not-graph6\n")
        self.assertEqual(malformed.returncode, 1)
        self.assertIn("empty or malformed", malformed.stderr.decode())

        conflicting = self.run_genus(
            graph6(5, complete_edges(5)),
            "--page-only",
            "--multi_genus-only",
        )
        self.assertEqual(conflicting.returncode, 2)
        self.assertIn("usage:", conflicting.stderr.decode())


if __name__ == "__main__":
    unittest.main()
