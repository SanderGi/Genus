#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Focused command-line regression tests for HoG/genus."""

import itertools
import os
import resource
import subprocess
import sys
import tempfile
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
    width = 1 if num_vertices < 256 else 2
    result = bytearray(num_vertices.to_bytes(width, byteorder="little"))
    for vertex in range(num_vertices - 1):
        for neighbor in sorted(neighbors[vertex]):
            result.extend((neighbor + 1).to_bytes(width, byteorder="little"))
        result.extend((0).to_bytes(width, byteorder="little"))
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

    def run_genus(self, data, *arguments, timeout=15):
        return subprocess.run(
            [str(BINARY), *arguments],
            input=data,
            capture_output=True,
            timeout=timeout,
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

    def test_multicode_mixes_one_and_two_byte_graphs(self):
        graphs = [
            (5, complete_edges(5), 1),
            (255, {(vertex, (vertex + 1) % 255) for vertex in range(255)}, 0),
            (256, {(vertex, (vertex + 1) % 256) for vertex in range(256)}, 0),
            (272, {(vertex, (vertex + 1) % 272) for vertex in range(272)}, 0),
            (660, {(vertex, (vertex + 1) % 660) for vertex in range(660)}, 0),
            (3, complete_edges(3), 0),
        ]
        data = b">>multi_code<<" + b"".join(
            multicode(num_vertices, edges)
            for num_vertices, edges, _ in graphs
        )
        result = self.run_genus(
            data, "--multicode", "--page-only", "--low-mem", "-j", "1"
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        for index, (_, _, genus) in enumerate(graphs, start=1):
            self.assertIn(
                f"Graph {index} has genus {genus}\n", result.stdout.decode()
            )

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

    def test_low_mem_page_on_bipartite_kneser_graph(self):
        data = (
            HERE.parent / "MultiGenus" / "graphs" / "bipartite-kneser8-2.mc"
        ).read_bytes()
        for arguments in (
            ("--multicode", "--page-only", "--low-mem", "-j", "1"),
            ("--multicode", "--low-mem", "-j", "2"),
        ):
            with self.subTest(arguments=arguments):
                result = self.run_genus(data, *arguments)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                self.assertIn("Graph 1 has genus 78", result.stdout.decode())

    def test_materialized_page_memory_limit_reports_error_and_continues(self):
        large_graph = (
            HERE.parent / "MultiGenus" / "graphs" / "bipartite-kneser13-2.mc"
        ).read_bytes()
        data = large_graph + multicode(5, complete_edges(5))
        result = self.run_genus(
            data, "--multicode", "--page-only", "-j", "1"
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn(
            "Graph 1 error: PAGE failed: materialized PAGE exceeded its 1024 MiB "
            "cycle-memory safety limit",
            result.stderr.decode(),
        )
        self.assertIn("rerun with --low-mem", result.stderr.decode())
        self.assertIn("Graph 2 has genus 1", result.stdout.decode())
        self.assertIn(
            "Processed 2 graphs: 1 succeeded, 1 failed", result.stdout.decode()
        )

    def test_auto_low_mem_retries_bipartite_kneser_graph(self):
        data = (
            HERE.parent / "MultiGenus" / "graphs" / "bipartite-kneser13-2.mc"
        ).read_bytes()
        result = self.run_genus(
            data,
            "--multicode",
            "--page-only",
            "--auto-low-mem",
            "-j",
            "1",
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stderr, b"")
        self.assertIn("Graph 1 has genus 996", result.stdout.decode())
        self.assertIn(
            "Processed 1 graph: 1 succeeded, 0 failed", result.stdout.decode()
        )

    def test_low_mem_page_handles_bridges_without_decomposition(self):
        pendant_k5 = complete_edges(5) | {(0, 5)}
        result = self.run_genus(
            graph6(6, pendant_k5), "--page-only", "--low-mem", "-j", "1"
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 1", result.stdout.decode())

    def test_low_mem_raises_small_stack_for_deep_face_search(self):
        block_count = 1200
        edges = set()
        for block in range(block_count):
            vertices = (
                0,
                block + 1,
                block_count + block + 1,
                2 * block_count + block + 1,
            )
            edges |= complete_edges_on(vertices)

        def reduce_stack():
            _, hard_limit = resource.getrlimit(resource.RLIMIT_STACK)
            resource.setrlimit(resource.RLIMIT_STACK, (1024 * 1024, hard_limit))

        result = subprocess.run(
            [str(BINARY), "--multicode", "--page-only", "--low-mem", "-j", "1"],
            input=multicode(1 + 3 * block_count, edges),
            capture_output=True,
            timeout=15,
            check=False,
            preexec_fn=reduce_stack,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn("Graph 1 has genus 0", result.stdout.decode())

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

    def test_rotation_oracle_all_solver_modes(self):
        # The shared Python oracle enumerates cyclic neighbor orders and counts
        # dart orbits. It uses neither native solver nor block decomposition.
        sys.path.insert(0, str(HERE.parent))
        try:
            from PAGE.test_page_python import connected, exhaustive_genus, rows_for
        finally:
            sys.path.pop(0)

        graphs = []
        for n in range(1, 6):
            possible = list(itertools.combinations(range(n), 2))
            seen = set()
            for mask in range(1 << len(possible)):
                edges = tuple(e for i, e in enumerate(possible) if mask & (1 << i))
                if edges in seen or not connected(rows_for(n, edges)):
                    continue
                graphs.append((n, edges))
                for labels in itertools.permutations(range(n)):
                    seen.add(tuple(sorted(
                        tuple(sorted((labels[u], labels[v]))) for u, v in edges
                    )))
        self.assertEqual(len(graphs), 31)  # All connected isomorphism classes through order five.

        k33 = complete_bipartite_edges(range(3), range(3, 6))
        # The two copies share a cut vertex in one graph and a bridge in the other.
        # Compute both answers on the whole graph to test genus additivity independently.
        cut = k33 | {(a + 5, b + 5) for a, b in k33}
        bridged = k33 | {(a + 6, b + 6) for a, b in k33} | {(5, 6)}
        subdivided = (k33 - {(0, 3)}) | {(0, 6), (6, 7), (7, 3)}
        graphs.extend([
            (6, k33),
            (8, subdivided),
            (9, subdivided | {(1, 8)}),
            (11, cut),
            (12, bridged),
        ])
        genera = [exhaustive_genus(rows_for(n, edges)) for n, edges in graphs]
        self.assertEqual(genera[-5:], [1, 1, 1, 2, 2])
        modes = (
            (),
            ("--low-mem",),
            ("--auto-low-mem",),
            ("--page-only",),
            ("--page-only", "--low-mem"),
            ("--page-only", "--auto-low-mem"),
            ("--multi_genus-only",),
        )
        for encoder, flag in ((graph6, "--graph6"), (multicode, "--multicode")):
            data = b"".join(encoder(n, edges) for n, edges in graphs)
            for mode in modes:
                with self.subTest(format=flag, mode=mode):
                    result = self.run_genus(data, flag, *mode, "-j", "2", timeout=30)
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    records = result.stdout.decode().splitlines()
                    self.assertEqual(len(records), len(graphs) + 1)
                    for index, (genus, graph) in enumerate(zip(genera, graphs), 1):
                        self.assertEqual(records[index - 1], f"Graph {index} has genus {genus}",
                                         f"graph6={graph6(*graph).decode().strip()}")
                    self.assertIn(f"{len(graphs)} succeeded, 0 failed", records[-1])

    def test_portfolio_with_materialized_memory_failure(self):
        # Build only in the temporary directory. A zero candidate budget forces
        # a real worker failure without exhausting host memory or depending on a race.
        with tempfile.TemporaryDirectory() as tmp:
            compiler = os.environ.get("CC", "cc")
            subprocess.run(
                ["make", "-Bs", "genus", f"BDIR={tmp}",
                 f"CC={compiler} -DHOG_PAGE_MAX_CYCLE_MEMORY_MB=0"],
                cwd=HERE, check=True,
            )
            binary = Path(tmp) / "genus"
            k4 = complete_edges(4)
            # Subdividing one edge preserves K4's genus but crosses the 128-vertex
            # MultiGenus limit. Thus the only successful worker can be low-memory PAGE.
            path = [0, *range(4, 129), 1]
            large = (k4 - {(0, 1)}) | set(zip(path, path[1:]))
            small_input, large_input = graph6(4, k4), graph6(129, large)

            def run(data, *args):
                return subprocess.run(
                    [binary, *args, "-j", "2"], input=data, capture_output=True, timeout=30,
                )

            for data in (small_input, large_input):
                with self.subTest(check="worker failure", n=len(data)):
                    failed = run(data, "--page-only")
                    self.assertEqual(failed.returncode, 1)
                    self.assertIn(b"cycle-memory safety limit", failed.stderr)
            unsupported = run(large_input, "--multi_genus-only")
            self.assertEqual(unsupported.returncode, 1)
            self.assertIn(b"exceeds MultiGenus", unsupported.stderr)

            # The small graph can still succeed on MultiGenus when PAGE fails.
            fallback = run(large_input + small_input)
            self.assertEqual(fallback.returncode, 1)
            self.assertIn(b"Graph 1 error: PAGE failed", fallback.stderr)
            self.assertIn(b"Graph 2 has genus 0\n", fallback.stdout)
            self.assertIn(b"1 succeeded, 1 failed", fallback.stdout)
            for mode in (("--auto-low-mem",), ("--page-only", "--auto-low-mem")):
                with self.subTest(retry=mode):
                    retried = run(large_input + small_input, *mode)
                    self.assertEqual(retried.returncode, 0, retried.stderr.decode())
                    self.assertEqual(retried.stdout.splitlines()[:2], [
                        b"Graph 1 has genus 0", b"Graph 2 has genus 0",
                    ])
                    self.assertIn(b"2 succeeded, 0 failed", retried.stdout)

    def test_canonical_graph6_order_and_padding(self):
        # K2 in the short form. Its three-byte order spelling is noncanonical.
        good = graph6(2, {(0, 1)})
        self.assertEqual(self.run_genus(good).returncode, 0)
        for data in (b"~??A" + good[1:], b"A`\n", b"", b">>graph6<<\n"):
            with self.subTest(data=data):
                run = self.run_genus(data)
                self.assertNotEqual(run.returncode, 0)
                self.assertNotIn(b"has genus", run.stdout)

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

        low_mem_multi_genus = self.run_genus(
            graph6(5, complete_edges(5)),
            "--low-mem",
            "--multi_genus-only",
        )
        self.assertEqual(low_mem_multi_genus.returncode, 2)
        self.assertIn("usage:", low_mem_multi_genus.stderr.decode())

        for incompatible in (
            ("--auto-low-mem", "--multi_genus-only"),
            ("--auto-low-mem", "--low-mem"),
        ):
            with self.subTest(incompatible=incompatible):
                result = self.run_genus(
                    graph6(5, complete_edges(5)), *incompatible
                )
                self.assertEqual(result.returncode, 2)
                self.assertIn("usage:", result.stderr.decode())


if __name__ == "__main__":
    unittest.main()
