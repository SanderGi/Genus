"""Run with python3 tests/test_c_solvers.py from the MultiGenus directory."""

import itertools
import os
from pathlib import Path
import shlex
import struct
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
EDGE = [(1, 2)]
K4 = list(itertools.combinations(range(1, 5), 2))
K33 = list(itertools.product(range(1, 4), range(4, 7)))


def multicode(order, edges):
    data = bytearray([order])
    for vertex in range(1, order):
        data.extend(v for u, v in sorted(edges) if u == vertex)
        data.append(0)
    return bytes(data)


def check_embedding(test, data, order, edges, genus):
    """Consume one rotation and check the labelled darts and their face cycles."""
    test.assertEqual(data[0], order)
    data = data[1:]
    successor = {}
    for vertex in range(1, order + 1):
        end = data.index(0)
        neighbors, data = data[:end], data[end + 1:]
        expected = [b if a == vertex else a for a, b in edges if vertex in (a, b)]
        test.assertCountEqual(neighbors, expected)
        for left, right in zip(neighbors, neighbors[1:] + neighbors[:1]):
            successor[left, vertex] = (vertex, right)

    pending = set(successor)
    faces = int(order == 1)
    while pending:
        start = dart = next(iter(pending))
        while dart in pending:
            pending.remove(dart)
            dart = successor[dart]
        test.assertEqual(dart, start)
        faces += 1
    test.assertEqual(2 - order + len(edges) - faces, 2 * genus)
    return data


class CSolvers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        cls.programs = []
        compiler = shlex.split(os.environ.get("CC", "cc"))
        for name in ("multi_genus", "multi_genus_parallel"):
            flags = ["-pthread"] if name.endswith("parallel") else []
            binary = Path(tmp.name) / name
            command = compiler + ["-O2", "-std=c17", "-DLONG"] + flags
            subprocess.run(command + [str(ROOT / (name + ".c")), "-lm", "-o", binary],
                           check=True)
            cls.programs.append(binary)
            if flags:
                command += ["-DPARALLEL_SOLVER"]
            checks = binary.with_suffix(".checks")
            subprocess.run(command + [str(ROOT / "tests/c_solver_invariants.c"),
                                      "-lm", "-o", checks], check=True)
            subprocess.run([checks], check=True, timeout=10)

    def solve(self, binary, args, data, threads=2, depth=1, success=True):
        env = dict(os.environ, MULTI_GENUS_THREADS=str(threads))
        env.pop("MULTI_GENUS_SPLIT_DEPTH", None)
        if depth is not None:
            env["MULTI_GENUS_SPLIT_DEPTH"] = str(depth)
        result = subprocess.run([binary, *args], input=data, capture_output=True,
                                env=env, timeout=20)
        self.assertEqual(result.returncode == 0, success, result.stderr)
        return result.stdout, result.stderr.decode()

    def test_graph_stream(self):
        # Subdivide 1--4, add a triangle on 2--5 and attach a leaf at 7.
        expanded = [(u, v) for u, v in K33 if (u, v) != (1, 4)]
        expanded += [(1, 7), (4, 7), (2, 8), (5, 8), (7, 9)]
        # The 128-vertex star exercises both halves of the BFS neighbor bitset.
        star = [(1, leaf) for leaf in range(2, 129)]
        graphs = [(4, K4, 0), (4, K4, 0), (9, expanded, 1),
                  (2, EDGE, 0), (128, star, 0)]
        stream = b"".join(multicode(n, edges) for n, edges, _ in graphs)
        for binary in self.programs:
            for args, threads, depth in [([], 2, 1), (["o"], 3, 2),
                                        (["nb"], 2, None), ([], 1, None)]:
                with self.subTest(binary=binary, args=args, threads=threads, depth=depth):
                    data, stats = self.solve(binary, ["L", "w", *args], stream, threads, depth)
                    for n, edges, genus in graphs:
                        self.assertEqual(data[:1], b"\xff")
                        data = check_embedding(self, data[1:], n, edges, genus)
                    self.assertEqual(data, b"")
                    self.assertIn("graphs with genus 0: 4\n", stats)
                    self.assertIn("graphs with genus 1: 1\n", stats)
                    self.assertIn("Wrote 5 embeddings.\n", stats)

    def test_genus_limits(self):
        edge, k33 = multicode(2, EDGE), multicode(6, K33)
        for binary in self.programs:
            with self.subTest(binary=binary):
                output, stats = self.solve(binary, ["F", "l0"], edge + k33)
                self.assertEqual(output, k33)
                self.assertIn("With genus larger than 0: 1\n", stats)
                for option in ["l2147483647", "fm2147483647"]:
                    output, stats = self.solve(binary, [option], edge + k33)
                    self.assertEqual(output, b"")
                    self.assertEqual([s for s in stats.splitlines() if s.startswith("graphs")],
                                     ["graphs with genus 0: 1", "graphs with genus 1: 1"])
                for args in [["l0", "f0"], ["l0", "fm0"], ["w", "fm1"],
                             ["f0", "fa1"], ["w", "F", "l0"], ["fa"], ["l1x"],
                             ["f2147483648"]]:
                    output, _ = self.solve(binary, args, edge, success=False)
                    self.assertEqual(output, b"")

    def test_format_and_size_limits(self):
        # At the edge limit a genus-zero cutoff decides by Euler's inequality.
        clique = list(itertools.combinations(range(1, 33), 2))
        edges = clique + [(v, 33) for v in range(1, 17)]
        at_limit = multicode(33, edges)
        over_limit = multicode(33, edges + [(17, 33)])
        long_path = multicode(129, [(v, v + 1) for v in range(1, 129)])
        # A 256-vertex path in the native-endian, two-byte multicode format.
        words = [256] + [word for v in range(1, 256) for word in (v + 1, 0)]
        extended = b"\x00" + struct.pack(f"={len(words)}H", *words)
        header = b">>multi_code<<"
        for binary in self.programs:
            with self.subTest(binary=binary):
                output, stats = self.solve(binary, ["l0", "F"], header + at_limit)
                self.assertEqual(output, at_limit)
                self.assertIn("With genus larger than 0: 1", stats)
                for data in (over_limit, long_path, extended, header + extended):
                    output, _ = self.solve(binary, [], data, success=False)
                    self.assertEqual(output, b"")

    def test_record_boundaries(self):
        header = b">>multi_code<<"
        path = [(1, 62)] + [(v, v + 1) for v in range(2, 62)]
        record = multicode(62, path)
        self.assertEqual(record[:3], b">>\0")
        # Neighbor order within an upper-triangle row is arbitrary.
        unsorted_k4 = bytes([4, 4, 2, 3, 0, 3, 4, 0, 4, 0])
        stream = record + header + record + bytes([1]) + unsorted_k4
        for binary in self.programs:
            with self.subTest(binary=binary):
                output, stats = self.solve(binary, ["w"], stream)
                for n, edges in [(62, path), (62, path), (1, []), (4, K4)]:
                    if n == 1:
                        self.assertEqual(output[:2], bytes([1, 0]))
                        output = output[2:]
                    else:
                        output = check_embedding(self, output, n, edges, 0)
                self.assertEqual(output, b"")
                self.assertIn("graphs with genus 0: 4", stats)
                self.assertEqual(self.solve(binary, [], header), (b"", ""))
                # Interrupt a normal record/header write; only a complete graph gets a marker.
                for partial in [header[:-1], record[:2], multicode(4, K4)[:-1]]:
                    output, message = self.solve(binary, ["L"], partial, success=False)
                    self.assertEqual(output, b"")
                    self.assertIn("incomplete", message)

                # A later interrupted record leaves the previous complete result intact.
                output, message = self.solve(binary, ["L", "w"],
                                             multicode(2, EDGE) + record[:-1], success=False)
                self.assertEqual(output[:1], b"\xff")
                self.assertEqual(check_embedding(self, output[1:], 2, EDGE, 0), b"")
                self.assertIn("incomplete", message)

    def test_simple_incidence_rows(self):
        for binary in self.programs:
            for record in ([3, 2, 2, 0, 3, 0], [3, 1, 0, 3, 0],
                           [3, 2, 0, 1, 0], [3, 4, 0, 3, 0]):
                with self.subTest(binary=binary, record=record):
                    output, message = self.solve(binary, ["L"], bytes(record), success=False)
                    self.assertEqual(output, b"")
                    self.assertIn("neighbor", message)

    def test_zero_output_filters(self):
        stream = multicode(4, K4) + multicode(6, K33)
        for binary in self.programs:
            for args in (["w", "l0"], ["l0", "w"], ["f0"], ["fa0"], ["fm0"]):
                with self.subTest(binary=binary, args=args):
                    output, stats = self.solve(binary, args, stream)
                    self.assertEqual(check_embedding(self, output, 4, K4, 0), b"")
                    self.assertIn("Wrote 1 embeddings.", stats)

    def test_exact_and_all(self):
        k4 = multicode(4, K4)
        for binary in self.programs:
            # K4 has 2^4 labelled rotations, paired under global reflection.
            # One pair is planar and seven pairs have genus one.
            for args, count, genus in [(["wa"], 1, 0), (["fa1"], 7, 1),
                                       (["f1", "nb"], 1, 1), (["fm1"], 0, 1),
                                       (["f2147483647"], 0, 1)]:
                with self.subTest(binary=binary, args=args):
                    data, stats = self.solve(binary, args, k4)
                    for _ in range(count):
                        data = check_embedding(self, data, 4, K4, genus)
                    self.assertEqual(data, b"")
                    self.assertIn(f"Wrote {count} embeddings.\n", stats)


if __name__ == "__main__":
    unittest.main()
