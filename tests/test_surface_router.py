# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Topology and geometry regressions for the higher-genus native exporter."""

import math
import json
from itertools import product
import shutil
import subprocess
import tempfile
import unittest
from collections import Counter, defaultdict
from pathlib import Path

K8_GENUS2 = [[1, 3, 7, 2, 5, 6, 4],
 [0, 4, 7, 5, 6, 2, 3],
 [0, 7, 4, 1, 6, 3, 5],
 [0, 1, 4, 5, 2, 6, 7],
 [1, 0, 6, 5, 3, 2, 7],
 [4, 1, 7, 6, 0, 2, 3],
 [5, 7, 3, 2, 1, 4, 0],
 [6, 5, 1, 4, 2, 0, 3]]
K9_GENUS3 = [[1, 3, 8, 2, 7, 6, 5, 4],
 [0, 4, 8, 7, 6, 5, 2, 3],
 [0, 8, 3, 1, 5, 6, 4, 7],
 [0, 1, 2, 4, 6, 7, 5, 8],
 [1, 0, 5, 7, 2, 6, 3, 8],
 [4, 0, 2, 1, 6, 8, 3, 7],
 [5, 1, 7, 3, 4, 2, 0, 8],
 [6, 1, 8, 0, 2, 4, 5, 3],
 [7, 1, 4, 2, 0, 3, 5, 6]]

# Fixed rotations from the reported cage examples (genus 3 and genus 4).
CAGE_3_6 = [[1, 2, 3],
 [0, 4, 5],
 [0, 6, 7],
 [0, 8, 9],
 [1, 10, 11],
 [1, 12, 13],
 [2, 10, 12],
 [2, 11, 13],
 [3, 10, 13],
 [3, 11, 12],
 [4, 6, 8],
 [4, 7, 9],
 [5, 6, 9],
 [5, 7, 8]]
CAGE_3_8 = [[15, 16, 17],
 [18, 19, 20],
 [21, 22, 23],
 [15, 18, 21],
 [15, 25, 24],
 [18, 27, 26],
 [21, 28, 29],
 [16, 19, 22],
 [16, 26, 28],
 [19, 24, 29],
 [22, 27, 25],
 [17, 23, 20],
 [17, 29, 27],
 [20, 28, 25],
 [23, 26, 24],
 [0, 3, 4],
 [0, 7, 8],
 [0, 11, 12],
 [1, 5, 3],
 [1, 7, 9],
 [1, 13, 11],
 [2, 6, 3],
 [2, 7, 10],
 [2, 14, 11],
 [4, 14, 9],
 [4, 13, 10],
 [5, 14, 8],
 [5, 10, 12],
 [6, 8, 13],
 [6, 9, 12]]


def layout_metrics(obj):
    """Physical length, sampled crowding, and departure arc/chord ratio.

    Ignore the immediate junction where incident edges necessarily meet.
    A spatial grid measures proximity between different curves, independently
    of the exporter's routing energy and triangle subdivisions.
    """
    points, curves = [], []
    for line in obj.splitlines():
        a = line.split()
        if a and a[0] == "v":
            points.append(tuple(map(float, a[1:4])))
        elif a and a[0] == "l":
            curves.append([points[int(i) - 1] for i in a[1:]])
    spacing = 0.02
    grid = defaultdict(list)
    samples = []
    length = worst_departure = 0
    for owner, curve in enumerate(curves):
        segments = [math.dist(a, b) for a, b in zip(curve, curve[1:])]
        total = sum(segments)
        length += total

        def at(distance):
            for i, segment in enumerate(segments):
                if distance <= segment:
                    t = distance / segment if segment else 0
                    return tuple(a + t * (b - a) for a, b in zip(curve[i], curve[i + 1]))
                distance -= segment
            return curve[-1]

        departure = min(0.35, total / 2)
        for start, distance in [(curve[0], departure), (curve[-1], total - departure)]:
            worst_departure = max(worst_departure, departure / math.dist(start, at(distance)))
        count = max(1, int(total / spacing))
        for i in range(count + 1):
            p = at(total * i / count)
            valid = min(math.dist(p, curve[0]), math.dist(p, curve[-1])) > 0.18
            key = tuple(math.floor(x / spacing) for x in p)
            grid[key].append((owner, p))
            samples.append((owner, p, key, valid))
    crowded = 0
    offsets = list(product((-1, 0, 1), repeat=3))
    for owner, p, key, valid in samples:
        if valid and any(other != owner and math.dist(p, q) < spacing
                         for offset in offsets
                         for other, q in grid.get(tuple(a + b for a, b in zip(key, offset)), ())):
            crowded += spacing
    return length, crowded, worst_departure


def complete(n):
    return [[v for v in range(n) if v != u] for u in range(n)]


class SurfaceRouterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which("cc")
        if not compiler:
            raise unittest.SkipTest("A C compiler is required for native exporter tests")
        cls.directory = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.directory.cleanup)
        cls.binary = str(Path(cls.directory.name) / "planar_draw")
        repo = Path(__file__).resolve().parents[1]
        subprocess.run([compiler, "-std=gnu89", "-O2", "-o", cls.binary,
                        str(repo / "MultiGenus/planar_draw.c"), "-lm"],
                       check=True, capture_output=True)

    def export(self, rotation, legacy=False, timeout=120):
        code = bytes([len(rotation)] + [value for row in rotation
                     for value in [*[v + 1 for v in row], 0]])
        prefix = str(Path(self.directory.name) / "surface")
        result = subprocess.run([self.binary, "f", "l", "o", prefix]
                                + (["--legacy-surface"] if legacy else []),
                                input=code, capture_output=True, timeout=timeout)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return Path(prefix + ".obj").read_text()

    def verify_embedding(self, obj, rotation, genus):
        positions, triangles, routes, labels = [], [], [], {}
        for line in obj.splitlines():
            tokens = line.split()
            if not tokens:
                continue
            if tokens[0] == "v":
                positions.append(tuple(map(float, tokens[1:4])))
            elif tokens[0] == "f":
                triangles.append(tuple(int(x) - 1 for x in tokens[1:4]))
            elif tokens[0] == "l":
                routes.append([int(x) - 1 for x in tokens[1:]])
            elif tokens[:2] == ["#", "graph_vertex_label"]:
                labels[int(tokens[2]) - 1] = int(tokens[3]) - 1
        self.assertEqual(set(labels.values()), set(range(len(rotation))))
        self.assertTrue(all(math.isfinite(x) for p in positions for x in p))
        directed = Counter((t[i], t[(i + 1) % 3]) for t in triangles for i in range(3))
        edges = {tuple(sorted(e)) for e in directed}
        used = {v for t in triangles for v in t}
        self.assertEqual(len(used) - len(edges) + len(triangles), 2 - 2 * genus)
        for a, b in edges:
            self.assertEqual((directed[a, b], directed[b, a]), (1, 1))
        rings = defaultdict(dict)
        for t in triangles:
            a, b, c = [positions[v] for v in t]
            ab, ac = [b[i] - a[i] for i in range(3)], [c[i] - a[i] for i in range(3)]
            cross = [ab[1]*ac[2]-ab[2]*ac[1], ab[2]*ac[0]-ab[0]*ac[2],
                     ab[0]*ac[1]-ab[1]*ac[0]]
            self.assertGreater(sum(x*x for x in cross), 0, "Collapsed surface triangle")
            for i in range(3):
                if t[i] in labels:
                    rings[t[i]][t[(i + 1) % 3]] = t[(i + 2) % 3]
        interiors, actual_edges, ports = set(), set(), defaultdict(dict)
        for route in routes:
            self.assertIn(route[0], labels)
            self.assertIn(route[-1], labels)
            self.assertEqual(len(set(route)), len(route), "Self-intersecting route")
            u, v = labels[route[0]], labels[route[-1]]
            self.assertNotIn(tuple(sorted((u, v))), actual_edges)
            actual_edges.add(tuple(sorted((u, v))))
            self.assertFalse(interiors.intersection(route[1:-1]))
            self.assertFalse(set(labels).intersection(route[1:-1]))
            interiors.update(route[1:-1])
            for a, b in zip(route, route[1:]):
                self.assertIn(tuple(sorted((a, b))), edges,
                              "An edge segment leaves the surface")
            ports[route[0]][route[1]] = v
            ports[route[-1]][route[-2]] = u
        expected_edges = {tuple(sorted((u, v))) for u, row in enumerate(rotation) for v in row}
        self.assertEqual(actual_edges, expected_edges)
        # Read rotations from the oriented surface triangles, independently of
        # exporter metadata or projected screen-space angles.
        for point, port in ports.items():
            start = current = next(iter(rings[point]))
            actual = []
            for _ in range(len(rings[point])):
                if current in port:
                    actual.append(port[current])
                current = rings[point][current]
                if current == start:
                    break
            # Input rotations follow the right-hand rule about outward normals.
            expected = rotation[labels[point]]
            self.assertIn(actual, [expected[i:] + expected[:i] for i in range(len(expected))])

    def test_k33_rotation_variants(self):
        rotation = [[3, 5, 4], [3, 4, 5], [3, 4, 5], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
        permutation = [2, 5, 0, 4, 1, 3]
        relabeled = [[] for _ in rotation]
        for u, row in enumerate(rotation):
            relabeled[permutation[u]] = [permutation[v] for v in row]
        for r in [rotation, [row[::-1] for row in rotation], relabeled]:
            with self.subTest(rotation=r):
                self.verify_embedding(self.export(r), r, 2)

    def test_cage_spacing_and_vertex_departures(self):
        k33 = [[3, 5, 4], [3, 4, 5], [3, 4, 5], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
        for rotation, genus, max_length, max_crowding, max_departure in [
            (k33, 2, 42, 0.1, 1.5),
            (CAGE_3_6, 3, 140, 0.5, 2.0),
            (CAGE_3_8, 4, 400, 1.0, 2.0),
        ]:
            with self.subTest(vertices=len(rotation), genus=genus):
                obj = self.export(rotation)
                self.verify_embedding(obj, rotation, genus)
                length, crowded, departure = layout_metrics(obj)
                self.assertLess(length, max_length, "Unnecessary winding around handles")
                self.assertLess(crowded, max_crowding, "Long visually overlapping bundles")
                self.assertLess(departure, max_departure, "Hairpin departure at a vertex")

    def test_dense_and_higher_genus(self):
        for rotation, genus in [(K8_GENUS2, 2), (K9_GENUS3, 3),
                                (complete(6), 4), (complete(7), 6)]:
            with self.subTest(genus=genus):
                self.verify_embedding(self.export(rotation), rotation, genus)

    def test_bridges_and_cut_vertices(self):
        rotation = [row[:] for row in K8_GENUS2]
        rotation[0].insert(2, 8)
        rotation.extend([[0, 9], [8]])
        self.verify_embedding(self.export(rotation), rotation, 2)

    def test_large_cage_normal_arcs(self):
        repo = Path(__file__).resolve().parents[1]
        rotation = json.loads((repo / "tests/fixtures/3-12-cage-genus17.json").read_text())
        graph = [list(map(int, row.split())) for row in
                 (repo / "PAGE/adjacency_lists/3-12-cage.txt").read_text().splitlines()[1:]]
        self.assertEqual([sorted(row) for row in rotation], [sorted(row) for row in graph])
        permutation = [(37 * i + 11) % len(rotation) for i in range(len(rotation))]
        relabeled = [[] for _ in rotation]
        for u, row in enumerate(rotation):
            relabeled[permutation[u]] = [permutation[v] for v in row]
        with_bridge = [row[:] for row in rotation]
        with_bridge[0].append(126)
        with_bridge.extend([[0, 127], [126]])
        for variant, r in [("original", rotation), ("mirror", [row[::-1] for row in rotation]),
                           ("relabel", relabeled), ("bridge", with_bridge)]:
            with self.subTest(variant=variant):
                obj = self.export(r, timeout=30)
                self.assertIn("surface_layout normal_arcs", obj)
                self.verify_embedding(obj, r, 17)
                # Bound geometric complexity, independently of machine speed.
                # The old refinement could exceed millions of triangles.
                self.assertLess(sum(line.startswith("f ") for line in obj.splitlines()), 250_000)

    def test_legacy_manual_surface(self):
        rotation = [[3, 5, 4], [3, 4, 5], [3, 4, 5], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
        obj = self.export(rotation, legacy=True)
        self.assertIn("thickened canonical loop chain", obj)
        self.assertNotIn("rotation-preserving vertex disks", obj)

    def test_deterministic_output(self):
        self.assertEqual(self.export(complete(5)), self.export(complete(5)))


if __name__ == "__main__":
    unittest.main()
