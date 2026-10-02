"""Independently check an expanded rotation system of H(h,2).

This verifier does not import the constructor or use its affine face equations.
It checks the two-subset graph, then traces every dart of the actual rotation.
For large h, use the much smaller base-cycle verifier instead.
"""
from __future__ import annotations
import argparse
import json
from math import comb
from pathlib import Path


def verify(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        obj = json.load(stream)
    h = int(obj["h"])
    labels = [(part, tuple(pair)) for part, pair in obj["vertex_labels"]]
    rows = obj["rotations"]
    v, d = h * (h - 1), comb(h - 2, 2)
    if len(labels) != v or len(rows) != v or len(set(labels)) != v:
        raise ValueError("Incorrect vertex set")
    for part, pair in labels:
        if part not in ("A", "B") or len(pair) != 2:
            raise ValueError("Invalid vertex label")
        if not 0 <= pair[0] < pair[1] < h:
            raise ValueError("Invalid two-subset")
    successor = []
    for vertex, row in enumerate(rows):
        if len(row) != d or len(set(row)) != d:
            raise ValueError("A rotation has the wrong degree or repeats a neighbor")
        part, pair = labels[vertex]
        for other in row:
            if not 0 <= other < v:
                raise ValueError("Neighbor outside vertex set")
            opposite, other_pair = labels[other]
            if part == opposite or set(pair) & set(other_pair):
                raise ValueError("An edge does not join disjoint opposite-class pairs")
        successor.append({other: row[(i + 1) % d]
                          for i, other in enumerate(row)})
    seen = set()
    faces = 0
    for vertex, row in enumerate(rows):
        for other in row:
            start = (vertex, other)
            if start in seen:
                continue
            dart, length = start, 0
            while dart not in seen:
                seen.add(dart)
                a, b = dart
                if a not in successor[b]:
                    raise ValueError("Adjacency is not symmetric")
                dart = (b, successor[b][a])
                length += 1
            if dart != start or length != 4:
                raise ValueError("A facial cycle does not have length four")
            faces += 1
    edges = v * d // 2
    if len(seen) != 2 * edges:
        raise ValueError("Some darts were not traced")
    genus = (2 - v + edges - faces) // 2
    lower_bound = 1 - v // 2 + edges // 4
    if genus != lower_bound:
        raise ValueError("The embedding does not attain the Euler lower bound")
    return {"h": h, "vertices": v, "edges": edges, "faces": faces,
            "genus": genus, "all_darts_traced": len(seen),
            "all_faces_length_four": True, "optimal": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rotation", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.rotation), indent=2))
