#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Convert the PAGE adjacency lists into multi code format."""

import os

INPUT_DIR = os.path.join("..", "PAGE", "adjacency_lists")
OUTPUT_DIR = "./graphs"
IGNORE_VERTEX = 65535


def convert(name):
    with open(os.path.join(INPUT_DIR, name + ".txt"), "r") as f:
        lines = f.readlines()
        num_vertices, num_edges = map(int, lines.pop(0).strip().split(" "))
        adjacency_list = [set() for _ in range(num_vertices)]
        min_number = min(map(int, " ".join(lines).split()))
        print(min_number)
        for v, line in enumerate(lines):
            neighbors = map(int, line.strip().split(" "))
            for u in neighbors:
                if u == IGNORE_VERTEX:
                    continue
                adjacency_list[v].add(u - min_number)
                adjacency_list[u - min_number].add(v)
        print(adjacency_list)

    with open(os.path.join(OUTPUT_DIR, name + ".mc"), "wb") as f:
        # Multicode is a binary code for storing undirected graphs. The first entry is the number of vertices. Vertices are numbered 1,...,n. To each vertex x there is a list of neighbours with higher numbers than x, followed by a zero. The last list is always empty (no neighbours of n with a higher number than n), so the last "list" is not followed by a zero. After the last byte the next graph follows. The length of a multicode is number of vertices + number of edges.
        readable = []
        num_bytes = 1 if num_vertices < 256 else 2
        f.write(num_vertices.to_bytes(num_bytes, byteorder="little"))
        readable.append(num_vertices)
        for v in range(num_vertices):
            for u in adjacency_list[v]:
                if u > v:
                    f.write((u + 1).to_bytes(num_bytes, byteorder="little"))
                    readable.append(u + 1)
            if v < num_vertices - 1:
                f.write((0).to_bytes(num_bytes, byteorder="little"))
                readable.append(0)

    print(readable)


if __name__ == "__main__":
    for name in os.listdir(INPUT_DIR):
        if name.endswith(".txt"):
            convert(name.removesuffix(".txt"))
