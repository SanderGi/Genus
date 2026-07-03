#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Convert graph6 format to the PAGE adjacency list input format."""

# Usage: python parse_graph6.py 'H?`e`qS'

import sys

MAX_VERTEX = 65535


def main(args: list[str]):
    adjacency = graph6_to_adjacency_list(args[0])
    degree = max(len(n) for n in adjacency.values())
    print(f"S=0 DEG={degree}")
    print(f"{len(adjacency)} {sum(len(n) for n in adjacency.values()) // 2}")
    for _, neighbors in adjacency.items():
        if len(neighbors) < degree:
            neighbors += [MAX_VERTEX] * (degree - len(neighbors))
        print(" ".join(map(str, neighbors)))


def graph6_to_adjacency_list(g6: str) -> dict[int, list[int]]:
    """
    Convert a graph6 string to an adjacency list.

    Supports standard graph6 strings for simple undirected graphs.
    Does not support sparse6 strings, which start with ':'.
    """
    g6 = g6.strip()

    if not g6:
        raise ValueError("Empty graph6 string")

    if g6.startswith(">>graph6<<"):
        g6 = g6[len(">>graph6<<") :]

    if g6.startswith(":"):
        raise ValueError("This appears to be sparse6, not graph6")

    values = [ord(c) - 63 for c in g6]

    if any(v < 0 or v > 63 for v in values):
        raise ValueError("Invalid graph6 character found")

    # Decode number of vertices
    if values[0] <= 62:
        n = values[0]
        data = values[1:]
    elif values[0] == 63:
        if len(values) < 4:
            raise ValueError("Invalid graph6 header")
        n = (values[1] << 12) | (values[2] << 6) | values[3]
        data = values[4:]
    else:
        raise ValueError("Invalid graph6 header")

    # Convert data chars to bits, 6 bits per char, most significant bit first
    bits = []
    for v in data:
        bits.extend((v >> shift) & 1 for shift in range(5, -1, -1))

    needed_bits = n * (n - 1) // 2
    if len(bits) < needed_bits:
        raise ValueError("Not enough edge data in graph6 string")

    adj = {i: [] for i in range(n)}

    # graph6 stores upper triangle of adjacency matrix:
    # (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), ...
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].append(j)
                adj[j].append(i)
            k += 1

    return adj


if __name__ == "__main__":
    main(sys.argv[1:])
