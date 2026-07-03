#!/usr/bin/env sage
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Check whether the faces output by PAGE are a valid embedding."""

import os
from sage.all import Graph, matrix  # type: ignore

IGNORE_VERTEX = 65535
GRAPH = "austin_test.txt"
FACES = [
    [0, 6, 2, 8, 1, 7, 0],
    [3, 9, 4, 11, 5, 10, 3],
    [0, 8, 2, 11, 4, 10, 5, 9, 3, 7, 1, 6, 0],
    [0, 7, 3, 10, 4, 9, 5, 11, 2, 6, 1, 8, 0],
]

# convert off-indexed to 0-indexed
off = min(min(v for v in f) for f in FACES)
solution = [[x - off for x in y] for y in FACES]

# load the graph
with open(os.path.join("adjacency_lists", GRAPH), "r") as f:
    lines = f.readlines()
    num_vertices, num_edges = map(int, lines.pop(0).strip().split(" "))
    adjacency_list = [set() for _ in range(num_vertices)]
    min_number = min(map(int, " ".join(lines).split()))
    for v, line in enumerate(lines):
        neighbors = map(int, line.strip().split(" "))
        for u in neighbors:
            if u == IGNORE_VERTEX:
                continue
            adjacency_list[v].add(u - min_number)
            adjacency_list[u - min_number].add(v)

adjacency_matrix = [[0 for i in range(num_vertices)] for j in range(num_vertices)]
for i in range(num_vertices):
    for j in adjacency_list[i]:
        adjacency_matrix[i][j] = 1
        adjacency_matrix[j][i] = 1

g = Graph(matrix(adjacency_matrix), format="adjacency_matrix")

# no duplicates edges
edges = set()
for c in solution:
    for i in range(len(c) - 1):
        assert (c[i], c[i + 1]) not in edges, (
            "Duplicate edge " + str(c[i]) + " " + str(c[i + 1])
        )
        edges.add((c[i], c[i + 1]))

# no duplicate cycles in the solution
for i, c1 in enumerate(solution):
    for j, c2 in enumerate(solution):
        if i == j:
            continue
        if list(reversed(c1)) == c2:
            continue
        try:
            offset = c2.index(c1[0])
        except ValueError:
            continue
        assert c2[offset:] + c2[:offset] != c1, (
            "Duplicate cycles " + str(c1) + " " + str(c2)
        )


def x_in_y(query, base):
    try:
        l = len(query)
    except TypeError:
        l = 1
        query = type(base)((query,))

    for i in range(len(base)):
        if base[i : i + l] == query:
            return True
    return False


# make sure if vertices i, j, k occur in the solution, k, j, i don't
for c in solution:
    c = c.copy() + [c[1]]
    for i in range(len(c) - 2):
        for c2 in solution:
            c2 = c2.copy() + [c2[1]]
            assert not x_in_y([c[i + 2], c[i + 1], c[i]], c2), (
                "Found "
                + str(c[i])
                + " "
                + str(c[i + 1])
                + " "
                + str(c[i + 2])
                + " in "
                + str(c2)
            )

# Make sure all vertices are used
vertex_uses = g.degree_sequence()
for c in solution:
    for v in c[:-1]:
        vertex_uses[v] -= 1
assert all([v == 0 for v in vertex_uses]), "All vertices should be used fully"

# convert edges list to adjacency list
al = [[] for _ in range(g.num_verts())]
for e in g.edges():
    al[e[0]].append(e[1])
    al[e[1]].append(e[0])

# check if every edge is used exactly once by removing them from the adjacency list
for c in solution:
    for i in range(len(c) - 1):
        assert c[i + 1] in al[c[i]], (
            "Edge " + str(c[i]) + " " + str(c[i + 1]) + " not in adjacency list"
        )
        al[c[i]].remove(c[i + 1])
assert all([len(v) == 0 for v in al]), "All edges should be used exactly once"

# verify the rotation system (sorted adjacency list)
adj = [[] for _ in range(num_vertices)]
pairs = [[] for _ in range(num_vertices)]
for c in solution:
    ce = c[:-1]
    for i in range(len(c) - 1):
        pairs[c[i]].append((ce[i - 1], c[i + 1]))
for i, p in enumerate(pairs):
    u, v = p.pop(0)
    s = u
    adj[i].append(u)
    while v != s:
        adj[i].append(v)
        u, v = list(filter(lambda x: x[0] == v, p))[0]
        p.remove((u, v))
    assert len(p) == 0, "Invalid rotation system"

print("Valid!")
