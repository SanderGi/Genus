#!/usr/bin/env sage
"""Visualize the faces output by PAGE."""

import os
from sage.all import Graph, matrix  # type: ignore
from sage.plot.text import Text  # type: ignore

# Inputs
GRAPH = "austin_test.txt"
FACES = [
    [0, 6, 2, 8, 1, 7, 0],
    [3, 9, 4, 11, 5, 10, 3],
    [0, 8, 2, 11, 4, 10, 5, 9, 3, 7, 1, 6, 0],
    [0, 7, 3, 10, 4, 9, 5, 11, 2, 6, 1, 8, 0],
]

# Constants
IGNORE_VERTEX = 65535
COLORS = {
    0: "black",
    1: "blue",
    2: "purple",
    3: "red",
    4: "green",
    5: "orange",
    6: "yellow",
    7: "brown",
    8: "pink",
    9: "cyan",
    10: "magenta",
    11: "grey",
    12: "lightblue",
    13: "lightgreen",
    14: "teal",
    15: "salmon",
    16: "navy",
    17: "gold",
    18: "lime",
    19: "indigo",
    20: "maroon",
    21: "olive",
    22: "khaki",
    23: "indianred",
    24: "salmon",
    25: "deeppink",
    26: "orchid",
    27: "royalblue",
    28: "tomato",
    29: "aquamarine",
    30: "navajowhite",
    31: "floralwhite",
    32: "tan",
    33: "darkgoldenrod",
    34: "paleturquoise",
    35: "darkslateblue",
    36: "lavenderblush",
    37: "hotpink",
    38: "crimson",
    39: "orangered",
}

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
g_directed = g.to_directed()


# Show the faces colored
def is_in_cycle(e, cycle):
    try:
        i = cycle.index(e[0])
        j = cycle.index(e[1])

        if i + 1 == j or (i == len(cycle) - 2 and j == 0):
            return True
        else:
            return False
    except ValueError:
        return False


for e in g_directed.edges():
    g_directed.set_edge_label(e[0], e[1], 0)
    for i, c in enumerate(solution):
        if is_in_cycle(e, c):
            g_directed.set_edge_label(e[0], e[1], i + 1)

p = g_directed.plot(
    edge_colors=g_directed._color_by_label(COLORS),
    vertex_size=70,
    vertex_color="midnightblue",
    transparent=True,
)
for object in p._objects:
    if isinstance(object, Text):
        object._options["rgbcolor"] = (1, 1, 1)

# export as PDF
p.save("faces_all.pdf", figsize=(14, 14))

g_directed.layout()
pos = g_directed.get_pos()
for i, c in enumerate(solution):
    for e in g_directed.edges():
        g_directed.set_edge_label(e[0], e[1], 0)
        if is_in_cycle(e, c):
            g_directed.set_edge_label(e[0], e[1], i + 1)

    g_directed.set_pos(pos)

    p = g_directed.plot(
        edge_colors=g_directed._color_by_label(COLORS),
        vertex_size=70,
        vertex_color="midnightblue",
        transparent=True,
        pos=pos,
        layout="circular",
    )
    for object in p._objects:
        if isinstance(object, Text):
            object._options["rgbcolor"] = (1, 1, 1)

    p.save(f"faces_{i}.pdf", figsize=(14, 14))
