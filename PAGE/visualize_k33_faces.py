#!/usr/bin/env sage
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Visualize K3,3's faces."""

from sage.all import graphics_array, graphs  # type: ignore
from sage.plot.text import Text  # type: ignore

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

G = graphs.CompleteBipartiteGraph(3, 3)
old_labels = G.vertices()
new_labels = list(range(1, len(old_labels) + 1))
label_map = dict(zip(old_labels, new_labels))
G = G.relabel(label_map, inplace=False)
g_directed = G.to_directed()
g_directed.layout()
pos = g_directed.get_pos()
cycles = g_directed.all_simple_cycles()


def is_in_cycle(e, cycle):
    i_s = [i for i, x in enumerate(cycle) if x == e[0]]
    j_s = [i for i, x in enumerate(cycle) if x == e[1]]

    for i in i_s:
        for j in j_s:
            if i + 1 == j or (i == len(cycle) - 2 and j == 0):
                return True
    return False


# Show all simple cycles
plots = []
for i, c in enumerate(cycles):
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
    # p.show(figsize=(10, 10))
    plots.append(p)

graphics_array([plots[i : i + 13] for i in range(0, len(plots), 13)]).save(
    "k33_simple_cycles.pdf", figsize=(130, 30)
)


def find_cycles(g, k, include_non_simple=False):
    """Find cycles of length k (including non-simple ones if enabled)."""
    # TODO: fix off-by-one bugs by matching page.c
    adjacency_list = [[] for _ in range(len(g.vertices()))]
    offset = min(g.vertices())
    for e in g.edges():
        adjacency_list[e[0] - offset].append(e[1] - offset)
        adjacency_list[e[1] - offset].append(e[0] - offset)

    cycles = []
    queue = []
    for i in range(len(g.vertices())):
        queue.append([i])
    if include_non_simple:
        while len(queue) > 0:
            path = queue.pop(0)
            if len(path) == k:
                if path[0] in adjacency_list[path[-1]] and path[-1] != path[1]:
                    repeated_edge = False
                    for j in range(len(path) - 1):
                        if path[j] == path[-1] and path[j + 1] == i:
                            repeated_edge = True
                            break
                    if repeated_edge:
                        continue
                    cycle = path + [path[0]]
                    cycles.append(cycle)
                continue
            for i in adjacency_list[path[-1]]:
                if len(path) > 2 and i == path[-2]:
                    continue
                repeated_edge = False
                for j in range(len(path) - 1):
                    if path[j] == path[-1] and path[j + 1] == i:
                        repeated_edge = True
                        break
                if repeated_edge:
                    continue
                if i >= path[0]:
                    queue.append(path + [i])
    else:
        while len(queue) > 0:
            path = queue.pop(0)
            if len(path) == k:
                if path[0] in adjacency_list[path[-1]]:
                    cycle = path + [path[0]]
                    cycles.append(cycle)
                continue
            for i in adjacency_list[path[-1]]:
                if i not in path and i > path[0]:
                    queue.append(path + [i])

    return [[v + offset for v in c] for c in cycles]


# Show closed trails of length 4
cycles = find_cycles(G, 4, include_non_simple=True)
plots = []
for i, c in enumerate(cycles):
    if not is_in_cycle((6, 2), c):
        continue

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
    # p.show(figsize=(10, 10))
    plots.append(p)

graphics_array([plots[i : i + 4] for i in range(0, len(plots), 4)]).save(
    "k33_length_4_faces.pdf", figsize=(40, 20)
)


# Show one solution
solution = [[2, 5, 1, 6, 2], [6, 1, 4, 3, 6], [5, 2, 4, 1, 5, 3, 4, 2, 6, 3, 5]]
for e in g_directed.edges():
    g_directed.set_edge_label(e[0], e[1], 0)
    for i, c in enumerate(solution):
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

p.save("k33_solution.pdf", figsize=(10, 10))
