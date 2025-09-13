from sage.graphs.graph_generators import graphs  # type: ignore
from sage.all import Graph  # type: ignore

K33 = graphs.CompleteBipartiteGraph(3, 3)
original_vertices = K33.vertices()
K33.subdivide_edges(K33.edges(), 2)
# K33.plot().save("K33.png")
# print(original_vertices, K33.edges())
new_vertices = set(K33.vertices()) - set(original_vertices)
# print(new_vertices)
COMPLETE = Graph({v1: [v2 for v2 in new_vertices if v2 != v1] for v1 in new_vertices})
# print(COMPLETE)
first_edges = []
for u, v, _ in COMPLETE.edges():
    test = K33.copy()
    if test.has_edge(u, v):
        test.delete_edge(u, v)
    else:
        test.add_edge(u, v)
    unique = True
    for _, _, g in first_edges:
        if g.is_isomorphic(test):
            unique = False
            break
    if unique:
        first_edges.append((u, v, test))
# print(len(first_edges))
second_edges = []
for a, b, start in first_edges:
    # print(len(second_edges))
    for u, v, _ in COMPLETE.edges():
        if u in [a, b] or v in [a, b]:
            continue
        test = start.copy()
        if test.has_edge(u, v):
            test.delete_edge(u, v)
        else:
            test.add_edge(u, v)
        unique = True
        for _, _, g in second_edges:
            if g.is_isomorphic(test):
                unique = False
                break
        if unique:
            second_edges.append(((a, b), (u, v), test))
print(len(second_edges))
# for (a, b), (u, v), _ in second_edges:
#     print(f"Edge 1: {a}->{b}\tEdge 2: {u}->{v}")
# third_edges = []
# for a, b, start in second_edges:
#     for u, v, _ in COMPLETE.edges():
#         if u in [*a, *b] or v in [*a, *b]:
#             continue
#         test = start.copy()
#         if test.has_edge(u, v):
#             test.delete_edge(u, v)
#         else:
#             test.add_edge(u, v)
#         unique = True
#         for _, _, g in third_edges:
#             if g.is_isomorphic(test):
#                 unique = False
#                 break
#         if unique:
#             third_edges.append(((a, b), (u, v), test))
# print(len(third_edges))
