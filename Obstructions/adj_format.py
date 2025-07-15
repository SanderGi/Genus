from sage.all import *

IGNORE_VERTEX = 65536


def to_adj_list(g, filename):
    adjacency_list = [[] for _ in range(len(g.vertices()))]
    for e in g.edges():
        adjacency_list[e[0]].append(e[1])
        adjacency_list[e[1]].append(e[0])
    max_degree = max(g.degree())
    for i in range(len(g.vertices())):  # pad adjacency list
        while len(adjacency_list[i]) < max_degree:
            adjacency_list[i].append(IGNORE_VERTEX)
    with open(filename, "w") as f:
        f.write(f"{len(g.vertices())} {len(g.edges())}\n")
        for i in range(len(g.vertices())):
            f.write(f'{" ".join(map(str, adjacency_list[i]))}\n')

    return adjacency_list, max_degree


def from_adj_list(adjacency_list):
    num_vertices = len(adjacency_list)
    start_ix = min(min(neighbors) for neighbors in adjacency_list)
    adjacency_matrix = [[0 for i in range(num_vertices)] for j in range(num_vertices)]
    for i in range(num_vertices):
        for j in adjacency_list[i]:
            adjacency_matrix[i][j - start_ix] = 1
            adjacency_matrix[j - start_ix][i] = 1
    return Graph(matrix(adjacency_matrix), format="adjacency_matrix")  # type: ignore


def to_multi_code(adj_list, filename):
    with open(filename, "wb") as file:
        num_vertices = len(adj_list)
        min_vertex_id = min(min(neighbors) for neighbors in adj_list)
        num_bytes = 1 if num_vertices < 256 else 2
        file.write(num_vertices.to_bytes(num_bytes, byteorder="little"))
        for v in range(num_vertices):
            for u in adj_list[v]:
                if u == IGNORE_VERTEX:
                    continue
                u = u - min_vertex_id
                if u > v:
                    file.write((u + 1).to_bytes(num_bytes, byteorder="little"))
            if v < num_vertices - 1:
                file.write((0).to_bytes(num_bytes, byteorder="little"))
        file.flush()


def to_upper_tri(g):
    upper_tri = f"{g.num_verts()} "
    adjacency_matrix = g.adjacency_matrix()
    for i in range(g.num_verts()):
        for j in range(i + 1, g.num_verts()):
            upper_tri += str(adjacency_matrix[i][j])
    return upper_tri


def from_upper_tri(upper_tri):
    num_vertices, upper_triangular_adj_matrix = upper_tri.split()
    num_vertices = int(num_vertices)
    upper_triangular_adj_matrix = list(map(int, upper_triangular_adj_matrix))
    # num_edges = sum(upper_triangular_adj_matrix)

    # load graph
    adj_matrix = [[0 for i in range(num_vertices)] for j in range(num_vertices)]
    for i in range(num_vertices - 1):
        for j in range(i + 1, num_vertices):
            adj_matrix[i][j] = upper_triangular_adj_matrix.pop(0)
            adj_matrix[j][i] = adj_matrix[i][j]
    matrix = Matrix(adj_matrix)
    g = Graph(matrix)

    return g
