from sage.graphs.graph_generators import graphs  # type: ignore
from find_obstructions import (
    is_obstruction,
    is_minor_obstruction,
    is_split_delete_minimal,
)
from adj_format import to_upper_tri, from_upper_tri


def one_vertex_sum(graph1, graph2, vertex1, vertex2):
    """
    Constructs the 1-vertex sum of two graphs.

    Args:
        graph1: The first graph (SageMath graph object).
        graph2: The second graph (SageMath graph object).
        vertex1: The vertex from graph1 to be merged.
        vertex2: The vertex from graph2 to be merged.

    Returns:
        A new graph that is the 1-vertex sum of graph1 and graph2.
    """

    # Ensure vertices are valid
    if vertex1 not in graph1.vertices() or vertex2 not in graph2.vertices():
        raise ValueError("Invalid vertex specified.")

    # Create copies to avoid modifying original graphs
    g1 = graph1.copy()
    g2 = graph2.copy()

    # Join the graphs, merging the specified vertices
    merged_graph = g1.disjoint_union(g2)
    merged_graph.merge_vertices([(0, vertex1), (1, vertex2)])

    return merged_graph


if __name__ == "__main__":
    with open("myrvold_minor_obs.txt", "r") as f:
        minor_obs = [from_upper_tri(l) for l in f.readlines()]

    def find_tri_format(g):
        for m in minor_obs:
            if g.is_isomorphic(m):
                return to_upper_tri(m)
        return to_upper_tri(g)

    K5 = graphs.CompleteGraph(5)
    K33 = graphs.CompleteBipartiteGraph(3, 3)

    K5K5 = one_vertex_sum(K5, K5, K5.vertices()[0], K5.vertices()[0])
    K5K33 = one_vertex_sum(K5, K33, K5.vertices()[0], K33.vertices()[0])
    K33K33 = one_vertex_sum(K33, K33, K33.vertices()[0], K33.vertices()[0])
    print(
        find_tri_format(K5K5),
        is_obstruction(K5K5, 2, "SAGE"),
        is_minor_obstruction(K5K5, 2, "SAGE"),
        is_split_delete_minimal(K5K5, 2, "SAGE", minor_obs),
    )
    print(
        find_tri_format(K5K33),
        is_obstruction(K5K33, 2, "SAGE"),
        is_minor_obstruction(K5K33, 2, "SAGE"),
        is_split_delete_minimal(K5K5, 2, "SAGE", minor_obs),
    )
    print(
        find_tri_format(K33K33),
        is_obstruction(K33K33, 2, "SAGE"),
        is_minor_obstruction(K33K33, 2, "SAGE"),
        is_split_delete_minimal(K5K5, 2, "SAGE", minor_obs),
    )

    print(
        is_split_delete_minimal(
            from_upper_tri("9 000001110000111000111111111111111000"),
            2,
            "MULTI",
            minor_obs,
        )
    )
