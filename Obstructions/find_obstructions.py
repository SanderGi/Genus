import sys

from sage.all import *

from genus_algos import run_algorithm
from adj_format import to_upper_tri


def get_edge_bounds(num_vertices):
    min_edges = (3 * num_vertices + 1) // 2
    max_edges = 6 + 3 * num_vertices
    return min_edges, max_edges


def get_max_possible_edges(num_vertices, max_degree=None):
    if max_degree:
        return num_vertices * max_degree // 2
    else:
        return num_vertices * (num_vertices - 1) // 2


def generate_non_isomorphic_graphs(
    num_vertices,
    min_edges,
    max_edges,
    k_regular=None,
    connected=True,
    min_degree=3,
    max_degree=None,
):
    assert k_regular is None or k_regular >= min_degree
    if max_degree is None:
        max_degree = num_vertices - 1
    assert k_regular is None or k_regular <= max_degree
    return list(
        graphs.nauty_geng(
            f"{num_vertices} {min_edges}:{max_edges} {'-c' if connected else ''} -d{k_regular if k_regular is not None else min_degree} -D{k_regular if k_regular is not None else max_degree}"
        )
    )


def is_obstruction(g, genus, algorithm):
    # G - e must embed on genus - 1 surface
    is_obstruction = True
    for e in g.edges():
        g.delete_edge(e)
        if run_algorithm(g, algorithm=algorithm) > genus - 1:
            is_obstruction = False
            break
        g.add_edge(e)
    return is_obstruction


def is_minor_obstruction(g, genus, algorithm):
    # to be a a minor order obstruction, G contract e must embed on genus - 1 surface
    # assumes g has already been checked to be an obstruction
    is_minor_obstruction = True
    for e in g.edges():
        g_contracted = g.copy()
        g_contracted.contract_edge(e)
        g_contracted.relabel()
        if run_algorithm(g_contracted, algorithm=algorithm) > genus - 1:
            is_minor_obstruction = False
            break
    return is_minor_obstruction


def is_split_delete_minimal(g, genus):
    raise NotImplementedError


def main(args):
    if len(args) < 1:
        print(
            "Usage: sage find_obstructions.py <min_vertices>:<max_vertices> [<genus_algorithm>] [<k_regular>] [--planarity] [--allow-disconnected]"
        )
        print("Example: sage find_obstructions.py 3:9")
        print("Example: sage find_obstructions.py 3:8 PAGE")
        print("Example: sage find_obstructions.py 3:10 MULTI 3")
        return

    FLAGS = [arg for arg in args if arg.startswith("--")]
    args = [arg for arg in args if arg not in FLAGS]
    USE_PLANARITY_CHECK = "--planarity" in FLAGS
    ONLY_CONNECTED = "--allow-disconnected" not in FLAGS
    MIN_VERTICES, MAX_VERTICES = map(lambda x: int(x), args[0].split(":"))
    GENUS_ALGORITHM = args[1] if len(args) > 1 else "MULTI"
    K_REGULAR = int(args[2]) if len(args) > 2 else None

    for num_vertices in range(MIN_VERTICES, MAX_VERTICES + 1):
        min_edges, max_edges = get_edge_bounds(num_vertices)
        max_possible_edges = get_max_possible_edges(num_vertices, K_REGULAR)
        if min_edges > max_possible_edges:
            print(
                f"No {'regular ' if K_REGULAR is not None else ''}graphs with {num_vertices} vertices satisfy the constraint of at least {min_edges} edges"
            )
            continue
        non_isomorphic_graphs = generate_non_isomorphic_graphs(
            num_vertices,
            min_edges,
            max_edges,
            k_regular=K_REGULAR,
            connected=ONLY_CONNECTED,
        )
        print(
            f"Found {len(non_isomorphic_graphs)} non-isomorphic connected {'regular ' if K_REGULAR is not None else ''}graphs with {num_vertices} vertices and {min_edges} to {max_edges} edges"
        )
        for g in non_isomorphic_graphs:
            if USE_PLANARITY_CHECK and g.is_planar():
                continue

            try:
                if run_algorithm(g, algorithm=GENUS_ALGORITHM) == 2:
                    if not is_obstruction(g, 2, algorithm=GENUS_ALGORITHM):
                        continue
                    if not is_minor_obstruction(g, 2, algorithm=GENUS_ALGORITHM):
                        continue

                    # print in upper triangular form
                    print(to_upper_tri(g))
            except Exception as e:
                g.show()
                raise e


if __name__ == "__main__":
    main(sys.argv[1:])
