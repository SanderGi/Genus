import sys
import itertools

from sage.all import *  # type: ignore

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
        graphs.nauty_geng(  # type: ignore
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


def gen_split(G):
    for v in G.vertices():
        N = list(G.neighbors(v))
        # split N into two non-empty sets
        for k in range(1, len(N) // 2 + 1):
            for part in itertools.combinations(N, k):
                part = set(part)
                rest = set(N) - part
                if not rest:
                    continue

                H = G.copy()
                H.delete_vertex(v)
                v1, v2 = max(G.vertices()) + 1, max(G.vertices()) + 2
                H.add_vertices([v1, v2])

                for u in part:
                    H.add_edge(v1, u)
                for u in rest:
                    H.add_edge(v2, u)

                yield H


def gen_split_delete(G):
    for H in gen_split(G):
        # Now H is a vertex-split of G; try deleting any subset of edges
        for subset in itertools.chain.from_iterable(
            itertools.combinations(H.edges(), r) for r in range(len(H.edges()))
        ):
            Hprime = H.copy()
            for edge in subset:
                Hprime.delete_edge(edge)
            yield Hprime


def is_split_delete_minimal(G, genus, algorithm, sorted_obstructions):
    """Checks if G is a split-delete minimal obstruction."""
    # TODO: doesn't work yet

    # has right genus
    if run_algorithm(G, algorithm=algorithm) != genus:
        return False

    # minimality under edge deletion
    if not is_obstruction(G, genus, algorithm):
        return False

    # minimality under edge contraction
    if not is_minor_obstruction(G, genus, algorithm):
        return False

    # cannot be obtained from an obstruction that has one less vertex by splitting at some vertex and then deleting some subset of the edges
    for H in sorted_obstructions:
        if H.num_verts() > G.num_verts() - 1:
            break
        if H.num_verts() < G.num_verts() - 1:
            continue

        for K in gen_split(H):
            if K.subgraph_search(G) is not None:
                return False

        # for K in gen_split_delete(H):
        #     if K.is_isomorphic(G):
        #         return False

    return True


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
