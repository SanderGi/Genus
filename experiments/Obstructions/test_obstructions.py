import sys

from sage.graphs.graph_generators import graphs  # type: ignore

from adj_format import from_upper_tri
from genus_algos import run_algorithm


def has_minor(G, H):
    """
    Return True if H is a minor of G, False otherwise.
    """
    try:
        return G.minor(H)
    except ValueError:
        return False


K5 = graphs.CompleteGraph(5)
K33 = graphs.CompleteBipartiteGraph(3, 3)


def main(args):
    if len(args) != 1:
        print("Usage: sage test_obstructions.py <obstructions_path>")
        print("Example: sage test_obstructions.py myrvold_minor_obs.txt")
        return

    obstructions_path = args[0]

    disconnected_count = 0
    both_planar_minors_count = 0
    with open(obstructions_path, "r") as f:
        lines = f.readlines()
        for line in lines:
            g = from_upper_tri(line)

            if not g.is_connected():
                print("DISCONNECTED", line)

                p = g.plot()
                p.save_image(f"disconnected{disconnected_count}.png")

                disconnected_count += 1
            else:
                genus = run_algorithm(g)
                assert genus == 2

                if has_minor(g, K33) and has_minor(g, K5):
                    # print("BOTH", line)
                    # p = g.plot()
                    # p.save_image(f"both{both_planar_minors_count}.png")
                    both_planar_minors_count += 1

    print("Num Disconnected", disconnected_count)
    assert disconnected_count == 3

    print("Num both K5 and K3,3", both_planar_minors_count)


if __name__ == "__main__":
    main(sys.argv[1:])
