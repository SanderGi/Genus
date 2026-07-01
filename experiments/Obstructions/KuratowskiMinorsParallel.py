import os
from adj_format import from_upper_tri
from sage.parallel.multiprocessing_sage import parallel_iter  # type: ignore
from sage.graphs.graph_generators import graphs  # type: ignore


def findKuratowskiMinorsIfAny(i, G):
    K5 = graphs.CompleteGraph(5)
    K33 = graphs.CompleteBipartiteGraph(3, 3)
    result = {"K5": None, "K33": None}
    try:
        result["K5"] = G.minor(K5)
    except ValueError:
        pass
    try:
        result["K33"] = G.minor(K33)
    except ValueError:
        pass
    return result


with open("myrvold_minor_obs.txt", "r") as f:
    minor_obs = [from_upper_tri(l) for l in f.readlines()]


if __name__ == "__main__":
    with open("KuratowskiMinors2.csv", "w") as f:
        f.write("graph_number,k5_minor,k33_minor\n")
        for ((i, _), _), minors in parallel_iter(
            os.cpu_count(),
            findKuratowskiMinorsIfAny,
            [((i, m), {}) for i, m in enumerate(minor_obs)],
        ):
            f.write(f"""{i},"{minors['K5']}","{minors['K33']}"\n""")
        f.flush()
