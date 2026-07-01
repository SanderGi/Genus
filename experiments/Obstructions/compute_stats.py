from sage.all import *  # type: ignore
from sage.graphs.connectivity import blocks_and_cut_vertices  # type: ignore

from adj_format import from_upper_tri


def compute_stats(obstructions_path, output_csv_path):
    with open(output_csv_path, "w") as csv:
        csv.write(
            "graph #,vertices,edges,girth,min degree,max degree,average degree,num deg 3,num deg 4,num deg 5,num deg 6,cut vertices,vertex connectivity\n"
        )
        with open(obstructions_path, "r") as f:
            lines = f.readlines()
            for i, line in enumerate(lines):
                g = from_upper_tri(line)

                vertices = len(g.vertices())
                edges = len(g.edges())
                girth = g.girth()

                degrees = g.degree_sequence()
                min_degree = min(degrees)
                max_degree = max(degrees)
                average_degree = g.average_degree()

                hist = g.degree_histogram()
                num_deg_3 = hist[3] if len(hist) > 3 else 0
                num_deg_4 = hist[4] if len(hist) > 4 else 0
                num_deg_5 = hist[5] if len(hist) > 5 else 0
                num_deg_6 = hist[6] if len(hist) > 6 else 0

                blocks_and_cuts = blocks_and_cut_vertices(g)
                cut_vertices = blocks_and_cuts[1]

                vertex_connectivity = g.vertex_connectivity()

                csv.write(
                    ",".join(
                        [
                            str(i),
                            str(vertices),
                            str(edges),
                            str(girth),
                            str(min_degree),
                            str(max_degree),
                            str(average_degree),
                            str(num_deg_3),
                            str(num_deg_4),
                            str(num_deg_5),
                            str(num_deg_6),
                            str(cut_vertices),
                            str(vertex_connectivity),
                        ]
                    )
                    + "\n"
                )


compute_stats("myrvold_minor_obs_split_delete_min.txt", "split_delete_stats.csv")
compute_stats("myrvold_minor_obs.txt", "minor_obs_stats.csv")
compute_stats("myrvold_obs.txt", "obs_stats.csv")
