<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Genus Polynomial Experiments

The main program is `compute_stats.c`. It reads graph6 records, validates
that each graph is simple, connected, and cubic, and writes one CSV row per
graph with ordinary invariants plus the exact orientable genus spectrum.

The `spectrum` column contains coefficients that count labeled orientable cubic
rotation systems. A connected cubic graph on `n` vertices has `2^n` such
systems. The C code enumerates half of them by fixing the highest vertex's
rotation bit and doubles the counts using global mirror symmetry.

## Build

```bash
cd experiments/genus-polynomial
make
```

The Makefile assumes Homebrew's nauty install at `/opt/homebrew` and a local
Flint build at `./flint`. Override either prefix if needed:

```bash
make NAUTY_PREFIX=/usr/local FLINT_PREFIX=/path/to/flint
```

The program also needs [Flint](https://github.com/flintlib/flint):
```bash
git clone https://github.com/flintlib/flint.git && cd flint
./bootstrap.sh
./configure --with-gmp=/opt/homebrew
make
```

## Run

Analyze a graph6 file:

```bash
./compute_stats --graph6 graphs.g6 --out results.csv
```

Stream all connected non-isomorphic cubic graphs of order `n` from nauty
`geng`:

```bash
./compute_stats --generate-cubic 20 --out cubic20_results.csv
```

Quick benchmark or smoke test:

```bash
./compute_stats --generate-cubic 20 --limit 100 --out cubic20_100.csv
```

Useful switches:

- `--threads N`: set worker threads.
- `--columns LIST`: compute and write only a comma-separated list of columns.
  The default is `--columns=all`. When a list is provided, the CSV header and
  rows use exactly that order.
- `--progress-every N`: progress on stderr.

For example, this writes only the graph index, graph6 string, genus spectrum,
and whether the corresponding genus polynomial has a non-real root:

```bash
./compute_stats --graph6 graphs.g6 --columns index,graph6,spectrum,has_nonreal_roots
```

## CSV format

The output is a headered CSV with one row per valid input graph. With the
default `--columns=all`, fields are:

- `index`: zero-based record index after reading the input stream or file.
- `graph6`: the graph6 string for the graph.
- `n`: number of vertices.
- `m`: number of edges.
- `girth`: length of the shortest cycle.
- `diameter`: maximum shortest-path distance between two vertices.
- `bipartite`: `True` or `False`.
- `vertex_connectivity`: minimum number of vertices whose removal disconnects
  the graph, capped naturally at `3` for cubic graphs.
- `edge_connectivity`: minimum number of edges whose removal disconnects the
  graph, capped naturally at `3` for cubic graphs.
- `automorphism_group_order`: order of the automorphism group computed by
  nauty.
- `triangle_count`, `four_cycle_count`, `five_cycle_count`,
  `six_cycle_count`: number of undirected simple cycles of lengths 3, 4, 5,
  and 6.
- `adjacency_spectrum`: sorted adjacency-matrix eigenvalues separated by
  semicolons.
- `laplacian_spectrum`: sorted Laplacian-matrix eigenvalues separated by
  semicolons.
- `spanning_tree_count`: exact number of spanning trees from the Matrix-Tree
  theorem.
- `spectrum`: exact orientable genus polynomial coefficients as
  `genus:count` terms separated by semicolons, for example `1:40;2:664;3:320`.
- `gamma`: minimum genus with nonzero coefficient in `spectrum`.
- `g_max`: maximum genus with nonzero coefficient in `spectrum`.
- `expected_genus`: expectation of genus under the uniform distribution over
  labeled orientable rotation systems.
- `variance`: variance of genus under that same distribution.
- `R`: probability of achieving `gamma`, equal to the `gamma` coefficient
  divided by `total_rotation_systems`.
- `R_1`: probability of genus at most `gamma + 1`.
- `R_2`: probability of genus at most `gamma + 2`.
- `total_rotation_systems`: total labeled orientable rotation systems; for a
  connected cubic graph this is `2^n`.
- `has_nonreal_roots`: `1` if the genus polynomial represented by `spectrum`
  has at least one non-real complex root, and `0` otherwise. This is computed
  exactly with Flint by applying its Descartes-rule/VAS real-root counter to
  the squarefree part of the integer genus polynomial.

## License
This project is licensed under the terms of the **GNU General Public License v2.0** (GPLv2). 
See the [LICENSE](../../LICENSE) file for the full text.

## Citation
If you use this code, please cite:
```bibtex
@article{Metzger_2026,
   title={An efficient genus algorithm based on graph rotations},
   volume={349},
   ISSN={0012-365X},
   url={http://doi.org/10.1016/j.disc.2026.115308},
   DOI={10.1016/j.disc.2026.115308},
   number={12},
   journal={Discrete Mathematics},
   publisher={Elsevier BV},
   author={Metzger, Alexander and Ulrigg, Austin},
   year={2026},
   month=Dec, pages={115308}
}
```
