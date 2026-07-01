# GenusPolynomial C pipeline

The main program is `genus_properties.c`. It reads graph6 records, validates
that each graph is simple, connected, and cubic, and writes one CSV row per
graph with ordinary invariants plus the exact orientable genus spectrum.

The `spectrum` column contains coefficients that count labeled orientable cubic
rotation systems. A connected cubic graph on `n` vertices has `2^n` such
systems. The C code enumerates half of them by fixing the highest vertex's
rotation bit and doubles the counts using global mirror symmetry.

## Build

```bash
cd GenusPolynomial
make
```

The Makefile assumes Homebrew's nauty install at `/opt/homebrew`. Override it
if needed:

```bash
make NAUTY_PREFIX=/usr/local
```

## Run

Analyze a graph6 file:

```bash
./genus_properties --graph6 graphs.g6 --out results.csv
```

Stream all connected non-isomorphic cubic graphs of order `n` from nauty
`geng`:

```bash
./genus_properties --generate-cubic 20 --out cubic20_results.csv
```

Quick benchmark or smoke test:

```bash
./genus_properties --generate-cubic 20 --limit 100 --out cubic20_100.csv
```

Useful speed switches:

- `--threads N`: set worker threads.
- `--no-automorphisms`: skip libnauty automorphism group order.
- `--no-matrix-spectra`: skip adjacency and Laplacian spectra.
- `--no-spanning-trees`: skip Matrix-Tree determinant.
- `--progress-every N`: progress on stderr.

## CSV format

The output is a headered CSV with one row per valid input graph. Fields are:

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
  nauty, or `NA` with `--no-automorphisms`.
- `triangle_count`, `four_cycle_count`, `five_cycle_count`,
  `six_cycle_count`: number of undirected simple cycles of lengths 3, 4, 5,
  and 6.
- `adjacency_spectrum`: sorted adjacency-matrix eigenvalues separated by
  semicolons, or `NA` with `--no-matrix-spectra`.
- `laplacian_spectrum`: sorted Laplacian-matrix eigenvalues separated by
  semicolons, or `NA` with `--no-matrix-spectra`.
- `spanning_tree_count`: exact number of spanning trees from the Matrix-Tree
  theorem, or `NA` with `--no-spanning-trees`.
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
