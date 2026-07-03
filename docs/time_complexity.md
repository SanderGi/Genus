<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Time Complexity
Let `n` be the size of the vertex set `V` and `m` the size of the edge set `E`. Let `G` be the girth of the graph.

The algorithm in this repository is roughly `O(n(4^m/n)^(n/G))`. It has some optimizations that allows it to stop early not captured in the below analysis.

- Upper bound on the number of directed trails of length `k`: `2m choose k = (2m)!/k!/(2m-k)!` which is bounded above by `\sqrt{\frac{1}{2\pi}}\frac{\left(2m\right)^{\left(2m+\frac{1}{2}\right)}}{k^{\left(k+\frac{1}{2}\right)}\left(2m-k\right)^{\left(2m-k+\frac{1}{2}\right)}}` as seen in [Bob Gallager's Information Theory and Reliable Communications](https://mathoverflow.net/questions/236508/are-there-good-bounds-on-binomial-coefficients). This is maximized for `k=m` where it simplifies to `4^m/\sqrt{\pi m}`. A simpler but less tight bound is `2m choose k <= (2em/k)^k`.
- The number of directed trails of any length is `O(4^m)` because it is the sum of the values in the `2m`th row of Pascal's triangle.
- This can also be used to upper bound the number of *non-backtracking closed* directed trails which is what our trail finding algorithm enumerates. Let `c` be the number of trails enumerated by our trail finding algorithm.
- Organizing the `c` trails by vertex is `O(2mc) < O(2m4^m)` since each trail has at most `2m` edges.

- Finding the most used vertex to explore: `O(n)` by iterating through the vertices (overall time complexity is better when write is kept `O(1)`)
- Looking up the cycles that use a vertex: `O(1)` via hashset lookup
- Checking if a cycle is used: `O(1)` via hashset lookup
- Checking if the edges of a cycle are used: `O(m)` by storing the edges used in a hashset
- Checking if adding cycle breaks rotation system: `O(m)` by storing the current rotation with the adjacency list
- Search iteration (f = implied fit, b = cycles by vertex >= u = unused >= a = w/ edges available >= d = rotation valid): `T(f) = O(n) + O(1) + b O(1) + u O(m) + a O(m) + d T(f-1); T(0) = 0` => `O(d^f * (n + b + um + am)) = O(d^f * (n + b + m(u + a))) < O(b^(f + 2))`
- All search iterations (h = number of start cycles to try out < `4^m`): `O(b^(f + 2) * h) < O((4^m / n)^(n/G) * 4^m) = O(n(4^m/n)^(n/G))`.

The algorithm is particularly advantageous for high girth graphs such as the cage family of graphs.
