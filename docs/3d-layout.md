# Higher-genus surface layout

The web app's **3D** output, `graph_genus.embed(..., output_format="3D")`,
and `planar_draw f l o PREFIX` use the same native exporter. Genus 0 and 1
retain their existing layouts. For genus 2–20, `MultiGenus/surface_router.h`
constructs and routes on a triangulated connected sum of tori.

## Construction and routing

1. Remove facing rectangular disks from adjacent tori and join their boundaries
   with annuli. Shared mesh indices make a closed, consistently oriented surface
   of exactly the requested genus. Small Taubin smoothing steps round the necks.
2. Place separated vertex disks using farthest-candidate sampling across the
   surface. Compute intrinsic shortest-path distances between these sites and
   anneal the assignment of equal-degree vertices to reduce total neighbor distance.
   Rotate each complete port star toward its neighbors. Fan triangles keep the
   ports in the input counterclockwise order, including degrees one and two.
3. Compute a minimum-length primal spanning tree and a disjoint dual spanning
   tree of the input rotation system. Compare several length-based choices of
   dual tree and routing order. The primal tree plus the remaining `2g` edges form a
   one-face spine. Route this spine first, then the dual-tree edges.
4. Search the surface's triangle adjacency graph for each route. When an
   ordinary shortest path would disconnect the complement of the spine, search
   a finite homology cover to explore paths around the handles. A corner-based
   connectivity test checks the actual cut surface, rather than treating a
   whole occupied triangle as an obstacle. Cover searches have a bounded state
   count and use successive groups of handle coordinates for large genus.
5. Split every traversed triangle along the accepted route. Its segments become
   constrained mesh edges that later paths cannot cross. Both sides remain
   available for subsequent routing. This adaptive refinement avoids artificial
   bottlenecks near vertex disks and narrow corridors.

The connected-complement check is essential: it prevents a locally valid early
path from using a handle in a way that obstructs the remaining embedding. Once
the spine has been routed, its complement is a disk. The remaining edges have
compatible endpoint order in that disk, as prescribed by the original rotation.

## Spacing and smoothing

Routing costs include distance from existing curves and vertex disks. Several
placements are compared using total length and subdivision count. Each route
is shortened by sliding its crossing points along triangle edges.

A tangential spring flow then balances curve smoothness and the surrounding mesh.
Inserted points may move inside their original surface triangle, or along its
edge. A signed-area line search preserves a fixed fraction of each triangle's
pre-flow area. Original surface vertices stay fixed. Thus the flow preserves the
polyhedral surface, edge disjointness, and vertex rotations.

After this flow, up to six cleanup passes reroute the longest edges first.
Temporarily release one curve's constraints while all other curves remain walls.
Open its endpoint sectors between the neighboring darts, allowing departure
angles to change without permuting the rotation. A multisource shortest-path
search uses physical length and clearance costs, so earlier mesh subdivisions
cannot make a short corridor artificially expensive. Accept a replacement only
when its measured length-plus-proximity energy improves and its refined triangles
remain positively oriented. This can remove entire detours around handles,
rather than merely smoothing their existing shape. Failed replacements roll back.

OBJ edges reference the surface's own vertex indices, with one complete `l`
record per original graph edge. The browser retains every polyline knot when
building its strokes, avoiding the old uniform resampling that could shortcut
surface bends. Stroke thickness and label size use the fixed handle scale,
rather than growing with the whole model's bounding radius. Labels reference the
same endpoints as the edge records.

## Large sparse maps

Maps with more than 50 vertices, genus at least 8, at most 10 vertices per handle,
and maximum degree at most 4 use a compact normal-arc representation. This covers
the 126-vertex, 189-edge (3,12)-cage at genus 17. Small-map layouts retain the
existing placement comparisons and rerouting cleanup.

The compact path uses a 24-by-16 mesh per torus, with appropriately sized neck
openings. After each edge insertion it discards subdivision diagonals that carry
no topology. Crossings of the original surface edges remain ordered. An empty
bigon can be removed only when its crossings are consecutive both along the
curve and along that surface edge. Once these bigons are removed, arcs inside
an original triangle join different sides and can be straightened simultaneously
without crossing. The resulting convex cells receive minimal triangulations;
obsolete vertices are reclaimed. This prevents repeated subdivision from growing
into millions of triangles.

The route search uses physical distances and a consistent Euclidean A* potential.
Two-sheet parity covers are tried before the larger homology covers, and clearance
is computed once per edge rather than once per retry. Forest edges join different
boundary components and need no separate connected-complement scan. All other
spine edges retain that check.

After the first valid placement, 48 coupled one-dimensional flow sweeps shorten
normal arcs and spread their crossings along the original surface edges. A
logarithmic spacing barrier and bounded Newton steps keep crossings strictly
ordered. This replaces the expensive triangle-by-triangle spring checks and
all-pairs proximity scans of the full cleanup for these large maps. Centerlines
remain on the same polyhedral surface with the same vertex rotations. The
coarser routing mesh and first-valid-placement policy trade some geometric detail
and layout optimization for interactive latency; dense bundles can still occur.

Reproduce the timing with fresh native processes (no layout cache):

```sh
make -C MultiGenus planar_draw
python3 tests/benchmark_surface_router.py --page --runs 3
```

The benchmark reports PAGE separately from layout plus OBJ export. Rendering and
browser parsing are not included. The former exporter had not completed the
(3,12)-cage after 90 seconds in the development benchmark; the compact exporter
had a median of **1.99 seconds** over three fresh exports on the same arm64
machine (1.958–2.136 seconds), with PAGE taking another 0.708 seconds. Exact time depends on the
rotation system, placement retries, compiler, and hardware.

## Compatibility and limits

The legacy surface remains available with `planar_draw ... --legacy-surface`.
The web app uses this only for `3d_raw`, which supports the saved manual K3,3
layout and its editor. Normal 3D requests do not use polygon-to-surface projection.

The native exporter's existing input and genus limits still apply. Route search
and placement retries are bounded; difficult inputs can return a routing error.
A failed search does not export a partially routed or crossing drawing. Dense
embeddings can still have tight bundles, and finite-width display strokes can
visually overlap even when their mathematical centerlines are disjoint.

## Verification

Run:

```sh
make -C MultiGenus planar_draw
PYTHONPATH=src python3 tests/test_graph_genus_package.py
python3 tests/test_surface_router.py
node tests/test_surface_strokes.mjs
```

The surface tests independently check closed oriented mesh incidence, Euler
characteristic, finite coordinates, nondegenerate triangles, exact edge endpoints,
complete edge coverage, disjoint route interiors, and local rotations recovered
from the oriented triangle fans. Cases include K3,3 variants, genus-2 K8,
genus-3 K9, genera 4 and 6, bridges, cut vertices, deterministic export, and the
legacy manual surface. Fixed (3,6)-cage and genus-4 (3,8)-cage rotations also
check these invariants, total route length, sampled inter-edge proximity away
from junctions, and departure arc/chord ratios to catch vertex hairpins. Proximity
sampling is an aesthetic regression metric, not a global clearance proof.
The genus-17 (3,12)-cage fixture, its mirror, a relabeling, and an attached bridge verify the
normal-arc path and bound mesh complexity to prevent refinement blowup. The
browser geometry test checks that short polyline segments retain their exact
centerline knots.
