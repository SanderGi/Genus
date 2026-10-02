# Bipartite Kneser graph embeddings

Code and certificates for *The Genus of Bipartite Kneser Graphs* by Alexander
Metzger and Austin Ulrigg.

For every prime `h > 3` with `h % 8 == 3`, the constructor gives a
vertex-transitive orientable quadrangulation of `H(h,2)`. This graph has two
copies of the two-element subsets of `{0,...,h-1}`; opposite-class vertices
are adjacent when their subsets are disjoint. Its genus is

```text
1 - h*(h-1)/2 + h*(h-1)*(h-2)*(h-3)/16.
```

The code requires **Python 3.10 or later**, with no third-party packages. 
Run without `-O` or `-OO` to disable assertions used in the checks.

## Verify the supplied certificates

From the repository root:

```bash
python BipartiteKneser/verify_all.py
python BipartiteKneser/test_certificates.py
```

The first command checks all 20,480 boundary patterns, replays all seven
exceptional-prime certificates, tests the generic construction at
`h = 131, 139, 163, 179`, and independently traces the expanded embeddings
for `h = 11, 19`. It also runs the interval certificate as a supplementary 
check; the paper proves the interval lemma algebraically.

The second command runs 18 regression tests, including rejection of altered
certificates and checks of the paper's translation order and splice paths.

## Files and paper references

| File | Purpose | Paper location |
| --- | --- | --- |
| [`kneser_constructor.py`](kneser_constructor.py) | Construct, verify, and expand base rotations. | Sections 4–8 |
| [`verify_bounded_permutation.py`](verify_bounded_permutation.py) | Exhaust the two fixed boundary problems. | Section 7, finite one-cycle verification |
| [`exceptional_certificates.json`](exceptional_certificates.json) | Full base cycles for 11 and 19; compact parameters and masks for 43, 59, 67, 83, and 107. | Section 8 |
| [`verify_exceptional.py`](verify_exceptional.py) | Read those records, reconstruct the five compact cases, and independently check Q1 and Q2 at every base label. | Section 8, exceptional-prime certificates |
| [`verify_expanded.py`](verify_expanded.py) | Check the two-subset graph and trace every dart of a full rotation. | Supplementary check |
| [`verify_all.py`](verify_all.py) | Run the checks above and generic regression cases. | Reproduction command |
| [`test_certificates.py`](test_certificates.py) | Test certificate validation and implementation conventions. | Regression tests |
| [`results/verification.json`](results/verification.json) | Saved output of the default verification command, with source hashes. | Reproduction record |
| [`results/regression_through_1000.json`](results/regression_through_1000.json) | Checks at all 43 admissible primes through 1000. | Supplementary regression record |
| [`results/unit_tests.txt`](results/unit_tests.txt) | Output of the 18 regression tests. | Test record |

## Construct a base rotation

```bash
cd BipartiteKneser
mkdir -p outputs
python kneser_constructor.py construct 43 --output outputs/h43.json
python kneser_constructor.py verify outputs/h43.json
```

For `h=43`, the report gives 1,806 vertices, 740,460 edges, 370,230 faces,
genus 184,213, and a base cycle of length 820.

An output file contains `h`, `u`, and `cycle`. Here `u` generates the
nonzero squares modulo `h`, and `(c,k)` denotes the map `z -> u^k*z+c`.
With `q=(h-1)/2`, multiplication is

```text
(c,k) * (b,l) = (c + u^k*b mod h, k+l mod q).
```

For `cycle = [s_0,...,s_(d-1)]`, the neighbor orders are

```text
A_g: B_(g*s_0), ..., B_(g*s_(d-1))
B_g: A_(g*s_(d-1)), ..., A_(g*s_0).
```

## Replay the exceptional cases

From `BipartiteKneser/`:

```bash
python verify_exceptional.py
python verify_exceptional.py --write-cycles outputs/base
```

The second command also writes all seven full base cycles. The compact
records are replayed directly, without searching for parameters or switches.
The checker validates each quadruple and both partitions of the connection
set, then checks the final base cycle using Q1 and Q2 independently.

The bundle uses `base_cycle` for the two explicit cycles. Generated standalone
files use `cycle`. Use `verify_exceptional.py` for the bundle, not the
constructor's single-file `verify` command.

## Expand and check a full embedding

After the preceding `--write-cycles` command:

```bash
python kneser_constructor.py expand outputs/base/h19_base_rotation.json \
    --output outputs/h19_full_rotation.json
python verify_expanded.py outputs/h19_full_rotation.json
```

`rotations[v]` is the cyclic neighbor order at vertex `v`.
`vertex_labels[v]` gives its class and two-subset. This verifier does not
import the constructor or use affine face equations. Full output grows as
`h^4`; keep a base rotation unless all vertex orders are needed.

## Conventions

A set mask bit switches the last ordinary transition of its fiber. The first
transition at fiber 1 is never switched. Bit 0 refers to the first coordinate
in the relevant order. Outside coordinates are ordered as

```text
Case I  (h % 3 == 1): 1,2,3,q-9,...,q-1
Case II (h % 3 == 2): 1,2,3,4,q-10,...,q-1.
```

The interval is `[4,q-10]` in Case I and `[5,q-11]` in Case II, in increasing
order. The strings in `forward_interval_maps` give images of `0,1,2`, not
cycle notation.

| Paper notation | Code notation |
| --- | --- |
| `chi_w` | The missing-fiber bit is `(1+chi_w)/2`. |
| Retained coordinate set `L` | `Reduced.outside` |
| `p_+^{-1}, p_-^{-1}` | Stored forward interval maps `P,Q` |
| `upsilon = 1+a-b mod q` | `report['z']['ell']` |
| Translation parameter `ell` | Local variable `c` in `_construct_large` |
| Number of initial zero transitions replaced (2 or 3) | `report['z']['L']`; this is not the retained set `L`. |

In the bounded checker, `q=41` and `h=83` only encode formal coordinate names.
They are used for both cases; Case I is not a test of the prime 83. The paper's
canonical-model argument establishes independence from the prime.

## Reproduce saved results

From the repository root:

```bash
python BipartiteKneser/verify_all.py --output BipartiteKneser/results/verification.json
```

For optional tests at every admissible prime through 1000:

```bash
python BipartiteKneser/verify_all.py --test-through 1000 \
    --output BipartiteKneser/results/regression_through_1000.json
```

The extra prime tests are regression checks, not the proof of the infinite
family.

## License

See the repository's [LICENSE](../LICENSE).
