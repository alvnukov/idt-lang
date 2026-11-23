# Which visible vertices could touch the reversed islands?

In the 250 K Apamea pair all 42 islands classified as reversed have **no
fourfold endpoint** in the reconstructed graph. Thirty-three of them lie on
two bounded simple faces. This tests a different hypothesis from the
[circuit-parity test](../ergodicity_asi/README.md): even if an update can
change *any subset* of the edges incident to a visible fourfold vertex,
it cannot touch such an island.

This support question was posed **after** the six-temperature transfer. It
is a retrospective analysis of the same classified data, not a preregistered
prediction. It reuses the [frozen geometry and all pair statuses](README.md).
Unknown transitions are never recoded as unchanged.

| K | Matched | Reversed | Reversed, no fourfold end | Of those, on two bounded faces | Minimum non-fourfold sites needed |
|---:|---:|---:|---:|---:|---:|
| 250 (pilot) | 1,061 | 42 | 42 | 33 | 34 |
| 260 | 1,036 | 57 | 54 | 40 | 44 |
| 270 | — | — | — | — | Inconclusive: frame encoding |
| 280 | 1,026 | 57 | 57 | 43 | 43 |
| 290 | — | — | — | — | Inconclusive: frame encoding |
| 300 | 1,015 | 52 | 52 | 44 | 43 |
| 310 | 1,011 | 48 | 46 | 36 | 36 |

For the last column keep only the reversed edges with no degree-four end.
A proposed set of additional sites has to contain at least one end of every
such edge. A matching of disjoint changed edges certifies a lower bound:
no site can touch two of the matching edges. A covering vertex set of the
same size certifies an upper bound, independently of how it was found. The
[executable](../../scripts/probe_apamea_vertex_support.py) returns both
witnesses and traces them to individual source rows. It checks the support
graph before applying the bipartite construction and verifies the resulting
matching and cover separately. This is an exact incidence minimum; it is
neither a count of flips nor a sufficient microscopic dynamics.

Timing matters differently in the two tests. Staggered edge readings can
give odd circuit parity even if a sequence of complete-star flips preserves
parity at every instant. They cannot turn a *truly constant* edge into a
changed one under a fixed faithful sign reader. A classification error,
an unobserved or incorrectly joined site, a different coupling, or dynamics
at lower-degree sites remains possible. Meeting two reconstructed bounded
faces is a useful location check, not independent validation of a magnetic
moment or of the entire physical incidence graph. No fundamental four-port
candidate is ruled out by this material system.

Replay: `python3 -B -O -m scripts.probe_apamea_vertex_support`. See the
[original source and its license](https://doi.org/10.5281/zenodo.8250892)
and the [experimental paper](https://doi.org/10.1038/s41467-023-41235-4).
