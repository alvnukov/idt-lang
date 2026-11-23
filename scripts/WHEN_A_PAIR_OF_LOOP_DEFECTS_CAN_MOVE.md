# When a pair of odd triangles can move

On an octahedron an earlier neighbor-exchange rule could change the set of odd
triangles but could not take a state with two odd triangles to a *different*
pair. That obstruction is not a general property of the rule. On a square of
an eight-cycle the very same rule can relocate the pair from 784 of 1,392
eligible starts. Two other rules also work on the octahedron. None of these
routes supplies the sequence of centers that actually fires.

## Which choices did we exhaust?

Put a bit on each edge of a supplied simple four-regular graph. Only a center
with two marked edges may act; elsewhere the rule is the identity. For each
of its four neighbors count the marked edges at that neighbor **excluding the
edge back to the center**. Allow the center to see only which of these four
counts coincide, not the count values, port names, geometry or order. On the
six possible two-mark subsets require a reversible local map equivariant
under port relabeling. The outside counts do not change during that move.

There are 2, 2, 2, 4 and 8 allowed maps at equality partitions of shapes
`4`, `3+1`, `1+1+1+1`, `2+2`, `2+1+1` respectively. Directly enumerating all
6! permutations at each shape and checking the port symmetries produces
exactly the same maps as the eight independent binary choices in the probe.
That is 256 candidate rules in **this class**. A rule that responds to the
absolute value zero, for example, is outside the census even if it is
reversible and insensitive to port names.

An odd triangle is a three-edge circuit whose bits sum to one modulo two.
We compare subsets of triangles on the **same persistent graph**. Starting
from a two-odd state, does a path end at a *different* two-odd subset?
Intermediate states can have more or fewer odd triangles. One center acts
at a time; every permitted order is included. The counts are numbers of
microscopic initial states, not particle counts or transition rates.

## Full census and transfer

On the half-filled complete graph on five vertices, all 256 rules preserve
triangle parities; there are no two-odd starts. Of the 256 on the half-filled
octahedron, 128 preserve the whole triangle readout, 64 can change it but
never relocate a pair, 32 can relocate it from 120 of 168 starts, and 32
from all 168. Rules 66 and 130 use the fewest active flags **in this encoding**
among rules that relocate. Each hits 120 starts: the shortest path is six
moves for 72 and seven moves for 48. The remaining 48 cannot reach a different
pair by *any* path. A six-move witness has four odd triangles in between.

For transfer, keep the rules fixed. In the table each entry is
**any-path starts / one-move starts**. T is the earlier rule that exchanges
edges selected by equal neighboring counts (flag 80); F is its matched-offer
full-star control (208). The eight-cycle square joins vertices at cyclic
distances one and two; the rook graph joins cells in a 3×3 array sharing a
row or column. These incidences and their triangle readers are inputs.

| Graph; number of marks | Two-odd starts | 66 | 130 | T | F |
|---|---:|---:|---:|---:|---:|
| Eight-cycle square; 8 | 1,392 | 1,072 / 192 | 1,088 / 192 | 784 / 192 | 0 / 0 |
| Rook; 8 | 19,620 | 15,084 / 5,850 | 15,804 / 5,850 | 11,538 / 5,850 | 0 / 0 |
| Rook; 9 | 0 | — | — | — | — |
| Rook; 10 | 21,465 | 16,830 / 5,364 | 17,856 / 5,364 | 12,582 / 5,364 | 0 / 0 |

Every rook edge belongs to exactly one of the six triangles. Their parities
therefore sum to total edge weight modulo two. At weight nine the 48,620
states have one, three or five odd triangles (8,910 / 30,800 / 8,910).
There is no pair to relocate. Scoring that row as a failure would discard a
candidate for a property the fixture cannot measure. In the other rows the
three positive rules agree in aggregate on one-step *counts*, not necessarily
on their full histories. F can act without moving any triangle parity.

Replay the [full census](probe_anonymous_shell_rules.py) and
[two transfer geometries](probe_shell_incidence_transfer.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_anonymous_shell_census`.
These are finite reachability tests. Neither changing circuit labels along a
chosen path nor retaining a reversible rule in history derives an autonomous
particle, quantum amplitudes, a spatial dimension, or a Standard Model sector.
