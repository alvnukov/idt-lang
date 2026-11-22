# Anonymous carrier and resource cost

These probes separate three questions: what anonymous adjacency forces, what a
retained frame lets a decoder label, and what a binary-site implementation can
read by fixed additive weights. The results are conditional finite mathematics,
not a model of a physical detector. A cube here is a graph of relations, not
an assumption about the dimension of physical space.

## From a local reunion rule to five anonymous operations

Assume a finite, connected, simple, triangle-free graph. Every non-backtracking
two-step walk must have exactly one different two-step route between the same
endpoints. This is a **local** rule: it says nothing about pairs with no such
route. Also require a certified odd closed walk, meaning that the last vertex
really equals the first, not just that their anonymous records agree. Both
assumptions and the minimum-size or minimum-degree criterion are inputs.

Square completion matches the other neighbors across every edge, so the graph
is regular of some degree `k`. The first three distance shells have sizes
`1, k, C(k,2)`. In the canonical bipartite double cover, an odd closed walk
connects the two lifts of its starting vertex, making the cover connected. The
cover inherits the local rule and degree. An induction by square completion
gives each vertex at distance `i` at least `i` neighbors on the previous
shell. Writing `s_i` for the shell sizes, counting edges between consecutive
shells gives `i s_i <= (k-i+1) s_(i-1)`, hence at most `2^k` vertices in the
cover. For the base size `v` this gives

```text
1 + k + C(k,2) <= v <= 2^(k-1).
```

Degrees below five are excluded. At degree five both bounds equal 16, and
degree greater than five requires more than 16 vertices. Every distance-two
vertex represents a pair of root ports and must join the three vertices
representing pairs disjoint from it. This forces the folded five-cube up to
isomorphism; the fixture verifies existence and an odd return. Larger controls,
such as the folded seven-cube and the Cartesian product of the folded five-cube
with an edge, satisfy the same local rule and oddness. The ordinary five-cube
also satisfies the local rule and can match the unsigned record of the
five-step return, but that path reaches the antipode, not its start.

The adjacency-only decoder groups opposite edges of squares and recovers five
perfect matchings, each giving an involutive operation. There are 40 squares,
16 translations, and all 120 permutations of the five root ports are possible
at a fixed root. The five operations are recovered as a set, not individually
named; adjacency alone singles out neither a root nor a pair of ports. The
folded graph and rectagraph terminology are standard: see
[Fawcett on rectagraphs and cube quotients](https://arxiv.org/abs/1507.01503)
and [the antipodal-quotient construction in Section 2.1](https://arxiv.org/html/2307.03345).

## What a retained frame adds

A non-backtracking path `r -> b -> m` supplies a nonadjacent pair. **Keeping
the ordered endpoints** `(r,m)` defines the frame: the routes from `r` to `m`
distinguish a two-port block, leaving a three-port block. There are 320 oriented
two-step paths, two per frame, and 160 frames. Neither a deterministic next
non-backtracking port nor persistent endpoint memory comes for free. At a
given terminal, ten different frames are possible; even if the last ingress
is known, four remain. Forgetting the middle reversibly also needs a two-way
record. In 960 ordered comparisons with the same last edge `b -> m` but
different starts `r` and `s`, the unchanged vertex `r` scores `0` in frame
`(r,m)` and `1` in frame `(s,m)`. The last edge alone cannot determine that
readout.

Choose a lift of `r` in the 32-vertex double cover and number its recovered
ports. Supply occupation additivity, zero at the vacuum (the chosen root
lift), invariance under the ordered-frame stabilizer, and sign reversal under
the covering involution. The stabilizer makes the weights constant within
each block, so `q = a k_3 + b k_2`. The involution complements all five bits;
antipodal oddness gives `3a + 2b = 0`. This is one real line. Choosing
primitive integer normalization and a positive weight on the two-port block
selects the ray with generator `(-2, 3)`. Neither oddness nor normalization is
derived from the bare graph. Without a mark the five equal weights give only
zero under these laws; an adjacent mark instead produces the `4+1` control
with primitive weights `(-1, 4)`.

On the even sheet, the signed frame convention assigns the following exact
labels. The other lift of each vertex has the opposite value.

| Occupation `(k_3,k_2)` | Distances `(d(r,x), d(m,x))` | `q` | Multiplicity |
| --- | --- | ---: | ---: |
| `(0,0)` | `(0,2)` | 0 | 1 |
| `(0,2)` | `(2,0)` | 6 | 1 |
| `(1,1)` | `(2,2)` | 1 | 6 |
| `(2,0)` | `(2,1)` | -4 | 3 |
| `(2,2)` | `(1,2)` | 2 | 3 |
| `(3,1)` | `(1,1)` | -3 | 2 |

Those labels change when the frame changes on the **same unchanged vertex**.
For instance, reversing the anchors changes the old root from `0` to `6`.
Among the 25,600 ordered frame comparisons, only the 160 identical-frame
pairs agree up to an invertible affine change of labels; an arbitrary
bijective relabeling adds just the 160 reversals. All 160 fields remain
distinct after taking absolute values, and a common coarsening, even allowing
a different relabeling in each frame, can only be constant. Covariance under
a graph action is a different test: it transports both anchors **and** the
tested vertex. The atlas also finds that diagnosing a retained frame needs
four exact readings in the worst case if the targets have stable shared
identities; without that resource the diagnosis does not follow.

## Labels, raw wires, and additive readout are different contracts

Four bits can name the 16 even masks, and a lookup from such names can print
`q`; this does not implement a raw rewire or an additive meter. For the
following stricter contracts, encode every mask injectively as a fixed-weight
subset of binary sites, with at most `K` occupied sites. For every even XOR
translation one input-independent site permutation must implement it on all
16 preparations. Optional block or all-five permutations here are logical
coordinate relabelings realized by the same kind of raw rewire. A decoder
can otherwise be arbitrary. The additive rows additionally require one fixed
weight per raw site and a constant to read the supplied `q` on every mask.

| Minimum number of raw sites | `K=1` | `K=2` | `K=3` | `K=4` | `K=5` |
| --- | ---: | ---: | ---: | ---: | ---: |
| Decoded state, translations only or with within-block relabeling | 16 | 8 | 8 | 8 | 8 |
| Decoded state, all five ports freely relabeled by wires | 16 | 16 | 16 | 16 | 10 |
| Additive `q`, translations only | 16 | 12 | 10 | 10 | 10 |
| Additive `q`, translations and within-block `S3 x S2` | 16 | 12 | 12 | 10 | 10 |

The wire census exhausts the 65,536 possible Boolean site functions under
each supplied symmetry. For additive readout, translation orbits of site
functions must cover the five nonzero Fourier components of `q`; the finite
cover bounds are matched by explicit encodings. Those bounds concern sites
and parked units, not update time, physical locality, or preparation cost.

The eight-site, two-unit code gives a countercontrol: its two banks each
address one of four values, with independent XOR updates and no carry between
banks. A table still labels every decoded state, but any raw additive readout
on these banks has the form `A(u) + B(v) + c`, whose mixed rectangle contrast
is zero. The four actual preparations used in the probe have labels
`0, 1, -4, -3` on the two diagonals, giving `0 + 1 - (-4) - (-3) = 8`.
That atlas is therefore a decoder, not an additive readout on those wires.
A cross-block transposition also fails to act by a raw wire permutation of
that eight-site code.

## Replay and boundary

From the repository root:

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle anonymous_carrier_origins
```

The individual checks are [local reunion](probe_local_reunion_minimum.py),
[anonymous decoding](probe_anonymous_folded_carrier.py),
[marked charge](probe_marked_carrier_charge.py),
[two-turn frames](probe_two_turn_charge_atlas.py),
[the additive frontier](probe_even_carrier_resource_frontier.py), and
[the wire census](probe_even_mask_wire_orbits.py). The anonymous decoding
probe also checks a separate selector with an explicitly **global**
common-neighbor assumption; the local minimum argument above does not use it.

Candidate sources for the reunion law, certified closure, retained frames,
and an additive detector remain generic possibilities, unsupported or
unassessed by these probes. A numerical match to a label table does not
identify any observed particle. These checks do not derive gauge dynamics,
chirality, physical geometry, or quantum mechanics, and they do not upgrade
any theory claim.
