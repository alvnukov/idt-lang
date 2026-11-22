# Do signs and the square have to be put in separately?

These probes distinguish three questions often hidden in the word
“amplitude”: what represents a relative minus, what fixes the **total**
available detector stock, and which individual event is recorded. The
first two have conditional answers here. They do not answer the third.

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle transfer_stock_and_trials
```

## Two candidates below signed currents

An [unsigned transfer](probe_unsigned_transfer_triangle.py) has a start and
an end. An arriving transfer can splice to a departing one at the same
mark; loops disappear. Signed currents then describe *boundaries*, not
negative objects. Splicing terminates and preserves the readout from
unmatched endpoints, even when two different original endpoints could have
been paired. A path-sensitive detector need not respect this equivalence.
If the raw two-input construction must commute with exchange and reverse
its actual net flow when either input is reversed, a symmetric square
requires four transfers. Its checkerboard boundary is twice the usual
unit product. Relaxing microscopic covariance can remove this factor.

In the [unoriented alternative](probe_bipartite_triangle_origin.py), even
the arrows disappear. Occurrences on a connected bipartite graph are
opposite if a connecting path has odd length; no part of the readout needs
a named positive color. Make two copies. Join corresponding occurrences
across the copies, or join each occurrence to copies of its neighbors.
These two uncolored wirings implement opposite relative alignments.
The ordinary Cartesian graph product of two independent packets constructs
the unit joint boundary without a chosen color or the previous doubling.
Starting from just one link per packet, the probe checks all 36 single reads
and 81 joint configurations in both orders. Two nonparallel seeds give
6 antisymmetric heralds of 16 and the known trine table; parallel seeds
give none. The same pair of disconnected inputs can give **8 or 0 events**
after different connections. Coherent wiring, a partition into readout
rails, the product rule and a detector remain assumptions. This probe
counts events; it does not transport microscopic detection addresses.

## A stock law without assuming a quadratic norm

Let W be any nonnegative total stock assigned to neutral integer triples,
with W(0)=0. For each transposition P, split a prepared v into v+Pv and
v−Pv. Suppose the two branch stocks add and their sum equals a positive
constant times W(v), the constant possibly different for each setting
but **not depending on the input**. Require this for every integer triple.
No rail-wise additivity, sign-evenness, label symmetry, known gain, or
ordered-pair formula for W is imposed.

The [integer argument and independent finite controls](probe_triangle_stock_rigidity.py)
leave exactly two nonzero possibilities, up to overall scale:

| Whole-packet stock W | Gain | Median preparation (2,−1,−1) |
| --- | ---: | --- |
| Sum of the three squared components | 4 | Bright |
| One unless all components agree modulo three, zero otherwise | 1 | Dark |

The setting gains become equal by splitting a doubled current. The relation
on the edge stocks at integer scales then fixes the two branches. A finite
matrix-rank check is an independent check of small instances, not a Lean
proof of this all-input statement. A lighted median distinguishes the two
global laws. **Preparing only one edge and repeatedly splitting it cannot
establish that these are the global laws:** positive alternatives with
other gains work at arbitrary depth on its accessible rays.

The [untouched bypass](probe_triangle_bypass_normalization.py) makes the
gain premise testable using relative frequencies. Preserve v in a separately
readable port alongside the two outputs. Under matched port response a
constant bypass fraction p implies gain (1−p)/p on positive inputs. An
alternative that doubles stock only away from all analyzer output rays
passes every ordinary normalized two-output reading, but on (2,1,−3) the
bypass gives 1/3 instead of 1/5. A rival modified only on multiples of seven
survives this preparation; the stated setting on (4,−3,−1) gives 13/114
instead of 1/5. A bypass with input-dependent efficiency can counterfeit the
whole result. None of these frequencies has been observed for this model.

The [candidate checker](../theory_experiments/triangle_stock.py) can test
submitted, label-dependent sums of squares of integer affine forms,
specified separately on residue classes of a chosen modulus up to seven.
Each split-gain residual is a degree-at-most-two polynomial on each residue
class. Six interpolation points per class and setting are enough to decide
the identity there and at all its integer translates. A full run is thus
complete **within this language**, not for all functions W. Unknown detector
pedestals and no signal are not physical counterexamples. The [batch](../data/triangle_stock_controls.json)
retains the median-dark alternative as a successful gain-law model, not
as a model of a detector already known to have a bright median.

## Preparation versus a particular detector click

At a common source one can [apply a coherent partial exchange](probe_native_partial_exchange.py)
to two data triangles after their references have been matched. Two raw
edges give CHSH 33/16 **without** a local herald cut. Those settings were
found by a finite scan. With an intermediate path record the score drops
to 9/8; with no reference turn, to 3/4. On a *different*, preselected
orthogonal input the specified settings give 5/2 on the local preparation
flag (probability 3/4); the other flag gives −1, and the complete score
is 13/8. The addressed simulation is not a Bell-local account of detector
outcomes or an experiment on separated particles.

The [prospective comparison protocol](probe_reference_sewing_trials.py)
instead tests the earlier one-copy independent-reference bound. Under its
explicit hidden-frame distribution and no class leakage, a win probability
of at most 3/4 contrasts with an ideal 5/6. For a fixed 317 complete trials,
at least 256 wins has null probability at most 0.009248; nominal iid ideal
power is 0.90245. At 255 the threshold is not crossed. Sending the class
label, synchronizing the two nominally independent frames, or restricting
preparations to the poles invalidates the intended comparison. This is a
design with synthetic controls, not a measured significance.
