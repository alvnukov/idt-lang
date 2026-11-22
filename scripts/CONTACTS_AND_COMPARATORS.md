# Which contacts can generate a joint preparation?

Three different questions matter here: can a source be **built**, what do
two preparations do when **compared**, and can an internal observer infer a
structure without being given its coordinate chart? The following are finite
model comparisons, not measurements of nature. Replay all seven:

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle primitive_contacts_and_comparators
```

## A joint state made from independent edges

Start with integer currents on three labels that sum to zero. An exchange
splits a current into a stay-plus-exchange and a stay-minus-exchange output.
Opposite paths cancel on the same rail. Ordered pairs of surviving addresses
on that rail are counted; a splitter multiplies the total ticket stock by
four. Those last rules are assumptions. Given identical sign-even rail
weights, positive off zero, additive across rails, a common gain on **all**
neutral integer triples forces a quadratic rail weight. This is not a
derivation of probabilities for arbitrary measurements.

The [triangle apparatus](probe_triangle_exchange_source.py) gives six rays
and the six relative frequencies `(4,3,1,0,1,3)/4` without an angle as
a routing input. A signed circulation around the triangle yields unbiased
single-arm outcomes and joint counts `(0,48,48,0)` for equal settings,
`(36,12,12,36)` otherwise. Its three-setting cyclic witness is 9/4
against a local limit of 2. This witness is not the CHSH expression.

Does one need to prescribe the circulation? **Not as a separate source**
in this apparatus. In the [heralded preparation](probe_heralded_triangle_factory.py)
two independent nonparallel edges first enter the same laboratory. Exchange
the complete payloads and record the branch **before** the analyzer choices.
All tickets retain that record through both analyzers:

| Pre-setting branch for the specified edges | Preparation tickets | Final tickets per setting | Cyclic witness |
| --- | ---: | ---: | ---: |
| Antisymmetric | 6 | 96 | 9/4 |
| Symmetric | 10 | 160 | −9/20 |
| All issued | 16 | 256 | 9/16 |

Parallel edges give no antisymmetric herald. Reversing the inputs changes
the current's sign. If both edge labels are independently uniform, the
herald fraction is 1/4 and the unconditional witness is zero. A fixed
ticket can change Bob's output when Alice changes her setting: correct
conditional marginals do **not** make the downstream router Bell local.

The same exchange compares independent rays in one lab. It reproduces the
antisymmetric-test benchmark on all 36 pairs. Two other joint mixtures,
indistinguishable by all product trine measurements, differ under this
global test (1/2 versus 0). This is consistent with the known [failure of
local tomography in real quantum theory](https://arxiv.org/abs/1005.4870);
it does not supply a missing local complex axis. The [universal pure-state
comparison result](https://doi.org/10.1016/S0375-9601(02)01602-X) and its
[optical realization](https://doi.org/10.1016/S0375-9601(03)00262-7)
motivate the benchmark; neither is a measurement of these primitives.

## Two five-tag preparations: a positive-comparator obstruction

The earlier five-tag instrument passes those same single-packet overlaps.
But with its four-ticket preparation made **independently** twice, no
positive stochastic device reading just the two terminal phases can match
all 36 antisymmetric-test frequencies, even if the arms meet and the
device is unrestricted. For common-shift and both-orientation averages
at separation d, all such devices obey `6q₂ − 4q₃ − 5q₀ ≤ 0`; the reference
gives 1/4. The best worst-entry error is exactly **1/36**. Two
[explicit five-tag contact schedules](probe_independent_phase_comparator.py)
in an independent 7:2 mixture attain it. These schedules were selected
against the target, not predicted ahead of it. Shared preparation histories
can fake the entire benchmark with unchanged single-arm frequencies.

A [signed five-tag joint](probe_signed_phase_join.py) is a different escape:
fitting the restricted windows retrospectively needs negative mass at least
1/4 and can yield CHSH 5/2. A middle-wire read gives a purported joint
singleton probability −1/48. The context-dependent ticket allocation that
restores positive window outputs is not a setting-independent source for
all the instrument's readings. Both alternatives are retained.

## Below the table and below the coordinates

In the [anonymous five-center factory](probe_autonomous_midpoint_repair.py)
each center already stores a matching of the four other marks. In each
common round every center counts foreign claims to its candidate pairs.
If its own matching is contested, it changes to the unique alternative
with the lowest **strictly positive** number of claims, if any. It neither
uses names nor chooses a random site. Of 243 input configurations, 6 are
already valid, 12 settle in one round and 180 in two. For the remaining
45, no admissible output on the **same marks** is fixed by all symmetries
of the input. No deterministic renaming-equivariant selector can do better
without extra symmetry-breaking resources. Outputting an isomorphism
class, giving names, or letting different centers update at random is a
different task. The [21-mark rival](LOWER_RELATIONS_AND_JOINTS.md) remains.

An [active internal ruler](probe_local_angular_rulers.py) asks which
neighbors can reach each other by a two-link signal. With complete local
discovery, the reciprocal shell on a particular four-port network reveals
three independent angular coordinates in 66 pair queries; the five-port
network gives four in 190. Overlaps let observers compare independent
placements. A tree with the same local degree fails the connected shell
test, and a finite periodically wrapped network has the same immediate
chart but not its global displacement. This chart is not the first-arrival
time metric. Stable neighbor identity, signal access and a length
normalization are inputs; three dimensions have not been selected.

## Five-slot sector: a rank constraint is not a mass prediction

For the specified 16 even-occupation states and 40 nonzero complex entries
in ten symmetric channels, the [weighted pencil](probe_weighted_chiral_pencil.py)
checks exact integer changes of variables. Absence of rank ten among
freely chosen channel combinations puts all the surviving weights in one
class **only if** arbitrary invertible diagonal state and channel
rescalings count as equivalent. If only phases are discarded, 20
magnitudes remain free; even separately fixing all ten channel norms leaves
10 independent magnitude parameters. A spectrum distinguishes two examples
under unitary transformations. A zero entry invalidates the division step.
No physical rank observable, Standard Model coupling, mass, gauge group,
or population of generations has been obtained this way.
