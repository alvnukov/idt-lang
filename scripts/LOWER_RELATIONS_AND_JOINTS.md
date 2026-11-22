# What survives when the labels, detector and second system are questioned?

These searches retain three distinct things: a procedure that **constructs**
a finite pattern, an observation that **distinguishes** models, and a
physical assumption that makes the comparison meaningful. None is a
universal reconstruction of nature. The exact numbers below are not new
measurements.

## Below the five tags

The [matching factory](probe_anonymous_midpoint_factory.py) does not give
the five marks numerical names or a precomputed addition table. At each
mark, pair up the *other* four. If two centers claim the same pair, one
may change its matching. Only 6 of the 243 initial configurations are
conflict-free; all are the same up to renaming. From every configuration
there is a path of at most three changes to success. If centers and
alternatives are selected uniformly, the worst **expected** number of
proposals is 17821/678, including stalled proposals. Not every schedule
terminates; insisting that every change immediately decrease the number
of missing pairs strands 30 nonterminal configurations.

Every pair in a conflict-free state has a unique center. Looking up the
center or its opposite endpoint computes the [midpoint instrument's
contact](INSTRUMENT_REALIZATION.md). All 20 ways to coordinate a terminal
state as the affine line on five elements give the same raw update.
Five is the smallest nontrivial size **under the centered pairing and
half-turn requirement**, not a size predicted by an observation. Five
centers, four available partners, the ability to detect conflicting claims
and the scheduler have not themselves been constructed here.

A concrete rival has **21 marks**, no preferred mark, and overlapping
five-mark lines. Every circuit starting with only two tag values and
using the same contact remains on their one line. Even perfect agreement
on all such experiments cannot decide whether the carrier was five or
21. With a third *independently uniform* tag, the probability that one of
five actual line comparisons matches is 1 versus 5/21. A biased or
same-line source need not discriminate them.

## One extra setting instead of a wholesale rejection

The [four-program escape](probe_affine_reset_escape.py) uses old *binary*
contacts only. Four independently selected schedules on the same 30-wire
bank, padded to 189 contacts each, reproduce the desired conditional
readout at all six original dials. It is not one fixed linear transformation
with a random additive offset. The old carrier is not excluded by those
two-click statistics.

One extra right contact R after writing the first record is enough to
test a more specific request: does the outgoing signal behave like its
claimed native preparation? Pool the original preparations P0, P2, P4
equally. Denote by p and q the bright-second probabilities conditional on
first bright, at settings zero and R, respectively; r is bright-second
conditional on first dark, at zero. For **every independent mixture of
affine color maps**, allowing outputs anywhere among 125 triples,

```text
3p + 3q − r ≤ 5.       Requested reset: (p,q,r)=(1,3/4,0), giving 21/4.
```

The [three-rate witness](probe_affine_instrument_witness.py) needs no
perfect repeatability. Its sharp maximum-coordinate gap is 1/28. Why:
the bright sets for zero and R intersect in one plane. If an affine map
puts all three independent first-bright inputs there, it also puts all
three first-dark inputs there. Identity, inverse R, and emitting a fresh
blank triple witness tightness. A prospective binary scoring procedure
counts *all* trials; its conditional null win cap is 11/12 and the
specified alternative gives 15/16. A fixed 1,500-trial design needs
1,393 wins at a 5% threshold, with about 92.65% power **if** the ideal
alternative is IID. No trials were collected; correct first preparation,
fresh choices and lack of hidden preparer-to-controller information matter.

## Two systems: when does a six-direction coincidence mean anything?

The [hexagon construction](probe_hexagon_composite_closure.py) starts
with the actual six operational preparation rows and named window tests.
For one common set of CHSH dials the maximum depends on what is allowed
at composition:

| Joint prescription | Maximum absolute score on those **fixed** dials |
| --- | ---: |
| Mixtures of products of the specified operational preparations | 7/4 |
| Nonnegative measured probabilities with the named affine effect identities | 3 |
| Conditional preparations remain in the measured hexagon in both directions | 5/2 |
| Positivity on all affine binary tests mathematically allowed by that hexagon | 9/4 |

The bilateral prescription leaves twelve vertices of the **correlator
projection**, not twelve full joint states. At fixed sign the 5/2 extremum
determines the measured table and its flat marginals. Bilaterality is
stronger than needed for this single score. These are finite relatives of
[Janotta and Lal's restricted-effect polygon constructions](https://doi.org/10.1103/PhysRevA.87.052131),
not new empirical bounds or a native entangled emitter. Changing the dials
also changes an optimization; 9/4 is not the unrestricted hexagon's
best score over all possible measurement choices.

In the raw F5 apparatus an immediate equality comparison on the middle
wire selects **one raw phase** before preparation smearing. Its six shifts
refine the original windows. If their joint products have nonnegative
probabilities and respect the local coarse-grainings in either arm,
there is one joint phase distribution and the Bell bound is 2. No physical
simultaneous read of all six partitions is required for this argument,
but a setting-independent positive extension **is** required. Simply
simulating the extremal table by communicating settings is not a
spatially separated experiment.

Could an [actual common eraser](probe_hidden_phase_erasure.py) remove this
distinction without spoiling visibility? For the original four-ticket
source the maximum contrast after exactly equalizing all three *output*
opposite mixtures is **2/3**. Uniformly applying backward, no, or forward
one step, discarding that choice and using the old reader attains it. The
noisy phase itself can still be read; retaining the omitted choice restores
information. An abstract positive model can reach 4/5 if it preserves only
the opposite-mixture equivalences, but then it distinguishes two triad
mixtures that are identical in the actual source. The script checks the
full tradeoff against both total-variation distances, including finite
fair-bit approximations. This is not a physical impossibility of erasure.

## Charges, signs and motion: separate holdouts

* [Five-slot charge test](probe_chiral_carrier_holdout.py). Supply an even
  exterior carrier and the pairing of complementary occupations except
  for one slot. Requiring one charge per oriented channel and opposite
  charges for its dual fixes all sixteen state charges from the five
  slot charges; additivity of state charges is **not** an input.
  After a separately supplied 3+2 split and the usual representations,
  local anomaly equations are checks, not fit equations. Hypercharge,
  spacetime chirality and the number of generations are not selected.
  A single aligned generation matrix misses simultaneous quark flavor
  links under standard charged-current interpretation; [PIBETA](https://arxiv.org/abs/hep-ex/0312030),
  [KLOE](https://arxiv.org/abs/0712.3841), and [NA48/2](https://arxiv.org/abs/hep-ex/0702015)
  measured decay rates, not our carrier.
* [Reverse sign test](probe_chiral_pencil_signs.py). The unsigned pair
  support gives **identical charges**. Fix the forty nonzero positions,
  their unit magnitudes and the ten named channel directions, but let
  every coefficient sign vary. Among 1,048,576 inequivalent sign choices,
  only the exterior-algebra class has no rank-ten linear combination.
  Eighty three-channel probes suffice (20 independent parity constraints).
  Testing creation and removal separately still leaves 512 classes.
  Rank ten is a basis-independent algebraic obstruction for this matrix
  family. Neither its absence in nature nor access to coherent rank
  measurements has been established.
* [Anonymous diffusion ruler](probe_anonymous_signal_rulers.py). Nine
  stations pass only arrival-count ratios and clock horizons to the
  decoder, not port coordinates. At 512 pairs of ticks the same resolution
  policy reports three directions for the four-port quotient and four for
  the five-port control; **exact finite rank is eight in both**. The earlier
  four-port horizons instead report 5,5,4,4,4. A moving-beacon continuation
  predicts the held-out squared ranges to 0.503% on one four-port layout;
  turning back after the same history fails. With independently sampled
  arrivals, even a one-standard-deviation distinction in one nearby range
  costs more than four billion trials in that example. Exact enumeration
  makes the mathematical probe cheap, not the physical measurement.

Replay the eight probes:

```sh
python3 -B scripts/replay_primitive_probe_campaign.py --bundle primitive_origins_and_composites
```
