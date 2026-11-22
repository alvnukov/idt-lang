# A simpler candidate: three pairs and a short memory

**Primitive data:** six unoriented marks with the operation “take the
opposite.” There are three pairs; no leg labels, cyclic wiring, spatial
coordinates or preferred signs are initially assigned. The number three
is a hypothesis, not a cosmological prediction.

**Four apparent legs.** Complete a record by picking one mark from each
pair. The eight completions fall into two sets of four: two completions
are on the same sheet if they differ in an even number of choices. No
orientation of the pairs is needed to define this *unordered* division.
On either sheet a single mark occurs in precisely two completions. Thus
the six marks are the six edges of a tetrahedron on that sheet; opposite
marks give opposite edges. Exchanging all choices identifies the two
tetrahedra. All 48 natural relabelings preserve the construction, 24 of
them preserving either sheet separately.

Let N be the number of partial records. Count how many of them are
compatible with each of the four completions, obtaining h. On the opposite
sheet the counts are **N−h**, entrywise, and the sum of h is 2N. Thus the
old four-port reflection h → (sum h)/2−h is already the relation between
the two readouts. Its squared-length invariance follows algebraically.
These are counts of *compatible completions*, not detector frequencies.
Looking from the opposite sheet changes no record. A real collision
needs an active mechanism and a detector that keeps its chart fixed.
The [origin probe](probe_three_opposition_origin.py) checks that the
nonnegative attainable h are exactly the even-total degree sequences
with no entry exceeding half the total. Three different balanced pair
stocks have the same h on **both** sheets: hidden correlations remain.

**Why three is interesting, not settled.** It is the smallest number of
pairs with two used by a four-cycle and an independent spare. For m≥2,
each individual mark occurs in 2^(m−2) completions of a given parity,
so m=3 alone makes those occurrences an ordinary two-ended edge. On the
other hand the complete bipartite graph K(2,3) has the same counts of three
visible and two hidden differences. Its edges each have two disjoint
partners, so it does not generate the same unique opposite operation.

**Where the turn comes from.** One mark alone cannot equivariantly choose
a mark in a *different* pair. Give the device two successive marks u,v
from distinct pairs. Require deterministic natural evolution, changing
pair on each step and no immediate retrace. Swapping the signs on the
unused pair fixes u and v; its members cannot be chosen individually.
The only allowed successor is the opposite of u. Thus the clock advances
(u,v) → (v,opposite u). Reversing the ordered observations reverses the
turn. Randomized successors and hidden extra memory are not excluded.

For all 24 initial flags the [clock probe](probe_opposition_clock_scatter.py)
finds **two** bijective data actions compatible with the same entire
clock orbit. Leaving the spare pair alone gives the previous mixing
reflection followed by a four-cycle on the legs. Flipping the spare pair
instead gives only a permutation of the four legs, without mixing.
A literal from the spare pair distinguishes these two actions. The
assumptions “all data follow this map” and “the spare is transparent”
are neither a clock theorem nor a probability rule.

### An actual hypothesis screen

The [five micro-candidates](../data/opposition_flag_controls.json) specify
the two marks, active or passive data coupling, accessible output, and
calibration contract. The checker generates the packet behavior from these
inputs; a precomputed output table is not accepted. A fixed calibration,
existence of **one common** calibration for both tests, and success for
every calibration are different claims. With resolved output, a correctly
calibrated transparent turn survives, the same mechanism under a particular
wrong calibration does not, and an existential version recovers it. Flipping
the spare or passively changing charts fails the specified resolved tests.
Observing only port totals can hide the wrong spare action. Small work
budgets yield inconclusive, not rejection. These are comparisons with
finite exchange/observation requirements, not laboratory evidence.

Replay the theoretical controls with `python3 -B scripts/replay_primitive_probe_campaign.py --bundle opposition_origin`.
To screen the five candidates without modifying canonical history, use
`python3 scripts/screen_hypotheses.py --batch-file data/opposition_flag_controls.json --no-cache --history-dir /path/to/disposable/history`.
The batch intentionally returns exit code 1 when it records a counterexample.
