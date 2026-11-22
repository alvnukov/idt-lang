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

### What the detector can and cannot read

The [cancellation test](probe_opposition_readout.py) pairs off opposite marks
exhaustively. Its remainder is independent of cancellation order. Counting
ordered pairs of the remaining marks gives a genuinely nonnegative total
of squared differences without a background subtraction. This uses an active
comparison, not a detector sampling a random leg. Bare per-axis square
counts cannot locate the whole stock in one of two coherent outputs: signs
matter in their cross term. One tested preparation has intended weights
(2,0) yet raw port populations (2,2). Routed cancellation streams can recover
the relative weights, but the single chart loses a uniform quadrature of
the full two-complex-port carrier. A two-copy encoding supplies it at the
cost of cross-copy operations. A ticket count is not selection of an event.

The [hidden-carrier check](probe_opposition_hidden_carrier.py) also identifies
a known single-system alternative. Uniform knowledge of two out of four
completions gives six preparations, as in [Spekkens' toy theory](https://arxiv.org/abs/quant-ph/0401052).
It reproduces the isolated three-axis preparation probabilities. But only
12 of the 24 generated proper axis rotations permute those four completions;
the other 12 require a coefficient −1/2 in their unique fixed-chart linear
action. A six-state positive model with stochastic responses and reset does
reproduce the entire specified single-system experiment. Fewer than six
cannot do so with fixed reusable Markov updates and linear readout. If every
axis must have a simultaneous deterministic covariant value, eight cube
completions suffice and are necessary. None is an independent-source or
Bell experiment. The original paper is prior art, not a measurement of IDT.

### Rotating a mark versus rotating a spinor

Four quarter-turns return every mark. An [additional binary record of the
path](probe_opposition_spin_lift.py) can distinguish that history from doing
nothing; in the binary octahedral lift it takes eight quarter-turns to return
the lifted state. Different consistent lift rules exist. An isolated sign
is not observable without a phase comparison, and not every six-state
mark plus a bit admits a faithful such action. [Werner et al.](https://doi.org/10.1103/PhysRevLett.35.1053)
measured a relative phase from controlled neutron **magnetic precession**,
not a mechanical rotation of these marks. Reproducing the sign in a finite
lift does not derive fermion statistics or the experiment's detection law.
