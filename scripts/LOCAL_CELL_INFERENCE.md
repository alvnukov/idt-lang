# What does detector timing actually select?

Earlier [local clock probes](INTERNAL_DETECTOR_CLOCKS.md) supplied a cell
that exchanged a carried bit with a stored one. Here the cell starts as a
**completely unknown lookup table**. Its three inputs are the incident side,
the carried bit and the local bit; its three outputs are the outgoing side
and the two updated bits. All sites use the same table. A fixed reciprocal
loop, ordinary propagation, a blank initial apparatus and a marked return
port are still supplied. The target time is **synthetic**, not measured in
a lab. The inferred cells are candidates within this specified architecture.

Train on fresh forward passages of lengths 2 and 3. Require the first
marked return after exactly n² equal edge hops. Hold out the reverse
preparations of those two lengths and both directions for lengths 4–12.
Distinguish timing alone from also restoring the direction and all cells.

| Local family | Trained: timing | Held-out: timing | Held-out: timing and restoration |
| --- | ---: | ---: | ---: |
| 764 involutions (reciprocal scatter, possible reflection) | 6 | 4 | 4 |
| All 16,777,216 deterministic tables with one bit per site | 222,528 | 164 | 128 |
| All 256 deterministic tables without writable site state | 0 | 0 | 0 |

Here “held-out” counts rules surviving both training and holdout. With
restoration demanded already in training, 75,984 unrestricted tables
survive the two short lengths. This is exact finite inference within the
table class, **not** a probability that any candidate is physical.

### What the surviving tables have in common

The [reciprocal census](probe_reversible_cell_census.py) tests every local
involution, including ones that create or erase marks or favor one
direction. In *all four* surviving rules, the two bits exchange places.
On empty inputs a carrier goes straight. The rules differ by two decisions:
whether to reflect when the bits differ and whether to reflect when both
are one. Only one of the four never reflects. No conservation constraint
or desired exchange table was supplied to the search.

Why do different spatial rules give the same time? Launch one mark into a
blank n-edge petal. At each of the n−1 interior sites the cursor drops it.
With no other mark present the empty cursor makes a full n-edge lap, picks
it up, then carries it one site farther. Reflection on both drop and pickup
restores the direction just as passing through both does. The total is
n ordinary forward hops plus n−1 laps of n hops: **n²**. The double-marked
row is never used. Two observations at the local hub suffice to tell the
four apart: on a blank channel of length five the first unmarked return
is at hop 2 or 5; on a length-three channel with both interior bits set,
the first marked return is at hop 2 or 3. Each logical hop here equals
four hops on the independently checked subdivided physical graph.

The [first-class clock projection](probe_cell_rule_clock_projection.py)
tests four signed packets, every live home and both signal directions. On
each of the 28 blank preparations the **complete compiled signal and clock
tables** coincide across all four rules after numbering states by first
visit. This is stronger than equal frequencies but weaker than identical
hardware. The more detailed port calendars do not coincide.

### What removing reciprocity changes

The [unrestricted solver](probe_unrestricted_cell_tables.py) branches on
a table row only when a simulated passage first needs that row. If a fixed
prefix already fails the contracted deadline, all its unused completions
share that outcome. Its disjoint wildcard words represent the survivors
exactly; any of the 16,777,216 IDs can be replayed. An independent [C
oracle](audit_cell_census.c) also evaluates **every complete table** and
the regression compares every first-failure count and every winning ID.
The [764 reciprocal maps](../data/reciprocal_cell_census.json) and the
[unrestricted partition](../data/unrestricted_cell_census.json) are
retained, not just the preferred choices.

The 128 restoring cases occupy just two wildcard words: `421*065*` and
`465*021*`. The two stars are the two incident directions for a
double-marked cell, with eight possible outputs apiece. Only four of
the 128 are locally bijective; the others can be irreversible on unseen
inputs. Across the larger set of 164 timing survivors seven are bijections.
So the scarce data do not select microscopic reversibility.

The extra 36 are *not* fresh-input failures: every one also matches timings
for both directions at lengths 13–35 and 64. The simpler intervention
is to reuse a length-two apparatus without resetting. For each of the 36,
one launch direction then returns in **two** hops on the second passage
instead of four. A contract that permits resetting is still different;
these candidates and their original outcomes remain in history.

### What about quantum exchange?

In the [fixed-occupation intervention](probe_cell_exchange_intervention.py),
the underlying cell is still an unsigned permutation. Acting on a **supplied
coherent difference of the two directions**, a reflection contributes a
minus sign. In the coherent sum sector it does not. Two dual-rail
preparations with exactly two excitations in every term, followed by
calibrated mixers, distinguish the double-occupancy reflection: equal
outputs have probability 1 or 1/2 in the odd sector. Changing the
one-body routing phase does not change the two-mode phase invariant.
One even-sector implementation acts like an ordinary swap on binary
occupations; this is not a multi-occupation boson model. Binary site
capacity, coherent preparation, optical-style mixers and quadratic
readout are not derivations of Pauli exclusion or particle statistics.

The [phase-reference comparison](probe_photonic_exchange_reference.py)
explains why an actual optical sign measurement is a different claim.
[Tschernig et al.](https://doi.org/10.1038/s41566-021-00818-7) extracted
−0.04 ± 0.07 rad (95% confidence interval) for photons, using calibrated
path phases and an apparatus geometric π. [Wang et al.](https://doi.org/10.1103/PhysRevApplied.18.064024)
reported +0.04 ± 0.06 rad (Monte Carlo standard deviation) in a different
postselected photonic experiment. Their phase near π was *programmed*,
not measured on fermionic matter. In the toy cell a local dynamical π
when both addressed bits are occupied exactly mimics the negative
odd-sector sign, including the empty-arm and path-tag controls. A fringe
measures a relative phase, not what caused it.

Run `python3 -B -m scripts.replay_primitive_probe_campaign --bundle local_cell_inference`.
For an independent full-table comparison when a C compiler is available:
`python3 -B -m unittest tests.test_exhaustive_cell_oracle`.
