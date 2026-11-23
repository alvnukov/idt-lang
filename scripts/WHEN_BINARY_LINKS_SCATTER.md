# What two occupied links can do

A pair of adjacent occupied links can move and reappear after a collision without a particle ID, a direction field on the pair, or a collision routine. The neighborhood and the order that offers links are physical inputs to this model. A bare fork then gives a signed response: the difference between outgoing counts on two arms is the negative of the corresponding incoming difference. Connecting two forks exposes what this result leaves undetermined.

## Straight line: the clock matters

Offer alternate links of an even cycle; an offered bit flips if at least one neighboring link is occupied. This is the known **staggered reversible Rule 54**, not a new automaton and not synchronous Wolfram iteration. See [Bobenko et al.](https://doi.org/10.1007/BF02097234) and the update in [Klobas et al., section 2](https://arxiv.org/abs/1807.05000). One adjacent pair in empty surroundings advances by one link per half-step; its direction depends on the matching that fires next. In a 30-link cycle, two counterpropagating pairs reduce for two cuts to one occupied link, then separate. At half-step 10 their locations **and next matching** agree with free motion at step 8, not step 10. Comparing support alone also admits an approaching configuration. A second 46-link preparation has the same two-step delay.

There are two conserved counts. Count adjacent occupied pairs by the parity of their start relative to the next matching; add the number of isolated ones to *both* counts. [Cycle census and collision traces](probe_binary_cycle_solitons.py) checks every state and both phases on the even cycles from 4 through 16 (174,752 cases), including overlapping marks. Omitting one offer can change the counts. These are soliton counts for this dynamics, not numbers of fundamental particles in nature.

Can the global tick be removed? In the [local clock variant](probe_binary_sink_clock.py), an additional arrow orders each pair of adjacent payload sites. A site may fire only when both arrows point to it; it updates the payload and reverses both arrows. Starting with alternating arrows, different legal schedules agree when compared after the **same number of firings at each site** in the tested cuts. Equal total events alone do not suffice. While one site is silent, each neighbor's count can exceed its count by at most one per edge of separation: at most the sum of distances, or floor(n²/4), events on a finite cycle. This is a bound in events, not wall-clock seconds. Only the two consistently directed cycles deadlock. Sink reversal preserves the clockwise arrow count, so other active sectors need not reach the alternating clock. The arrows and their sector are supplied; this is not a derivation of a clock from the payload. Compare [Barbosa and Gafni's edge-reversal scheduling](https://doi.org/10.1145/69558.69560).

## A bare fork: a sign without signed marks

The [star probe](probe_binary_star_contrast.py) applies the *same* bit rule to a degree-d star. In each sweep, even links are offered arm by arm in a fixed cyclic order, then odd links. For arm i, read the number of even-start adjacent occupied pairs minus the number of odd-start pairs. Its sweep increment equals the near-end bit minus the far-end bit, both read after the even offers. Starting at an empty center, each complete burst selects every arm once. Between empty-center cuts with far ends empty throughout, if all incoming and outgoing signals are clean moving pairs, the incoming and outgoing counts obey

    O_i + I_i = K     (the same burst count K on each arm).

The probe checks 4,608 raw states with finite ends and 165 prepared cases. It does not say every state eventually cleans. Timing can change the common part: two preparations with the same inputs (1,0,1) yield (1,2,1) or (0,1,0). Changing the order *between* sweeps can break even the contrast identity. There is no nonzero assignment of nonnegative additive incoming/output weights conserved on all eight synchronous trivalent rows.

## Does the common part propagate?

With one incoming pair on each of three arms, remove one pair and average the counts over three equally weighted cyclic starts. At an isolated fork the change is exactly R times the input change, with R = (2/3)J − I and J the all-ones matrix. Remove **two** pairs and all three outputs differ from that linear prediction by +1/3. Neither the supplied clock average nor these raw counts are amplitudes.

The [joined-star probe](probe_joined_binary_stars.py) shares a physical 41-link path between two forks. All pulses are present initially; no intermediate reading prepares the second fork. For each of two launch offsets, enumerate nine pairs of fixed cyclic starts. Entries below are nine times the change at B, in the order (exterior 0, exterior 1, return path). Each row omits one input at A relative to its full reference.

| Input omitted at A | Two successive linear maps | Measured at offset 47 | Measured at offset 49 |
| --- | --- | --- | --- |
| 0 | (−4,−4,+2) | (−5,−5,+1) | (−5,−5,+1) |
| 1 | (−4,−4,+2) | (−6,−6,0) | (−4,−4,+2) |
| 2 | (+2,+2,−1) | (+1,+1,−2) | (+5,+5,+2) |

All six rows preserve the predicted port **differences**; only one preserves all three values. The return pulse is checked in motion on the bridge and later on the exterior arms of A. Nothing here rejects the binary contact as a primitive. It rejects treating this isolated-fork response as a closed linear law for connected apparatus. Geometry, clock state, observation cuts, and the physical meaning of the readout remain separate questions.
