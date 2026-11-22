# Which event labels can be treated as independent?

The signed-stock candidate routes a whole event, but a correct histogram
does not explain which event occurs next. These probes compare three
different contracts. None establishes a microscopic source of randomness.
Replay: `python3 -B scripts/replay_primitive_probe_campaign.py --bundle sampling`.

| Candidate or control | What distinguishes it |
| --- | --- |
| Arbitrarily extendible symmetric sampling of visible labels | Chance collision forces independent uniform draws for those labels. At finite length, even the one-label marginal may be biased. |
| Unread ticks can be inserted into every ordered context | For a finite stochastic instrument, the visible law is a mixture of independent, identically distributed draws. Only a chance collision forces uniformity on its accessible components. |
| One fixed two-state stochastic detector repeated at three circuit depths | It misses the native triple `(1, 1/2, 1/8)` by a positive margin, even with nonuniform states and stochastic readout. A three-state clock can fit it. |

## Symmetric records versus causal time

For a symmetric extension to N trials with h visible labels, let f be the
empirical frequencies, u the uniform vector, and c the probability of equal
labels in two distinct positions. Direct counting gives

    A = E ||f-u||₂² = (1-1/h)/N + (1-1/N)(c-1/h).

For k≤N, coupling draws without replacement to draws with replacement
costs at most the probability b that k independent indices repeat. The
distance of the observed k-record law from uniform independent draws is
at most `b + k sqrt(h A)/2` in total variation. If E f = u is independently
known, the linear term of the product expansion cancels; the alternative
bound is `b + k(k-1) h A/4`. One may take the smaller bound. A fixed k-law
with arbitrarily long symmetric extensions with c≤1/h is therefore exactly
uniform iid; no consistency of the separately supplied extensions is needed.

**Finite counterexamples.** For N=s² binary positions with exactly
(N+s)/2 ones, c=1/2 but the single-bit bias is 1/(2s). For *fair*
pairwise-independent signs the sharp three-sign parity is at most
1/(N−2) at odd N≥3 and 1/(N−1) at even N≥4. The
[finite probe](probe_exchangeable_event_labels.py) constructs attaining
laws and independently enumerates moment-polytope vertices for N=3…21.
Without symmetry, randomly aligned independent triples (A,B,AB) are
stationary and pairwise fair, yet adjacent three-sign parity is 1/3.

**Chronological alternative.** Divide a joint record into k successive
blocks of length L≥2, then independently choose one position in each block
without seeing its labels. Given the record the selected labels have law
equal to the product of block frequencies. If C is the mean within-block
collision of two distinct positions and b_gap the TV discrepancy between
the selected law and the actual consecutive k-law, their distance bound is

    TV(consecutive, uniform iid) ≤ b_gap + (k/2) sqrt((h-1)/L + h(1-1/L)(C-1/h)).

The gap term cannot be removed: the stationary 0011 rotor gives uniform iid
under this sampling at L=4, but its consecutive four-label law is distance
3/4 from iid. Shuffling an existing log does not establish nondisturbance
of an omitted physical operation. A detector which combines fine labels
can similarly conceal shared memory.

## A machine-checkable unread operation

For a supplied d-state stochastic instrument, write P as the sum of the
outcome-labelled transition matrices. The [unread-tick probe](probe_unread_tick_instruments.py)
tests whether inserting P rather than the identity changes any ordered
record, using bases of reachable rows and observable columns. Representative
prefixes and suffixes need at most d−1 symbols each. If the condition holds,
Cesàro-averaging arbitrarily long unread gaps selects each closed class's
stationary law, giving a mixture of iid records. The excess of the pair
collision over 1/h is exactly the mixture-weighted squared deviation of the
class response vectors from uniform. Inaccessible classes do not count.
Stationarity alone is not the condition; commuting raw matrices are not
required. This is a finite certificate **for specified matrices**, not a
certificate from a finite experimental histogram for unknown dynamics.

## A different test: varying the circuit depth

In the [two-state probe](probe_two_state_readout_barrier.py) the independent
variable is the number t of repetitions of a circuit before a *final*
readout, not the index of a shot. A single two-state stochastic transition,
fixed preparation, and fixed binary response give probabilities p(t)
satisfying p(0)≥p(1) ⇒ p(2)≥p(1)². The exact best uniform approximation
to the native triple misses by 1−√(7/8), about 6.46 percentage points.
This lower bound is attained. For the exact **conditional detected** triple,
with no false clicks and outcome-dependent deletion, a common certified
retention strictly above (√113−7)/4 is necessary and sufficient for
exclusion by these three rates under that loss contract. The boundary is
attained by a detector model with outcome-dependent loss. Intervals must cover the three rates
simultaneously; a non-exclusion is not a feasibility certificate.

No measured stream has been declared iid or inconsistent with these models
here. No original candidates were removed and no public claim status changed.
