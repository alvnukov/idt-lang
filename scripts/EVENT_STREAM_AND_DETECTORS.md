# One click, repeated clicks, and a detector that retains a record

The [event router](ROUTED_EVENT_CANDIDATE.md) is a bijection on finite
tags. That fact alone does not generate randomness or cause irreversible
absorption. These independent trials distinguish those questions.

The [same-port shutter test](TRANSPARENCY_FROM_A_SHUTTER.md) goes in the
opposite direction: a retained signal can select a property of the
*operation*, provided that the raw echo and port-local gain are already
established. Neither a click label nor a normalized survivor count suffices.

### Events need not be independent to have the right frequencies

At each gate, give each arriving tag its own persistent counter, cycling
through that gate's h seeds. Start with one reproducible source tag. For a
fixed device word, a run of h₁⋯hₖ injections visits every stage-k tag
exactly once, for arbitrary initial counter offsets. Inductively every
parent is visited hₖ times, takes every seed once, and the local route is
bijective. The schedule repeats on that period. A single synchronized
mixed-radix clock also works, but requires knowledge of previous gains.
A fresh reset to the same state on each shot does **not** work.

The [stream probe](probe_rotor_event_stream.py) checks 96 combinations of
words, matchings, offsets and schedules. On three ports the per-address
clocks give the correct 8:4:4. One uncoordinated counter per gate gives
8:0:8 with the tested zero offset. Neither counting method explains
the origin of a preparation, clock, independence between devices, or
the statistics of randomly chosen settings.

On the fixed single splitter with one token the ideal stream is a cyclic
permutation of four addresses, two of each port. Every sliding block of
four triggers is balanced. Four iid fair clicks are balanced with
probability 3/8. In the tested 0011 order, even the ideal lag-one
conditional probability is 1/2; a pair-correlation test alone misses the
determinism. With stationary initial phase and independent 50% detection
efficiency, the same rotor gives P(balanced four detected clicks)=63/125,
P(four left)=8/375; dead time or outcome-dependent losses need not follow
this formula.

The [trigger alignment check](probe_trigger_alignment.py) instead computes
the *least* missed true arrivals needed to embed a binary record in any
balanced four-cycle with unknown start. An uninterrupted record `000011`
requires two misses. A certified maximum of one excludes the model; two
do not. Insertions and resets invalidate that exclusion. The independent
exhaustive oracle checks every word through length seven. If the target
is an iid fair stream, the asymptotic least missing fraction over the
two cycle types is 1/3. That is not a threshold for finite observations.

### The cost of exact versus approximate sampling

With t repeats of the [native three-port word](probe_native_recurrence_witness.py),
its fixed-port return has reduced denominator exactly 2^(2t−1). Let
π=1+i; π² times the word matrix has rows (iπ,π,0),(i,−1,π),(1,i,iπ).
Modulo π the injected first basis vector maps to the fixed (0,1,1).
The first numerator at every positive t is π times an element nonzero
modulo π; its norm cancels exactly one factor of two. Direct integer
propagation checks t=1,…,128.

A fixed finite uniform seed stock needs this divisor to give the exact
rate. For an autonomous deterministic device operated repeatedly under one
fixed setting, its eventual shot-boundary cycle must have a length divisible
by that denominator. A fresh bounded fair-bit Bernoulli sampler needs at
least 2t−1 bits in the worst case. This does **not** imply an exponential
simulation-time or mean-bit lower bound: for a known target with denominator
2ᵈ, binary comparison costs exactly 2−2^(1−d) fresh fair bits on average.
At each depth k<d at least one prefix must remain undecided; comparison
attains that bound. This comparison presupposes the answer, so it is a
computational control, not a microscopic readout.

### A detector assembled from swaps stores rather than destroys

In [the native memory probe](probe_native_absorber_memory.py), two layers of
native swaps transport a source excitation onto distinct finite delay lines.
It stays off the source for H ticks and returns at H+1. For an isolated
source space S and storage D orthogonal to it, exact lossless retention
UᵗS⊂D for t=1,…,H makes those H images mutually orthogonal. Hence
dim D≥H dim S. The finite examples attain this capacity (using active tape
modes); no finite closed unitary can provide permanent irreversible capture
of that entire source subspace. A coherent split can be reversed; it is not
observation of two half-energy clicks. Converting the record into deposited
energy, or erasing it with a reservoir, requires further dynamics.

### Contact with measurements

[Jacques et al., Science 2007](https://doi.org/10.1126/science.1136303)
report closed-interferometer visibility 0.94, and in a separate open
configuration anticoincidence α=0.12±0.01. The [benchmark](probe_interferometer_benchmark.py)
uses the authors' aggregates, not reconstructed raw data. A phase-blind
path label with fixed throughput gives no fringe; splitting a *common*
fluctuating intensity into two monotonically responding, conditionally
independent detectors gives population α≥1. The ideal coherent, exclusive
model gives V=1 and α=0, not the exact observed values. Ordinary quantum
optics already accounts for these effects: neither result is an IDT-specific
prediction. Figure 3 rates were dark-count corrected; no invented uncertainty
or fitted explanation is used.

For a timing comparison, [Luo et al.](https://doi.org/10.1364/OL.396561)
report nonoverlapping raw-pair extraction from a two-port click stream.
Their stated rates imply an interior fraction of unequal raw pairs,
not an exact event count. Every strictly balanced sliding-four stream is
period four; all six such words have an unequal nonoverlapping-pair
fraction either zero or one at fixed alignment. This comparison challenges
the rotor on **uninterrupted detected-click indices** only. The continuous
source, missed arrivals, dark counts, timing and acquisition segmentation
preclude transferring it to a rotor on unobserved emitted trials. No raw
time series from this paper was replayed or used to fit a candidate.
