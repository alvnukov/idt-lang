# How much of the past must reach one detector?

This packet tests a **specified** rule for an event, not whether a physical
detector obeys it. Four signed integer currents accumulate by individual
updates. On a nonzero final current, the reference event is either of the last
two rails, and its target probability is the sum of their squared currents
divided by the total squared norm. No sampling law is derived here.

## A cut which the input clock cannot label

Choose one of `d` equal-duration prefixes. After the cut, independently choose
one of `d` equal-duration suffixes. Neither a private copy of the prefix nor a
precomputed current is given to the suffix. The explicit updates give final
currents `(t,-t,1,-1)`, where `t=2g(i-j)`. Thus the all-attempt probability
of the reference event is `H[i,j]=1/(1+4g²(i-j)²)`. The case `i=j` has
probability one. Log all starts; do not discard a run merely because its
terminal detector failed to fire.

If the entire relevant cut memory has `s` classical states, each row is a
mixture of the same `s` suffix responses, so rank is at most `s`. For a
`D`-level quantum message the upper bound is `D²`. The off-diagonal row
sums of H are less than `1/g²`, so all `d` rows are independent. A finite
error bound is printed for every tested matrix. Even for input lengths
without a fixed upper limit, a fixed sufficient memory with no uncounted
shared seed cannot uniformly beat absolute error 1/2 on this one binary
event: sufficiently many prefix states must be close in the compact state
space, while a matched suffix separates their requested probabilities.
This is a supremum, not necessarily an attained error; it is not a minimax
calculation for the full four-outcome distribution.

There is a different bound when the diagonal is **exactly** one. For
preparation `rho_i` and effect `E_i`, saturation implies that the effect is
identity on the state's support. Summing the overlaps between preparations
gives `d² ≤ D sum(H)`. Unlike the unconditional rank check, this inequality
survives averaging over input-independent *shared classical* randomness.
The general adapter skips rank when such an uncounted shared seed is allowed.
Uncounted time stamps, earlier published outcomes, extra communications,
rereadable inputs and pre-shared entanglement invalidate the relevant model
premise; none is ruled out in nature by this calculation.

## Why a filter need not be a counterexample

A two-level, sign-controlled lossy filter reproduces the required probabilities
on this input family **conditional on success**. The reference probability
per original attempt is instead flat across suffix choices at a fixed prefix.
One matched example has success only once per 4,294,967,296 attempts in
expectation. More generally, on this family an exact conditional implementation
whose all-attempt numerator has deficient rank cannot keep an efficiency
bounded away from zero for *all* input lengths. This does not say every
input has low efficiency, or exclude an arbitrary apparatus with an external
record. The two source probes contain distinct filter constructions.

## A finite observable and two external comparisons

Five all-attempt probabilities from three prefixes and two suffixes give
the prepare-and-measure **dimension witness** of
[Gallego et al., Eq. 7 and Table I](https://arxiv.org/abs/1010.5064).
This is not the three-path Sorkin interference statistic. The signed
correlator score is 347/85, above the one-qubit limit `1+2√2` even if
each of the five probabilities changes by at most 1/40. A classical trit
already suffices; this is not a witness of quantumness. A lossy qubit gives
the same score on accepted clicks, but only 131/125 with all nonclicks
assigned the nonreference outcome.

The published [Ahrens et al. figure](https://www.nature.com/articles/nphys2333/figures/3)
reports 3.7815 ± 0.0782 with their optimized qubit preparations and
4.9303 ± 0.1032 with qutrits. These are the **journal** values, not the
different values in the preprint. [Hendrych et al.](https://www.nature.com/articles/nphys2334/figures/3)
report 8.57 ± 0.06 in a four-preparation, three-measurement test; their
statistic is not the three-preparation one above. Neither experiment
implements our raw signed stream. Detector-channel normalizations cannot
be relabeled all-attempt probabilities without accounting for loss.

## Replaying the boundary

The `prepare_measure_cut` candidate family takes rational probability
intervals and an explicit proposed communication cut. It tests necessary
rank and saturated-diagonal conditions. A strict violation contradicts
**only** that declared model/box combination. A surviving box remains
inconclusive; an accepted-only table is unsupported. Input intervals are
declared bounds, not automatically simultaneous confidence intervals.
The adapter does not infer a table or a memory bound from a source candidate.

Run the `streaming_memory_cut` campaign or the two modules directly:

```sh
python3 -B -m scripts.probe_streaming_observer_cut
python3 -B -m scripts.probe_linear_cut_dimension_witness
python3 -B -m unittest tests.test_prepare_measure_cut tests.test_prepare_measure_cut_pipeline tests.test_prepare_measure_cut_archive
```

Nine predictive controls in `data/prepare_measure_cut_controls.json` retain
unconditional versus selected versus joint-efficiency events, shared versus
unshared messages, distinguishable intervals and boxes admitting a fair
coin. Their immutable first observation is pinned independently from the
two source candidates. No change to the theory manifest or public claims.
