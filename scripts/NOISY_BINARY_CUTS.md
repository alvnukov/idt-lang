# A memory screen that tolerates nonzero error and shared classical randomness

The original `prepare_measure_cut` screen correctly refuses its rank test
with an uncounted shared classical seed. Its other dimension bound can
use a diagonal of *exactly* one. Those safeguards remain unchanged. A
separate family, `binary_overlap_cut`, can still extract information from
uncertain unconditional binary events without assuming a perfect diagonal,
a square table or an unshared seed.

For preparations `i,j`, consider one chosen binary suffix with reference
probabilities `p,q`. Its squared classical affinity is

```text
f(p,q) = (sqrt(p q) + sqrt((1-p)(1-q)))².
```

For quantum states/effects this upper bounds their Hilbert–Schmidt overlap:
split the product of the state square roots using the two complementary
effects and bound the two terms separately. Classical distributions with a
finite classical message are a diagonal quantum special case. Summing all
state overlaps is at least `d²/D` for `d` preparations and `D` message
levels. Use the best common suffix for each preparation pair. The underlying
dimension-witness strategy is known; see
[Sikora, Varvitsiotis and Wei](https://arxiv.org/abs/1606.03878).
No assumption that this graph, experiment or physical universe is quantum
is proved by implementing this implication.

Crucially, the squared affinity for **binary** distributions is jointly
concave. Thus the same pairwise upper bound holds for the mean overlaps
after averaging over an input-independent classical seed accessible on both
sides. This does not assume such a seed away. Generalizing that argument to
multi-outcome distributions is unsafe: a supplied six-output classical-bit
example would be falsely assigned dimension at least 27/11. Pre-shared
entanglement, unaccounted communication, setting-dependent seed selection
and accepted-only ratios fall outside this screen.

The input consists of simultaneous outer intervals for each unconditional
event probability (or for joint event-and-acceptance per original attempt).
The maximum binary affinity in a box is one for intersecting intervals and
otherwise occurs at their nearest endpoints. The adapter rounds square-root
contributions **outward**, keeps the minimizing setting and its rational
upper bound for every pair, and reports a counterexample only for a strict
final inequality. A truncated pair budget, equality or a surviving model
cannot become a success or an exclusion. Even a cached witness is checked.
No statistical coverage or physical sufficiency of the cut is inferred
from the numbers supplied in a file.

## Exact controls

- The five-prefix raw signed-stream target at spacing three still contradicts
  dimension at most four with simultaneous absolute tolerance 39/4000. A
  simpler summed near-diagonal test no longer distinguishes this box. These
  are *prescribed* probabilities, not detector measurements.
- A genuine qubit with a shared permutation of five labels has exact
  rank five and sits **on** the overlap bound. It is not rejected, even
  before adding noise. Nor is the same model after an unconditional
  bit flip of probability 1/25 and interval radius 1/100.
- Five distinct three-bit code words, with the suffix choosing a bit to
  read, give a rectangular example without a privileged diagonal. A wide
  box admitting all probabilities is inconclusive; accepted-only input is
  unsupported.

## When are the supplied intervals about the same device?

If preparations are mostly tested when an instrument is active and other
settings when it is quiet, separately precise per-cell frequencies can form
a table no single stable instrument produced. A one-state synthetic control
gives apparent probabilities 0.9 and 0.1 in 20,000 attempts. With the
actually declared probabilities of assigning each setting, inverse-probability
weighting targets the **same time average** for both entries, giving 0.5
and 0.5, and simultaneous anytime 95% intervals [0.439306, 0.560694]
(rounded for display). Falsely declaring uniform assignment produces the
false exclusion again. A finite betting grid, conservative rational bounds
and a simultaneous error budget cover the selected stopping time; see
[Howard et al.](https://arxiv.org/abs/1808.03204) for the underlying
time-uniform concentration framework. The target may vary with past history,
while the randomized current setting must not leak to the initialized
state. A common time average preserves the shared-classical-seed bound;
it does not preserve arbitrary unshared rank constraints.

For an actual comparison the default offline campaign uses the unmodified
273-byte first CSV from [Drotos and Taoutioui's public dataset](https://doi.org/10.5281/zenodo.10723401)
with its [attribution and license](../data/processor_cut/README.md). The
selection was by filename, not witness score. All 12 preparation/measurement
cells have 8,192 registered shots; 50,833 of 98,304 outputs were zero.
The recomputed witness and its authors' plug-in standard error are
1.970586 and 0.008118. Matching the paper is arithmetic reproduction, not
independent experimental replication. It is a different quantity from
the simultaneous dimension intervals.

**Conditional on** stable cell responses, independent shots within cells
and a sufficient preparation–measurement cut, simultaneous ±0.02 intervals
exclude dimension one, not dimension two. They do not distinguish a classical
bit from a qubit. [The paper, Appendix C](https://doi.org/10.1088/1367-2630/ad4e5c)
specifies consecutive shots per circuit; the raw CSV does not certify
per-shot random assignment probabilities, isolation or stationarity. The
anytime randomized protocol above therefore **cannot** be retrospectively
applied to make a drift-robust empirical dimension claim. That claim is
unassessed.

The three source probes and eight predictive controls are pinned independently.
Run `python3 -B scripts/replay_primitive_probe_campaign.py --bundle noisy_binary_cuts`
and `python3 -B -m unittest tests.test_binary_overlap_cut tests.test_binary_overlap_cut_pipeline tests.test_binary_overlap_cut_archive`.
These are necessary conditions on a declared table and dimension, not an
automatic fit to an experiment, a sufficient reconstruction of the device
or a bound on all of nature's hidden degrees of freedom.
