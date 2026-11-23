# What a missing click or a repeated phase choice can change

If a single carrier learns the setting of only one interferometer arm, and
the detector receives no information from the other arm, it cannot learn
the parity of two independently and uniformly chosen phase bits. This is
a constraint on **one-arm influence**, not on indivisible detection events:
a model with a field or other information in the nominally empty arm is
outside that hypothesis. The earlier [two active phase plates](HIDDEN_MODE_CANDIDATES.md)
already distinguish these cases. Here the new question is whether losses,
the analysis denominator, or a detector retaining earlier information can
change that comparison.

**Register every trigger.** For each setting pair x,y, count left only,
right only, neither, and double. Give these outcomes signed weights −1, +1,
0 and 0. Neither and double are separate recorded classes: zero score is
not a known negative click or a success on the opposite side. Average this
score over **all heralds in its cell**; then take the signed average over
the four cells with coefficients +, −, −, +. A missing trigger denominator
or unobserved cell makes the empirical comparison inconclusive.

In a one-arm model with arm choice independent of the settings, each raw
outcome has a subprobability of the form a(x)+b(y). The signed four-cell
contrast cancels exactly even when the losses depend on the setting in the
visited arm. Joint conditioning need not preserve additivity.

| Readout, assuming uniform fresh settings | One-arm prediction |
|---|---|
| Signed port-parity contrast per trigger | Exactly 0 |
| Correct fraction after *pooling* single clicks under the uniform design | Exactly 1/2 when defined |
| Average of the four correct fractions *each normalized within its own single clicks* | Can exceed 1/2; strict supremum 3/4 if all denominators are positive |

For example, give each cell eight triggers. Single-click counts 2, 5, 5, 8
and correct counts 2, 4, 4, 0 yield pooled 1/2 but stratified 13/20. Both
come from exactly the same local-loss table. For stratification with fixed
positive cell weights summing to one the sharp supremum is one minus the
smallest weight. To see the uniform bound, write the single-click rates
as rₓ+cᵧ. For each local arm response, maximizing success assigns its clicks
to the more favorable of the two priors after division by those totals.
Order rows and columns by their local rates: the four cell accuracies sum
to at most (1+c₁/(r₀+c₁)+r₁/(r₁+c₀)<3) when the smallest total is
positive. One can approach 3 by taking both small local rates to zero;
actually dropping a cell does not attain a valid four-cell score.

Two adversaries illustrate why the protocol matters:

- A censor that sees both settings can keep only correct trials. Perfect
  conditional accuracy then says nothing about all-trigger success; removing
  the count of rejected trials is a missing denominator, not a null result.
- If one setting pair is held for N shots, a persistent receiver can remember
  the bit reported from each visited arm. With independent fair arm choices
  it guesses until both have been seen. Its success on shot k is 1−2⁻ᵏ;
  the block mean is 1−(1−2⁻ᴺ)/N. At N=15,000 this exceeds 0.9999.
  Fresh independent bits on each shot give the same single-arm receiver
  only 1/2. This is a countermodel for an insufficient trial contract, not
  an explanation of the experiment.

**Experimental boundary.** [Massa et al., Fig. 3 and appendices](https://arxiv.org/html/1802.05102)
report a correct-port fraction of 0.961 ± 0.006 at visibility 0.941 ± 0.007,
and 0.498 ± 0.006 without temporal overlap. They used 100 random setting
pairs per visibility and many registered events during each 0.5 s setting;
the quoted success uncertainty is a standard error across the sequence.
The separate heralded source check gave g²(0)=0.004 ± 0.010, not a guarantee
of exactly one particle in every trial. These results are not a four-cell
table of all heralds with independent choices on every emission, so the
checker does **not** assign the new statistic to them. The [single-particle
multiple-access channel](https://quantum-journal.org/papers/q-2022-02-16-653/)
and the [two-way communication proposal](https://doi.org/10.1103/PhysRevLett.120.060503)
are antecedents, not additional experimental replications.

A prospective comparison needs fresh private settings after the path
preparation, one fixed response deadline per herald, and the complete
four-outcome table. An independently designed two-arm control can give a
nonzero contrast; neither a zero score nor the selected-click result alone
identifies the underlying primitive. Replay the [deterministic counts and
adversarial receivers](probe_single_photon_loss_memory.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_one_arm_herald_budget`.
