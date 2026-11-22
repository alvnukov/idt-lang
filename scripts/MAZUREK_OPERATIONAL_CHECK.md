# A real data check: separate the counts, the assumptions and the fit

[Mazurek, Pusey, Kunjwal, Resch and Spekkens (2016)](https://www.nature.com/articles/ncomms11780)
tested a noncontextuality inequality with photon polarizations. Their
operational procedures, not the IDT primitives, were the apparatus.
The public supplementary data permit three distinct checks. None is an
independent experimental replication.

## 1. What was recorded?

The [offline reader](../theory_experiments/mazurek_primary.py) uses the
integer outcome counts for eight preparations, four binary measurements,
and 100 runs. It pools neither settings nor denominators across different
matched cells. These are *detected-coincidence* frequencies, not raw
clicks per emitted or heralded particle. The fourth pair is retained for
tomography, not counted in the matched score A.

| Statistic | Result | Interpretation |
| --- | ---: | --- |
| Mean of the 100 primary matched scores | 0.9998691364 | Sample SD 0.0000175010; SEM 0.0000017501. |
| Pool within each of the six matched pairs, then average | 0.9998691622 | Different weighting. Neither primary number is the published secondary A. |
| Mean A from the **stored author plot** | 0.9970895242 | SEM 0.0000724423. Read as 100 points without executing Mathematica, not recomputed from counts. |
| Independent secondary reconstruction from **counts** | 0.9970325959 | SEM 0.0000766895, using the fixed default solver and source conventions. Does not round to the published result. |

File [1462 (aggregate)](https://static-content.springer.com/esm/art%3A10.1038%2Fncomms11780/MediaObjects/41467_2016_BFncomms11780_MOESM1462_ESM.xlsx)
actually contains the aggregate table; [1463 (per run)](https://static-content.springer.com/esm/art%3A10.1038%2Fncomms11780/MediaObjects/41467_2016_BFncomms11780_MOESM1463_ESM.xlsx)
contains the 100-run table. The first six preparation rows agree exactly
when pooled. All 16 entries of the last pair differ in their original
order, and agree after exchanging those two rows as a diagnostic.
**The stored integers retain both orders.** We do not settle which label
was physically intended by choosing the one with a smaller model residual.

The [normalized fixture](../data/raw_observations/mazurek2016_counts.json.gz)
is a re-encoding of those two supplementary datasets (authors above,
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). Sheet names,
cell ranges, original hashes and checks on all paired denominators are
in the reader/receipt. The repository includes neither an edited workbook
nor the authors' software.

## 2. Which part of the published analysis is reproducible?

The [optional numerical reanalysis](reproduce_mazurek_secondary.py) fits
the four observed probabilities to a three-dimensional affine state space
and constructs secondary procedures by convex mixtures. The two linear
objectives maximize preparation and measurement self-weights, **not A**.
The default keeps the source's ordinal aggregate weighting and asymmetric
fourth-pair variance term. Alternative conventions are sensitivities,
not fixes chosen to improve agreement. Across 100 runs the cached primary
fit chi-squares agree to about 1.2e−12 and optimal total self-weight
scores to about 1.2e−7 in absolute value. Floating-point agreement does
not certify identical mixture weights.

At numerically unchanged optimal self-weights, concrete alternative
mixtures yield **mean** A values 0.99696163 and 0.99718621. These are
attained choices, neither confidence limits nor global extrema. A second
solver also differs. Only 25 of the 100 default A values round to the
same five decimal places as the saved plot. The historical numerical
origin of each difference is unresolved; ties alone are not a complete
explanation. No solver was selected for matching the headline.

A useful robustness check avoids that choice. Let m be the mean of the
six matched success probabilities in the **fitted primary** table;
Cₚ and Cₘ are the average retained preparation and measurement
self-weights. Convexity and nonnegative contributions imply
A ≥ m − (1−Cₚ) − (1−Cₘ). Even if only the total 6Cₚ+3Cₘ is known to
be within 0.000001 of the attained optimum, the weaker bound is at
least 0.98478538 in every run. This is a bound *conditional on those
fitted tables*, not an uncertainty interval. Comparing to 5/6 requires
both preparation and measurement noncontextuality and the operational
equivalences. Tomographic completeness and fair sampling are physical
assumptions; neither follows from a good numerical fit.

## 3. Can the five-tag candidate be compared at all?

The [fixed-interface comparison](probe_mazurek_operational_bridge.py)
maps the three named trine directions and a fourth polar direction to the
[already specified finite exercise](probe_affine_fourth_axis.py). It does
not infer that these abstract operations were implemented by the optics.
On the pooled per-run rows, the largest deviation from the **ideal** table
is 0.01308750. The model constrained to its original center stock, a
deterministic fourth analyzer and one rotation per pole misses the **raw**
table by at least 0.23730508; this is the actual optimum over that
model class. Independent random analyzer choices have lower bounds
0.08550405 (ordinary choices) or 0.07024583 (allowing component flips)
by the triangle inequality, not measured confidence levels.

The previously specified alternative stock reproduces the *ideal* exactly,
so its largest raw discrepancy is 0.01308750. No parameters were inferred
by comparing residuals in this bridge, but the dataset already existed;
this is not a blind lab prediction. With the **aggregate workbook's own
labels**, its ideal discrepancy is instead 0.99983653. The deterministic
class optimum remains 0.23730508 because both pole rotations are freely
chosen; it cannot resolve the labeling issue. No candidate is promoted or
discarded by these distances.

Offline primary and model checks:

```sh
python3 -B scripts/replay_mazurek_primary.py
python3 -B -O -m scripts.probe_mazurek_operational_bridge
```

Optional numerical replay (NumPy/SciPy); add `--notebook-checkpoints PATH`
for the hash-verified, unexecuted [supplementary TXT](https://static-content.springer.com/esm/art%3A10.1038%2Fncomms11780/MediaObjects/41467_2016_BFncomms11780_MOESM1464_ESM.txt).

```sh
python3 -B -m scripts.reproduce_mazurek_secondary --audit-faces --sensitivities
```
