# Raw detector-signal replay: Gstir2021

The standalone replay reduces **every recorded photodiode voltage sample** in
both pinned 23°C and 30°C runs: 314,400 binary64 samples, 6,960 context records,
870 complete cycles. It reports exact arithmetic on digitized voltages, not
exact physical means, probabilities, uncertainty estimates, or an empirical
acceptance/rejection of a primitive. `candidate_verdict` is `not_assessed`.

No candidate family, old candidate, history baseline, manifest status, or
existing `published_observation` behavior is changed. The latter still uses
the distinct Sinha2010 published summary, not these raw files. No QM derivation,
Born-rule violation, or replacement-theory confirmation follows from this replay.

## Reproduce

The dataset is Gstir, Chan, Eichelkraut, Szameit, Keil and Weihs,
[Datasets for “Towards probing for hypercomplex quantum mechanics in a waveguide interferometer”](https://doi.org/10.5281/zenodo.5497283),
version 1.0.0, published 2021-09-07, CC-BY-4.0. The
[paper](https://arxiv.org/html/2104.11577v2) has DOI
[10.1088/1367-2630/ac2451](https://doi.org/10.1088/1367-2630/ac2451).
See §4 and Appendix B, equations 32–33. The
[fixed registry](data/raw_observations/gstir2021.json) records provenance,
native schema, hashes, selection lists and independent regression oracles.
Author analysis code is not supplied in the archive.

Download explicitly into a fresh temporary directory; the script never fetches
or runs source-supplied code. Raw HDF5 files (~17.7 MB together) are not committed.
Commands below require `curl` and `uv`; alternatively install `h5py` in your own
Python environment and run the same script directly. The standard checker and
pure arithmetic tests need neither `h5py` nor NumPy.

```sh
raw_dir=$(mktemp -d /tmp/idt-gstir2021.XXXXXX)
curl --fail --location 'https://zenodo.org/api/records/5497283/files/23degrees%20measurement.h5/content' --output "$raw_dir/23degrees_measurement.h5"
curl --fail --location 'https://zenodo.org/api/records/5497283/files/30degrees%20measurement.h5/content' --output "$raw_dir/30degrees_measurement.h5"
uv run --with h5py python scripts/replay_gstir2021.py --raw-directory "$raw_dir"
IDT_GSTIR2021_RAW_DIRECTORY="$raw_dir" uv run --with h5py python -m unittest tests.test_raw_signal_replay
python3 -m unittest tests.test_raw_signal_replay
```

The CLI prints a compact primary summary. The full deterministic report defaults
to ignored `dist/gstir2021-raw-replay-v2.json`; select `--output` for another path.
The `/2` schema adds per-run nuisance assessments. Old `/1` reports are retained,
not overwritten. The compact summary prints each assessment and missing bounds
alongside arithmetic execution status.
An identical existing report is left intact; different existing contents are
never overwritten. Exit 0 means completed descriptive processing only. Exit 2
means input/data/operational error, never a primitive counterexample. Reports
contain no execution-time timestamp. Source, registry, recipe and implementation
hashes bind the calculation; changes since import or during execution fail closed.
These are integrity/provenance checks, not independent proof certification.

Pinned raw SHA256 values:

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `23degrees_measurement.h5` | 7,559,592 | `d45d525407eb64668cdecbf085a93bd7da31d8c48690ea7bcaaa98e0c0402a6a` |
| `30degrees_measurement.h5` | 10,145,888 | `e78c032673c3aabca6eff54c6f26a6b41f1f50f9e3fb7e9200e20ead291d53af` |

## Explicit reduction, not the authors' inference pipeline

Each consecutive eight context records is one cycle. Each mask 0–7 must occur
exactly once, preserving its randomized acquisition order; A is the low bit,
B the next, C the high bit. For each context, `p[mask]` is the exact mean of
**all** recorded PD values using `Fraction.from_float`. This full-window choice
is our named recipe, not a claim to reproduce author settling-time processing.

```text
epsilon = p7 - p3 - p5 - p6 + p1 + p2 + p4 - p0
delta   = |p3-p1-p2+p0| + |p5-p1-p4+p0| + |p6-p2-p4+p0|
kappa   = epsilon / delta                         (when delta != 0)
aggregate kappa = mean(cycle epsilon) / mean(cycle delta)
```

The `-p0` epsilon term implements same-cycle empty-context background subtraction.
Aggregation is neither mean(cycle kappa) nor delta of pooled context means.
A zero-delta cycle remains in the complete inventory and both aggregate sums;
its kappa is null with an explicit reason. All 870 actual cycle denominators
are nonzero. No fitted parameters, gain calibration or primary outlier cuts.
Fractions are authoritative; decimal display is deterministically rounded to
18 significant digits and is not an uncertainty statement.

| Primary all-cycle replay | 23°C label | 30°C label |
| --- | ---: | ---: |
| Cycles / samples per context | 420 / 40 | 450 / 50 |
| Mean epsilon (V), rounded | -0.00134503161222477862 | 0.000342929919478711226 |
| Mean delta (V), rounded | 1.03035238993435856 | 0.703538370090745378 |
| Kappa, rounded | -0.00130540931953432706 | 0.000487435986518373778 |

Independent exact binary64 aggregate oracles are frozen in the registry; separate
NumPy reductions agree within their last rounded digits. These are software
regression checks, not data-acceptance thresholds or independent physical evidence.

The report keeps original one-based cycle/record IDs, all eight context means,
acquisition order, sample counts and calendar time windows, epsilon, delta,
kappa/undefined reason, and every cut flag. Schema, binary64 dtype, native units,
devices, counts, finite PD samples, integer/unique masks, valid calendar components
and nondecreasing sample times are checked. File/schema failures do not return
partial successful inventories or relabel incomplete cycles as complete.

## Ancillary telemetry imperfection

30°C housing telemetry contains **one recorded NaN**, at one-based record 1167,
cycle 146. The run retains all 450 cycles; 3,599 temperature-channel voltages are
finite and one is explicitly null with `recorded_nonfinite_nan`. The 23°C file
has no such dataset: all 3,360 contexts are `not_recorded`, not inferred missing
sensor readings. Nonfinite ancillary values preserve NaN/positive-infinity/
negative-infinity classification, with per-run counts, and are never imputed.

This channel is unused in reduction and is not a certified phase or temperature
bridge. Sensor voltages remain volts, without conversion to Celsius. Nominal
temperature labels/set values are metadata, not inferred measured temperatures.
Calendar sample times are not exposure durations, trigger counts or UTC assertions.

## Separate historical-cut diagnostic

The Zenodo description supplies Mathematica index lists but does not explicitly
confirm their index base. We retain the convention
`published_indices_interpreted_as_one_based_not_explicitly_confirmed` in both
the report name and status. If any context of a cycle is listed, only this
diagnostic excludes the whole cycle. All original cycles and mask-specific
cut reasons remain in the primary inventory.

Under that **conditional index interpretation**, 328/420 and 433/450 cycles
remain; approximate diagnostic kappa values are -0.00140221277074117 and
0.001127318358195. They are near the paper's rounded centers (-0.00140 and
0.0011), but that supports neither confirmed indexing nor exact author
reproduction. We do not reproduce their quoted uncertainties (±0.00008 and
±0.0004), uncertainty model or crosstalk treatment. Historical dataset/cut
selection is not prospective preregistration.

## Remaining physical walls

The existing fixed-path quadratic ideal zero is mentioned only descriptively,
under its supplied readout assumptions. Ideal kappa is zero only if the
**ideal-model delta is nonzero**; positive/nonzero recorded denominators do not
establish this ideal-model condition or the physical readout bridge.
A common positive affine detector
response preserves kappa; negative gain flips its sign. Neither gain/polarity
convention is inferred from these files. Context-dependent gains, nonlinearity,
shutter effects and other nuisance biases are unmodeled, not assumed zero.
The paper attributes its nonzero results to shutter crosstalk and reports
independent detector-nonlinearity measurements as Peres ΔF corrections, not
transferable epsilon-voltage bounds; this replay makes no automatic correction
or contrary claim.

Native primitives still lack a derived physical preparation/path/detector bridge.
No confidence/acceptance rule, inference engine, universal apparatus prediction,
physical-temperature calibration or proof-status upgrade is introduced. The
typed task/boundary record is in
`Proofs/MetaLang/V8CheckerResearchProgram.lean`.

## Conditional signed epsilon enclosure

The new scalar layer separates a recorded estimator from its expectation and
from a supplied ideal quantity. It does not estimate any of them from the paper:

```text
ehat = existing exact mean_cycle_epsilon_volt, ALL recorded cycles
mu   = expectation of the identical acquisition/reduction estimator
       under a supplied ensemble (not an observed mean or a fitted null)
q    = corresponding ideal fixed-path epsilon
s    = ehat - mu       supplied sampling/measurement error [sL, sU]
b    = mu - q          supplied apparatus/context-switch bias [bL, bU]
q in [ehat - sU - bU, ehat - sL - bL]
```

Both signed bounds must hold **simultaneously**. No independence, Gaussian
distribution or covariance assumption is needed for this algebraic implication.
The ensemble/expectation definition, complete decomposition, validity of both
bounds, and physical bridge remain supplied external assumptions. Software
checks declared provenance and eligibility, not their truth or independence.

`theory_experiments/nuisance_bounds.py` provides a small typed Python interface:
exact `Fraction` intervals, provenance-bearing `SuppliedBound` records,
`NuisanceBounds`, and `assess_epsilon`. `replay(raw_directory)` still works;
an explicit operator may supply `bounds_by_run` as a keyword argument. There is
no candidate input, command-line bound parser, automatic bound selection, fitted
shutter simulator, SEM/variance implementation, threshold or kappa propagation.
Each bound must match the observable, error quantity, sign convention, volts,
run ID, raw SHA256 and recipe SHA256, with nonempty source and assumptions.
Invalid bindings/shapes are input/contract errors, not primitive counterexamples.

The statuses have deliberately narrow meanings:

| Input/result | Status | Meaning |
| --- | --- | --- |
| Either bound missing, without ineligible supplied evidence | `inconclusive_missing_bounds` | Never substitute zero. |
| SD, SEM, confidence interval or other unsupported kind | `unsupported_evidence_kind` | Not interpreted as a deterministic signed bound. |
| Explicit dependence on tested null | `unsupported_circular_null_calibration` | Cannot independently test that null. Same-data provenance alone is not disqualifying. |
| Enclosure contains zero, including endpoints | `zero_not_excluded_by_supplied_bounds` | Not empirical acceptance or model feasibility. |
| Enclosure strictly excludes zero | `conditional_joint_null_bridge_bounds_inconsistent` | The joint null/bridge/bounds assumptions are inconsistent; not primitive rejection. |

Input/contract errors raise before eligibility assessment. Ineligible supplied
evidence takes status precedence over a simultaneously missing slot, while
`missing_bounds` still lists every absent slot. Neither case yields an enclosure.
Circularity is determined only by the explicit null-dependence declaration, not
by an evidence-kind label or a shared dataset/hash.

`candidate_verdict` remains `not_assessed` in every assessment. For **both actual
runs**, both supported bounds are missing, despite nonzero recorded epsilon.
Consequently both are `inconclusive_missing_bounds`, not an accepted null,
rejected primitive, Born violation, or successful physical comparison.

### Why published corrections do not fill the missing bounds

The fixed registry now carries a source-linked evidence audit, with actual
sampling and bias bounds explicitly null:

| Source | Evidence and boundary |
| --- | --- |
| [§5.1, Eq. 9](https://arxiv.org/html/2104.11577v2#S5.SS1) | Independent detector measurements yield ΔF correction estimates (-4.7e-5, -9.4e-5), but no epsilon-voltage bound, transfer curve or uncertainty artifact. |
| [§5.4, Eqs. 14–16, Table 3; App. B, Eqs. 31/36](https://arxiv.org/html/2104.11577v2#S5.SS4) | Crosstalk phases -0.017/-0.014 rad are inferred from the same epsilon under the Born/null assumption, selecting the smaller root. They are not independent calibration. |
| [§5.2 and App. A.2](https://arxiv.org/html/2104.11577v2#S5.SS2) | Independent Gaussian power/phase fluctuation assumptions and moments from tested data do not make SD/SEM deterministic bounds. |
| [§4 and App. B](https://arxiv.org/html/2104.11577v2#S4) | Autocorrelation-corrected SEM is reported, but the implemented lag/window algorithm is unavailable. None is invented here. |
| [§5.5](https://arxiv.org/html/2104.11577v2#S5.SS5) | Leakage estimates 2.20(2)e-4 / 2.707(4)e-4 use main data and assumptions, with unknown shutter phase; not independent bias intervals. |
| [§5.6 Table 4 versus Table 3](https://arxiv.org/html/2104.11577v2#S5.SS6) | The 23°C ΔF_CT entries disagree (-6.4e-3 versus -9.0e-3). No consolidated correction budget is manufactured. |
| [Zenodo v1.0.0 inventory](https://zenodo.org/records/5497283) | Two main runs and a contrast HDF5 file; no detector-calibration artifact or author analysis code. |

ΔF is a different observable from epsilon in volts; a numerical correction
cannot be transferred without a justified bridge. No numbers above are used as
deterministic bounds or fitted to the replay result.

### Universal algebra and countercontrols

`Proofs/QMClosure/SorkinErrorBudget.lean` proves scalar-transfer soundness,
null-containment and strict-exclusion consequences, zero-retention under interval
widening, and endpoint sharpness in the **unconstrained scalar error abstraction**.
Endpoint witnesses are not physical preparations or proof of model feasibility.
The file is an explicit Lake root and imported by the typed research ledger.

It also proves epsilon zero for an affine cube of fixed amplitudes: each path
has an independent fixed closed/open amplitude; the coherent baseline is the
sum of closed amplitudes, increments are open-minus-closed, and the empty context
includes that baseline. The quadratic-weight/common-affine-rate identity holds
for all real eta, gain and background without positivity assumptions. It does
not cover cross-influence, drift, nonlinear detection, arbitrary imperfect
shutters, Peres F, or the actual apparatus. A conditional corollary composes this
identity with the supplied signed bounds; it does not establish their validity.
These are mathematical Lean proofs, not formal verification of Python or
physical-coverage proofs. No theorem card, manifest or theory version is upgraded.

Controls include bias explaining or hiding a nonzero signal, inclusive endpoints,
missing/unsupported bounds, exact signed fractions, wrong bindings, same-data
non-null-derived assertions, and independent fixed open/closed leakage cancellation.
Changing only ABC (cross-influence) or applying nonlinear response can break that
cancellation without rejecting a primitive. A separate vector in mask order 0–7,
`[0,1,1,9,1,1,1,8]`, has epsilon zero but cannot meet the supplied nonnegative
quadratic/common-zero-background pair bound: pAB=9 exceeds
`(sqrt(pA)+sqrt(pB))^2=4`. Zero epsilon alone is not model feasibility.

```sh
python3 -m unittest tests.test_nuisance_bounds tests.test_raw_signal_replay
IDT_GSTIR2021_RAW_DIRECTORY="$raw_dir" uv run --with h5py --no-project python -m unittest tests.test_nuisance_bounds tests.test_raw_signal_replay
lake build Proofs.QMClosure.SorkinErrorBudget
lake build Proofs.MetaLang.V8CheckerResearchProgram
```

Run Lake commands sequentially. All 314,400 samples, 870 cycles and ancillary
NaN metadata remain retained; the scalar assessment changes none of the raw
arithmetic, candidate pipeline, published-summary adapter or history baselines.
