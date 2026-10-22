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
to ignored `dist/gstir2021-raw-replay.json`; select `--output` for another path.
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
The paper attributes its nonzero results to shutter crosstalk and independently
bounds detector nonlinearity; this replay makes no correction or contrary claim.

Native primitives still lack a derived physical preparation/path/detector bridge.
No confidence/acceptance rule, inference engine, universal apparatus prediction,
physical-temperature calibration or proof-status upgrade is introduced. The
typed task/boundary record is in
`Proofs/MetaLang/V8CheckerResearchProgram.lean`.
