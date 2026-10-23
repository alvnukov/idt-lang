# Hensen2015: one conditional local-response test

The pinned released event-candidate replay yields **245 trials, 196 CHSH-game
wins**. At the fixed analysis policy `alpha = 1/20`, its exact rational tail is
approximately **0.0391746435587900276**, conditional on the stated local-null,
settings, herald/readout, predictability and fixed-N contracts. The independent
critical threshold is 196 wins. This is a conditional statistical exclusion of
that joint null, not an exact counterexample or an unconditional primitive verdict.

## What is tested

Each `bell_local_response` candidate supplies its actual four integer signs
`A0,A1,B0,B1`. All sixteen tables are retained in
`data/bell_local_response_controls.json`. Their four setting-cell truth tables
are computed before observation access; each wins at most three cells. There is
no trusted `is_local` label, source-theory-to-locality binding, or hidden fit.
Unknown source/nonlocal models need a separate prediction adapter and are not
rejected by this family.

All sixteen candidate reports use **one common local-class test**, identified by
`hensen2015_N245_K196_local_class_q_v1`. They are not sixteen independent
discoveries; the repeated records neither multiply the evidence nor automatically
require a sixteen-test correction. The conservative class bound is used for every
table instead of fitted table-specific parameters.

The null permits local stochastic mixtures and dependence on earlier trial
history. It requires a per-history conditional win cap. Joint setting control is
essential: fair marginals alone are insufficient. Perfectly correlated fair bits
can make a suitable local table win every trial. A context-first base that admits
a local realization does not thereby entail locality; this test does not reject
`context_first_b0_five` or IDT's base.

## Exact reduction and conditional risk

The released records already contain broad two-photon preselected candidates,
not the full acquisition timetag stream. Replay retains every released row,
its original fields/order, filter reasons, and accepted row IDs in the external
full report. It does not reconstruct first-photon or excluded-attempt acquisition.
Timestamps remain naive calendar timestamps, not certified UTC.

The fixed source recipe selects different herald detectors with channel starts
`[5426350,5425700] ps`, length `52450 ps`, second-window shift `250000 ps`,
left-closed/right-open endpoints; each invalid-marker age is zero or `>250`,
and both post-excitation fields are zero. A readout is `+1` iff
`10620 < t <= 14320 ns`, otherwise `-1`. Zero/no-click is valid and retained.
A win is `(-1)^(a*b)*x*y = 1`, counted directly, never recovered from CHSH S.

Counts progress `4746 -> 361 herald -> 248 also markers -> 245 all filters`.
The outcome matrix (rows `ab=00,01,10,11`; columns `++,+-,-+,--`) is:

| ab | ++ | +- | -+ | -- |
|---|---:|---:|---:|---:|
| 00 | 23 | 3 | 4 | 23 |
| 01 | 33 | 11 | 5 | 30 |
| 10 | 22 | 10 | 6 | 24 |
| 11 | 4 | 20 | 21 | 6 |

The paper's model gives `tau=27/2500000` and
`q=3/4+3*(tau+tau^2)=4687702502187/6250000000000`.
The recurrence is `B(0,0)=1`, `B(0,k+1)=0`, `B(n+1,0)=1`,
`B(n+1,k+1)=q*B(n,k)+(1-q)*B(n,k+1)`.
The implementation uses common-denominator integer arithmetic, with exact
fractions in reports and separately labeled decimal displays. A closed-form
integer-combination sum is an independent test oracle. `N,q,alpha` alone determine
the rejection threshold, not observed K. The paper's `0.039` is rounded; the
computed value is not literally `<=0.039`.

`Proofs/QMClosure/BellLocalTrialNull.lean` proves the local table cap, finite
mixture and explicit product-setting bound, and a fixed-N tail domination/risk
bound for arbitrary real-probability finite history trees satisfying node win
probabilities in `[0,q]`. It does not assume IID trials. The theorem does not
formally verify Python, infer physical assumptions, or permit optional stopping.

Important unresolved applicability conditions remain explicit:

- The QRNG tau is a paper two-sigma estimate plus a model, not a certified
  deterministic conditional cap. Its uncertainty is not silently zero.
- The paper requires data-independent N; no independently timestamped N=245
  commitment has been verified here. Repeated fixed-N boundary crossing does not
  inherit this risk bound.
- Dataset and analysis-policy selection here are retrospective, not a new
  preregistration. The per-run conditional risk guarantee does not cover that
  selection process. Physical setting independence and herald/readout validity
  remain assumptions, not facts certified by these counts.

The typed task/result/blockers are recorded in
`Proofs/MetaLang/V8CheckerResearchProgram.lean`. No manifest status, proof card,
theory version, or old candidate/history semantics are upgraded. Ordinary pipeline
completion remains a four-cell structural check, with statistical status in a
separate empirical assessment. `not_excluded` would not mean acceptance.

## Reproduce

From the repository root, the following opt-in command downloads the fixed public
mirror, checks archive SHA256 and byte size, reads only the named CSV member,
checks its SHA256/size, and runs the reduction. It never executes downloaded code
or extracts arbitrary archive paths. Default replay does not use the network.

```sh
python3 scripts/replay_hensen2015.py --fetch \
  --raw-file dist/hensen2015-source/bell_open_data.txt \
  --output dist/hensen2015-trial-replay-v1.json
```

Existing identical raw/output files are reusable; different contents are never
overwritten. The report includes exact tail fractions, provenance, and all 4746
released rows. Keep this full report and raw data outside version control.
To replay an already obtained CSV, omit `--fetch`.
For the optional real-source test:

```sh
IDT_HENSEN2015_RAW=dist/hensen2015-source/bell_open_data.txt \
  python3 -m unittest tests.test_bell_trial_test
```

Ordinary candidate/history replay instead uses the reviewed count record in
`data/raw_observations/hensen2015.json`, explicitly labeled
`reviewed_count_replay_not_raw_reexecution`; it does not require a download or
synthesize fake trial records from aggregate counts.

## Provenance and scope

Primary sources: [Hensen et al. paper](https://arxiv.org/abs/1508.05949),
[supplement](https://static-content.springer.com/esm/art%3A10.1038%2Fnature15759/MediaObjects/41586_2015_BFnature15759_MOESM113_ESM.pdf)
(I: QRNG; K: selection; N: tail; O: conditional settings/locality; P: stopping),
and [official dataset metadata](https://api.figshare.com/v2/articles/12703235),
DOI `10.4121/uuid:6e19e9b2-4a2d-40b5-8dd3-a660bf3c0a31`.

The official download timed out during source review. The pinned mirror archive
matches the official published byte size `152913` and MD5
`342f29f8288c46575818acd2acebd535`; this is not an independent retrieval of
original archive bytes. Mirror SHA256 is
`c28eb0f075759aef620a0b2e00a70fd675ce712bc8214d11c103f5a3d29492c0`.
CSV SHA256 is
`5a6b1853554ad508d35c795415d64922ed9e5bc0469f6052ad222486ad3566ff`,
size `431094` bytes. No verified permission for redistributing the raw records
was established under the 4TU General Terms of Use, so only metadata, the fixed
recipe, and reviewed derived counts are committed. The released author example
was inspected as source but never executed.

This result does not establish QM, GR, physical constants, experimental
confirmation of IDT, or empirical acceptance of any primitive base.
