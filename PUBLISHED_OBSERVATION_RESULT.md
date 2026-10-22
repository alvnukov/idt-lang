# Conditional published-summary comparison

This milestone separates a supplied algebraic prediction, an explicit physical
observation bridge, and an independent descriptive comparison with one published
experimental summary. It does **not** establish empirical acceptance, reject a
primitive, select complex amplitudes, or derive QM.

## What is computed

The new `published_observation` candidate has exactly five fields: `id`, `family`,
`experiment`, `bridge`, and `model`. Its nested model is an explicit
`amplitude_algebra` or an exactly reviewed immutable `source_theory` snapshot.
No candidate-supplied observation, answer, tolerance, fitted preparation, or
arbitrary data-file path is accepted.

For the supplied weight `W(a,b)=a²+eta*b²`, the predictor computes the
parameter-independent ideal fixed-path null `epsilon=0`, hence `kappa=0`
**conditionally on a nonzero denominator**. This predictor does not read the
measurement registry. Only afterward does a separate function subtract the ideal
value from the selected published summary and divide by its quoted uncertainty.
There is no normalization by a sum of weights, clipping, stochastic sampling,
fit, ranking, threshold, p-value, z-score, or acceptance decision.

The Python adapter supports nonnegative quadratic weights (`eta >= 0`, including
the scalar `eta=0` case). Multiplication's `product_square` parameter is unused:
no path propagation or experimental preparation is inferred. Quadratic scalar,
Gaussian and degenerate-dual controls all return the same ideal zero. This test
does not distinguish those candidates. Negative `eta`, zero-weight, quartic and
absolute-weight controls remain unsupported for this physical comparison; their
literal weights are not repaired and their primitive status is not changed.

## Explicit bridge and its walls

`fixed_path_quadratic_rate_v1` supplies, rather than derives:

- the same path contributions in all eight contexts, including the empty context;
- additive recombination and a real-coordinate extension of the supplied integer
  quadratic weight (not a derived physical continuum);
- response `rate = g*W + background`, with one positive gain, one shared
  nonnegative background, and a common exposure/rate convention;
- a nonzero pair-interference denominator.

Physical path assignment, preparability, the apparatus response and nuisance
bias are not established. Nuisance bias is **unmodeled**, not set to zero.
There is no apparatus-level measured-kappa prediction. No arbitrary three-arm
preparation is fitted: the new predictor uses an algebraic ideal null, not a
new numerical triple-path bench.

The fixed-path assumption is significant. Switching slits changes boundary
conditions, and nonclassical interslit paths can produce nonzero kappa within
ordinary QM. Thus a measured nonzero kappa alone is not a Born-rule violation.
See Sawant et al., [Non-classical paths in interference experiments,
arXiv:1308.2022v2](https://arxiv.org/html/1308.2022v2). That paper's `Imax`
normalization is **not** imported into the Sinha comparison and no numerical
correction is applied here.

An independent toy test makes the bridge wall executable: with scalar arms all
equal to 1, adding 1 only to the ABC detector rate gives `epsilon=1`, `delta=6`,
and `kappa=1/6`, despite the unchanged quadratic weight. This is a bridge-failure
control, not experimental evidence or primitive rejection.

## Frozen published extraction

Source: Sinha et al. (2010), [Ruling Out Multi-Order Interference in Quantum
Mechanics](https://arxiv.org/abs/1007.4193),
[versioned PDF](https://arxiv.org/pdf/1007.4193v1),
[DOI 10.1126/science.1190545](https://doi.org/10.1126/science.1190545).
The frozen extraction is
`data/published_observations/sinha2010_hsps_kappa.json`; the full PDF is not
committed. Its checked PDF SHA-256 is
`58f815646f439747e81506ce732aa88923451641ea61ed466b3fa885112aa448`.

Page 5 equations (4)–(6) define
`epsilon=pABC-pAB-pAC-pBC+pA+pB+pC-p0`, `kappa=epsilon/delta`, and
`delta=|pAB-pA-pB+p0|+|pAC-pA-pC+p0|+|pBC-pB-pC+p0|`.
The observable is dimensionless. The selected regime is heralded single
photons (HSPS), central interference maximum.

The primary page-8 body summary is `0.0064 ± 0.0120`. Figure 3 on page 6 reports
`0.0064 ± 0.0119`. Both were checked against the PDF text and visually checked
page images. The discrepancy is retained: these are the **same data summary**,
not independent observations to average. The body value is the fixed primary
comparison; no result-dependent selection occurs at runtime.

With ideal zero, exact primary residual arithmetic gives `4/625`, and
`residual / quoted_uncertainty = 8/15`. The caption's alternative uncertainty
would give `64/119`; it is retained as source metadata, not a second comparison
outcome. These fractions are descriptive arithmetic only. No iid-Gaussian SEM,
total likelihood, significance or confidence interpretation is assigned.

The publication discusses mask shifts giving illustrative `|kappa|` of order
`0.01`, not a rigorous apparatus bound. APD counts were kept below `100000/s`
to limit dead-time effects. The meter-only `0.003` systematic estimate is not
assigned to HSPS. Raw context counts, covariance and an apparatus nuisance
model are unavailable to this adapter. Freezing a runtime policy for historical
data is **not prospective preregistration**.

## Evidence and reproducibility

`Proofs/QMClosure/PublishedSorkinNull.lean` proves the literal quadratic
eight-context affine-response identity over the assumed real extension by
`ring`. The algebraic identity holds even for arbitrary real gain/background;
physical positive-gain/nonnegative-background interpretation is an additional
supplied bridge restriction. Kappa uses `Option`: zero denominator returns
`none`, not a valid zero readout. A bridge-equality hypothesis plus nonzero
denominator gives `some 0`. This is neither a formal verification of the Python
implementation nor a physical/QM closure artifact. No manifest status changes.

The active item `published_summary_fixed_path_null_comparison` in
`Proofs/MetaLang/V8CheckerResearchProgram.lean` records the artifact and the
physical-bridge/raw-data/nuisance walls. Python execution retains
`proof_status=not_attempted` because it does not invoke Lean.

Run the ten controls through the existing history/cache/CLI:

```sh
python3 scripts/screen_hypotheses.py --batch-file data/published_observation_controls.json --json
python3 -m unittest tests.test_published_observation
```

The demo's expected exit code is `3` because seven controls are unsupported,
not because a completed computation failed. The default CLI durably archives
runs; use `--history-dir /path/to/temporary-history` for a smoke run that must
not append to the repository archive.

Three literal quadratic controls complete the descriptive comparison; seven
controls remain unsupported. `no_counterexample_within_bounds` denotes only
completion of one closed-form comparison (`planned=checked=1`), not empirical
success. Unsupported cases have `checked=0`. `empirical_status` changes to
`published_summary_compared_conditionally` only after comparison completes;
`candidate_verdict=not_assessed` throughout. Old families retain their exact
report semantics, including `empirical_status=not_tested`.

Source hashes bind code, frozen data and the Lean artifact. Stale loaded sources
fail closed; data or label changes change cache keys. The existing durable
history retains unsupported candidates and old observations without replacing
old pins. This result document is not a hash input, avoiding a history-ID cycle.

The independent finite arithmetic cross-check enumerated 93750 eight-context
rate cases: six integer coordinates in `[-2,2]`, `eta` in `{0,1,2}`, and
`(gain,background)` in `{(1,0),(3/2,7/3)}`. Literal `model.weight` and independent
inclusion/exclusion gave zero mismatches. This is a finite software cross-check,
not a proof or physical validation; the universal artifact has the narrower
supplied-algebra scope stated above.

## Verification record

The frozen implementation passed 185 tests across the published-observation,
primitive/physics, pipeline/cache, source-candidate, amplitude, native-operation,
identical-particle, universe-bench and history modules. Ruff and strict mypy
passed for both touched Python modules and the new test module. Sequential MCP
builds passed for `Proofs.QMClosure.PublishedSorkinNull` and
`Proofs.MetaLang.V8CheckerResearchProgram`. The new artifact is registered as an
explicit Lake root and imported by the checker ledger. Provenance also binds
`lakefile.lean` and `lean-toolchain`; execution still does not claim to check Lean.
IDT graph validation passed and the claim audit reported zero issues.

Before the append, all 330 old candidates across 34 submissions and 41 retained
observations rechecked unchanged, with no errors or semantic differences. All
110 existing tracked history files remained byte-identical.

Only the ten-control batch was appended, with no old baseline replacement:

- submission/baseline key:
  `2b8647af81f28e4d1da7c8f7d2267fde6df697fe4c45479886aa0ff1d375726e`;
- observation key:
  `c0494b52addafdae257e761c7576916ccc318ec677adb7796abe074a1b1eaaf1`.

After the append, all 340 candidates across 35 submissions and 42 retained
observations rechecked unchanged, with no errors or semantic differences.

No manifest, theory version, primitive status or physical proof status was
upgraded. The existing user-owned QM research task ledger was not edited.
