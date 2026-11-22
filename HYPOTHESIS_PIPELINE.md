# Cheap hypothesis screening without weaker evidence

This is a batch **algebraic and finite compatibility screen**, not a universal
physics simulator. It uses exact rational arithmetic, no model/API calls, no
fitting and no external solver dependencies (Python 3.10+, macOS/Linux). The
original [primitive screen](PRIMITIVE_SCREEN.md) remains available unchanged.
See [checker trust and development priority](CHECKER_TRUST.md) for guarantees,
automated quality controls, limitations and proposed safe accelerations.

## Run

```sh
python3 scripts/screen_hypotheses.py --builtin square fourth non_psd qm_born qm_fourth sm_reference sm_bad_charge sm_one_generation
python3 scripts/screen_hypotheses.py --builtin qm_born sm_reference --show-candidates
python3 scripts/screen_hypotheses.py --batch-file candidates.json
python3 scripts/screen_hypotheses.py --builtin qm_born --fresh
python3 scripts/screen_hypotheses.py --replay /absolute/path/from/card.json
```

Batch input is an array of 1–64 candidate specifications, at most 128 KiB.
Duplicate JSON keys, unknown fields, floats and executable inputs are rejected.
`--show-candidates` provides editable specifications, not precomputed outcomes.
The QM family selects `norm_power` (1–4). The SM family specifies 1–16
left-handed Weyl multiplets: `label`, `color` (1, 3, -3 for antifundamental),
`weak` (1 or 2), exact-string `hypercharge`, and `copies` (1–8), plus the
hypercharge of one supplied scalar doublet. New primitive semantics require a
reviewed adapter; this is not an exhaustive hypothesis language.

Default output is one JSON card per candidate. Every check retains its status,
checked/planned counts and the first violating value. The card links to the
complete local artifact, including exact witness inputs, imports and gaps.
`--json` prints complete reports. Exit codes: 0 = completed finite screen without
a counterexample; 1 = at least one counterexample; 2 = invalid input/operational
error; 3 = incomplete or unsupported. Code 0 never means physical truth.

## Test an explicit triangle stock across an entire lattice

`triangle_stock` describes W(a,b,−a−b) by a sum of at most five squared
affine integer forms. Each residue pair (modulus 1 through 7) can override
the default list. The three instrument gains are independent positive
fraction strings; the machine does not infer them by fitting. Test the
[controlled input batch](data/triangle_stock_controls.json) with
`--max-cases 882`. An actual residual gives the input and the two output
stocks. A complete six-point stencil per residue and setting certifies
the identity for this submitted function, including negative and distant
integer translates. A partial run does not. See the [scientific
scope, dark alternative and bypass readout](scripts/TRANSFER_AND_STOCK.md).

## Compare a supplied light neutral current with invisible Z-width summaries

`neutral_current_width` takes 1–12 labeled species and an exact Hermitian
matrix of [real, imaginary] fraction-string pairs. The mass regime and
current bridge must be explicit. See the [width data, controls and replay](scripts/Z_INVISIBLE_WIDTH.md).
The candidate's matrix, not the historical central value or a family count,
sets the prediction. A completed numerical comparison is **not** empirical
acceptance. Nothing in this family automatically binds a primitive or an
archived sixteen-state carrier to these data.

## Check raw five-slot pencil weights without fitting a reference pattern

`chiral_pencil` accepts 40 real rational weights as exact strings. In
increasing order take the even five-bit masks, then their unordered pairs
in lexicographic order at Hamming distance four. A pair contributes one
symmetric matrix entry (and its transpose); the common slot and its bit
choose one of ten channels. The support and the proposed absence of a
rank-ten channel combination are assumptions, **not** measured inputs.

```sh
python3 scripts/screen_hypotheses.py --batch-file data/chiral_pencil_controls.json --max-cases 20 --no-cache
```

The adapter constructs the 80 three-channel hexagons from the support. An
integer certificate, including the signs, reduces their alternating-product
checks to 20. On a violation it rebuilds the three-channel sum and reports
its exact rational rank with the offending weights. At a budget of 19 one
of the controls remains inconclusive; at 20 it produces a rank-ten witness.
Uniform positive weights fail immediately. Both the signed reference and a
nonuniform rescaling survive, so this is not a mass or coupling estimator.
A zero edge is preserved as unsupported by **this nonzero-domain adapter**.
The [weighted model and restrictions](scripts/CONTACTS_AND_COMPARATORS.md)
are separate from any claim about the Standard Model. The batch deliberately
contains counterexamples; an exit code of 1 is expected.

## Compare a local relay without assuming spatial coordinates

A `marked_relay` input specifies a directed row of four destinations per
state (1–128 states). Each named port must undo itself on a second traversal.
Ports may coincide or fix a state: those are testable behaviors, not parser
errors. The input also specifies the detector's `marker_classes` and whether
a single named origin, *some* origin, or *every* origin must pass. A return
means landing in the starting marker class. It need not mean equality of the
full hidden states. Neither the raw table nor the detector is derived here.

The two programs compare against a **specified model**, not experimental
data. `named_six` tries 36 six-tick words; `through_six` tries all 1,456
nonempty non-retracing words of lengths one through six. The target returns
when the four alternating counts of port traversals vanish. Reciprocal
cancellations do not change this predicate or the supplied dynamics.
One origin must meet all requirements together. A budget exhausted before
the relevant quantifier is decided is inconclusive.

The checker reuses one origin's trials for another only after matching their
reachable graphs, in port order, including the detector predicate relative to
each origin. Identical serialized rows certify the required bijection; equal
shell sizes do not. On the published 64-state relay this reduces the whole
through-six comparison from 93,184 trajectories to 1,456. On a different
105-state relay no roots merge this way: the original mark passes, whereas
moving the same mark one step produces an unexpected five-tick return.
Outputs give the word, raw path, detector classes, and what was expected.

For this family, the adapter and its directly used validation helpers also
capture their source digests on import. If either was loaded before the
pipeline and then edited on disk, a batch, cache read or replay is refused.
That is a request to restart from a stable checkout, not a counterexample
to the candidate. This check is not attestation of a modified interpreter.

To replay nine contrasting inputs **without modifying the historical
archive**, use a fresh directory. Exit 1 is expected for this deliberately
mixed batch:

```sh
relay_trial_dir=$(mktemp -d)
python3 -B -m scripts.marked_relay_controls > "$relay_trial_dir/controls.json"
python3 -B scripts/screen_hypotheses.py --batch-file "$relay_trial_dir/controls.json" \
  --max-cases 5000 --no-cache --history-dir "$relay_trial_dir/history"
```

The [local shuttle probe](scripts/probe_shuttle_local_reunions.py) searches
for such tables from a common bit and identical cells instead of giving the
checker a path identity. These are distinct questions: existence of a gate,
correct response from a privileged preparation, and correct response at
every internally marked origin.

## Candidate history and false-rejection protection

Normal batch runs now save inputs before adapter validation and complete results
in tracked `data/candidate_history/`, independently of the disposable cache.
Rejected, incomplete and unsupported candidates are retained. Use
`--history-dir` to select another archive. For programmatic research use
`theory_experiments.candidate_history.record_batch`; the low-level `run_batch`
remains side-effect-free unless a cache is requested.

`python3 scripts/check_candidate_history.py` freshly recomputes the complete
history at original bounds. Both directions of verdict change, changes to
requirements/imports/coverage and checker failures require review (exit 4).
`--record` appends current evidence but never refreshes a baseline. Screening
also returns exit 4 for drift against an existing baseline. Old observations
are comparison points, not physical truth labels. See the
[archive contract](data/candidate_history/README.md) for review and scope limits.

## Cost reduction and cache contract

- A batch runs in one process. Duplicate identical requests reuse the result.
- Persistent entries default to ignored `dist/primitive-screen-cache/`;
  `--cache-dir` selects a directory and `--no-cache` disables cache persistence
  only; candidate history remains enabled.
- A key includes normalized candidate input (including its id), every bound,
  protocol version, relevant source/ledger/document hashes, Python version,
  implementation and platform. Dependency hashes are a conservative superset;
  unnecessary misses are preferable to stale reuse. No cross-bound or
  cross-candidate scientific inference is cached.
- Full reports are retained; short output never replaces evidence. Integrity
  digests detect accidental corruption, **not malicious forgery**. This is a
  trusted local performance cache, not a proof authority or signed archive.
- Publication uses a same-directory temporary file and an atomic no-overwrite
  hard link. Symlinks, partial entries, oversized entries, non-regular files,
  request mismatches and digest mismatches fail closed. Conflicting results
  are preserved and reported, never overwritten. Use a new cache directory
  after corruption; do not silently repair it.
- `--fresh` bypasses persistent reads and compares any existing entry with a
  recomputed result. Duplicate requests within that fresh batch still reuse
  the newly computed result. `--replay` recomputes an artifact and compares the
  complete report, including provenance; it does not count a cache hit as a
  successful replay. Neither operation is an independent proof checker.
- Source changes during a batch abort its returned result; changes since module
  import require restarting the interpreter, including for cache hits. Run from
  a stable checkout with a normally installed Python standard library. Runtime version
  fingerprinting does not attest arbitrary locally modified interpreter or
  standard-library binaries. There is no subprocess sandbox for custom code,
  because candidate inputs cannot supply code.

The same bounds apply with and without caching. A limited search is
`inconclusive`, never upgraded to a completed search. The first counterexample
terminates that check only; neighboring checks and their gaps remain visible.
No aggressive surrogate rejection, cross-candidate witness transfer, shrinking,
approximate arithmetic or automated promotion to a formal claim is implemented.

## Exact pair-kernel positivity (protocol 2)

Pair kernels now have an additional mandatory `exact_kernel_positivity` check.
For each admitted rational symmetric matrix of dimension 1–3, a Schur-complement
algorithm constructs either a weighted-square decomposition or a negative
coefficient vector with nonzero sum. A separate verifier checks the full matrix
identity or directly recomputes the negative quadratic/reference weight.
The finite grid is not used to decide this algebraic property.

The full certificate and its scope are retained in the report. A negative
certificate rejects the candidate under the explicitly admitted rank-one
reference and tensor-composition assumptions. A positive certificate covers
all rational coefficient vectors for that one supplied matrix; it does not
prove the primitive representation, full QM, or the program itself in Lean.
The reported `checked=planned=1` means one algebraic certificate, not one
sampled direction. The overall status still preserves all other bounded,
incomplete or unsupported checks. Those checks are not skipped.

Disk cache hits reverify the positivity certificate and its associated
check/status without rerunning generation or grid search. An invalid certificate
is an operational error (exit 2), not a counterexample to the candidate.
Other cached results retain the trusted-local-cache contract above.

The report request schema is now `idt-hypothesis-screen/2`. Old artifacts are
not overwritten or silently upgraded; replay them at their matching source
version. The 12 non-PSD kernels missed by the earlier radius-2 grid are explicit
regression cases and are now rejected automatically, even with a small grid
budget. Existing primitive-only CLI behavior remains unchanged.

## Native integer amplitude algebra

The `amplitude_algebra` family preserves supplied addition, multiplication and
weight. Its scalar carrier is Z; its plane carrier is Z[u]/(u^2-k), represented
by integer pairs. Fields are `carrier` (`integer_scalar` or `integer_plane`),
`product_square` (k), `imaginary_weight` (eta), and `weight_rule`
(`quadratic`, `quartic`, scalar-only `absolute`, or `zero`). Both parameters
are integers from -2 to 2; scalar parameters must be zero. Quadratic weight is
`a*a + eta*b*b`; quartic squares that expression. These are supplied laws,
not laws inferred from a source's name or a successful benchmark.

Six checks cover empty weight, unit-amplitude convention, bounded nonnegative
weights, seven-term Sorkin I3, product-weight factorization and an interference
existence witness. Histories stay fixed; no context-dependent normalization is
introduced. The coefficient radius bounds inputs, not their sums/products.
A finite failure to find an existence witness is inconclusive, never a universal
rejection. Unit-phase and zero-weight samples are diagnostics, not selection
gates. `reference_radius` and `max_copies` are explicitly unused here: algebraic
multiplication is not a derivation of physical tensor products.

Two exact archived `source_theory` specifications now bind to this adapter:
the signed-integer and Gaussian-integer pair-history realizations. Binding uses
the full specification hash; changed/unknown sources remain unsupported. The
request keeps the original source and all its open bridges. Both realizations
pass at default bounds; neither is thereby selected as physical. The generic
pair-history lower law still has no executable carrier/readout bridge.

A real Gram projection must not replace the Gaussian operations: it preserves
single-system weights but changes a composite event from 0 to 1/2. The exact
counterexample is checked in `Proofs/QMClosure/PairHistoryAdapterSafety.lean`.
See [the adapter result](PAIR_HISTORY_ADAPTER_RESULT.md) for scope and controls.

```sh
python3 scripts/screen_hypotheses.py --batch-file data/amplitude_algebra_controls.json --no-cache
python3 -m unittest tests.test_amplitude_algebra
```

The control batch intentionally exits 1: five laws have scoped counterexamples;
a degenerate dual carrier survives, exposing an insufficiency of these gates.
No experiment, continuous phase space, full QM, SM or gravity is checked here.

## First deterministic finite universe bench

The `universe_bench` family executes one supplied `two_path_v1` protocol through
existing native integer amplitude operations. Its ordered exact trace records
preparation, path multiplication, recombination, raw and blocked-arm weights,
and their diagnostic residual. All laws and preparations are supplied; computed
weights are not probabilities or derived detector laws. Completion checks only
execution, not physical validity or model selection. Unsupported carrier/scenario
mappings leave the candidate verdict unchanged. See the bounded input contract,
controls and run/replay instructions in [the bench result](UNIVERSE_BENCH_RESULT.md).

## QM: a conditional readout benchmark

A separate [raw detector-voltage replay](RAW_SIGNAL_REPLAY_RESULT.md) processes
both pinned Gstir2021 runs without introducing a candidate family or changing
any candidate/history verdict. It retains all 870 cycles and treats historical
cuts only as a separately labeled unconfirmed-index diagnostic; no uncertainty,
physical calibration or empirical acceptance is inferred.

The supplied carrier is complex amplitudes with rational real/imaginary parts.
Linear context maps, projective measurements, tensor composition and chosen
states are **imports**. The candidate computes
`p_i = (Re(a_i)^2 + Im(a_i)^2)^norm_power / sum_j(...)`.
Born QM is the external target, not a result derived from IDT primitives here.

Six checks cover one unequal-amplitude preparation; five relative phases;
two projective repeatability outcomes; one local-operation/no-signalling
comparison; four rational-setting singlet correlations; and the squared
Tsirelson bound `S^2 <= 8`. Hadamard is represented up to a common nonzero
scalar, canceled by normalization. The singlet is `|01> - |10>`; Alice uses
identity and Hadamard, Bob uses rotations with rows `(4/5, ±3/5)` and
`(∓3/5, 4/5)`. The independent Born targets are
`E00=E01=-7/25`, `E10=-24/25`, `E11=24/25`, hence `|S|=62/25 > 2`.
These are finite analytic benchmarks, **not laboratory Bell evidence**.

`qm_born` is a positive control. `qm_fourth` changes the readout only, not the
states or transformations. Its marginal probabilities change under the supplied
remote rotation; rejection is conditional on that composite/context semantics.
Finite agreement does not establish all states, settings, POVMs, continuum
dynamics, detector actualization, a complex-Hilbert derivation, or the physical
value of hbar. Successful mathematical fixtures do not fill empirical gaps.

## SM: a conditional chiral-spectrum benchmark

The Lie algebra `su(3)+su(2)+u(1)`, spin assignments and representation classes
are supplied. The global gauge-group quotient is not fixed. All fermions are
left-handed; right-handed observed species are entered as charge conjugates.
Electric readouts use the imported convention `Q=T3+Y`.

The engine computes six consistency conditions: SU(3) cubic, SU(3)^2 U(1),
SU(2)^2 U(1), U(1) cubic, mixed gravitational-U(1), and even SU(2) doublet
parity (Witten) within the supported representations. Mixed non-Abelian sums
omit the common Dynkin factor 1/2 (`2T(fundamental)=1`). Scalars do not
contribute to these chiral fermion anomalies. The gravitational anomaly check
does **not** derive gravitation. These are not checks of all possible global
anomalies on arbitrary backgrounds.

A separate target compares the exact multiset of minimal three-generation
fermion representations/hypercharges (ignoring labels), and a Higgs check
requires a neutral lower doublet component for the selected vacuum convention.
Charges of every supplied multiplet are reported. Content mismatch means
failure of this **minimal-content target**, not exclusion of every extension.
Masses, Yukawa matrices, mixing, cross sections, decays, running couplings and
the neutrino-mass mechanism are not calculated. This is not the full physical
particle spectrum and is not an explanation of why these inputs exist.

`sm_reference` is the known positive control, `sm_bad_charge` mutates the
conjugate-electron hypercharge, and `sm_one_generation` illustrates that anomaly
cancellation does not select three generations. The reference itself is not a
complete model of all known observations; the minimal massless-neutrino sector
needs extension to account for neutrino masses/oscillations.

## Source basis and integration boundary

The representation, Higgs and anomaly conventions follow David Tong,
[Standard Model, section 5.1](https://davidtong.org/pdfs/teaching/standard-model/standardmodel5.pdf),
with right-handed fields converted to left-handed conjugates. Section 5.2.3
explains why the global gauge-group quotient is a separate issue. The source
supports the QFT conventions, not a claim that IDT derived them.

The research pass found existing pieces of the intended loop:
[counterexample-guided synthesis](https://people.csail.mit.edu/asolar/SynthesisCourse2023/Lecture10.htm),
[Hypothesis reuse/shrinking](https://hypothesis.readthedocs.io/en/latest/reference/api.html),
[QuTiP dynamics](https://qutip.readthedocs.io/en/latest/guide/dynamics/dynamics-master.html),
[FeynRules model interfaces](https://cp3.irmp.ucl.ac.be/projects/feynrules/wiki/WikiStart),
[MadGraph processes](https://cp3.irmp.ucl.ac.be/projects/madgraph/), and
[ColliderAgent's model-building/validation workflow](https://arxiv.org/html/2603.14553).
They informed separation of candidate, checker, evidence and expensive escalation.
These tools are **not installed or integrated by this milestone**. They do not
derive primitives: numerical dynamics assumes a model, and event generators
require explicit interactions. Expensive adapters must declare approximation,
validity domain, tool version, uncertainty and independent comparison targets.

Before a candidate can explain QM and SM jointly, it needs one shared lower-level
specification and derived bridges to both adapters. Separate positive controls
do not establish such a bridge. That remains an explicit research obligation in
`Proofs/MetaLang/V8PrimitiveScreenBoundary.lean`; no manifest claim is upgraded.

## Conditional published-summary comparison

The distinct `published_observation` family keeps raw algebra, the explicit
`fixed_path_quadratic_rate_v1` bridge, and the frozen Sinha 2010 HSPS summary
separate. It computes a parameter-independent fixed-path ideal null before
reading measured values, then reports exact descriptive residual arithmetic.
It does not assess empirical acceptance, select a primitive, model apparatus
bias, or interpret the quoted uncertainty as a Gaussian confidence measure.
Scalar, Gaussian and degenerate-dual quadratic controls remain indistinguishable.
Unsupported mappings do not refute a model. Existing family reports and history
baselines remain unchanged. See [PUBLISHED_OBSERVATION_RESULT.md](PUBLISHED_OBSERVATION_RESULT.md)
for the source extraction, eight-context assumptions, zero-denominator exclusion,
slit-boundary caveat and reproducible command.

## Verification

```sh
python3 -m unittest tests.test_primitive_screen tests.test_physics_screen tests.test_candidate_pipeline tests.test_quadratic_certificate
ruff check theory_experiments/primitive_screen.py theory_experiments/physics_screen.py theory_experiments/candidate_pipeline.py theory_experiments/quadratic_certificate.py scripts/screen_hypotheses.py tests/test_primitive_screen.py tests/test_physics_screen.py tests/test_candidate_pipeline.py tests/test_quadratic_certificate.py
mypy --strict theory_experiments/primitive_screen.py theory_experiments/physics_screen.py theory_experiments/candidate_pipeline.py theory_experiments/quadratic_certificate.py scripts/screen_hypotheses.py tests/test_primitive_screen.py tests/test_physics_screen.py tests/test_candidate_pipeline.py tests/test_quadratic_certificate.py
```

Tests compare batch/single and cold/hit results, ensure a hit does not execute
the evaluator, exercise provenance/bound invalidation and corrupt/conflicting
entries, and preserve the legacy negative controls. Independent hand-computed
rational targets detect normalization, chirality and degeneracy mistakes.
