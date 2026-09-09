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

## QM: a conditional readout benchmark

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
