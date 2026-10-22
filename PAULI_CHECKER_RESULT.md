# Supplied two-particle Pauli benchmark

This adds an exact finite-state checker, not a derivation of identical-particle
statistics from IDT primitives. The raw input is a supplied two-particle tensor;
the checker does not construct a tensor that already satisfies the target law.
Canonical `spinStatistics`, the manifest, and QM-closure statuses are unchanged.

## Contract

`identical_pair_amplitudes` takes an `id`, `statistics` (`fermion` or `boson`),
`origin: "supplied_fixture"`, 1–4 distinct `modes`, and an N×N `amplitudes` matrix.
Each mode has `orbital` and `internal` labels, using the existing short lowercase
identifier grammar. Each coefficient is `[real, imaginary]`, with both components
bounded rational strings accepted by the existing exact parser (up to 12 decimal
digits per numerator/denominator). Floats, booleans, duplicate complete modes,
malformed dimensions, unknown fields and unsupported origins are invalid input,
not physical counterexamples.

The orthonormal complete-mode basis, complex amplitudes and statistics are
explicit assumptions. Labels alone certify neither completeness of physical
degrees of freedom nor orthogonality. Equal orbital labels with different
internal/spin labels denote different supplied complete modes.

The checks are independent:

- `nonzero_prepared_two_particle_state`: a zero tensor is `inconclusive` for this
  prepared two-particle benchmark, not a successful verification or a global
  rejection of vacuum states.
- `pauli_same_complete_mode`: for a declared fermion, every `A[i,i] = 0`.
- `exchange_symmetry`: `A[i,j] + A[j,i] = 0` for fermions, and
  `A[i,j] - A[j,i] = 0` for bosons. This is transpose, not conjugate transpose.

Every real and imaginary residual is checked separately, with an exact witness
on failure; residuals cannot cancel between components or entries. Upper-triangle
exchange checks suffice for these identities and include the diagonal. The
`max_cases` budget counts scalar component checks; an incomplete traversal is
`inconclusive` unless an actual counterexample was found.

For bosons, `scope.requirement_applicability.pauli_same_complete_mode` is
`not_applicable`, and no Pauli success check is emitted. A successful boson report
therefore does not mean that Pauli exclusion was established. Double occupancy
is allowed, not required in every boson state. Sparse, unnormalized nonzero
tensors are allowed because the tested identities are homogeneous. No
probabilities, occupation predictions or detector outcomes are inferred.

The external physics requirement is the distinction between full states and
orbital labels, and symmetric/antisymmetric exchange amplitudes, described in
[Feynman Lectures III, Chapter 4](https://www.feynmanlectures.caltech.edu/III_04.html),
§§4–1, 4–2 and 4–7, including Eq. 4.44. This is an imported benchmark requirement,
not proof from IDT primitives.

## Run

```bash
python3 scripts/screen_hypotheses.py \
  --batch-file data/identical_particle_controls.json --no-cache --json
python3 scripts/check_identical_particles.py \
  --batch-file data/identical_particle_controls.json
python3 scripts/check_candidate_history.py
python3 -m unittest tests.test_identical_particles
```

The screen uses the existing durable history APIs even with `--no-cache`; that
flag disables the disposable cache, not history publication. The separate
coverage audit is read-only and uses no disk cache. Both commands return 1 for
the supplied mixed controls because intentional violations are present, 0 for
completed nonzero identity-compatible fixtures, 3 for unsupported/inconclusive
coverage without a violation, and 2 for invalid input/execution errors. The
existing screen additionally retains its review-required exit code 4.

## Evidence

The 12 saved controls give five identity-compatible reports, five scoped
counterexamples and two inconclusive zero tensors:

| Supplied control | Outcome |
| --- | --- |
| Same orbital, different spin; complex antisymmetric amplitudes | Compatible |
| Nonzero fermion diagonal | Pauli and exchange violation |
| Symmetric real off-diagonal, zero diagonal | Pauli compatible, exchange violation |
| Symmetric imaginary off-diagonal, zero diagonal | Pauli compatible, exchange violation |
| Sparse complex fermion tensor, four modes | Compatible |
| Single-mode boson with nonzero diagonal | Compatible; Pauli not applicable |
| Boson with zero diagonal | Compatible; Pauli not applicable |
| Symmetric imaginary boson tensor | Compatible; Pauli not applicable |
| Antisymmetric boson tensor | Exchange violation; Pauli not applicable |
| Single-mode zero fermion tensor | Inconclusive |
| Single-mode imaginary fermion diagonal | Pauli and exchange violation |
| Single-mode zero boson tensor | Inconclusive; Pauli not applicable |

New append-only history records:

- Submission and initial pin: `3168366a2033adfd65c752528755155acfb69c9307ab2e5dcb8e8c22fab0620e`.
- Observation: `6bd77434e35ac95a19ad415feeb69d245bce7a7d1eb180402ad1d65efc9aba1a`.

Fresh all-family history replay covers 320 candidate occurrences (308 existing
plus 12 new), 33 submissions and 40 retained observations: `unchanged`, no
changes and no errors. Aggregate statuses are 154 counterexamples, 141
`no_counterexample_within_bounds`, 23 unsupported and 2 inconclusive. These are
scoped computational outcomes, not physical truth labels.

The dedicated pair-coverage audit was also run on all 320 retained candidate
occurrences through the existing history loader. It reports all 308 old
occurrences as `unsupported` for this new requirement, because they have no
reviewed identical-pair prediction adapter. Their original family-specific
verdicts remain unchanged. The 12 fixtures retain the outcomes above; Pauli
applicability is 7 applicable and 5 not applicable. Checksums of all 106 real
history files, including `.json.gz` observations, are identical before and after
the read-only audit/replay. All 103 preexisting history files remain unchanged.

Verification used Python 3.14: 22 new tests and 90 neighboring pipeline, history,
source, amplitude, physics and primitive tests; strict mypy and Ruff on the four
touched Python files; the single touched Lean ledger target; graph source-hash
validation and claim audit. Python HAPP diagnostics were unavailable because
`pyright-langserver` is not installed; mypy is the type-checking evidence.

## Remaining boundary

The active work item in `Proofs/MetaLang/V8CheckerResearchProgram.lean` records
the missing native primitive-to-amplitude bridge, statistics selection, physical
mode completeness, and empirical preparation/readout bridge. This checker does
not establish an N-body theorem, CAR, spin–statistics, uniqueness of QM, or
empirical confirmation. No canonical physical claim is upgraded.
