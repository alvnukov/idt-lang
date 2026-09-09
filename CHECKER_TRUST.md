# Checker trust and development priority

The current priority is to improve checker coverage, automate its quality checks,
and use research failures as new regression cases. A large number of passing
tests is not a probability that the primitives are true. Trust is specific to a
stated property, input domain, implementation and evidence path.

The authoritative work ledger is
`Proofs/MetaLang/V8PrimitiveScreenBoundary.lean`, especially
`currentDevelopmentPriority` and `checkerQualityOpenObligations`.

## Current guarantees and limits

| Area | Mechanism | Remaining limit |
| --- | --- | --- |
| Rational kernel positivity, dimensions 1–3 | Exact weighted-square identity or negative reference direction, checked separately from generation | Python/Fraction execution and verifier soundness are not formally certified |
| Other primitive probes | Exact finite enumeration, explicit budgets and witnesses | Unchecked directions/domains remain unchecked |
| QM readout | Fixed analytic preparations/settings and negative controls | QM carrier, maps and composition are imports; not an empirical suite |
| SM chiral spectrum | Exact anomaly sums, representations and charge readouts | No masses, interactions, process predictions or neutrino-mass mechanism |
| Cached results | Input/code/runtime keys, integrity digest and no-overwrite publication | Digests are not authentication; the cache directory is trusted |
| Cached positivity evidence | Recheck the certificate and its associated check/status on every disk hit | Other cached scientific checks retain the trusted-cache contract |

The positivity certificate is stored in `scope.positivity_certificate` of the
full report. Its generator uses rational Schur complements. Its verifier does
not call the generator: it checks either `K_ij = sum_t w_t v_ti v_tj` with
positive weights, or directly checks `v^T K v < 0`, `sum(v) != 0`, and the
normalized-reference event weight. It rejects missing, malformed or inconsistent
evidence. Invalid evidence is an operational error, not a scientific rejection.

This closes the previous radius-2 blind spot for supported pair kernels. The
admitted-reference/tensor semantics remain explicit assumptions. The old finite
checks still run, and their counts, failures and incompleteness are retained.
The exact algebraic check is not a derivation of the representation from lower
primitives and does not raise the theory's proof status.

## Automated quality controls

The dedicated `Hypothesis checker quality` CI step runs the primitive, QM/SM,
pipeline and certificate test modules, with lint and strict typing for the
screen implementation. The existing broader Python gates remain in place.
Local execution is tested; configuring CI is not evidence of a remote CI pass
before the commit has been published and run there.

The suite includes:

- comparison with the independent all-principal-minors criterion on all 729
  symmetric 3x3 matrices with entries in {-1,0,1};
- the 169-kernel research grid, independently classified as 130 PSD and 39
  non-PSD matrices, including all 12 formerly missed cases;
- 64 cases with large rational coefficients and near-singular examples;
- permutation, positive scaling and invertible-congruence consistency;
- singular kernels, zero pivots and non-leading-minor traps;
- mutated certificate fields, omitted terms, wrong signs/dimensions, forged
  cache digests and generator-error injection;
- direct replay of negative certificates through the existing tensor/event
  calculation, and cache reuse without regenerating the certificate.

These tests detect different failure modes but still share Python rational
arithmetic. They do not eliminate all common-mode errors. Certificate mutation
tests are not the same as a source-code mutation-testing campaign; the latter
remains open.

## Improvement loop

For every new check, specify the scientific statement, imported assumptions,
supported input domain, reference target and failure meaning before upgrading
coverage. Require a failing control, an independent calculation where feasible,
machine-readable evidence and automatic regression coverage. Preserve unknown,
unsupported and exhausted-budget outcomes. Every discovered checker limitation
should become an executable regression or an explicit scoped exclusion.

Next trust improvements recorded in Lean are formal verifier soundness with a
runtime evidence bridge, source-code mutation testing, independent QM numerical
comparisons, SM interaction/process benchmarks and versioned experimental data
with uncertainty and held-out comparisons. None is recorded as completed here.

## Acceleration proposals, not weaker criteria

1. **Certificate-first triage.** Reject a candidate after a verified exact
   counterexample, then run expensive probes only for survivors. Preserve a
   separate triage report that explicitly marks unrun checks; retain the full
   diagnostic mode. This optimization is not enabled by this milestone.
2. **Counterexample regression bank.** Try previously found witness inputs
   before search on a new candidate, recomputing every value. A failed old
   witness cannot establish that the new candidate passes the full domain.
3. **Dependency-scoped scheduling.** Recompute only checks whose inputs or
   verified dependencies changed. First prove equivalence with a complete run;
   the current conservative source-hash cache remains the default.

Each optimization should report measured runtime/output savings together with
unchanged evidence and coverage contracts. Never translate smaller output into
stronger scientific confidence.
