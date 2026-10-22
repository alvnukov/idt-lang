# First deterministic finite universe bench

This is one supplied two-path arithmetic protocol, **not a universe simulator**.
It evaluates existing integer-amplitude candidates without fitting, randomness,
numeric target answers, new dependencies, or changes to their retained history.
Execution completion is not physical compatibility, a detector law, or empirical
validation. Neither this bench nor its controls derive QM, SM, or Pauli exclusion.

## Run and inspect

```sh
python3 scripts/screen_hypotheses.py --batch-file data/universe_bench_controls.json --no-cache --json
python3 -m unittest tests.test_universe_bench
python3 scripts/check_candidate_history.py
```

The control batch exits **3**, because its scalar/nonreal mapping is unsupported.
Other controls complete their supplied arithmetic; none is selected as physics.
The ordinary command appends an observation through the existing candidate history
interface. Use `--history-dir /absolute/temporary/archive` for exploratory runs.
Omit `--no-cache` to retain a replayable cache artifact; its card contains the path
for `python3 scripts/screen_hypotheses.py --replay /absolute/artifact.json --json`.
Only `--json` exposes the full trace, supplied origins and missing bridges.
The compact check is named `two_path_execution_completion_only` deliberately.

## Input and deterministic bound

The `universe_bench` family has exactly `id`, `family`, `scenario`, `model`, and
`preparations`. The only implemented scenario is `two_path_v1`. A different valid
scenario identifier is unsupported, not a candidate counterexample. The nested
model is an existing `amplitude_algebra` or `source_theory` specification; other
input grammars, including nested benches, are input errors, not physics verdicts.
Only the two existing reviewed exact source hashes receive source adapters.
Changed or unbound source specifications remain unsupported; retained source text
is never executed and its open bridges remain visible.

There are 1–16 preparations with unique ids. Each has exactly `id`, `left`,
`right`, `left_factor`, and `right_factor`; each amplitude/factor is an integer
pair with coordinates in [-2, 2]. Unknown fields, booleans, floats, fractions,
duplicate JSON keys, and out-of-bound inputs are errors. No expected-answer field
is accepted. Coordinates of computed sums/products are not clipped to input bounds.

The whole request is preflighted before execution. A scalar model cannot represent
any preparation or factor with nonzero second coordinate. Such a request is
unsupported with the first offending preparation and field recorded, no projection,
coercion, partial execution, silent skip, or rejection of the base candidate.

For each preparation, nine ordered steps execute:

1. Retain the supplied left amplitude.
2. Retain the supplied right amplitude.
3. Multiply left by its supplied factor using the model's multiplication.
4. Multiply right by its supplied factor using the model's multiplication.
5. Add the propagated amplitudes using the model's addition.
6. Apply the model's raw weight to the sum.
7. Apply raw weight to the propagated left arm alone (right arm deleted).
8. Apply raw weight to the propagated right arm alone (left arm deleted).
9. Compute the diagnostic residual `both - left_only - right_only`.

Each trace event records its inputs, output, dependencies, and operation/result
origin. `max_cases` counts **trace steps** in this family, not elapsed time or
preparations. Execution stops at exactly that prefix: no subsequent model
operation is performed. `planned = 9 * preparation_count`; `checked` is the trace
length. Incomplete execution is inconclusive, never pass or rejection. A summary
is emitted only after all nine steps of its preparation. `coefficient_radius`,
`reference_radius`, and `max_copies` are explicitly unused. There is no search
beyond these preparations, extrapolation, clock, lattice, or imported physical time.

## Independent software controls

| Supplied preparation/model | Both-arm raw weight | Blocked weights | Residual |
| --- | ---: | --- | ---: |
| Real `1 + 1`, quadratic scalar/Gaussian/dual | 4 | 1, 1 | 2 |
| Real `1 - 1`, quadratic scalar/Gaussian/dual | 0 | 1, 1 | -2 |
| `1 + u*u`, Gaussian `u*u = -1` | 0 | 1, 1 | -2 |
| `1 + u*u`, degenerate dual `u*u = 0` | 1 | 1, 0 | 0 |
| Same nonreal input, scalar | unsupported | unsupported | unsupported |
| Real `1 + 1`, quartic | 16 | 1, 1 | 14 |
| Real `1 + 1`, zero weight | 0 | 0, 0 | 0 |
| `u + u`, split model with weight `a*a - b*b` | -4 | -1, -1 | -2 |
| Real `1 + 1`, absolute scalar weight | 2 | 1, 1 | 0 |

These are independent algebraic software oracles, not experimental targets.
Tests compare literal expected values and independently expanded arithmetic,
including deliberate differences and mutation controls. The engine itself accepts
no numeric target and does not check equality to this table. All admitted weight
rules execute literally: no implicit absolute value, clamping or normalization.
The scalar/Gaussian/dual common real controls agree; this does not select one.
The nonreal controls expose different supplied multiplication, not a refutation.

## Retained evidence

The ten saved controls have nine execution-complete reports and one unsupported
scalar/nonreal mapping, with no physical verdict. Their immutable history keys are:

- Submission/baseline: `b65fe5f04de537ec82faccb8a3f24e6b62b2233588adf526c285a7e3dff10451`.
- Compressed observation: `845a6a6f921a2af84a3f6337c09b17c21ea81d0a4bfb46b5daeeb69816903238`.

The corresponding records are under `data/candidate_history/submissions/`,
`baselines/`, and `observations/`. The result note is not an executable provenance
input, so recording these keys does not create a self-referential snapshot.

Verification at this snapshot: 22 bench tests and 118 neighboring tests passed
(140 total), including exact controls, operation-count budgets, fresh-process
hash-seed repeatability, full-report cache/fresh/replay equivalence, source guards,
and read-only downstream audits. Ruff and strict mypy passed for the three touched
Python files. The typed checker work ledger built through the IDT Lean interface;
graph validation and claim audit passed with zero audit issues.

A fresh full-history recheck passed all 330 candidate evaluations across 34
submissions and 41 retained observations, with no changes or execution errors.
All 320 earlier evaluations and their original archive bytes were preserved;
only the new submission, baseline pin, and compressed observation were added.
The history result counts are 154 scoped counterexamples, 2 inconclusive,
150 completed screens, and 24 unsupported. These are regression statuses across
different supplied contracts, not physical truth labels or comparable model scores.

## Evidence and claim boundary

The carrier, product, weight, preparations, path factors, path multiplication,
additive recombination, and blocked-arm deletion are **supplied**. Only the resulting
arithmetic is conditionally computed. Raw weight is neither probability nor a
derived detector law, even when it happens to be nonnegative. Physical preparation,
allowed operations, readout, and the bridge from native IDT primitives remain open.
There is no empirical dataset or uncertainty model in this bench.

The shared pipeline report schema, content-addressed provenance, exact source
binding, cache replay and append-only history are reused. Model, scenario,
preparations and bounds all bind the request key. Existing observations and baseline
pins are never refreshed. Downstream native-operation, observability, and pair
audits may report this new wrapper unsupported without rejecting its underlying
candidate. `proof_status` remains `not_attempted`; `empirical_status` remains
`not_tested`; the candidate verdict remains `unchanged` in every bench outcome.
