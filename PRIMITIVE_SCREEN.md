# Fast primitive-candidate screen

An offline **pre-proof counterexample search**, not a universe simulator, an
experimental confirmation, or a replacement for Lean. A run computes outputs
from a candidate's rules; it never accepts a candidate's expected test results.
The command runs without launching Lean, using only Python's standard library
(Python 3.10+). Use the project's newer Python interpreter where necessary.

## Run and replay

```sh
python3 scripts/screen_primitives.py --builtin square
python3 scripts/screen_primitives.py --builtin fourth
python3 scripts/screen_primitives.py --builtin non_psd --output /tmp/idt-screen-report.json
python3 scripts/screen_primitives.py --replay /tmp/idt-screen-report.json
```

Output creation refuses to overwrite an existing file. `--json` prints the full
report. Replay recomputes the recorded search and compares the whole report,
including candidate, implementation/ledger hashes, bounds and witnesses. It is
a reproducibility check, **not an independent proof checker**. Replay requires
the same source versions. A replayed counterexample retains exit code 1.

Exit codes: 0 = no counterexample in the completed finite search; 1 = a
counterexample to a selected requirement under stated assumptions; 2 = invalid
input or operational error; 3 = incomplete or unsupported checks. None means
"the primitives are correct". A failure dominates incomplete/unsupported checks;
all individual results remain in the report. Empty checks cannot pass.

## Propose a hypothesis

`--builtin fourth --show-candidate` prints this editable input:

```json
{"id":"fourth","family":"power_sum","dimension":2,"exponent":4}
```

Save a modified specification and run `--candidate-file path/to/candidate.json`.
The power family computes `w(c) = |sum(c)/dimension|^exponent`. It specifies no
composition law; composition tests therefore return `unsupported`, including
for exponent 2. The kernel family accepts exact fraction strings:

```json
{"id":"my_kernel","family":"pair_kernel","matrix":[["1/6","1/3"],["1/3","1/6"]]}
```

This adapter computes `w(c) = sum(i,j, c[i] K[i,j] c[j])`. Inputs are symmetric
rational matrices, dimension 1–3. No automatic normalization or PSD repair is
performed. Floats, unknown fields, duplicate JSON keys and executable code in
inputs are rejected. A genuinely different primitive language needs a new,
reviewed adapter; these two families are **not an exhaustive search space**.

## What is tested

| Check | Finite domain and exact requirement |
| --- | --- |
| Unit weight | The all-ones event has weight 1. This is a selected normalization convention. |
| Event nonnegativity | All binary indicator events have weight >= 0. |
| Coefficient third difference | The alternating eight-term difference at the origin vanishes for coefficient triples in the integer grid. |
| Self-composition | All indicator events of each tensor power up to the copy bound have nonnegative weight. |
| Signed-reference composition | The diagonal event of `K tensor R` has nonnegative weight for grid vectors `v` with nonzero sum and `R[i,j]=v[i]v[j]/sum(v)^2`. |

The third-difference check assumes coefficient addition. It is not a laboratory
three-slit test: operational preparation, changing apertures, detector response
and uncertainties are not modeled. Kernel event weights are interference/history
weights, **not additive probabilities of mutually exclusive detector records**.
References are normalized square-weight systems admitted as an explicit extra
assumption, not derived from lower primitives. Zero-sum vectors are outside this
reference family; no universal positivity conclusion follows from its finite grid.

Defaults: coefficient radius 1, reference radius 2, up to 2 copies, at most 1000
evaluations **per check**. All arithmetic uses exact fractions. Grid order is
lexicographic; events use increasing bitmasks. A check stops at its first
violation, not necessarily the globally smallest counterexample. Reports give
planned/checked counts, bounds and exact witness inputs. Resource caps are
explicit: dimensions <=3, radii <=2, copies <=2, and cases per check <=5000.
An exhausted budget is `inconclusive`, never a successful exhaustive result.

## Known controls, not discoveries

- `square`: a normalized real rank-one kernel; completes the default finite
  checks without a counterexample. It is not the full complex quantum theory.
- `fourth`: computes a third difference of 36 at the first default grid triple;
  composition remains unsupported.
- `non_psd`: passes local weights, third difference and the tested self-copies,
  but produces diagonal-event weight -1/2 with normalized reference vector
  `(-2,1)`. With `--reference-radius 1`, this search misses the contradiction.
  That deliberate regression test illustrates why a finite pass is not truth.

These controls are already known from repository research; they validate the
search implementation, not a novel physical prediction. See
`Proofs/QMClosure/CoherentReferencePositivity.lean` for the independent existing
mathematical result. Its universal self-copy theorem is stronger than this
program's finite enumeration and is not relabeled as a new search result.

## Research loop and remaining work

Write executable rules and expose imports; run the fixed screen; inspect a
counterexample or extend bounds; only then select a precise statement for proof.
Changing a requirement or inspecting a dataset during candidate selection must
not later be presented as independent validation. There is no fitting, random
sampling, laboratory dataset, or held-out empirical validation in this version.

`Proofs/MetaLang/V8PrimitiveScreenBoundary.lean` records the evidence category,
checks and open research obligations. It does not certify the Python runtime.
The current manifest, formal-proof ledger and experiment runner are unchanged.
The fast path never promotes a claim or edits them.

Lower-primitive derivation, detector records, Bell correlations, complex quantum
closure, experimental data, the Standard Model and gravity remain explicitly
untested. Rejection applies to the candidate **plus the named assumptions and
selected requirements**, not automatically to every possible realization of its
lower primitives.

Targeted verification:

```sh
python3 -m unittest tests.test_primitive_screen
ruff check theory_experiments/primitive_screen.py scripts/screen_primitives.py tests/test_primitive_screen.py
mypy --strict theory_experiments/primitive_screen.py scripts/screen_primitives.py tests/test_primitive_screen.py
```
