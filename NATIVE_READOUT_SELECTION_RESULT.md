# Native weight and detector response: a conditional selection result

## Result and claim boundary

The original signed-scalar pair-history weight remains **W(n) = n²**. This
cluster does not replace that native law. It asks which additional, entrywise
detector responses are compatible with a supplied local reference operation.
It adds a universal mathematical classifier and a separate exact finite
diagnostic bound to the actual archived native sources.

The new theorem is conditional, not a derivation of a detector from IDT
primitives. Physical preparation accessibility, local operations, normalized
readout, and the applicability of no-signalling remain operational bridges.
No full QM, SM, gravity, physical data comparison, or empirical acceptance is
established. No manifest version, proof card, or existing claim status changes.

## Universal mathematical statement

In `Proofs/QMClosure/NativeReadoutSelection.lean`, namespace
`IDT.QMClosure.NativeReadoutSelection`,
`reference_invariant_iff_quadratic` concerns arbitrary **g : ℤ → ℝ** with:

- g(n) ≥ 0 for every integer n;
- g(0) = 0 and g(1) > 0;
- entrywise response followed by normalization over the whole supplied context;
- preparations C(x,y) = [[x,y],[1,0]] for all integers x,y;
- Bob's supplied alternatives I and H = [[1,1],[1,-1]].

Reference-row marginal invariance across I/H for every x,y holds **if and only
if g(n) = g(1)n² for every integer n**. Evenness, a scaling law, and a monomial
ansatz are not assumptions. The positive reference contribution makes the
normalization denominators strictly positive.

`weight_response_invariant_iff_on_reachable_squares` specializes this result to
g(n) = f(W(n)). It constrains f only on reachable integer-square weights. It
does not classify f at other weights, Gaussian off-real amplitudes, or a
continuous amplitude domain. It is not a general arbitrary-function solver.

Prior work already established a natural-power selector over rational
amplitudes in `RecordReplicationAndLocalReadout.lean`, and the same-preparation
square/fourth separation in `InternalDetectorReadoutSeparation.lean`. Those
are not new achievements of this cluster. The new mathematical result removes
the monomial restriction on the integer domain; the new software result binds
selected-response diagnostics to the existing native trace.

## Exact finite diagnostics

`native_readout_probe` accepts exactly `id`, `family`, `protocol`, and
`response`. `protocol` is a full existing `native_bell_bridge` specification,
including its complete native algebra or exact archived source snapshot.
The three supplied response recipes are:

| Recipe | Response to the unchanged native weight W |
| --- | --- |
| `native_weight` | W |
| `squared_native_weight` | W² |
| `spike_49` | W + 1 when W = 49, otherwise W |

The evaluator first calls the existing native bridge, including its exact
source binding and operation-admissibility checks. Selected responses are
computed from that trace's actual `raw_weights`, not its reference
probabilities or hard-coded expected answers. The nested
`native_protocol_evidence` retains the separate original reference readout;
`response_contexts` contains the selected detector calculation. A protocol
hash excludes the selected response and is identical across response choices
for the same protocol. The spike recipe is a deliberate nonlinear diagnostic,
not a claim of homogeneity or product-weight compatibility.

The twelve controls fit below the 128 KiB history submission limit and retain
exact scalar/Gaussian source snapshots. Ten execute all four
contexts, one zero-weight preparation is inconclusive, and one unbound
context-first source is unsupported. Completion is not acceptance: the
no-signalling diagnostic can fail while execution completes successfully.

| Supplied preparation/protocol | Native response | Alternative response |
| --- | --- | --- |
| Existing symmetric scalar/Gaussian Bell protocol | S = 14/5; win = 17/20 | W²: S = 2590/697; win = 2689/2788 |
| C = [[1,0],[1,1]], Alice I/I, Bob I/H | Alice row-0 marginal 1/3 → 1/3 | W²: 1/3 → 1/9 |
| C = [[3,4],[1,0]], Alice I/I, Bob I/H | Reference-row marginal 1/26 → 1/26 | Spike: 1/26 → 2/53 |

All marginals of the symmetric Bell protocol are 1/2 under both W and W².
The spike also agrees with W on that protocol and the first asymmetric control.
Thus those finite successes do not establish a unique detector response or
universal reference invariance. `bounded_input_reference_exposes_spike` and
`bounded_agreement_does_not_imply_reference_invariance` record the corresponding
mathematical caution. As a fixed, unnormalized amplitude response W² = n⁴,
the alternative has I3 = 36 for three unit paths, not zero; this exact negative
is already established by
`InternalDetectorReadoutSeparation.three_path_test_separates_rules`. The native
W retains zero I3 in that supplied fixed-path model. Neither fact is an
empirical detector claim.

## What remains blocked

The classifier does not establish that every integer reference preparation is
physically accessible, H is a physically admissible local operation, a detector
is context independent and entrywise, its output is the supplied normalized
response, or there are no further hidden apparatus freedoms. The ideal
zero-response and positive unit-response hypotheses are mathematical
requirements, not experimental detector certification. Failure of a diagnostic
is a conditional incompatibility of a selected response and supplied operations,
not a primitive counterexample, faster-than-light claim, or global model rejection.
H has determinant −2 and is not an integer-lattice bijection. The conditional
theorem requires its availability, not physically reversible dynamics.

`Proofs/MetaLang/V8CheckerResearchProgram.lean` records the conditional theorem
as a typed proof field and separately keeps the primitive operational bridge
blocked. The older combined operational-readout obligation is not fully closed.
Lean does not formally verify this Python evaluator, and the finite evaluator
does not invoke or certify the universal theorem's physical hypotheses.

## Reproduction and preservation

```sh
python3 - <<'PY'
from pathlib import Path
from theory_experiments.candidate_pipeline import run_batch
from theory_experiments.primitive_screen import Limits, load_json
specs = load_json(Path("data/native_readout_controls.json"))
assert isinstance(specs, list)
for result in run_batch(specs, Limits(max_cases=4)):
    print(result.card())
PY
python3 -m unittest discover -s tests -p test_native_readout_probe.py
ruff check theory_experiments/native_readout_probe.py theory_experiments/candidate_pipeline.py tests/test_native_readout_probe.py
mypy --strict theory_experiments/native_readout_probe.py theory_experiments/candidate_pipeline.py tests/test_native_readout_probe.py
lake build Proofs.MetaLang.V8CheckerResearchProgram
git diff --check
```

The example executes without appending history. The screen also accepts the
controls through `--batch-file`; choose a context budget of at least four.
Any history append requires a stable,
reviewed source freeze; existing observations and baseline selections must
remain byte-identical. Tests use temporary history only. Unknown response,
source binding, bridge, or inadmissible operation is unsupported, not rejected;
an insufficient atomic budget executes zero native contexts. All finite reports
retain `proof_status = not_attempted`, `proof_check = not_run_by_this_evaluator`,
and `empirical_status = not_tested`.
