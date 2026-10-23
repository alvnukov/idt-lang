# Bounded native reference-readout search

## Result and scope

The `native_readout_search` adapter searches the supplied reference family
`C(x,y) = [[x,y],[1,0]]` with Alice I/I and Bob I/H, where
`H = [[1,1],[1,-1]]`. It reuses the existing native algebra, exact archived
source binding, and selected-response formulas. It does not change the native
weight, derive a detector, or perform an empirical test.

Within radius four, the first squared-weight response witness is `(-1,-1)`
at preparation index 6: the reference-row marginal changes from `1/3` to
`1/9`, with signed before-minus-after difference `2/9`. The first `spike_49`
witness is `(-4,-3)` at index 70: `1/26` becomes `2/53`, with difference
`1/1378`. These require respectively 24 and 280 native joint contexts.
The unchanged native response has no violation in the 81-preparation box.
The spike has no violation in the radius-three box. Neither finite absence
establishes universal reference invariance or physical acceptance.
The six retained controls include the full exact archived signed-scalar and
Gaussian source candidates, alongside four small explicit-algebra controls.
Both archived candidates give these same witnesses on the real integer
reference family; this does not distinguish their off-real behavior.

“First” means only first in this explicit bounded enumeration: the full signed
square `[-radius,radius]²`, sorted by
`(max(abs(x),abs(y)), abs(x)+abs(y), x, y)`. No symmetry pruning, fitting,
search-dependent formula changes, or claims of minimality over all experiments
are involved. The prefix sizes are 1, 9, 25, 49, and 81 for radii zero to four.

## Input, budget, and output contract

The strict input fields are `id`, `family`, `model`, `radius`, and `responses`.
`model` is an existing explicit amplitude algebra or a full source-candidate
snapshot. Radius is an integer from zero to four; responses are an ordered,
nonempty, duplicate-free list of up to three existing names: `native_weight`,
`squared_native_weight`, and `spike_49`. An unknown response makes the entire
request unsupported before native arithmetic. Unknown source binding and
unsupported native weight law are also preflight-unsupported, even when the
budget is below four. Malformed inputs are parse errors, not scientific results.

`Limits.max_cases` counts native joint contexts: four per atomic preparation.
No preparation starts with fewer than four contexts remaining. The other
generic limit fields are explicitly unused. Each visited preparation executes
the existing native bridge once, then all still-unresolved selected responses
consume that same trace. Each response stops at its first reference-row
violation; the search stops when all responses have witnesses, the domain is
exhausted, or the budget cannot fund another preparation.

Per-response states are `conditional_violation_found`,
`no_violation_within_bounds`, or `inconclusive`. A budget-limited unresolved
response makes aggregate status inconclusive, while preserving witnesses
already found. Otherwise aggregate `no_counterexample_within_bounds` means
search completion only, including runs that found conditional violations.
It never means that primitives were accepted or rejected. `stop_reason`,
`domain_exhausted`, and `search_complete` are separate; an all-witness early
stop need not exhaust the box or spend the planned context budget.

Reports retain per-response visited counts and first witnesses, not every
preparation trace. Each witness includes a full replayable
`NativeReadoutProbe` specification, its four-context limits, completion checks,
exact native evidence nested inside selected-response evidence, and the
reference-row before/after values and signed difference. No witness evidence
is recomputed outside the budget. Other no-signalling diagnostics corroborate
the trace but are not substituted for the specific reference-row criterion.
The compact result card shows stop/completion flags and each response's state,
visited count, and first-witness coordinates/index/reference values, without
embedded source archives or traces. Its completion-only and no-primitive-rejection
labels remain visible alongside the findings; older result cards are unchanged.

## Mathematical and physical boundary

`NativeReadoutSelection.reference_counterexample_refutes_invariance` proves
the elementary implication from an exact reference-row inequality to the
negation of the supplied universal `ReferenceInvariant` predicate. The existing
conditional arbitrary-response classifier remains unchanged. The Lean checker
research ledger records the bounded-search task, this typed implication,
finite software-result fields, and explicit limitations. Lean does not formally
verify the Python implementation or certify its recorded numerical fields.

Normalization, all-integer physical reference accessibility, entrywise
context-independent detector response, and availability of H remain supplied
operational bridges. H has determinant −2; no physical reversible map or
integer-lattice bijection is established. Violations concern the selected
operational package, not IDT primitives. Gaussian off-real or continuous
response classification, empirical confirmation, and full QM/SM/gravity
derivations remain outside scope. QM is not proved. No manifest, proof-card,
theory-version, or prior claim-status upgrade is made.

## Reproduction and preservation

Run the new controls through the existing non-recording batch interface with at least
324 contexts to exhaust the radius-four box:

```sh
python3 - <<'PY'
from pathlib import Path
from theory_experiments.candidate_pipeline import run_batch
from theory_experiments.primitive_screen import Limits, load_json
specs = load_json(Path("data/native_readout_search_controls.json"))
assert isinstance(specs, list)
for result in run_batch(specs, Limits(max_cases=324)):
    print(result.card())
PY
python3 -m unittest discover -s tests -p test_native_readout_search.py
python3 scripts/check_candidate_history.py
git diff --check
```

The unknown-response negative control intentionally returns unsupported. The
batch interface and history check above do not append history; tests use
temporary cache/history. The command-line screen always records history and
must not be used against the repository archive before review.
Existing history files and baseline selections must remain byte-identical.
Cache and history schemas are unchanged; source provenance conservatively
invalidates old cache keys while historical semantic reports stay unchanged.
