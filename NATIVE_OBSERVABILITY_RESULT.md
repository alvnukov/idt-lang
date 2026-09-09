# Native observability: redundancy is not a rejected primitive

## Research result

The dual-coordinate control from the previous pass is not ruled out by its
nonzero zero-weight direction. Under the currently supplied operations it is
an observationally redundant description of the signed-integer model.

For integer pairs, define

```
(a,b) * (c,d) = (ac + kbd, ad + bc)
W(a,b) = a² + eta b²
pi(a,b) = a
```

`Proofs/QMClosure/NativeAmplitudeObservability.lean` proves, for arbitrary
integer parameters and inputs, that nonnegative multiplicative weight holds
exactly when `eta >= 0` and `k = -eta`. Thus these two requirements alone admit
a whole family, not just Gaussian integers. A bounded independent check of the
25 parameter pairs accepted by the Python adapter gives three surviving pairs:
`(-2,2)`, `(-1,1)`, `(0,0)`. The finite check is not the universal proof.

For `k=eta=0`, `pi` preserves addition and multiplication and `W=pi²`.
The Lean proof quantifies over every finite expression built from amplitude
variables, coordinate constants, addition and multiplication. Every terminal
weight agrees with the scalar evaluation after projecting both inputs and
constants. Hence the hidden coordinate cannot be detected by this grammar.
Neither representation is deleted, merged or marked physically correct.

This sharpens the earlier "blind spot" finding: the old gates are insufficient
to select physics, but failure to distinguish these two restricted descriptions
is not by itself a checker defect. An added coordinate-swap operation would
make a hidden coordinate observable; that operation is not in the proved grammar.

The follow-up [operation bridge result](NATIVE_OPERATION_BRIDGE_RESULT.md) proves
that even reversibility and individual weight preservation are insufficient
to extend this quotient to arbitrary added operations. Its analyzer keeps
operation-contract failures separate from candidate verdicts.

## Countercontrols

| Model | Proposed scalar projection | Existing candidate screen |
| --- | --- | --- |
| Archived signed integers | Identity | Survives selected bounded laws |
| Dual coordinates, k=eta=0 | Weight-preserving quotient for the declared grammar | Survives selected bounded laws |
| Archived Gaussian integers | Fails already on (0,1): weights 1 and 0 | Still survives selected bounded laws |
| Composition activation, k=-1, eta=0 | Initial weight of (0,1) is 0, but its square has weight 1 | Fails the selected product-weight law |
| Weighted plane, k=-2, eta=2 | Fails on (0,1): weights 2 and 0 | Survives selected bounded laws |

These failures reject only `pi`, not all representations or the candidate.
The activation control prevents declaring a coordinate unobservable merely
because its isolated weight vanishes. Both new probes are retained in candidate
history. Existing observations and baseline pins remain unchanged.

## Executable interface and evidence

```
python3 scripts/check_native_observability.py --batch-file data/native_observability_probes.json
python3 scripts/screen_hypotheses.py --batch-file data/native_observability_probes.json --no-cache
python3 scripts/check_candidate_history.py
```

The first command analyzes the projection, with exact coefficients or an
explicit witness. It returns 0 for completed analysis, including a failed
projection; unsupported analysis returns 3, invalid input/tool failure 2.
It never changes candidate verdicts, archives or baselines. The second command
uses the existing candidate screen and intentionally finds a counterexample.

`data/native_observability_review.json` retains the five source specifications,
analysis reports and source hashes. Its `proof_status` is deliberately
`not_checked_by_this_command`: runtime coefficient analysis does not invoke Lean.
The separate Lean artifact supplies the universal mathematical statements;
no manifest claim or physical status is promoted. Source changes before/during
analysis are detected, and the command must run from a stable checkout.

## Physical bridge remains open

No apparatus, probabilistic readout, set of physically preparable amplitudes,
or full composite-system dynamics has been derived here. In particular, do not
add nondegeneracy, continuous complex phases or purification merely to select
a favored carrier. Each needs a separately justified operational contract.

For context, the abstract of [Chiribella, D'Ariano and Perinotti, arXiv:1011.6451v3](https://arxiv.org/abs/1011.6451v3)
explicitly states additional informational axioms and a purification postulate
in its reconstruction. We have not adopted those assumptions or reproduced
that reconstruction. Only the abstract was retrieved; the larger HTML document
exceeded the helper's retrieval limit. No new empirical requirement is inferred
from that abstract or from the algebraic results above.

The next obligation is to derive an operational preparation/readout/composition
contract and check whether it respects or breaks this quotient. The authoritative
work ledger is `Proofs/MetaLang/V8CheckerResearchProgram.lean`.

## Checker substrate and verification

This pass also found two tooling defects: newly added source paths did not
invalidate the graph, and in-process reload retained an old cached graph
builder while reloading its validator. Both now have regression tests. Source
selection fingerprints preserve declared scope; custom/partial graphs require
explicit rebuilding rather than silent expansion. Legacy graphs without this
metadata auto-migrate only at the canonical default graph path, whose scope is
assumed to be the repository's default; legacy noncanonical paths fail closed.

Verification: 113 checker/history tests and 73 graph/MCP tests passed; both Lean
targets built; the manifest verifier reported no issues. Strict mypy passed for
the changed Python modules/tests. Ruff passed on the native-analysis files;
the five legacy graph/server files still have 12 pre-existing Ruff findings,
with no new findings. This is not an entirely green repository lint gate.

A fresh stdio server on the actual repository found the previously missing
adapter artifact and the new observability artifact, and validated the graph.
The original app MCP connection closed during the faulty reload and was not
reconnected. Source/server validation is not claimed to restore that transport.
Python language-server diagnostics also remain unavailable (missing pyright).

History now contains 308 entries. The two new candidate observations supplement
all earlier records; no old baseline pin was changed in this pass. The separate
projection report does not silently change candidate-screen semantics.
