# Native operation bridge: a counterexample and a conditional route

## Result

Reversibility and preservation of every individual weight do **not** suffice
to preserve coherent-reference observations. This is a mathematical result
for supplied integer amplitudes, not evidence for a physically realizable device.

For the dual carrier, use addition componentwise, multiplication
`(a,b)*(c,d)=(ac,ad+bc)`, and `W(a,b)=a²`. The previous scalar quotient
`pi(a,b)=a` preserves every expression in the old addition/multiplication
grammar. Now supply the transformation

```
T(a,b) = (a,b) if b is even, otherwise (-a,b).
```

`T` is its own inverse and preserves every individual weight. Nevertheless,
`x=(1,0)` and `y=(1,1)` initially have the same observation in every old-grammar
context, while adding the same reference `(1,0)` after applying `T` gives
weights **4 and 0**. The failure is in extending the old quotient to the new
operation, not in the primitive candidate. A genuinely realizable new operation
can legitimately refine observational equivalence.

`Proofs/QMClosure/NativeOperationBridge.lean` proves the involution, weight
identity, counterexample and the following conditional route:

1. Additivity plus individual weight preservation implies pair-sum weight
   preservation: `W(Fx+Fy)=W(x+y)`.
2. Surjectivity plus pair-sum weight preservation transports equivalence under
   all supplied coherent references.
3. For the dual carrier this reference equivalence is exactly equality of the
   real coordinate. Every integer-linear weight-preserving map respects it,
   even without invertibility.

These are universal statements about the supplied mathematical carrier.
Additivity, surjectivity and access to every reference are explicit assumptions;
the conditional implications do not derive them from the lower primitives.

## Faster exact checks and false-rejection controls

For `F(a,b)=(pa+qb,ra+sb)` and `W(a,b)=a²+eta*b²`, weight preservation is
equivalent to three coefficients vanishing:

```
p² + eta*r² - 1 = 0
2*(p*q + eta*r*s) = 0
q² + eta*s² - eta = 0
```

The Lean artifact proves this equivalence for all integer parameters and inputs.
The Python analyzer evaluates the exact coefficients; it does not infer a
universal identity from an unsuccessful finite search. Independent grid tests
check the implementation. Its matrix-input bounds are -4 through 4, not a
physical restriction on candidates. Unsupported operations need a new adapter.

Seven versioned operation probes are retained in `data/native_operation_probes.json`.
The tests replay all 35 combinations with the five previously retained candidates:

| Control | Diagnostic result | Scope protection |
| --- | --- | --- |
| Parity sign on dual plane | Reversible and individually weight-preserving, but changes coherent pair weights and breaks the old quotient | Does not reject the dual base |
| Gaussian quarter-turn `(-b,a)` | Reversible, additive, weight-preserving; not multiplicative under the same unary map on both factors | Multiplicativity is not a dynamics requirement |
| Projection onto the real coordinate | Reversible on the scalar carrier, not on the full dual plane | Uses the actual carrier, not its ambient plane |
| Hidden-coordinate shear | Preserves dual weight and quotient; leaves the scalar carrier | An operation-domain mismatch is not a candidate rejection |

The Gaussian quarter-turn already equals multiplication by `(0,1)` in the old
Gaussian grammar. Requiring it to be an algebra automorphism would wrongly
exclude this control. Physical transformations on composite systems and their
tensor representation remain a separate open bridge.

## Reproduce

```
python3 scripts/check_native_observability.py \
  --batch-file data/native_observability_probes.json \
  --operations-file data/native_operation_probes.json
python3 -m unittest tests.test_native_operations tests.test_native_observability
lake build Proofs.QMClosure.NativeOperationBridge
lake build Proofs.MetaLang.V8CheckerResearchProgram
python3 scripts/check_candidate_history.py
```

Run Lake commands sequentially. The optional operation mode reports independent
properties and two explicitly supplied contracts; neither is an empirical
admissibility gate. Completed contract failures and carrier mismatches return 0,
unsupported adapters return 3, malformed inputs/source changes return 2.
Candidate verdicts, old observations and baseline pins are unchanged.
The report binds candidate and operation inputs and loaded source hashes;
`proof_status=not_checked_by_this_command` remains explicit because this command
does not invoke Lean. The retained review snapshot is
`data/native_operation_review.json`; it is evidence, not a promoted theory claim.

## Missing physical bridge and external context

The next obligation is **joint physical realizability of the compared
preparations, operation, and coherent reference/readout**. There is no derived
apparatus or empirical probability map here. Existing IDT distinguishability
non-collapse is not the same proposition as indistinguishability congruence.
The signed, unnormalized polarization of a weight is also not the existing
supplied `Nat`-valued normalized-overlap interface. These results do not close
that QM obligation. The authoritative task and blockers are recorded in
`Proofs/MetaLang/V8CheckerResearchProgram.lean`.

In [Barrett, *Information processing in generalized probabilistic theories*,
quant-ph/0508211v3, Appendix A](https://arxiv.org/html/quant-ph/0508211v3), the
transformation-linearity argument works with vectors of measurement
probabilities and preservation of their probabilistic mixtures. This does not
establish additivity of our coherent integer amplitudes: the state description
and operational identification would need their own derivation. We import
neither QM nor a new experimental exclusion criterion from this paper.

Retrieved evidence: normalized document `web_4dbce076a61fda07`, byte range
107460–112460 (Appendix A ends within this fragment), normalized SHA-256
`8a6d449d073df953b4fd930a63edd5bb3fefe08652b6225ce81de9ced31b160a`.
The retrieved HTML artifact was complete; only this bounded passage was read.
The attempted separate arXiv PDF retrieval was blocked and is not evidence.

## Verification of this snapshot

Both Lean targets built successfully. The checker/history regression passed
124 tests before the final snapshot-replay test was added; the final targeted
operation suite passed all 12 tests. A separate fresh replay checked all 308
candidate entries across 32 submissions and validated 39 retained observations:
no changed baselines, execution errors or candidate removals. The 22 archived
sources without native prediction adapters remain unsupported, not rejected.

Ruff and strict mypy passed on the three changed/new Python files. The live IDT
graph validated its source hashes and the claim audit found no issues or
formal-proof residuals. Python language-server diagnostics remain unavailable
because pyright is absent; this is not reported as a passed check. Repository-wide
lint and the entire repository test suite were not rerun for this isolated mode.

The correct primitive base, full QM, the Standard Model and gravity remain
unestablished. This pass narrows an operational ambiguity and makes repeated
hypothesis checks cheaper without silently turning a modeling assumption into
a law of nature.
