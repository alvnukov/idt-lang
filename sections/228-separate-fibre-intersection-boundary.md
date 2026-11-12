# Separate-fibre intersection boundary

Separate low-rate bounds on two reference-fibre spans can coexist with zero
intersection. The new intersection theorem and explicit controls record the
boundary of an attempted shared-carrier argument. The continuing research
question starts conditionally with a hypothetical nonzero product-invisible
deviation and asks which complete operational hypotheses force compatible
hidden representations or quotients.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Artifact | Exact scope | Research boundary |
| --- | --- | --- |
| Fibre intersection obstruction | Complementary operators with separate invariant submodules and separate uniform bounds have zero intersection when `‖c‖ > qA+qB`. | Either submodule can remain nonzero. Hidden containment and other quotient routes require further arguments. |
| Algebraic two-axis control | Positive actual operators with `q=1/4`, `c=√3/2`, `a=c-q` have nonzero disjoint controlled axes and no global `qⁿ` envelopes. | This is a bounded algebraic control of the separate-axis inference. A full GPT core countermodel would require additional structure. |
| Normalized classical fibre control | The construction uses `q=1/4`, `a=3/4`, `c=1`, positive natural branches summing to identity, and bounded pure-pointer fibres. | Coordinate product readouts separate every table, so its product-invisible deviation space is zero. |

All three kernel tasks carry `parentAccepted` after successful Lean builds,
independent source review and a transitive dependency audit. Historical ledger rows and checkpoint sections
retain their earlier scope.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Intersection obstruction

`IDT.QMClosure.FibreIntersectionObstruction.intersection_eq_bot_of_separate_envelopes`
works over one real or complex field on one normed ambient space. It assumes
`A+B=cI`, invariance of `U` under `A`, invariance of `V` under `B`, and vector
power bounds on the respective submodules with nonnegative constants and
positive rates. Scalar complementarity derives the cross-invariance required
for `U∩V`.
[FibreIntersectionObstruction.lean](../Proofs/QMClosure/FibreIntersectionObstruction.lean)

The restrictions to the intersection carry both bounds and the same scalar
complementarity. If `‖c‖ > qA+qB`, the direct complementary-operator obstruction
forces `U∩V={0}`. Finite dimension, completeness and closedness are absent from
the theorem's hypotheses. The result leaves the individual submodules free to
be nonzero.
[FibreIntersectionObstruction.lean](../Proofs/QMClosure/FibreIntersectionObstruction.lean)

## Algebraic two-axis control

`IDT.QMClosure.SeparateCarrierCountercontrol` uses actual continuous linear
operators on `ℝ²` with

```text
q = 1/4,   c = √3/2,   a = c-q > q
A = diag(a,q),   B = diag(q,a),   A+B = cI.
```

`A_preserves_standardOrthant` and `B_preserves_standardOrthant` give positivity
on the coordinate cone. `A_vertical_power_norm` and `B_horizontal_power_norm`
give exact `qⁿ` bounds on their respective nonzero axes.
`axes_intersection_zero` gives zero overlap. `A_no_global_q_envelope` and
`B_no_global_q_envelope` exclude extending either rate to the whole ambient
operator, because the other axis has rate `a>q`.
[SeparateCarrierCountercontrol.lean](../Proofs/QMClosure/SeparateCarrierCountercontrol.lean)

This control invalidates automatic nonzero overlap or global-envelope inference
from the separate-axis bounds. It establishes no complete GPT model satisfying
the full atomicity research contract.
[SeparateCarrierCountercontrol.lean](../Proofs/QMClosure/SeparateCarrierCountercontrol.lean)

## Normalized classical fibre control

The separate classical construction uses nonnegative two-by-two tables, a
row-sum marginal and the two pure-pointer marginal fibres. Its normalized
calibration is

```text
q = 1/4,   a = 3/4,   c = 1,   A+B = I.
```

The algebraic two-axis control above retains `c=√3/2`. These are distinct
calibrations.
[ClassicalSeparateFibreControl.lean](../Proofs/QMClosure/ClassicalSeparateFibreControl.lean)

`IDT.QMClosure.ClassicalSeparateFibreControl.branches_sum_identity` checks the
normalized sum. `branchA_positive`, `branchB_positive`, `branchA_natural` and
`branchB_natural` supply the actual positive natural branch maps. `K0_bounded`
and `K1_bounded` establish bounded pure-pointer fibres, while the nonzero
`d0` and `d1` witnesses lie in their difference spans.
`fibre_spans_intersection` proves those spans are disjoint.
[ClassicalSeparateFibreControl.lean](../Proofs/QMClosure/ClassicalSeparateFibreControl.lean)

`branchA_fibre_envelope` and `branchB_fibre_envelope` invoke the checked bounded
marginal-fibre theorem for their respective branches. `product_readouts_separate`
shows that four coordinate product readouts separate all tables, and
`product_invisible_zero` makes the product-invisible deviation space zero. Thus
the example targets an inference about separate reference fibres, with no actual
nonzero hidden deviation in its scope.
[ClassicalSeparateFibreControl.lean](../Proofs/QMClosure/ClassicalSeparateFibreControl.lean)

## Conditional hidden-carrier continuation

The open task `hypothetical_hidden_carrier_continuation` begins with a
hypothetical nonzero product-invisible deviation under the full proposed
operational contract. It asks whether complete process comparisons, rich
rotations or the specified generative structure force compatible hidden
representations or quotients. A countermodel must satisfy that exact package to
resolve the alternative route.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A reference-fibre difference span can contain ordinary reference directions.
Its relation to a hypothetical hidden deviation needs an explicit containment
or transport theorem. The research route seeks no unconditional nonzero hidden
carrier. The controls address the naive separate-bound inference, while general
quotient and transport constructions retain their own proof obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The Lie/weight route, controlled-phase construction and independent physical
origins remain open. This checkpoint leaves full atomicity, independent
primitive origin and completed QM reconstruction unresolved.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
