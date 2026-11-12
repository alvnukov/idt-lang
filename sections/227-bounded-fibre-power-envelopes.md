# Bounded fibres and power envelopes

This continuation connects bounded fixed-success fibres, uniform operator-power
bounds, surjective intertwining images and a direct complementary-operator
obstruction. The common hidden representation needed by the atomicity research
route remains an open obligation in the operational ledger. Earlier checkpoint
sections retain their historical scope.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
[Phase-echo interface checkpoint](226-phase-echo-interface-closure.md)

| Package | Mathematical scope | Current boundary |
| --- | --- | --- |
| Bounded fibre | Exact fixed success gives an invariant algebraic difference span, its actual restricted operator and a uniform `qⁿ` operator-norm envelope. Cone scale closure, positivity, marginal intertwining and the supplied endpoint relation `Lx=qx` derive the fixed-success law. | Boundedness and the operational maps remain supplied. The difference span can include ordinary reference directions. |
| Surjective image | An original power envelope descends through an actual continuous surjective intertwiner to a complete target. | The intertwiner and target operators must be supplied. The theorem does not construct a hidden quotient. |
| Complementary operators | On one nontrivial real or complex normed carrier, two uniform envelopes and `A+B=cI` force `‖c‖ ≤ qA+qB`. | Both bounds and complementarity must hold on that same carrier. Its existence remains a separate question. |

All three kernel tasks carry `parentAccepted` after successful Lean builds,
independent source review and a transitive dependency audit. The common hidden-carrier continuation remains an
open physical bridge.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Bounded spanning sets and fixed success

The fibre module first treats a real Banach space and a bounded set whose
algebraic span is the whole space. An operator preserving that set has bounded
orbits on its generators. Points with bounded orbits form a real submodule, so
algebraic spanning gives pointwise boundedness everywhere. Banach–Steinhaus then
gives one uniform bound on all operator powers. Completeness and algebraic
spanning are part of this contract.
[BoundedFibrePowerEnvelope.lean](../Proofs/QMClosure/BoundedFibrePowerEnvelope.lean)

For a fixed `q > 0` and `T(K) ⊆ qK`, rescaling to `U=q⁻¹T` gives an operator
preserving `K`. In a finite-dimensional real ambient space, let `H` be the
algebraic span of all `v-w` with `v,w∈K`. The fixed-success law derives
`T(H) ⊆ H`. Boundedness of `K` and uniform boundedness on `H` then give one
nonnegative constant `C` with

```text
‖Tⁿv‖ ≤ C qⁿ ‖v‖     for every n and every v∈H.
```

The vector endpoint is `fixed_success_fibre_power_envelope`.
`restrictedFibreOperator` constructs the actual endomorphism of `H` from the
derived invariance. `restrictedFibreOperator_pow_apply` identifies its powers with
ambient powers, and `subtype_restrictedFibreOperator` gives the inclusion
intertwining identity. `fixed_success_restricted_fibre_power_envelope` supplies
its operator-norm envelope. This operator can be passed directly to
`QuotientPowerEnvelope.surjective_power_envelope` when that theorem's actual
surjective-target contract is supplied. The constant is uniform over all powers
for the chosen operator and set. Uniformity across reference dimensions remains
unproved. `H` may contain ordinary reference directions. Identifying a product-invisible
hidden kernel, an invariant quotient or a common carrier needs further
containment and selection arguments.
[BoundedFibrePowerEnvelope.lean](../Proofs/QMClosure/BoundedFibrePowerEnvelope.lean)

## Marginal geometry supplies the fixed-success law

The geometric endpoint takes a cone closed under nonnegative scaling,
a positive branch `T`, a marginal map and a local map `L`. Naturality gives
`marginal ∘ T = L ∘ marginal`, and the supplied endpoint relation is `Lx=qx`.
For `v` in the fibre with marginal `x`, the vector `w=q⁻¹Tv` remains in the cone
and has marginal `x`, giving `Tv=qw`. Thus the exact fixed-success law follows
from these map equations and positivity.
[BoundedFibrePowerEnvelope.lean](../Proofs/QMClosure/BoundedFibrePowerEnvelope.lean)

`bounded_marginal_fibre_power_envelope` combines that law with the difference-span
argument. Boundedness of the marginal fibre remains assumed. The actual branch,
marginal, local endpoint relation and their operational origins also remain
supplied. This construction makes no identification of every fibre direction
with a hidden physical degree of freedom.
[BoundedFibrePowerEnvelope.lean](../Proofs/QMClosure/BoundedFibrePowerEnvelope.lean)

The control fibre is `K={(1,t) | |t|≤1}`. Its difference span contains the nonzero
vertical direction `(0,1)`, and the constant-success operator `qI` supports the
power-envelope construction. The variable-success control
`T(a,b)=(a/2+b/4,0)` always normalizes to `(1,0)` with success in `[1/4,3/4]` on
`K`. It sends `(0,1)` to `(1/4,0)`, outside the difference span. Bounded variable
success therefore leaves the fixed-success invariance step unsupported.
[BoundedFibrePowerEnvelope.lean](../Proofs/QMClosure/BoundedFibrePowerEnvelope.lean)

## Surjective-image and complementary bounds

`IDT.QMClosure.QuotientPowerEnvelope.surjective_power_envelope` takes an actual
continuous surjective intertwiner `π`, original operator `T`, target operator
`S`, and a fixed all-power envelope on `T`. It derives the corresponding
envelope on `S`. Completeness is required only on the target. The source may be
incomplete, and the argument requires no right inverse or supplied quotient
power bound. [QuotientPowerEnvelope.lean](../Proofs/QMClosure/QuotientPowerEnvelope.lean)

`quotient_complementary_rate_bound` additionally takes a nontrivial complete real
or complex target, two original envelopes with independent positive rates, both
intertwining equations and target complementarity. It derives `‖c‖ ≤ qA+qB` on
that supplied target.
[QuotientPowerEnvelope.lean](../Proofs/QMClosure/QuotientPowerEnvelope.lean)

`IDT.QMClosure.ComplementaryPowerEnvelope.complementary_operator_rate_bound`
proves the direct same-carrier obstruction over a real or complex normed space.
Scalar complementarity derives commutation. A binomial estimate controls powers
of the sum, and the scalar power-envelope obstruction gives `‖c‖ ≤ qA+qB`.
Finite dimension, completeness, eigenvectors and real-complexification are
unneeded for this theorem. `complementary_operator_equal_rate_bound` gives the
real equal-rate conclusion `c ≤ 2q`.
[ComplementaryPowerEnvelope.lean](../Proofs/QMClosure/ComplementaryPowerEnvelope.lean)

## The remaining common-carrier obligation

The proposed atomicity contradiction starts from a hypothetical nonzero hidden
deviation. The three interfaces do not yet turn that hypothetical violation into
a shared nontrivial carrier where both low-endpoint bounds and scalar
complementarity hold together. The next substantive work is to prove the required
hidden-fibre containment and compatible invariant representation or quotient,
or identify an obstruction to that implication. An actual surjective intertwining map is required for the
surjective-image route.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The direct same-carrier scalar argument removes the need for a real-to-complex
norm bridge in that argument. The separate Lie/weight route may still require
complexification and quotient norm transfer. Bounded-fibre origins, fixed-success
origins, positive natural branch maps and complete process comparisons remain
physical premises. Full atomicity, independent primitive origin and completed
QM reconstruction remain open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
