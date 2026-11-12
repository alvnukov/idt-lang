# Fixed programs, recovery and the phase boundary

Four Lean-checked modules supply sharp-effect, complete-branch, fixed-program
restriction and recovered-phase kernels. Their operational premises remain
explicit. A checked real-matrix dephased control tests the missing recovery
inference in the normalized controlled-process route, and its coherent companion
exhibits a concrete nontrivial reduced phase. The
operational research ledger keeps that origin obligation open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Kernel | Checked conclusion | Supplied contract |
| --- | --- | --- |
| Sharp effect and rank one | Finite-dimensional endpoint certainty determines the sharp ball effect. Calibrated positive branches have the rank-one formula. | Ball/Lorentz geometry, positivity and exact endpoint calibration. |
| Fixed pure program | A reversible joint control induces a base-preserving local equivalence. Forward intertwining alone gives a left recovery. | Joint reversibility, embedding/retraction laws and the appropriate atomicity and naturality premises. |
| Complete sharp branch | Two positive complete lifts of one rank-one branch are equal. | Unnormalized output atomicity, local compatibility, separating reference effects and all-reference effect interchange. |
| Program phase | Mixed-program linearity and one left recovery give `J=2E-I`, `J²=I` and `E=(I+J)/2`. | The explicit response identities, `RF+=I`, `F+E=E` and `E²=E`. |

The five kernel entries carry `parentAccepted` after independent source review
and kernel checks.
The controlled-program recovery-origin task is an open physical bridge.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Sharp effects and positive rank-one branches

`IDT.QMClosure.SharpEffectRankOne.linear_effect_representation` represents every
algebraic linear effect on the finite-dimensional real Lorentz space through its
scalar and vector coefficients. Finite-dimensional continuity and Riesz supply
this full effect representation.
[SharpEffectRankOne.lean](../Proofs/QMClosure/SharpEffectRankOne.lean)

`sharp_unique` derives the unique sharp effect from positivity and exact
one/zero pointer endpoints. `sharp_interval_ray` proves that every effect in its
positive order interval lies on its ray. `bounded_effects_separate` checks that
bounded positive Lorentz effects distinguish every output vector. Together with
positive-map calibration, `calibrated_lorentz_endomorphism` gives the global
measure-and-prepare formula

```text
M(v) = sharpEffect(n)(v) · (1,n).
```

The ball geometry and instrument calibration remain supplied inputs.
[SharpEffectRankOne.lean](../Proofs/QMClosure/SharpEffectRankOne.lean)

## Complete branch uniqueness needs every reference effect

`IDT.QMClosure.CompleteSharpBranchRigidity.complete_sharp_branch_unique` takes
two positive joint lifts with the same rank-one local action. Its atomicity
premise applies to unnormalized positive outputs whenever their local marginal
is proportional to the pointer, including the zero-weight case.
[CompleteSharpBranchRigidity.lean](../Proofs/QMClosure/CompleteSharpBranchRigidity.lean)

Atomicity factors each output into a pointer append and reference marginal.
Interchange with every supplied reference effect determines identical reference
readouts. Reference-effect separation then gives equality on the positive cone,
and cone spanning extends it to the whole joint space. The proof uses no
joint-state tomography premise. All-reference effect interchange is an explicit
contract requiring justification beyond discard naturality.
[CompleteSharpBranchRigidity.lean](../Proofs/QMClosure/CompleteSharpBranchRigidity.lean)

`unnormalized_atomicity_of_normalized` derives the zero-inclusive premise from
supplied normalized atomicity, nonnegative cone scaling and faithful
normalization. Faithfulness means that the normalization effect is strictly
positive on every nonzero cone element. The proof treats zero directly and
normalizes and rescales every nonzero output.
[CompleteSharpBranchRigidity.lean](../Proofs/QMClosure/CompleteSharpBranchRigidity.lean)

## Fixed-program restriction and the weaker recovery bridge

`IDT.QMClosure.FixedPureProgramRestriction.fixed_pure_program_restriction`
derives forward and inverse target-program invariance from a pure target,
local midpoint symmetry and an embedded fixed centre. Under supplied joint
reversibility and target-fibre atomicity, `reversible_fibre_restriction` packages
the induced forward and inverse maps as a normalized-base-preserving linear
equivalence.
[FixedPureProgramRestriction.lean](../Proofs/QMClosure/FixedPureProgramRestriction.lean)

The weaker `left_recovery_of_forward_intertwining` needs only the forward
embedding identity, the embedding/retraction law and the inverse joint control.
It derives

```text
R = retract ∘ G⁻¹ ∘ embed,     R F+ = I.
```

`induced_mapsTo` transfers normalized-base preservation through those maps.
`induced_pointer_fixed` transfers pointer fixation.
`reference_target_transfer` uses supplied marginal naturality to extend the
target-program conclusion to arbitrary reference systems. Local midpoint
symmetry is used only on the local base. Reference-composite symmetry and an
interior product centre are absent from these transfer premises.
[FixedPureProgramRestriction.lean](../Proofs/QMClosure/FixedPureProgramRestriction.lean)

Joint reversibility is an additional assumption in this package. The existing
normalized controlled-process route has no checked derivation of that premise
or of the weaker recovery relation.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Phase synthesis from one left recovery

`IDT.QMClosure.ProgramPhaseSynthesis.program_response_sum` uses linear response
to equal mixed programs and the supplied branch-response identities to derive
`F+ + F- = 2E`. `program_phase_package` additionally assumes one left recovery
`RF+=I`, destructive-range fixation `F+E=E` and idempotence `E²=E`. These give
`RE=E` and

```text
J = RF- = 2E-I,     J² = I,     E = (I+J)/2.
```

`normalized_recovered_phase` packages the involution as a linear equivalence
preserving the supplied set in both directions when `R` and `F-` preserve it.
For a normalized base this gives normalized-base preservation. Cone positivity
requires preservation of the actual cone or a separate generating argument.
The signatures admit `E=I` and `J=I`. Nontriviality requires separate evidence.
[ProgramPhaseSynthesis.lean](../Proofs/QMClosure/ProgramPhaseSynthesis.lean)

The source assumes both program identities `Φ(y+)=Φ(y-)=E`. The sharp-effect and
complete-branch modules provide possible supporting steps, while their
integration into the actual operational program construction remains open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Dephased-control boundary and continuing origin work

`IDT.QMClosure.DephasedControlledCountercontrol.reference_positive`,
`reference_trace`, `reference_state` and `reference_product` check the actual
finite real reference extensions of the Kraus control. `sector_zero` and
`sector_one` give the controlled pointer laws, and `phase_yPlus` gives the
specified target-program flip. `fixed_program_zero` and `fixed_program_one`
show that both distinguished fixed programs induce noninjective control
dephasing. Positive trace-one product inputs are supplied by
`product_yPlus_state` and `product_yMinus_state`. Their `controlled_collision`
supports `dephase_no_state_recovery` and `controlled_no_state_recovery`, which
exclude even an arbitrary recovery function on all normalized positive inputs.
[DephasedControlledCountercontrol.lean](../Proofs/QMClosure/DephasedControlledCountercontrol.lean)

This targets recovery inferred from the normalized controlled contract.
Conjugation by `U=K0+K1` is positive, trace preserving and involutive.
`coherent_program_zero` and `coherent_program_one` derive its reduced responses
as identity and phase. `coherent_program_yPlus` and `coherent_program_yMinus`
derive dephasing for both flipped-program reductions. `phase_nontrivial` proves
`phase(yPlus) ≠ yPlus`, while `dephase_as_phase_average` gives the sharp half-sum
identity in this supplied model. A full atomicity-core or local-dimension-three
countermodel would require additional verified structure. Matrix-theory
atomicity and pure-marginal factorization remain unchecked here.
[DephasedControlledCountercontrol.lean](../Proofs/QMClosure/DephasedControlledCountercontrol.lean)

`controlled_program_recovery_origin` tracks the operational origin of a left
recovery or sufficient reversible control. It also tracks all-reference effect
interchange and the complete destructive-response identities needed to combine
the kernels. The geometric central/noncentral, Lie/weight, rank/dimension and
independent primitive-origin obligations remain open. This checkpoint leaves
full atomicity and completed QM reconstruction unresolved.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A next falsification obligation distinguishes algebraic invertibility from
positive operational recovery. The candidate mixture
`Gη=η coherent+(1-η)dephased`, with `0<η<1`, is to be checked for its exact
pointer/program laws and algebraic invertibility, together with a possible
obstruction to positive linear left recovery. This candidate remains an
unchecked planned test.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
