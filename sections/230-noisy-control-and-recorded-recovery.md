# Noisy control and recorded recovery

Three checked kernels distinguish algebraic inversion, positive operational
recovery and recovery with an accessible branch record. The noisy-control probe
planned in the previous checkpoint now has a checked real-matrix artifact. Its
inverse exists algebraically, while positive linear recovery already fails on
two specified states. A separate recorded construction supplies exact positive
recovery when an extra classical label is retained.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Kernel | Checked scope | Continuing boundary |
| --- | --- | --- |
| Positive mixture obstruction | Positive linear recovery cannot separate the two supplied strictly positive mixtures. A common selected readout-error bound is at least `(1-η)/2`. | The exact and approximate theorems have their own readout contracts. Algebraic inverse identities provide no guarantee of cone positivity. |
| Noisy controlled matrices | For `0<η<1`, the actual channel is bijective and preserves positivity and trace after every finite real reference extension. Positive linear recovery fails on two explicit states. | Arbitrary algebraic recovery functions remain available. The example supplies no full atomicity-core or simplex exclusion. |
| Recorded mixture | An encoding into `V×V` has a positive normalized left recovery. Discarding the label gives the original mixture. | Retaining and accessing the extra classical record is a supplied resource. Same-space reversibility and complete program-ensemble origins remain separate. |

The three new kernel entries carry `parentAccepted` after independent source
review and kernel checks.
`controlled_program_recovery_origin` remains
`openPhysicalBridge/openObligation`, with checked boundary evidence and an open
operational-origin agenda. Sections 225–229 retain their historical scope.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Strictly positive mixtures and positive recovery

`IDT.QMClosure.PositiveMixtureRecoveryObstruction.no_positive_two_state_recovery`
takes two cone states distinguished by a nonnegative linear readout with values
zero and one. Their swapped mixtures use two strictly positive coefficients.
No cone-positive linear map can send both mixtures back to their respective
original states. The argument needs no topology or spanning hypothesis.
[PositiveMixtureRecoveryObstruction.lean](../Proofs/QMClosure/PositiveMixtureRecoveryObstruction.lean)

The companion `scaleComplement_inverse_left` and
`scaleComplement_inverse_right` prove algebraic inversion for a map that fixes
an idempotent projector range and rescales its complement by a nonzero scalar.
These signatures contain no positivity conclusion for the inverse.
[PositiveMixtureRecoveryObstruction.lean](../Proofs/QMClosure/PositiveMixtureRecoveryObstruction.lean)

## An invertible noisy controlled channel

`IDT.QMClosure.NoisyControlledRecoveryBoundary` constructs

```text
Gη = η coherent + (1-η) dephased,     0 < η < 1.
```

`noisy_reference_positive`, `noisy_reference_trace` and
`noisy_reference_product` check positivity, trace preservation and product
compatibility after every finite real matrix reference extension. This gives
the stated real-reference complete-positivity scope.
[NoisyControlledRecoveryBoundary.lean](../Proofs/QMClosure/NoisyControlledRecoveryBoundary.lean)

`inverse_left`, `inverse_right` and `noisy_bijective` give the explicit algebraic
inverse for nonzero `η`. `noisy_fixed_zero` and `noisy_fixed_one` derive the
fixed-program responses with coherence parameters `η` and `-η`.
`noisy_flipped_plus` and `noisy_flipped_minus` give dephasing for the flipped
program reductions. `noisy_sector_zero` and `noisy_sector_one` preserve the
controlled pointer laws.
[NoisyControlledRecoveryBoundary.lean](../Proofs/QMClosure/NoisyControlledRecoveryBoundary.lean)

`noisy_no_positive_recovery` excludes positive linear recovery even on the two
explicit normalized positive states `yPlus⊗P0` and `yMinus⊗P0`.
`algebraic_inverse_not_positive` checks the corresponding inverse boundary.
Arbitrary algebraic recovery functions exist through that explicit inverse.
`half_noisy_recovery_boundary` combines bijectivity, valid-state preservation
and the recovery obstruction in the concrete case `η=1/2`.
[NoisyControlledRecoveryBoundary.lean](../Proofs/QMClosure/NoisyControlledRecoveryBoundary.lean)

## Exact quantitative readout scope

`positive_two_mixture_error_bound` uses prescribed zero/one target inequalities.
The generic theorem supplies no calibration of those targets to arbitrary
original-state readouts. In the matrix example, `jointReadout_plus` and
`jointReadout_minus` provide the actual calibration for the selected states.
[PositiveMixtureRecoveryObstruction.lean](../Proofs/QMClosure/PositiveMixtureRecoveryObstruction.lean)
[NoisyControlledRecoveryBoundary.lean](../Proofs/QMClosure/NoisyControlledRecoveryBoundary.lean)

For `0≤η<1`, `noisy_two_readout_error_bound` assumes a positive linear recovery
`R` and the common upper bound

```text
ℓ(R(Gη(x))) ≤ ε,
1 - ℓ(R(Gη(y))) ≤ ε.
```

It concludes `ε ≥ (1-η)/2` for those two states and that one readout. The theorem
uses the displayed one-sided deviations. Normalization of `R` is absent, so
its recovered readouts need not be probabilities.
`identity_attains_two_readout_bound` gives equality for both deviations under
identity recovery. The bound depends on `η` and tends toward zero as `η`
approaches one. A single positive gap across all `η<1` is outside this result.
[NoisyControlledRecoveryBoundary.lean](../Proofs/QMClosure/NoisyControlledRecoveryBoundary.lean)

## Recovery with the label retained

`IDT.QMClosure.RecordedMixtureRecovery` supplies a reversible branch `J`
preserving a cone in both directions, nonnegative weights `a+b=1`, and the
recorded construction

```text
T(x) = (a·x, b·Jx),
R(x,y) = x + J⁻¹y,
D(x,y) = x+y.
```

The record space is `V×V` with product cone and summed unit
`uJoint(x,y)=u(x)+u(y)`. `recovery_record_identity` proves `RT=I`.
`record_positive` and `recovery_positive` give cone preservation. Under the
supplied invariant-unit law, `record_normalized_state` and
`recovery_normalized_state` give preservation of the corresponding normalized
state sets. `discard_record_mixture` identifies the forgotten map as `aI+bJ`.
[RecordedMixtureRecovery.lean](../Proofs/QMClosure/RecordedMixtureRecovery.lean)

The classical bit specialization uses swap on the nonnegative orthant, the
summed-coordinate unit and
`a=(1+η)/2`, `b=(1-η)/2` for every `0<η<1`. Both weights are strictly positive.
`ClassicalBit.recorded_bit_recovery` combines exact recovery with normalized
state preservation. `ClassicalBit.forgotten_no_positive_pointer_recovery`
checks the obstruction after discarding the label, even for the two pointer
states. `ClassicalBit.forgotten_normalized_state` confirms preservation of the
forgotten channel's normalized states.
[RecordedMixtureRecovery.lean](../Proofs/QMClosure/RecordedMixtureRecovery.lean)

The recorded map is an encoding into a larger space with a left recovery.
Identifying it with a same-space automorphism is outside this construction, and
the strictly mixed classical bit has the checked no-positive-recovery obstruction.
The supplied reversible branch can be arbitrary, with no involution premise.
This construction retains a classical branch label and leaves its operational
accessibility explicit.
[RecordedMixtureRecovery.lean](../Proofs/QMClosure/RecordedMixtureRecovery.lean)

## Recovery-origin questions

The continuation now asks which operational assumptions derive positive
recovery, whether a branch record is accessible and retained, and how the
fixed/flipped pure-program alternative ensembles arise. Retaining labels is a
checked recovery resource for the mixture, so a unique derivation of
cancellation requires an additional resource contract. Excluding simplex-based
representations remains a separate investigation.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The three kernels supply no complete controlled-program dual-ensemble
construction, atomicity-core model, independent recovery origin, cancellation
origin or completed QM reconstruction. The positive-recovery boundary and the
recorded alternative retain their exact supplied mathematical contracts.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
