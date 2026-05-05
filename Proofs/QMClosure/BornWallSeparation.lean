import Proofs.QMClosure.QMSemanticContentScaffoldBundle

namespace IDT
namespace QMClosure

/-!
Born wall separator.

The current finite readout scaffold proves normalization, additivity,
coarse-graining, and operational-equivalence accounting for supplied finite
weights. It does not select which supplied weights are physically actualized.

The separator below gives a small machine-checked witness: both a linear and a
quadratic two-branch readout are admitted by the finite accounting scaffold, but
they are distinct. Therefore the present B1/scaffold layer has not derived the
quadratic/Born actualization rule; that selector must be proved separately or
introduced as an explicit boundary assumption.
-/

def linearTwoBranchReadout : StableFiniteReadout :=
  {
    weights := [3, 4],
    positive_total := by decide
  }

def quadraticTwoBranchReadout : StableFiniteReadout :=
  {
    weights := [9, 16],
    positive_total := by decide
  }

def ReadoutAccountingAdmits (readout : StableFiniteReadout) : Prop :=
  normalizationDenominator readout > 0
    ∧ (normalizedReadout readout).length = readout.weights.length
    ∧ (∀ normalized,
        normalized ∈ normalizedReadout readout →
          normalized.denominator = normalizationDenominator readout)

theorem stable_readout_is_admitted_by_accounting
    (readout : StableFiniteReadout) :
    ReadoutAccountingAdmits readout :=
  And.intro
    (stable_finite_readout_has_positive_denominator readout)
    (And.intro
      (normalized_readout_length_matches readout)
      (normalized_readout_common_denominator readout))

theorem linear_two_branch_admitted_by_accounting :
    ReadoutAccountingAdmits linearTwoBranchReadout :=
  stable_readout_is_admitted_by_accounting linearTwoBranchReadout

theorem quadratic_two_branch_admitted_by_accounting :
    ReadoutAccountingAdmits quadraticTwoBranchReadout :=
  stable_readout_is_admitted_by_accounting quadraticTwoBranchReadout

theorem linear_two_branch_denominator :
    normalizationDenominator linearTwoBranchReadout = 7 := by
  rfl

theorem quadratic_two_branch_denominator :
    normalizationDenominator quadraticTwoBranchReadout = 25 := by
  rfl

theorem linear_and_quadratic_two_branch_readouts_are_distinct :
    normalizationDenominator linearTwoBranchReadout
      ≠ normalizationDenominator quadraticTwoBranchReadout := by
  decide

theorem readout_accounting_does_not_select_quadratic_actualization :
    ReadoutAccountingAdmits linearTwoBranchReadout
      ∧ ReadoutAccountingAdmits quadraticTwoBranchReadout
      ∧ normalizationDenominator linearTwoBranchReadout
          ≠ normalizationDenominator quadraticTwoBranchReadout :=
  And.intro
    linear_two_branch_admitted_by_accounting
    (And.intro
      quadratic_two_branch_admitted_by_accounting
      linear_and_quadratic_two_branch_readouts_are_distinct)

theorem finite_h11_born_like_context_probability_is_conditional
    (readout : StableFiniteReadout) :
    normalizationDenominator readout > 0
      ∧ (normalizedReadout readout).length = readout.weights.length :=
  And.intro
    (stable_finite_readout_has_positive_denominator readout)
    (normalized_readout_length_matches readout)

theorem calibrated_phase_scale_boundary_remains_non_derivational :
    calibratedOnlyBoundary.calibratedAnchor = true
      ∧ calibratedOnlyBoundary.firstPrinciplesDerivation = false :=
  calibrated_anchor_is_not_first_principles_derivation

end QMClosure
end IDT
