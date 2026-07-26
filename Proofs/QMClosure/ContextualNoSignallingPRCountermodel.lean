import Mathlib

namespace IDT.QMClosure

/-!
# Contextual no-signalling PR countermodel

Absence of a global outcome assignment is necessary to escape the deterministic
Bell countermodel, but it is not sufficient to select quantum correlations.
This file gives the finite Popescu-Rohrlich countermodel: normalized,
nonnegative and no-signalling local tables with no global section, yet CHSH
equal to four.

No Hilbert space, Born rule, or quantum correlation bound is imported. The
result rejects contextual obstruction plus no-signalling as a sufficient lower
primitive package; it does not reject either property as a necessary ingredient.
-/

def bitXor (left right : Bool) : Bool :=
  if left then !right else right

def prParity (aliceSetting bobSetting : Bool) : Bool :=
  aliceSetting && bobSetting

def outcomeSign (outcome : Bool) : ℚ :=
  if outcome then -1 else 1

structure BinaryNoSignallingBox where
  weight : Bool → Bool → Bool → Bool → ℚ
  weightNonnegative : ∀ x y a b, 0 ≤ weight x y a b
  normalized : ∀ x y,
    weight x y false false + weight x y false true +
      weight x y true false + weight x y true true = 1
  aliceMarginalIndependent : ∀ x a y₀ y₁,
    weight x y₀ a false + weight x y₀ a true =
      weight x y₁ a false + weight x y₁ a true
  bobMarginalIndependent : ∀ y b x₀ x₁,
    weight x₀ y false b + weight x₀ y true b =
      weight x₁ y false b + weight x₁ y true b

def BinaryNoSignallingBox.HasGlobalSection
    (box : BinaryNoSignallingBox) : Prop :=
  ∃ aliceOutcome bobOutcome : Bool → Bool,
    ∀ x y, 0 < box.weight x y (aliceOutcome x) (bobOutcome y)

def BinaryNoSignallingBox.correlation
    (box : BinaryNoSignallingBox)
    (x y : Bool) : ℚ :=
  box.weight x y false false * outcomeSign false * outcomeSign false +
    box.weight x y false true * outcomeSign false * outcomeSign true +
    box.weight x y true false * outcomeSign true * outcomeSign false +
    box.weight x y true true * outcomeSign true * outcomeSign true

def BinaryNoSignallingBox.chsh
    (box : BinaryNoSignallingBox) : ℚ :=
  box.correlation false false +
    box.correlation false true +
    box.correlation true false -
    box.correlation true true

def prBoxWeight
    (x y a b : Bool) : ℚ :=
  if bitXor a b = prParity x y then 1 / 2 else 0

theorem pr_box_weight_is_nonnegative
    (x y a b : Bool) :
    0 ≤ prBoxWeight x y a b := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    norm_num [prBoxWeight, bitXor, prParity]

theorem pr_box_is_normalized
    (x y : Bool) :
    prBoxWeight x y false false + prBoxWeight x y false true +
      prBoxWeight x y true false + prBoxWeight x y true true = 1 := by
  cases x <;> cases y <;>
    norm_num [prBoxWeight, bitXor, prParity]

theorem pr_box_alice_marginal_is_uniform
    (x y a : Bool) :
    prBoxWeight x y a false + prBoxWeight x y a true = 1 / 2 := by
  cases x <;> cases y <;> cases a <;>
    norm_num [prBoxWeight, bitXor, prParity]

theorem pr_box_bob_marginal_is_uniform
    (x y b : Bool) :
    prBoxWeight x y false b + prBoxWeight x y true b = 1 / 2 := by
  cases x <;> cases y <;> cases b <;>
    norm_num [prBoxWeight, bitXor, prParity]

def prBox : BinaryNoSignallingBox where
  weight := prBoxWeight
  weightNonnegative := pr_box_weight_is_nonnegative
  normalized := pr_box_is_normalized
  aliceMarginalIndependent := by
    intro x a y₀ y₁
    rw [pr_box_alice_marginal_is_uniform,
      pr_box_alice_marginal_is_uniform]
  bobMarginalIndependent := by
    intro y b x₀ x₁
    rw [pr_box_bob_marginal_is_uniform,
      pr_box_bob_marginal_is_uniform]

theorem pr_box_positive_weight_iff_parity_constraint
    (x y a b : Bool) :
    0 < prBox.weight x y a b ↔ bitXor a b = prParity x y := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    norm_num [prBox, prBoxWeight, bitXor, prParity]

theorem pr_parity_constraints_have_no_global_section :
    ¬ ∃ aliceOutcome bobOutcome : Bool → Bool,
      ∀ x y,
        bitXor (aliceOutcome x) (bobOutcome y) = prParity x y := by
  native_decide

theorem pr_box_has_no_global_section :
    ¬ prBox.HasGlobalSection := by
  intro globalSection
  apply pr_parity_constraints_have_no_global_section
  rcases globalSection with ⟨aliceOutcome, bobOutcome, supported⟩
  exact ⟨aliceOutcome, bobOutcome, fun x y =>
    (pr_box_positive_weight_iff_parity_constraint
      x y (aliceOutcome x) (bobOutcome y)).mp (supported x y)⟩

theorem pr_box_correlation_profile
    (x y : Bool) :
    prBox.correlation x y = if prParity x y then -1 else 1 := by
  cases x <;> cases y <;>
    norm_num [BinaryNoSignallingBox.correlation, prBox, prBoxWeight,
      bitXor, prParity, outcomeSign]

theorem pr_box_chsh_is_four :
    prBox.chsh = 4 := by
  norm_num [BinaryNoSignallingBox.chsh, pr_box_correlation_profile,
    prParity]

theorem contextual_no_signalling_does_not_force_quantum_chsh_boundary :
    ∃ box : BinaryNoSignallingBox,
      ¬ box.HasGlobalSection ∧ box.chsh = 4 := by
  exact ⟨prBox, pr_box_has_no_global_section, pr_box_chsh_is_four⟩

inductive ContextualNoSignallingFinding where
  | prBoxIsNormalizedAndNonnegative
  | prBoxIsNoSignalling
  | prBoxHasNoGlobalSection
  | prBoxChshIsFour
  | contextualNoSignallingPackageIsInsufficient
  | reversiblePurificationOrEquivalentSelectorRemainsNecessary
  deriving DecidableEq, Repr

def contextualNoSignallingFindings :
    List ContextualNoSignallingFinding :=
  [ .prBoxIsNormalizedAndNonnegative,
    .prBoxIsNoSignalling,
    .prBoxHasNoGlobalSection,
    .prBoxChshIsFour,
    .contextualNoSignallingPackageIsInsufficient,
    .reversiblePurificationOrEquivalentSelectorRemainsNecessary ]

theorem contextual_no_signalling_probe_records_six_findings :
    contextualNoSignallingFindings.length = 6 := by
  rfl

inductive ContextualNoSignallingOpenObligation where
  | deriveQuantumCorrelationBoundaryWithoutHilbertImport
  | deriveUniversalReversiblePurificationFromLowerRewrites
  | deriveLocalEquivalenceFromBoundarySemantics
  | connectContextualSupportToNumericalReadout
  | excludeHigherOrderInterferenceAndNonQuantumCarriers
  deriving DecidableEq, Repr

def contextualNoSignallingOpenObligations :
    List ContextualNoSignallingOpenObligation :=
  [ .deriveQuantumCorrelationBoundaryWithoutHilbertImport,
    .deriveUniversalReversiblePurificationFromLowerRewrites,
    .deriveLocalEquivalenceFromBoundarySemantics,
    .connectContextualSupportToNumericalReadout,
    .excludeHigherOrderInterferenceAndNonQuantumCarriers ]

theorem contextual_no_signalling_probe_keeps_five_open_obligations :
    contextualNoSignallingOpenObligations.length = 5 := by
  rfl

def contextualNoSignallingProbeStatus : String :=
  "contextual_gluing_plus_no_signalling_rejected_as_sufficient_primitive_package"

def contextualNoSignallingProbeClaimBoundary : String :=
  "A finite PR box is normalized, nonnegative, no-signalling and has no global section while reaching CHSH four. Thus contextual obstruction plus no-signalling does not select quantum mechanics; no Standard Model or gravity claim follows."

end IDT.QMClosure
