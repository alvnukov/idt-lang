import Proofs.QMClosure.OriginalMaskCircuitAncestry
import Proofs.QMClosure.OriginalOccurrenceNormSelection
import Proofs.QMClosure.RegularReadoutOccurrenceKernelSeparation

/-!
# Original-mask local readout controls

The compiler and DAG ancestry arguments are finite combinatorics. This module
alone adds the native selector and the regular native countercontrol to obtain
selection and separation statements. The normalized norm witness uses the
existing nonnegative pair kernel on actual original subsets.

Physical shutter realizability, one W on every mask, a uniform complete
dependency bound for each summand, and interpretation of the external additive
report remain supplied. No physical resource budget is used here.
-/

noncomputable section

namespace IDT.QMClosure.OriginalMaskLocalityControls

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalOccurrenceNormSelection
open OriginalMaskLocalKernel
open OriginalMaskCircuitAncestry
open NativeRegularReadoutCountercontrol
open RegularReadoutOccurrenceKernelSeparation

attribute [local instance] presentationCommRing presentationCharZero

/-- Universal selection retains the full native-transfer and all-mask contract. -/
theorem readout_eq_complex_norm_of_allMaskLocalFamily
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ}
    (H : AllMaskLocalFamily W K) (p : Presentation) :
    W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_original_kernel L (compatible_of_allMaskLocalFamily H) p

theorem readout_eq_complex_norm_of_completeCircuitFamily
    {W : Presentation → ℝ} (L : NativeTransfer W) {r D : ℕ}
    (hr : 1 ≤ r) (H : CompleteCircuitFamily W r D) (p : Presentation) :
    W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_original_kernel L (compatible_of_completeCircuitFamily hr H) p

/-- Every local output of the K=2 witness is nonnegative, on every local mask. -/
theorem pairApparatus_localValue_nonnegative (n m : ℕ)
    (T : {T : Finset (Occurrence n m) // T.card ≤ 2}) (M : Finset (Occurrence n m)) :
    0 ≤ (kernelApparatus 2 pairKernel n m).localValue T M := by
  change 0 ≤ if T.val ⊆ M then pairKernel T.val.toLeft.card T.val.toRight.card else 0
  split_ifs
  · exact pairKernel_nonnegative _ _
  · exact le_rfl

theorem pairApparatus_allMaskAgreement (n m : ℕ) :
    AllMaskAgreement normReadout (kernelApparatus 2 pairKernel n m) :=
  kernelApparatus_allMaskAgreement pairKernel_compatible_normReadout n m

/-- Singletons contribute 1/2 and selected same-type unordered pairs contribute 1.
Mixed pairs contribute zero. This identity covers every original mask. -/
theorem pairApparatus_value (n m : ℕ) (S : Finset (Occurrence n m)) :
    (kernelApparatus 2 pairKernel n m).value S =
      ((S.toLeft.card : ℝ) ^ 2 + (S.toRight.card : ℝ) ^ 2) / 2 := by
  rw [← pairApparatus_allMaskAgreement n m S]
  exact normReadout_bag _ _

theorem normReadout_allMaskLocalFamily : AllMaskLocalFamily normReadout 2 := by
  intro n m
  exact ⟨kernelApparatus 2 pairKernel n m, pairApparatus_allMaskAgreement n m⟩

/-- One constant empty-support output calibrates any full universe for any W. -/
def fullMaskConstantApparatus (W : Presentation → ℝ) (n m : ℕ) :
    LocalApparatus (Occurrence n m) 0 where
  Output := Unit
  finiteOutput := inferInstance
  support _ := ∅
  support_le _ := by simp
  localValue _ _ := W (bagEval n m)

theorem fullMaskConstantApparatus_value (W : Presentation → ℝ) (n m : ℕ)
    (S : Finset (Occurrence n m)) :
    (fullMaskConstantApparatus W n m).value S = W (bagEval n m) := by
  simp [LocalApparatus.value, fullMaskConstantApparatus]

/-- Full-mask agreement by itself permits arbitrary readouts at order zero. -/
theorem any_readout_has_fullMask_order_zero (W : Presentation → ℝ) (n m : ℕ) :
    ∃ A : LocalApparatus (Occurrence n m) 0,
      W (bagEval n m) = A.value Finset.univ := by
  exact ⟨fullMaskConstantApparatus W n m,
    (fullMaskConstantApparatus_value W n m Finset.univ).symm⟩

/-- The full-mask constant construction already fails the singleton empty-mask
test for every native readout, whose zero and singleton values differ. -/
theorem fullMaskConstantApparatus_fails_allMaskAgreement
    {W : Presentation → ℝ} (L : NativeTransfer W) :
    ¬ AllMaskAgreement W (fullMaskConstantApparatus W 1 0) := by
  intro H
  have h := H ∅
  rw [fullMaskConstantApparatus_value] at h
  have hz : maskEval (∅ : Finset (Occurrence 1 0)) = 0 := by simp [maskEval, bagEval]
  have ha : bagEval 1 0 = a := by simp [bagEval]
  rw [hz, ha, readout_zero L, readout_a L] at h
  norm_num at h

/-- A positive regular nonnorm readout lacks every uniform finite local order. -/
theorem counterWeight_no_allMaskLocalFamily (c : ℝ) (hc : 0 < c) :
    ¬ ∃ K : ℕ, AllMaskLocalFamily (counterWeight c) K := by
  rintro ⟨K, H⟩
  apply counterWeight_no_finite_original_kernel c hc
  exact ⟨K, countKernel (counterWeight c), compatible_of_allMaskLocalFamily H⟩

/-- Uniform complete per-summand fanin/depth cannot realize that countercontrol.
The external additive collector remains unrestricted in output count. -/
theorem counterWeight_no_completeCircuitFamily (c : ℝ) (hc : 0 < c) :
    ¬ ∃ r D : ℕ, 1 ≤ r ∧ CompleteCircuitFamily (counterWeight c) r D := by
  rintro ⟨r, D, hr, H⟩
  apply counterWeight_no_allMaskLocalFamily c hc
  exact ⟨r ^ D, allMaskLocalFamily_of_completeCircuitFamily hr H⟩

end IDT.QMClosure.OriginalMaskLocalityControls
