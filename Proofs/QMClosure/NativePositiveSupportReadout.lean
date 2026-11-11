import Proofs.QMClosure.PositiveUnboundedKernelDuplication
import Proofs.QMClosure.PersistentOriginalEventAtoms
import Proofs.QMClosure.OriginalOccurrenceNormSelection

/-!
# Native adapter for positive unrestricted original-a/b kernels

The generic unrestricted-kernel result is proved before importing the existing
native carrier extension. Frozen positive event families are supplied premises
on the original positive a/b bag family. The final extension uses the existing
native phase and normal-form transport. The event characterization supplies no
physical derivation of event identities, scores or principal activation.
-/

noncomputable section

namespace IDT.QMClosure.NativePositiveSupportReadout

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalMaskLocalKernel
open OriginalOccurrenceNormSelection
open PersistentOriginalEventAtoms
open PositiveUnboundedKernelDuplication
  (transform canonical canonical_formula transform_canonical quadraticKernel
    eq_quadraticKernel_of_eventuallyNonnegative support_le_two_of_eventuallyNonnegative
    EventuallyNonnegative)

attribute [local instance] presentationCommRing presentationCharZero

/-- Compatibility uses one unrestricted coefficient function on all count bags. -/
def CompatibleUnrestrictedOriginalKernel (W : Presentation → ℝ) (κ : Kernel) : Prop :=
  ∀ n m : ℕ, W (bagEval n m) = transform κ n m

/-- The Boolean mask coefficients coincide with the unique Newton coefficients. -/
theorem countKernel_eq_canonical (W : Presentation → ℝ) :
    countKernel W = canonical (fun n m => W (bagEval n m)) := by
  funext j k
  simpa only [countKernel, cardinalSum, mul_assoc] using
    (canonical_formula (fun n m => W (bagEval n m)) j k).symm

/-- Any same-W count readout has its canonical signed unrestricted kernel. -/
theorem canonical_compatible (W : Presentation → ℝ) :
    CompatibleUnrestrictedOriginalKernel W (countKernel W) := by
  intro n m
  rw [countKernel_eq_canonical, transform_canonical]

/-- Proved support collapse converts an unrestricted kernel to the finite contract. -/
theorem finite_compatible_of_support {W : Presentation → ℝ} {κ : Kernel}
    (H : CompatibleUnrestrictedOriginalKernel W κ)
    (hsupport : ∀ j k, 2 < j + k → κ j k = 0) :
    CompatibleOriginalKernel W 2 κ := by
  classical
  intro n m
  rw [H n m]
  symm
  calc
    originalSubsetCount 2 κ n m =
        ∑ T : Finset (Occurrence n m), κ T.toLeft.card T.toRight.card := by
      unfold originalSubsetCount
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hcard : T.card ≤ 2
      · simp [hcard]
      · have hdegree : 2 < T.toLeft.card + T.toRight.card := by
          rw [Finset.card_toLeft_add_card_toRight]
          omega
        simp [hcard, hsupport _ _ hdegree]
    _ = cardinalSum n m κ := by
      simpa using sum_powerset_typecounts (Finset.univ : Finset (Occurrence n m)) κ
    _ = transform κ n m := rfl

/-- Native doubling transfers to the generic unrestricted transform. -/
theorem compatible_doubling {W : Presentation → ℝ} (L : NativeTransfer W)
    {κ : Kernel} (H : CompatibleUnrestrictedOriginalKernel W κ) :
    ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m := by
  intro n m
  rw [← H, ← H, bagEval_double, readout_double_mul L]

/-- Native calibrations select exactly the existing pairKernel coefficients. -/
theorem kernel_eq_pairKernel_of_eventuallyNonnegative
    {W : Presentation → ℝ} (L : NativeTransfer W) {κ : Kernel}
    (H : CompatibleUnrestrictedOriginalKernel W κ) (hpos : EventuallyNonnegative κ) :
    κ = pairKernel := by
  change κ = quadraticKernel
  apply eq_quadraticKernel_of_eventuallyNonnegative (compatible_doubling L H) hpos
  · rw [← H 1 0]
    simpa [bagEval] using readout_a L
  · rw [← H 0 1]
    simpa [bagEval] using readout_b L
  · rw [← H 1 1]
    simpa [bagEval, transparent] using L.unit

/-- A global finite order is derived under one total-degree positivity threshold. -/
theorem pairKernel_compatible_of_eventuallyNonnegative
    {W : Presentation → ℝ} (L : NativeTransfer W) {κ : Kernel}
    (H : CompatibleUnrestrictedOriginalKernel W κ) (hpos : EventuallyNonnegative κ) :
    CompatibleOriginalKernel W 2 pairKernel := by
  have hfinite := finite_compatible_of_support H
    (support_le_two_of_eventuallyNonnegative (compatible_doubling L H) hpos)
  rw [kernel_eq_pairKernel_of_eventuallyNonnegative L H hpos] at hfinite
  exact hfinite

/-- Native carrier extension is invoked only after positive-kernel compilation. -/
theorem readout_eq_complex_norm_of_eventuallyNonnegative_kernel
    {W : Presentation → ℝ} (L : NativeTransfer W) {κ : Kernel}
    (H : CompatibleUnrestrictedOriginalKernel W κ) (hpos : EventuallyNonnegative κ)
    (p : Presentation) : W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_original_kernel L
    (pairKernel_compatible_of_eventuallyNonnegative L H hpos) p

theorem pairKernel_compatible_of_nonnegative
    {W : Presentation → ℝ} (L : NativeTransfer W) {κ : Kernel}
    (H : CompatibleUnrestrictedOriginalKernel W κ) (hpos : ∀ j k, 0 ≤ κ j k) :
    CompatibleOriginalKernel W 2 pairKernel :=
  pairKernel_compatible_of_eventuallyNonnegative L H ⟨0, fun j k _ => hpos j k⟩

/-- Same-W principal-support event positivity compiles to the selected pair kernel. -/
theorem pairKernel_compatible_of_allMaskEventFamily
    {W : Presentation → ℝ} (L : NativeTransfer W) (H : AllMaskEventFamily W) :
    CompatibleOriginalKernel W 2 pairKernel :=
  pairKernel_compatible_of_nonnegative L (canonical_compatible W)
    (countKernel_nonnegative_of_allMaskEventFamily H)

/-- The supplied event premise selects the native readout on the full carrier. -/
theorem readout_eq_complex_norm_of_allMaskEventFamily
    {W : Presentation → ℝ} (L : NativeTransfer W) (H : AllMaskEventFamily W)
    (p : Presentation) : W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_original_kernel L
    (pairKernel_compatible_of_allMaskEventFamily L H) p

/-- A native nonnorm readout has negative canonical coefficients above every
finite total-degree threshold. The canonical qualifier prevents choosing a
convenient representation or changing coefficients after looking at a readout. -/
theorem canonical_negative_arbitrarily_high
    {W : Presentation → ℝ} (L : NativeTransfer W)
    (hnot : ¬∀ p, W p = Complex.normSq (complexEval p)) :
    ∀ D : ℕ, ∃ j k : ℕ, D < j + k ∧ countKernel W j k < 0 := by
  intro D
  by_contra hnone
  push_neg at hnone
  apply hnot
  intro p
  exact readout_eq_complex_norm_of_eventuallyNonnegative_kernel L (canonical_compatible W)
    ⟨D, hnone⟩ p

end IDT.QMClosure.NativePositiveSupportReadout
