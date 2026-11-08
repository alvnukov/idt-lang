import Proofs.QMClosure.BoundedLikelihoodProcessRigidity
import Proofs.QMClosure.InternalReferenceProcessControls

/-!
# Reused omission controls for bounded likelihood rigidity

Both previously checked finite controls contain a Dirac preparation bounded by
four times their uniform reference and distinct from it. The retained process
laws and the omitted assumptions are those of the existing control modules.
-/

namespace IDT.QMClosure.BoundedLikelihoodProcessControls

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open BoundedDominationProcess
open scoped ENNReal

/-- A full unit of mass at the selected atom dominates its Dirac law. -/
private theorem dirac_le_of_singleton {A : Type*} [MeasurableSpace A]
    (Q : Measure A) (a : A) (h : 1 ≤ Q {a}) : Measure.dirac a ≤ Q := by
  apply Measure.le_iff.2
  intro s hs
  by_cases ha : a ∈ s
  · have hsub : Q {a} ≤ Q s := measure_mono (Set.singleton_subset_iff.mpr ha)
    simpa only [Measure.dirac_apply' a hs, Set.indicator_of_mem ha, Pi.one_apply] using
      h.trans hsub
  · simp only [Measure.dirac_apply' a hs, Set.indicator_of_notMem ha]
    exact zero_le _

namespace WithoutFixedDiagonal

open InternalReferenceProcessControls.WithoutFixedDiagonal

theorem dirac_preparation : preparation (false, false) = Measure.dirac (false, false) := by
  simp only [preparation, bitLaw, Bool.false_eq_true, if_false, Measure.dirac_prod_dirac]

theorem preparation_le_four_reference :
    preparation (false, false) ≤ (4 : ℝ≥0∞) • reference := by
  rw [dirac_preparation]
  apply dirac_le_of_singleton
  rw [Measure.smul_apply, reference_singleton, smul_eq_mul, one_div]
  rw [ENNReal.mul_inv_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]

theorem preparation_boundedDom_reference : boundedDom (preparation (false, false)) reference :=
  ⟨4, by norm_num, by norm_num, preparation_le_four_reference⟩

theorem preparation_ne_reference : preparation (false, false) ≠ reference := by
  intro h
  apply reference_not_absolutelyContinuous
  simpa only [h] using (Measure.AbsolutelyContinuous.rfl : reference ≪ reference)

/-- The existing model has the finite bound and distinct laws while its
previously checked raw diagonal is not fixed. -/
theorem omission_control :
    preparation (false, false) ≤ (4 : ℝ≥0∞) • reference ∧
      preparation (false, false) ≠ reference ∧
      operation ((false, true), (false, true)) ≠ ((false, true), (false, true)) :=
  ⟨preparation_le_four_reference, preparation_ne_reference, diagonal_not_fixed⟩

end WithoutFixedDiagonal

namespace WithoutCommonChannel

open InternalReferenceProcessControls.WithoutCommonChannel

theorem preparation_le_four_reference : preparation 1 ≤ (4 : ℝ≥0∞) • reference := by
  change Measure.dirac (0 : Sample) ≤ (4 : ℝ≥0∞) • reference
  apply dirac_le_of_singleton
  rw [Measure.smul_apply, reference_singleton, smul_eq_mul, one_div]
  rw [ENNReal.mul_inv_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]

theorem preparation_boundedDom_reference : boundedDom (preparation 1) reference :=
  ⟨4, by norm_num, by norm_num, preparation_le_four_reference⟩

theorem preparation_ne_reference : preparation 1 ≠ reference := by
  intro h
  apply reference_not_absolutelyContinuous
  simpa only [h] using (Measure.AbsolutelyContinuous.rfl : reference ≪ reference)

/-- The existing model has the finite bound and distinct laws, and no single
kernel can supply all of its displayed covariances. -/
theorem omission_control :
    preparation 1 ≤ (4 : ℝ≥0∞) • reference ∧ preparation 1 ≠ reference ∧
      ¬ ∃ κ : Kernel (Sample × Sample) (Sample × Sample),
        ∀ p, κ ∘ₘ ((preparation p.1).prod (preparation p.2)) =
          (preparation (operation p).1).prod (preparation (operation p).2) :=
  ⟨preparation_le_four_reference, preparation_ne_reference, no_common_channel⟩

end WithoutCommonChannel
end
end IDT.QMClosure.BoundedLikelihoodProcessControls
