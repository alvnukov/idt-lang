import Mathlib
import Proofs.QMClosure.ExclusivityAdditivityProof

namespace IDT.QMClosure

/-!
# Coarse Graining Consistency Proof
-/

variable {H : Type} [Fintype H] [DecidableEq H]
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)

theorem coarse_graining_consistency
    (Γ_hermitian : ∀ h h', star (Γ h h') = Γ h' h)
    (A B C : Finset H)
    (h_AB_disjoint : Disjoint A B)
    (h_AC_disjoint : Disjoint A C)
    (h_BC_disjoint : Disjoint B C)
    (h_AB_facticity : crossActualization W Γ A B = 0)
    (h_AC_facticity : crossActualization W Γ A C = 0)
    (h_BC_facticity : crossActualization W Γ B C = 0) :
    actualizationMeasure W Γ (A ∪ B ∪ C) =
      actualizationMeasure W Γ A + actualizationMeasure W Γ B +
      actualizationMeasure W Γ C := by
  have h_union_disjoint : Disjoint A (B ∪ C) :=
    Finset.disjoint_union_right.mpr ⟨h_AB_disjoint, h_AC_disjoint⟩
  have h_union_facticity : crossActualization W Γ A (B ∪ C) = 0 := by
    unfold crossActualization
    have key : ∀ h : H,
        ∑ h' ∈ B ∪ C, W h * star (W h') * Γ h h' =
        ∑ h' ∈ B, W h * star (W h') * Γ h h' + ∑ h' ∈ C, W h * star (W h') * Γ h h' := by
      intro h
      rw [Finset.sum_union h_BC_disjoint]
    simp only [key, Finset.sum_add_distrib]
    -- Goal: (∑ h ∈ A, ∑ h' ∈ B, ...) + (∑ h ∈ A, ∑ h' ∈ C, ...) = 0
    -- = crossActualization(A, B) + crossActualization(A, C) = 0 + 0 = 0
    unfold crossActualization at h_AB_facticity h_AC_facticity
    exact by rw [h_AB_facticity, h_AC_facticity]; simp
  rw [show A ∪ B ∪ C = A ∪ (B ∪ C) from Finset.union_assoc A B C,
      exclusivity_additivity W Γ Γ_hermitian A (B ∪ C) h_union_disjoint h_union_facticity,
      exclusivity_additivity W Γ Γ_hermitian B C h_BC_disjoint h_BC_facticity]
  abel

end IDT.QMClosure
