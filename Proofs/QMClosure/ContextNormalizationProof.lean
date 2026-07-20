import Mathlib

namespace IDT.QMClosure

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Facticization stability (real): for all v, v^T Γ v ≥ 0 -/
def FacticizationStabilityReal (Γ : H → H → ℝ) : Prop :=
  ∀ (v : H → ℝ), ∑ h, ∑ h', v h * v h' * Γ h h' ≥ 0

/-- Actualization measure (real) -/
noncomputable def measureReal (W : H → ℝ) (Γ : H → H → ℝ) (A : Finset H) : ℝ :=
  ∑ h ∈ A, ∑ h' ∈ A, W h * W h' * Γ h h'

/-- THEOREM: F → μ(A) ≥ 0

For any event A, the actualization measure is nonneg.
Proof: v = W restricted to A (0 outside). F(v) = μ(A) ≥ 0.

This is the core of the `context_normalization` closure obligation.
Forbidden imports: born_rule, probability_axiom, hilbert_space -/
theorem measure_nonneg
    (W : H → ℝ) (Γ : H → H → ℝ)
    (hF : FacticizationStabilityReal Γ)
    (A : Finset H) :
    measureReal W Γ A ≥ 0 := by
  have hv := hF (fun h => if h ∈ A then W h else 0)
  have key : ∑ h, ∑ h',
      (if h ∈ A then W h else 0) * (if h' ∈ A then W h' else 0) * Γ h h' =
    measureReal W Γ A := by
    simp only [measureReal]
    have outer : ∑ h, (∑ h', (if h ∈ A then W h else 0) * (if h' ∈ A then W h' else 0) * Γ h h') =
                 ∑ h ∈ A, (∑ h', (if h ∈ A then W h else 0) * (if h' ∈ A then W h' else 0) * Γ h h') :=
      (Finset.sum_subset (Finset.subset_univ A)
        (fun h _ hA => by rw [if_neg hA]; simp)).symm
    rw [outer]
    simp
  linarith [hv, key]

end IDT.QMClosure
