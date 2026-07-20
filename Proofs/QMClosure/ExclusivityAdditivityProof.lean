import Mathlib

namespace IDT.QMClosure

/-!
# Exclusivity Additivity Proof

Machine-checked proof for the `exclusivity_additivity` closure obligation.

**Obligation:** Prove additivity over facticized exclusive alternatives.
**Forbidden imports:** born_rule, kolmogorov_axioms_assumed, hilbert_space

Establishes: for disjoint A, B with vanishing cross-actualization (facticity),
the actualization measure is additive: μ(A ∪ B) = μ(A) + μ(B).

Uses only: bilinearity of finite sums, Γ Hermitian, facticity condition.
Does NOT use: Born rule, Kolmogorov axioms, Hilbert space, Γ ≥ 0.
-/

variable {H : Type} [Fintype H] [DecidableEq H]
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)

/-- Actualization measure μ(A) -/
noncomputable def actualizationMeasure (A : Finset H) : ℂ :=
  ∑ h ∈ A, ∑ h' ∈ A, W h * star (W h') * Γ h h'

/-- Cross-actualization A(A,B) -/
noncomputable def crossActualization (A B : Finset H) : ℂ :=
  ∑ h ∈ A, ∑ h' ∈ B, W h * star (W h') * Γ h h'

/-- Cross-actualization conjugate symmetry: A(B,A) = star(A(A,B)) -/
theorem cross_actualization_star_symm
    (Γ_hermitian : ∀ h h', star (Γ h h') = Γ h' h)
    (A B : Finset H) :
    crossActualization W Γ B A = star (crossActualization W Γ A B) := by
  unfold crossActualization
  symm
  calc star (∑ x ∈ A, ∑ y ∈ B, W x * star (W y) * Γ x y)
      = ∑ x ∈ A, ∑ y ∈ B, star (W x * star (W y) * Γ x y) := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro _ _
        rw [star_sum]
    _ = ∑ y ∈ B, ∑ x ∈ A, star (W x * star (W y) * Γ x y) := by
        rw [Finset.sum_comm]
    _ = ∑ y ∈ B, ∑ x ∈ A, W y * star (W x) * Γ y x := by
        apply Finset.sum_congr rfl
        intro _ _
        apply Finset.sum_congr rfl
        intro _ _
        simp only [star_mul, star_star]
        rw [Γ_hermitian]
        ring
    _ = ∑ h ∈ B, ∑ h' ∈ A, W h * star (W h') * Γ h h' := rfl

/-- Measure of disjoint union splits into four parts -/
theorem measure_disjoint_union_split
    (A B : Finset H) (h_disjoint : Disjoint A B) :
    actualizationMeasure W Γ (A ∪ B) =
      actualizationMeasure W Γ A + actualizationMeasure W Γ B +
      crossActualization W Γ A B + crossActualization W Γ B A := by
  have split : ∀ (f : H → ℂ), ∑ x ∈ A ∪ B, f x = ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
    intro f
    exact Finset.sum_union h_disjoint
  unfold actualizationMeasure crossActualization
  simp only [split]
  simp only [Finset.sum_add_distrib]
  abel

/-- Main theorem: additivity for facticized exclusive alternatives.

For disjoint events A, B with vanishing cross-actualization (facticity),
the actualization measure is additive: μ(A ∪ B) = μ(A) + μ(B).

This is the `exclusivity_additivity` closure obligation.
Forbidden imports: born_rule, kolmogorov_axioms_assumed, hilbert_space -/
theorem exclusivity_additivity
    (Γ_hermitian : ∀ h h', star (Γ h h') = Γ h' h)
    (A B : Finset H)
    (h_disjoint : Disjoint A B)
    (h_facticized : crossActualization W Γ A B = 0) :
    actualizationMeasure W Γ (A ∪ B) =
      actualizationMeasure W Γ A + actualizationMeasure W Γ B := by
  rw [measure_disjoint_union_split W Γ A B h_disjoint,
      h_facticized,
      cross_actualization_star_symm W Γ Γ_hermitian A B,
      h_facticized]
  simp

end IDT.QMClosure
