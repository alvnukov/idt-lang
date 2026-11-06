import Proofs.QMClosure.CompositeProductControls
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace IDT.QMClosure.CoherentPortRayBoundary

noncomputable section

open CompositeProductControls.RawSign

/-!
Mathematical controls on supplied complex spaces. A coherent pair has one
global scalar freedom: quotienting its two entries independently forgets the
relative phase needed by the supplied mixer. Only nonzero vectors represent
rays. No projective-space API or physical ray identification is assumed here.

These controls do not reconstruct complex coordinates from raw operational
data. A native coherent port and reference, including their physical
availability, remain a separate primitive question. A named frame, an
independent ancilla, or an algebraic complex structure does not establish that
coherent lift. The predicate action in ProjectiveActionProof.ProjectiveFact
is not a bridge to rays. No result here establishes actualization, separation
by available effects, completed effect availability, or full QM.
-/

/-- Phase equivalence for the supplied scalar control. -/
def PhaseEq (x y : ℂ) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ y = c * x

theorem phaseEq_one_I : PhaseEq 1 Complex.I := by
  exact ⟨Complex.I, by simp, by simp⟩

theorem phaseEq_one_one : PhaseEq 1 1 := by
  exact ⟨1, by simp, by simp⟩

theorem chosen_weight_one : Complex.normSq (n 1 1) = 1 := by
  simp [n_diagonal]

theorem chosen_weight_I : Complex.normSq (n Complex.I 1) = 0 := by
  have hn : n Complex.I 1 = 0 := by
    apply Complex.ext <;> norm_num [n_re, n_im]
  simp [hn]

/-- The chosen output weight cannot descend to independent phase classes. -/
theorem independent_phase_compatibility_fails :
    ¬ ∀ x x' y y' : ℂ, PhaseEq x x' → PhaseEq y y' →
      Complex.normSq (n x y) = Complex.normSq (n x' y') := by
  intro h
  have hw := h 1 Complex.I 1 1 phaseEq_one_I phaseEq_one_one
  rw [chosen_weight_one, chosen_weight_I] at hw
  norm_num at hw

/-- A numerical port ratio; at zero the division convention has no ray meaning. -/
def normalizedPortWeight (x y : ℂ) : ℝ :=
  Complex.normSq (n x y) / (Complex.normSq x + Complex.normSq y)

theorem normalized_port_one : normalizedPortWeight 1 1 = 1 / 2 := by
  norm_num [normalizedPortWeight, chosen_weight_one]

theorem normalized_port_I : normalizedPortWeight Complex.I 1 = 0 := by
  simp [normalizedPortWeight, chosen_weight_I]

theorem normalized_independent_phase_compatibility_fails :
    ¬ ∀ x x' y y' : ℂ, PhaseEq x x' → PhaseEq y y' →
      normalizedPortWeight x y = normalizedPortWeight x' y' := by
  intro h
  have hw := h 1 Complex.I 1 1 phaseEq_one_I phaseEq_one_one
  rw [normalized_port_one, normalized_port_I] at hw
  norm_num at hw

theorem n_scalar (c x y : ℂ) : n (c * x) (c * y) = c * n x y := by
  dsimp [n]
  ring

/-- Both coherent ports transform by the same complex scalar. -/
theorem N_scalar (c : ℂ) (p : ℂ × ℂ) : N (c • p) = c • N p := by
  apply Prod.ext <;>
    simpa only [N, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using
      n_scalar c _ _

/-- Numerical descent under a common nonzero rescaling of the whole pair. -/
theorem normalizedPortWeight_scalar (c x y : ℂ) (hc : c ≠ 0) :
    normalizedPortWeight (c * x) (c * y) = normalizedPortWeight x y := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  simp only [normalizedPortWeight, n_scalar, Complex.normSq_mul]
  rw [← mul_add]
  exact mul_div_mul_left _ _ hn

/-- The square law ensures that the coherent mixer never kills a nonzero pair. -/
theorem N_nonzero {p : ℂ × ℂ} (hp : p ≠ 0) : N p ≠ 0 := by
  intro hz
  have hs : p.swap = 0 := by
    rw [← N_square, hz]
    simp [N, n]
  exact hp (by simpa using congrArg Prod.swap hs)

section SuppliedOutput

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A mathematical normalized expectation on an explicitly supplied space.
Positivity and completeness are not needed for the invariance theorem. -/
def normalizedExpectation (E : H →L[ℂ] H) (ψ : H) : ℝ :=
  (inner ℂ ψ (E ψ)).re / ‖ψ‖ ^ 2

theorem expectation_numerator_scalar (E : H →L[ℂ] H) (c : ℂ) (ψ : H) :
    (inner ℂ (c • ψ) (E (c • ψ))).re =
      Complex.normSq c * (inner ℂ ψ (E ψ)).re := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Numerical ray descent for a supplied operator, with no positivity premise.
The identity also holds at the zero vector by Lean's division convention;
that vector is not interpreted as a ray. -/
theorem normalizedExpectation_scalar (E : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0)
    (ψ : H) : normalizedExpectation E (c • ψ) = normalizedExpectation E ψ := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  simp only [normalizedExpectation, expectation_numerator_scalar, norm_smul, mul_pow,
    ← Complex.normSq_eq_norm_sq]
  exact mul_div_mul_left _ _ hn

/-- Restricting the preceding numerical identity to genuine ray representatives. -/
theorem nonzero_rescaling (E : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0)
    (ψ : H) (hψ : ψ ≠ 0) :
    c • ψ ≠ 0 ∧ normalizedExpectation E (c • ψ) = normalizedExpectation E ψ := by
  exact ⟨smul_ne_zero hc hψ, normalizedExpectation_scalar E c hc ψ⟩

section BilinearComparison

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

/-- Algebraic comparison only: a supplied bilinear product is scalar covariant.
This is neither a tensor reconstruction nor a coherent direct-sum lift. -/
theorem bilinear_left_scalar (p : A →ₗ[ℂ] B →ₗ[ℂ] H) (c : ℂ) (x : A) (y : B) :
    p (c • x) y = c • p x y := by
  simp

theorem bilinear_normalizedExpectation_scalar (p : A →ₗ[ℂ] B →ₗ[ℂ] H)
    (E : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0) (x : A) (y : B) :
    normalizedExpectation E (p (c • x) y) = normalizedExpectation E (p x y) := by
  rw [bilinear_left_scalar]
  exact normalizedExpectation_scalar E c hc (p x y)

end BilinearComparison
end SuppliedOutput

end

end IDT.QMClosure.CoherentPortRayBoundary
