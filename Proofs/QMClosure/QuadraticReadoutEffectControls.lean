import Proofs.QMClosure.MixerRecordNaturality
import Mathlib.Analysis.InnerProductSpace.Basic

namespace IDT.QMClosure.QuadraticReadoutEffectControls

open QuadraticRecordRefinement

noncomputable section

/-!
Fixed controls on the supplied coordinate space ℂ. These are mathematical
countermodels, not a reconstruction of complex physical preparation scalars.
They separate common-phase compatibility, branch resolution, and projectivity.
An effect contract supplies neither a state-update map nor repeatability.
No physical availability or scientific status is asserted here.
-/

def qRe (z : ℂ) : ℝ := z.re ^ 2
def qIm (z : ℂ) : ℝ := z.im ^ 2

theorem qRe_positiveQuadratic : PositiveQuadratic qRe := by
  constructor
  · intro z; exact sq_nonneg z.re
  · intro z w; simp [qRe]; ring

theorem qIm_positiveQuadratic : PositiveQuadratic qIm := by
  constructor
  · intro z; exact sq_nonneg z.im
  · intro z w; simp [qIm]; ring

theorem qRe_le_normSq (z : ℂ) : qRe z ≤ Complex.normSq z := by
  dsimp [qRe]
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.im]

theorem qIm_le_normSq (z : ℂ) : qIm z ≤ Complex.normSq z := by
  dsimp [qIm]
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re]

def coordinateBranch (b : Bool) : ℂ → ℝ := if b then qIm else qRe

theorem coordinateBranch_positiveQuadratic (b : Bool) :
    PositiveQuadratic (coordinateBranch b) := by
  cases b
  · exact qRe_positiveQuadratic
  · exact qIm_positiveQuadratic

theorem coordinateBranch_bounds (b : Bool) (z : ℂ) :
    0 ≤ coordinateBranch b z ∧ coordinateBranch b z ≤ Complex.normSq z := by
  constructor
  · exact (coordinateBranch_positiveQuadratic b).nonnegative z
  · cases b
    · exact qRe_le_normSq z
    · exact qIm_le_normSq z

theorem coordinateBranch_resolution (z : ℂ) :
    (∑ b : Bool, coordinateBranch b z) = Complex.normSq z := by
  simp [coordinateBranch, qRe, qIm, Complex.normSq_apply]
  ring

theorem qRe_not_phase_invariant :
    ¬ (∀ z : ℂ, qRe (Complex.I * z) = qRe z) := by
  intro h
  have h1 := h 1
  norm_num [qRe] at h1

/-- Every complex-linear expectation has the common phase invariance missing
from the real-coordinate branch, even without assuming self-adjointness. -/
theorem linear_expectation_phase_invariant (E : ℂ →ₗ[ℂ] ℂ) (z : ℂ) :
    (inner ℂ (Complex.I * z) (E (Complex.I * z))).re =
      (inner ℂ z (E z)).re := by
  have he : E (Complex.I * z) = Complex.I * E z := by
    simpa only [smul_eq_mul] using E.map_smul Complex.I z
  simp [RCLike.inner_apply, he, Complex.mul_re, Complex.mul_im]

theorem qRe_has_no_complex_linear_effect :
    ¬ ∃ E : ℂ →ₗ[ℂ] ℂ, ∀ z : ℂ, (inner ℂ z (E z)).re = qRe z := by
  rintro ⟨E, h⟩
  apply qRe_not_phase_invariant
  intro z
  rw [← h (Complex.I * z), ← h z]
  exact linear_expectation_phase_invariant E z

theorem norm_positiveQuadratic : PositiveQuadratic (Complex.normSq : ℂ → ℝ) :=
  MixerRecordNaturality.Controls.complex_norm_positive_quadratic

theorem norm_phase_invariant (z : ℂ) :
    Complex.normSq (Complex.I * z) = Complex.normSq z := by
  simp [Complex.normSq_mul]

def duplicatedBranch (_b : Bool) : ℂ → ℝ := Complex.normSq

theorem duplicatedBranch_individual_contract (b : Bool) :
    PositiveQuadratic (duplicatedBranch b) ∧
      (∀ z, duplicatedBranch b (Complex.I * z) = duplicatedBranch b z) ∧
      (∀ z, 0 ≤ duplicatedBranch b z ∧ duplicatedBranch b z ≤ Complex.normSq z) :=
  ⟨norm_positiveQuadratic, norm_phase_invariant,
    fun z => ⟨Complex.normSq_nonneg z, le_rfl⟩⟩

theorem duplicatedBranch_resolution_fails :
    (∑ b : Bool, duplicatedBranch b 1) ≠ Complex.normSq 1 := by
  norm_num [duplicatedBranch]

def identityEffect : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ

theorem identityEffect_expectation (z : ℂ) :
    (inner ℂ z (identityEffect z)).re = Complex.normSq z := by
  change (z * star z).re = Complex.normSq z
  rw [Complex.mul_re]
  simp [Complex.normSq_apply]

theorem identityEffect_selfadjoint_identity (z w : ℂ) :
    inner ℂ (identityEffect z) w = inner ℂ z (identityEffect w) := by
  rfl

theorem identityEffect_bounds (z : ℂ) :
    0 ≤ (inner ℂ z (identityEffect z)).re ∧
      (inner ℂ z (identityEffect z)).re ≤ Complex.normSq z := by
  rw [identityEffect_expectation]
  exact ⟨Complex.normSq_nonneg z, le_rfl⟩

theorem duplicated_effects_sum_ne_identity :
    identityEffect + identityEffect ≠ ContinuousLinearMap.id ℂ ℂ := by
  intro h
  have h1 := congrArg (fun E : ℂ →L[ℂ] ℂ => (E 1).re) h
  norm_num [identityEffect] at h1

theorem duplicated_effects_finite_sum :
    (∑ _b : Bool, identityEffect) = (2 : ℂ) • identityEffect := by
  ext
  simp [identityEffect, smul_eq_mul]

theorem duplicated_effects_finite_resolution_fails :
    (∑ _b : Bool, identityEffect) ≠ ContinuousLinearMap.id ℂ ℂ := by
  intro h
  have h1 := congrArg (fun E : ℂ →L[ℂ] ℂ => (E 1).re) h
  norm_num [identityEffect] at h1

def halfBranch (_b : Bool) (z : ℂ) : ℝ := Complex.normSq z / 2

theorem halfBranch_positiveQuadratic (b : Bool) : PositiveQuadratic (halfBranch b) := by
  constructor
  · intro z; exact div_nonneg (Complex.normSq_nonneg z) (by norm_num)
  · intro z w
    have h := norm_positiveQuadratic.parallelogram z w
    dsimp [halfBranch]
    linarith

theorem halfBranch_phase_invariant (b : Bool) (z : ℂ) :
    halfBranch b (Complex.I * z) = halfBranch b z := by
  simp only [halfBranch, norm_phase_invariant]

theorem halfBranch_bounds (b : Bool) (z : ℂ) :
    0 ≤ halfBranch b z ∧ halfBranch b z ≤ Complex.normSq z := by
  have hn := Complex.normSq_nonneg z
  dsimp [halfBranch]
  constructor <;> linarith

theorem halfBranch_resolution (z : ℂ) :
    (∑ b : Bool, halfBranch b z) = Complex.normSq z := by
  simp [halfBranch]
  ring

def halfEffect : ℂ →L[ℂ] ℂ := (1 / 2 : ℂ) • identityEffect

theorem halfEffect_apply (z : ℂ) : halfEffect z = (1 / 2 : ℂ) * z := by
  simp [halfEffect, identityEffect, smul_eq_mul]

theorem halfEffect_expectation (b : Bool) (z : ℂ) :
    (inner ℂ z (halfEffect z)).re = halfBranch b z := by
  rw [halfEffect_apply]
  simp [RCLike.inner_apply, halfBranch, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The self-adjoint inner-product identity for the actual continuous operator. -/
theorem halfEffect_selfadjoint_identity (z w : ℂ) :
    inner ℂ (halfEffect z) w = inner ℂ z (halfEffect w) := by
  apply Complex.ext <;>
    norm_num [halfEffect_apply, RCLike.inner_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem halfEffect_bounds (z : ℂ) :
    0 ≤ (inner ℂ z (halfEffect z)).re ∧
      (inner ℂ z (halfEffect z)).re ≤ Complex.normSq z := by
  rw [halfEffect_expectation false]
  exact halfBranch_bounds false z

theorem halfEffects_sum_identity :
    (∑ _b : Bool, halfEffect) = ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp [halfEffect_apply]

/-- A resolved positive contraction need not be an idempotent projector.
This alone says nothing about any independently chosen state-update rule. -/
theorem halfEffect_not_idempotent : halfEffect.comp halfEffect ≠ halfEffect := by
  intro h
  have h1 := congrArg (fun E : ℂ →L[ℂ] ℂ => (E 1).re) h
  norm_num [ContinuousLinearMap.comp_apply, halfEffect_apply] at h1

/-- All premises belong to the same fixed resolved family and concrete
operators; projectivity is still false for either branch operator. -/
theorem resolved_nonprojective_control :
    (∀ b : Bool, PositiveQuadratic (halfBranch b)) ∧
    (∀ (b : Bool) z, halfBranch b (Complex.I * z) = halfBranch b z) ∧
    (∀ (b : Bool) z, 0 ≤ halfBranch b z ∧ halfBranch b z ≤ Complex.normSq z) ∧
    (∀ z, (∑ b : Bool, halfBranch b z) = Complex.normSq z) ∧
    (∀ (b : Bool) z, (inner ℂ z (halfEffect z)).re = halfBranch b z) ∧
    (∀ z w, inner ℂ (halfEffect z) w = inner ℂ z (halfEffect w)) ∧
    ((∑ _b : Bool, halfEffect) = ContinuousLinearMap.id ℂ ℂ) ∧
    halfEffect.comp halfEffect ≠ halfEffect :=
  ⟨halfBranch_positiveQuadratic, halfBranch_phase_invariant, halfBranch_bounds,
    halfBranch_resolution, halfEffect_expectation, halfEffect_selfadjoint_identity,
    halfEffects_sum_identity, halfEffect_not_idempotent⟩

end

end IDT.QMClosure.QuadraticReadoutEffectControls
