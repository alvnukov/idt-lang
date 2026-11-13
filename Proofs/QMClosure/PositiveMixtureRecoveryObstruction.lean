import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Positive mixture recovery obstruction

Strictly positive two-state mixtures cannot be separated back into two states
by a cone-positive linear map when a nonnegative readout distinguishes those
states by zero and one. The argument needs no topology or spanning premise.
The companion projector identities concern algebraic invertibility only.
-/

namespace IDT.QMClosure.PositiveMixtureRecoveryObstruction

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Positivity with respect to a supplied cone carrier. -/
def PositiveOn (K : Set V) (R : V →ₗ[ℝ] V) : Prop := ∀ x ∈ K, R x ∈ K

/-- The obstruction already holds for recovery of just the two chosen states. -/
theorem no_positive_two_state_recovery
    (K : Set V) (x y : V) (hx : x ∈ K) (hy : y ∈ K)
    (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ z ∈ K, 0 ≤ ℓ z)
    (hℓx : ℓ x = 0) (hℓy : ℓ y = 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (T : V → V) (hTx : T x = a • x + b • y) (hTy : T y = b • x + a • y) :
    ¬ ∃ R : V →ₗ[ℝ] V, PositiveOn K R ∧ R (T x) = x ∧ R (T y) = y := by
  rintro ⟨R, hR, hRx, hRy⟩
  have hpx : 0 ≤ ℓ (R x) := hℓ _ (hR x hx)
  have hpy : 0 ≤ ℓ (R y) := hℓ _ (hR y hy)
  have hzero : a * ℓ (R x) + b * ℓ (R y) = 0 := by
    have h := congrArg ℓ hRx
    simpa [hTx, map_add, map_smul, smul_eq_mul, hℓx] using h
  have hone : b * ℓ (R x) + a * ℓ (R y) = 1 := by
    have h := congrArg ℓ hRy
    simpa [hTy, map_add, map_smul, smul_eq_mul, hℓy] using h
  have hax : a * ℓ (R x) = 0 := by
    apply le_antisymm
    · linarith [mul_nonneg hb.le hpy]
    · exact mul_nonneg ha.le hpx
  have hby : b * ℓ (R y) = 0 := by
    apply le_antisymm
    · linarith [mul_nonneg ha.le hpx]
    · exact mul_nonneg hb.le hpy
  have hrx : ℓ (R x) = 0 := (mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)
  have hry : ℓ (R y) = 0 := (mul_eq_zero.mp hby).resolve_left (ne_of_gt hb)
  rw [hrx, hry] at hone
  norm_num at hone

/-- A sharp lower bound for the two selected readout errors. The scalar
argument only needs nonnegativity of the first recovered readout. -/
theorem scalar_two_mixture_error_bound (η p s ε : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hp : 0 ≤ p)
    (hA : ((1 + η) / 2) * p + ((1 - η) / 2) * s ≤ ε)
    (hB : 1 - (((1 - η) / 2) * p + ((1 + η) / 2) * s) ≤ ε) :
    (1 - η) / 2 ≤ ε := by
  let a := (1 + η) / 2
  let b := (1 - η) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hcone : b * (b * p + a * s) ≤ a * (a * p + b * s) := by
    have hid : a * (a * p + b * s) - b * (b * p + a * s) = η * p := by
      dsimp [a, b]
      ring
    nlinarith [mul_nonneg hη0 hp]
  change a * p + b * s ≤ ε at hA
  change 1 - (b * p + a * s) ≤ ε at hB
  have hleft : b * (1 - ε) ≤ b * (b * p + a * s) :=
    mul_le_mul_of_nonneg_left (by linarith [hB]) hb
  have hright : a * (a * p + b * s) ≤ a * ε :=
    mul_le_mul_of_nonneg_left hA ha
  have hbound := hleft.trans (hcone.trans hright)
  dsimp [a, b] at hbound
  nlinarith

/-- Positive linear recovery has a uniform error at least `(1-η)/2` on
these two specified inputs and this one nonnegative readout. -/
theorem positive_two_mixture_error_bound
    (K : Set V) (x y : V) (hx : x ∈ K)
    (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ z ∈ K, 0 ≤ ℓ z)
    (η ε : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (T : V → V)
    (hTx : T x = ((1 + η) / 2) • x + ((1 - η) / 2) • y)
    (hTy : T y = ((1 - η) / 2) • x + ((1 + η) / 2) • y)
    (R : V →ₗ[ℝ] V) (hR : PositiveOn K R)
    (hA : ℓ (R (T x)) ≤ ε) (hB : 1 - ℓ (R (T y)) ≤ ε) :
    (1 - η) / 2 ≤ ε := by
  apply scalar_two_mixture_error_bound η (ℓ (R x)) (ℓ (R y)) ε hη0 hη1
    (hℓ _ (hR x hx))
  · simpa [hTx, map_add, map_smul, smul_eq_mul] using hA
  · simpa [hTy, map_add, map_smul, smul_eq_mul] using hB

/-- Keep the projector range fixed and rescale its algebraic complement. -/
def scaleComplement (P : V →ₗ[ℝ] V) (t : ℝ) : V →ₗ[ℝ] V :=
  P + t • (LinearMap.id - P)

@[simp] theorem scaleComplement_apply (P : V →ₗ[ℝ] V) (t : ℝ) (x : V) :
    scaleComplement P t x = P x + t • (x - P x) := rfl

@[simp] theorem scaleComplement_one (P : V →ₗ[ℝ] V) :
    scaleComplement P 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp

/-- Composition multiplies the complement scale for an idempotent map. -/
theorem scaleComplement_comp (P : V →ₗ[ℝ] V) (hP : ∀ x, P (P x) = P x)
    (s t : ℝ) :
    (scaleComplement P s).comp (scaleComplement P t) = scaleComplement P (s * t) := by
  apply LinearMap.ext
  intro x
  have hPs : P (scaleComplement P t x) = P x := by
    simp only [scaleComplement_apply, map_add, map_smul, map_sub, hP,
      sub_self, smul_zero, add_zero]
  change P (scaleComplement P t x) +
    s • (scaleComplement P t x - P (scaleComplement P t x)) =
      P x + (s * t) • (x - P x)
  rw [hPs]
  simp only [scaleComplement_apply]
  module

theorem scaleComplement_inverse_left (P : V →ₗ[ℝ] V)
    (hP : ∀ x, P (P x) = P x) (t : ℝ) (ht : t ≠ 0) :
    Function.LeftInverse (scaleComplement P t⁻¹) (scaleComplement P t) := by
  intro x
  have h := LinearMap.congr_fun (scaleComplement_comp P hP t⁻¹ t) x
  simpa [ht] using h

theorem scaleComplement_inverse_right (P : V →ₗ[ℝ] V)
    (hP : ∀ x, P (P x) = P x) (t : ℝ) (ht : t ≠ 0) :
    Function.RightInverse (scaleComplement P t⁻¹) (scaleComplement P t) := by
  intro x
  have h := LinearMap.congr_fun (scaleComplement_comp P hP t t⁻¹) x
  simpa [ht] using h

end

end IDT.QMClosure.PositiveMixtureRecoveryObstruction
