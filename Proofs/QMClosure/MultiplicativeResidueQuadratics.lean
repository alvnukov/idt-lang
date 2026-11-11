import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multiplicative families of real homogeneous Gaussian quadratics

An internal polynomial-classification bridge. The index carrier is an arbitrary monoid. The hypothesis supplies an
identity for every real coordinate pair, independently of the indices.

This file supplies no extension from residue lattices to polynomial identities,
no finite translate-rank result, and no physical selection statement.
-/

namespace IDT.MultiplicativeResidueQuadratics

abbrev Plane := ℝ × ℝ

/-- Gaussian multiplication on real coordinate pairs. -/
def gaussianMul (z t : Plane) : Plane :=
  (z.1 * t.1 - z.2 * t.2, z.1 * t.2 + z.2 * t.1)

/-- The real squared Gaussian norm. -/
def normSq (z : Plane) : ℝ :=
  z.1 ^ 2 + z.2 ^ 2

variable {A : Type*} [Monoid A]

/-- A homogeneous real quadratic indexed by a monoid element. -/
def quadratic (α β γ : A → ℝ) (r : A) (z : Plane) : ℝ :=
  α r * z.1 ^ 2 + β r * z.1 * z.2 + γ r * z.2 ^ 2

/--
The supplied universal polynomial identity. Both coordinate pairs range over
all of `ℝ × ℝ`, independently of `r` and `s`.
-/
def PolynomialMultiplicative (α β γ : A → ℝ) : Prop :=
  ∀ (r s : A) (z t : Plane),
    quadratic α β γ (r * s) (gaussianMul z t) =
      quadratic α β γ r z * quadratic α β γ s t

variable {α β γ : A → ℝ}

/-- The identity-index polynomial is exactly the squared Gaussian norm. -/
theorem identity_coefficients
    (hcal : quadratic α β γ 1 (1, 0) = 1)
    (hmul : PolynomialMultiplicative α β γ) :
    α 1 = 1 ∧ β 1 = 0 ∧ γ 1 = 1 := by
  have ha : α 1 = 1 := by
    simpa [quadratic] using hcal
  -- The product i * i gives γ(1)^2 = 1.
  have hsq : γ 1 ^ 2 = 1 := by
    have h := hmul 1 1 (0, 1) (0, 1)
    norm_num [gaussianMul, quadratic, ha] at h
    nlinarith only [h]
  -- The product (1 + i)^2 = 2i makes γ(1) nonnegative.
  have hsum := hmul 1 1 (1, 1) (1, 1)
  norm_num [gaussianMul, quadratic, ha] at hsum
  have hnonneg : 0 ≤ γ 1 := by
    nlinarith only [hsum, sq_nonneg (1 + β 1 + γ 1)]
  have hc : γ 1 = 1 := by
    have hfactor : (γ 1 - 1) * (γ 1 + 1) = 0 := by
      nlinarith only [hsq]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · linarith only [hminus]
    · linarith only [hplus, hnonneg]
  -- Quarter rotation of (1, 1) forces the mixed coefficient to vanish.
  have hrotate := hmul 1 1 (0, 1) (1, 1)
  norm_num [gaussianMul, quadratic, ha, hc] at hrotate
  have hb : β 1 = 0 := by
    linarith only [hrotate]
  exact ⟨ha, hb, hc⟩

/-- The polynomial at the identity index agrees with the real norm everywhere. -/
theorem identity_eq_norm
    (hcal : quadratic α β γ 1 (1, 0) = 1)
    (hmul : PolynomialMultiplicative α β γ) (z : Plane) :
    quadratic α β γ 1 z = normSq z := by
  rcases identity_coefficients hcal hmul with ⟨ha, hb, hc⟩
  simp [quadratic, normSq, ha, hb, hc]

/-- The complete coefficient and function conclusions of the internal bridge. -/
structure CoefficientClassification (α β γ : A → ℝ) : Prop where
  alpha_one : α 1 = 1
  beta_zero : ∀ r, β r = 0
  gamma_eq_alpha : ∀ r, γ r = α r
  scaled_norm : ∀ r z, quadratic α β γ r z = α r * normSq z
  alpha_mul : ∀ r s, α (r * s) = α r * α s

/--
Every supplied multiplicative quadratic family is a real multiplicative
coefficient times the squared Gaussian norm. No finiteness or commutativity of
`A` is required.
-/
theorem classify
    (hcal : quadratic α β γ 1 (1, 0) = 1)
    (hmul : PolynomialMultiplicative α β γ) :
    CoefficientClassification α β γ := by
  rcases identity_coefficients hcal hmul with ⟨ha, hb, hc⟩
  -- The formal value z = 1 is allowed independently of the index r.
  have hscale (r : A) (z : Plane) :
      quadratic α β γ r z = α r * normSq z := by
    have h := hmul r 1 (1, 0) z
    simpa [gaussianMul, quadratic, normSq, ha, hb, hc] using h
  have hgamma (r : A) : γ r = α r := by
    simpa [quadratic, normSq] using hscale r (0, 1)
  have hbeta (r : A) : β r = 0 := by
    have h := hscale r (1, 1)
    norm_num [quadratic, normSq, hgamma r] at h
    linarith only [h]
  have halpha_mul (r s : A) : α (r * s) = α r * α s := by
    simpa [gaussianMul, quadratic] using hmul r s (1, 0) (1, 0)
  exact
    { alpha_one := ha
      beta_zero := hbeta
      gamma_eq_alpha := hgamma
      scaled_norm := hscale
      alpha_mul := halpha_mul }

/--
The classified coefficient is a monoid homomorphism to the multiplicative real
monoid. Its contract imposes no zero-preservation requirement.
-/
def coefficientHom (h : CoefficientClassification α β γ) : A →* ℝ where
  toFun := α
  map_one' := h.alpha_one
  map_mul' := h.alpha_mul

/-- Gaussian norm multiplicativity follows directly by polynomial expansion. -/
theorem normSq_gaussianMul (z t : Plane) :
    normSq (gaussianMul z t) = normSq z * normSq t := by
  dsimp [normSq, gaussianMul]
  ring

/-- The diagonal coefficient family evaluates to its coefficient times the norm. -/
theorem diagonal_quadratic (c : A → ℝ) (r : A) (z : Plane) :
    quadratic c (fun _ => 0) c r z = c r * normSq z := by
  dsimp [quadratic, normSq]
  ring

/-- Every real multiplicative coefficient supplies a calibrated quadratic family. -/
theorem diagonal_calibrated (c : A →* ℝ) :
    quadratic (fun r => c r) (fun _ => 0) (fun r => c r) 1 (1, 0) = 1 := by
  simp [quadratic]

/--
Generic converse. The family defined by any monoid homomorphism to the real
multiplicative monoid satisfies the full universal polynomial identity.
-/
theorem diagonal_multiplicative (c : A →* ℝ) :
    PolynomialMultiplicative
      (fun r => c r) (fun _ => 0) (fun r => c r) := by
  intro r s z t
  simp only [diagonal_quadratic, map_mul, normSq_gaussianMul]
  ring

/--
An independent nonvacuity witness on every monoid. The constant coefficient one
family is calibrated and satisfies the universal Gaussian polynomial identity.
-/
theorem norm_family_witness :
    quadratic (fun _ : A => 1) (fun _ => 0) (fun _ => 1) 1 (1, 0) = 1 ∧
      PolynomialMultiplicative
        (fun _ : A => 1) (fun _ => 0) (fun _ => 1) := by
  constructor
  · norm_num [quadratic]
  · intro r s z t
    simpa [quadratic, normSq] using normSq_gaussianMul z t

end IDT.MultiplicativeResidueQuadratics
