import Mathlib.Tactic

namespace IDT.QMClosure.CentralInversionWitness

noncomputable section

/-!
Conditional coordinate witness for a supplied visible output branch.
The visible-branch formula is a premise. Its derivation from a central
inversion, twirl, masker, or atomic dynamics is outside this artifact.
The coefficient convention is rho = (sum_ij coefficient_ij basis_i ⊗ basis_j)/4.
-/

abbrev Direction := Fin 3 → ℝ
abbrev Coefficients := Fin 4 → Fin 4 → ℝ

def normSquared (a : Direction) : ℝ := ∑ i, a i ^ 2

def preparation : Fin 4 → ℝ := ![1, 1, 0, 0]
def inputCoefficients : Coefficients := fun i j => preparation i * preparation j

def inputDirection : Direction := ![1, 0, 0]
def alpha : Direction
  | 0 => -1/2 | 1 => 0 | 2 => Real.sqrt 3 / 2
def beta : Direction
  | 0 => -1/2 | 1 => 0 | 2 => -(Real.sqrt 3 / 2)

/-- The identity coordinate of an effect is one, followed by its direction. -/
def effect (a : Direction) : Fin 4 → ℝ
  | 0 => 1 | 1 => a 0 | 2 => a 1 | 3 => a 2

def productReadout (r : Coefficients) (a b : Direction) : ℝ :=
  (∑ i : Fin 4, ∑ j : Fin 4, r i j * effect a i * effect b j) / 4

/-- Coordinates m,v,Jv,z on each wire. Here s=√3/4 and δ=1/2.
The κ term occupies exactly the Jv⊗Jw entry. -/
def visibleBranch (κ : ℝ) : Coefficients
  | 0, 0 => 1/2
  | 0, 1 => Real.sqrt 3 / 4
  | 1, 0 => Real.sqrt 3 / 4
  | 1, 1 => Real.sqrt 3 / 4
  | 2, 2 => κ
  | 3, 3 => 1/4
  | _, _ => 0

theorem input_direction_unit : normSquared inputDirection = 1 := by
  norm_num [normSquared, inputDirection, Fin.sum_univ_succ]

theorem alpha_unit : normSquared alpha = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  norm_num [normSquared, alpha, Fin.sum_univ_succ]
  nlinarith

theorem beta_unit : normSquared beta = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  norm_num [normSquared, beta, Fin.sum_univ_succ]
  nlinarith

/-- The chosen effects annihilate the Jv and Jw coordinates separately. -/
theorem transverse_effects_zero : effect alpha 2 = 0 ∧ effect beta 2 = 0 := by
  norm_num [effect, alpha, beta]

theorem input_readout_formula (a b : Direction) :
    productReadout inputCoefficients a b = (1 + a 0) * (1 + b 0) / 4 := by
  norm_num [productReadout, inputCoefficients, preparation, effect, Fin.sum_univ_succ]
  ring

/-- Explicit positivity of this product preparation under effects whose
selected local coordinates are at least -1. -/
theorem input_readout_nonnegative (a b : Direction)
    (ha : -1 ≤ a 0) (hb : -1 ≤ b 0) :
    0 ≤ productReadout inputCoefficients a b := by
  rw [input_readout_formula]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)

theorem unit_direction_first_lower_bound (a : Direction) (ha : normSquared a = 1) :
    -1 ≤ a 0 := by
  simp [normSquared, Fin.sum_univ_succ] at ha
  nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]

theorem input_product_positive (a b : Direction)
    (ha : normSquared a = 1) (hb : normSquared b = 1) :
    0 ≤ productReadout inputCoefficients a b := by
  exact input_readout_nonnegative a b
    (unit_direction_first_lower_bound a ha) (unit_direction_first_lower_bound b hb)

theorem chosen_input_readout : productReadout inputCoefficients alpha beta = 1/16 := by
  rw [input_readout_formula]
  norm_num [alpha, beta]

/-- This is the full coefficient contraction, including the κ entry. -/
theorem visible_branch_readout (κ : ℝ) :
    productReadout (visibleBranch κ) alpha beta = (5 - 3 * Real.sqrt 3) / 64 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  norm_num [productReadout, visibleBranch, effect, alpha, beta, Fin.sum_univ_succ, Fin.succ]
  nlinarith

theorem witness_value_negative : (5 - 3 * Real.sqrt 3) / 64 < 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlt : 5 < 3 * Real.sqrt 3 := by nlinarith
  linarith

/-- Any supplied output satisfying this visible-branch coordinate formula
violates the stated product readout positivity requirement. -/
theorem conditional_visible_output_negative (output : Coefficients) (κ : ℝ)
    (houtput : output = visibleBranch κ) : productReadout output alpha beta < 0 := by
  rw [houtput, visible_branch_readout]
  exact witness_value_negative

theorem conditional_visible_output_not_product_positive
    (output : Coefficients) (κ : ℝ) (houtput : output = visibleBranch κ) :
    ¬ (∀ a b : Direction, normSquared a = 1 → normSquared b = 1 →
      0 ≤ productReadout output a b) := by
  intro h
  have hn := h alpha beta alpha_unit beta_unit
  have hl := conditional_visible_output_negative output κ houtput
  linarith

end

end IDT.QMClosure.CentralInversionWitness
