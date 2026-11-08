import Proofs.QMClosure.RawPlanePhaseParameterFamily
import Proofs.QMClosure.RawPlanePhaseParameterBounds

/-!
# Universal exclusion of nonzero ordinary-plane phase amplitudes

The witness is evaluated against the response of the actual operation on the
supplied complex-coordinate carrier.
-/

namespace IDT.QMClosure.RawPlanePhaseParameterWall

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open RawPlanePhaseParameterFamily
open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

attribute [local simp] Matrix.cons_val_two

def X : Vec := ![1, 1, 1]
def Y : Vec := ![1, Complex.I, 1]
def Z (e : ℝ) : Vec := ![0, Complex.I - 1, (e : ℂ)]
def eta (l : ℝ) : ℂ := phase (-l / 6)
def preparations (l : ℝ) : Fin 3 → Vec :=
  ![X, -Y, eta l • Z (RawPlanePhaseParameterBounds.epsilon l)]

def inner (x y : Vec) : ℂ :=
  star (x 0) * y 0 + star (x 1) * y 1 + star (x 2) * y 2

theorem nativeG_eq_inner_re (x y : Vec) : nativeG x y = (inner x y).re := by
  simp only [nativeG, inner, Complex.add_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem inner_smul (c q : ℂ) (x y : Vec) :
    inner (c • x) (q • y) = star c * q * inner x y := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  simp only [phase, RawSparsePhaseTwistControl.phase, star_div₀, star_add, star_sub,
    star_one, star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg]
  congr 1 <;> ring

theorem G_eq_inner (l : ℝ) (x y : Vec) :
    RawPlanePhaseParameterFamily.G l x y =
      (phase (l * parameter x y * ratio x) *
        phase (-(l * parameter x y * ratio y)) * inner x y).re := by
  rw [RawPlanePhaseParameterFamily.G_eq_nativeG_transport, nativeG_eq_inner_re]
  simp only [H, inner_smul, star_phase, neg_mul, neg_neg]

theorem phase_composition (a b t : ℝ) (h : b - a = t * (1 + a * b)) :
    phase (-a) * phase b = phase t := by
  have ha := RawSparsePhaseTwistControl.phase_denominator_ne_zero (-a)
  have hb := RawSparsePhaseTwistControl.phase_denominator_ne_zero b
  have ht := RawSparsePhaseTwistControl.phase_denominator_ne_zero t
  unfold phase RawSparsePhaseTwistControl.phase
  field_simp [ha, hb, ht]
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

theorem X_ratio : ratio X = 1 / 3 := by norm_num [ratio, W, X, Complex.normSq_apply]
theorem Y_ratio : ratio Y = 1 / 3 := by norm_num [ratio, W, Y, Complex.normSq_apply]
theorem Z_ratio (e : ℝ) : ratio (Z e) = 0 := by simp [ratio, Z]

theorem parameter_smul_right (x y : Vec) (c : ℂ) (hc : c ≠ 0) :
    parameter x (c • y) = parameter x y := by
  simpa using parameter_change_basis x y 1 0 0 c (by simpa using hc)

theorem Z_denominator_plus_positive (e : ℝ) : 0 < 2 + e + e ^ 2 := by
  nlinarith [sq_nonneg (e + 1 / 2)]

theorem Z_denominator_minus_positive (e : ℝ) : 0 < 2 - e + e ^ 2 := by
  nlinarith [sq_nonneg (e - 1 / 2)]

theorem parameter_X_Z (e : ℝ) :
    parameter X (Z e) = (1 + e + e ^ 2) / (2 + e + e ^ 2) := by
  have hd := (Z_denominator_plus_positive e).ne'
  norm_num [parameter, wedge, W, X, Z, Complex.normSq_apply]
  field_simp
  nlinarith [sq_nonneg (e + 1 / 2)]

theorem parameter_Y_Z (e : ℝ) :
    parameter Y (Z e) = (1 - e + e ^ 2) / (2 - e + e ^ 2) := by
  have hd := (Z_denominator_minus_positive e).ne'
  norm_num [parameter, wedge, W, Y, Z, Complex.normSq_apply]
  field_simp
  nlinarith [sq_nonneg (e - 1 / 2)]

theorem phase_zero : phase 0 = 1 := by
  norm_num [phase, RawSparsePhaseTwistControl.phase]

theorem G_X_Y (l : ℝ) : RawPlanePhaseParameterFamily.G l X Y = 2 := by
  rw [G_eq_inner, X_ratio, Y_ratio]
  have hp (t : ℝ) : phase t * phase (-t) = 1 := by
    simpa using RawSparsePhaseTwistControl.phase_neg_mul (-t)
  rw [hp, one_mul]
  norm_num [inner, X, Y, Complex.star_def]

theorem inner_X_Z (e : ℝ) : inner X (Z e) = (e : ℂ) - 1 + Complex.I := by
  norm_num [inner, X, Z, Complex.star_def]
  ring

theorem inner_Y_Z (e : ℝ) : inner Y (Z e) = (e : ℂ) + 1 + Complex.I := by
  apply Complex.ext <;>
    norm_num [inner, Y, Z, Complex.star_def, Complex.mul_re, Complex.mul_im]
  ring

theorem inner_smul_right (q : ℂ) (x y : Vec) :
    inner x (q • y) = q * inner x y := by
  simpa using inner_smul 1 q x y

theorem G_X_eta_Z (l e : ℝ) :
    RawPlanePhaseParameterFamily.G l X (eta l • Z e) =
      (eta l * phase (l * parameter X (Z e) / 3) *
        ((e : ℂ) - 1 + Complex.I)).re := by
  have he : eta l ≠ 0 := RawSparsePhaseTwistControl.phase_ne_zero _
  rw [G_eq_inner, parameter_smul_right _ _ _ he, X_ratio,
    ratio_smul _ he, Z_ratio, inner_smul_right, inner_X_Z]
  simp only [mul_zero, neg_zero, phase_zero, mul_one]
  congr 1
  rw [show l * parameter X (Z e) * (1 / 3) = l * parameter X (Z e) / 3 by ring]
  ring

theorem G_Y_eta_Z (l e : ℝ) :
    RawPlanePhaseParameterFamily.G l Y (eta l • Z e) =
      (eta l * phase (l * parameter Y (Z e) / 3) *
        ((e : ℂ) + 1 + Complex.I)).re := by
  have he : eta l ≠ 0 := RawSparsePhaseTwistControl.phase_ne_zero _
  rw [G_eq_inner, parameter_smul_right _ _ _ he, Y_ratio,
    ratio_smul _ he, Z_ratio, inner_smul_right, inner_Y_Z]
  simp only [mul_zero, neg_zero, phase_zero, mul_one]
  congr 1
  rw [show l * parameter Y (Z e) * (1 / 3) = l * parameter Y (Z e) / 3 by ring]
  ring

theorem eta_phase_plus (l : ℝ) :
    eta l * phase (l * parameter X (Z (RawPlanePhaseParameterBounds.epsilon l)) / 3) =
      phase (RawPlanePhaseParameterBounds.p l) := by
  unfold eta
  rw [show -l / 6 = -(l / 6) by ring]
  apply phase_composition
  rw [parameter_X_Z]
  unfold RawPlanePhaseParameterBounds.p
  field_simp [(RawPlanePhaseParameterBounds.Uplus_positive l).ne',
    (Z_denominator_plus_positive (RawPlanePhaseParameterBounds.epsilon l)).ne']
  unfold RawPlanePhaseParameterBounds.Uplus RawPlanePhaseParameterBounds.L
    RawPlanePhaseParameterBounds.M
  ring

theorem eta_phase_minus (l : ℝ) :
    eta l * phase (l * parameter Y (Z (RawPlanePhaseParameterBounds.epsilon l)) / 3) =
      phase (-RawPlanePhaseParameterBounds.m l) := by
  unfold eta
  rw [show -l / 6 = -(l / 6) by ring]
  apply phase_composition
  rw [parameter_Y_Z]
  unfold RawPlanePhaseParameterBounds.m
  field_simp [(RawPlanePhaseParameterBounds.Uminus_positive l).ne',
    (Z_denominator_minus_positive (RawPlanePhaseParameterBounds.epsilon l)).ne']
  unfold RawPlanePhaseParameterBounds.Uminus RawPlanePhaseParameterBounds.L
    RawPlanePhaseParameterBounds.M
  ring

theorem phase_response_identity (e p m : ℝ) :
    4 + e ^ 2 + 2 * (phase p * ((e : ℂ) - 1 + Complex.I)).re -
        2 * (phase (-m) * ((e : ℂ) + 1 + Complex.I)).re =
      e ^ 2 + 4 * ((-m + (1 + e) * m ^ 2) / (1 + m ^ 2) -
        (p + (e - 1) * p ^ 2) / (1 + p ^ 2)) := by
  norm_num [phase, RawSparsePhaseTwistControl.phase, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp
  ring

theorem G_neg_left (l : ℝ) (x y : Vec) :
    RawPlanePhaseParameterFamily.G l (-x) y = -RawPlanePhaseParameterFamily.G l x y := by
  simpa using RawPlanePhaseParameterFamily.G_real_smul_left l (-1) x y

theorem G_neg_right (l : ℝ) (x y : Vec) :
    RawPlanePhaseParameterFamily.G l x (-y) = -RawPlanePhaseParameterFamily.G l x y := by
  simpa using RawPlanePhaseParameterFamily.G_real_smul_right l (-1) x y

theorem W_eta_Z (l e : ℝ) : W (eta l • Z e) = 2 + e ^ 2 := by
  rw [W_smul, eta, RawSparsePhaseTwistControl.phase_normSq, one_mul]
  norm_num [W, Z, Complex.normSq_apply]
  ring

theorem actual_quadratic_scalar (l : ℝ) :
    RawGramGeometry.quadratic (RawPlanePhaseParameterFamily.G l)
      (preparations l) ![1, 1, 1] = RawPlanePhaseParameterBounds.scalarQ l := by
  rw [RawGramGeometry.quadratic_three (RawPlanePhaseParameterFamily.G_symmetric l)]
  simp only [preparations, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    RawPlanePhaseParameterFamily.G_diagonal, G_neg_left, G_neg_right]
  rw [G_X_Y, G_X_eta_Z, G_Y_eta_Z, eta_phase_plus, eta_phase_minus, W_eta_Z]
  norm_num [W, X, Y, Complex.normSq_apply]
  have h := phase_response_identity (RawPlanePhaseParameterBounds.epsilon l)
    (RawPlanePhaseParameterBounds.p l) (RawPlanePhaseParameterBounds.m l)
  norm_num at h
  unfold RawPlanePhaseParameterBounds.scalarQ
  linear_combination h

theorem actual_quadratic_upper (l : ℝ) (hl : l ≠ 0) :
    RawGramGeometry.quadratic (RawPlanePhaseParameterFamily.G l)
      (preparations l) ![1, 1, 1] ≤ -2 * RawPlanePhaseParameterBounds.epsilon l ^ 2 := by
  rw [actual_quadratic_scalar]
  exact RawPlanePhaseParameterBounds.scalarQ_upper l hl

theorem actual_quadratic_negative (l : ℝ) (hl : l ≠ 0) :
    RawGramGeometry.quadratic (RawPlanePhaseParameterFamily.G l)
      (preparations l) ![1, 1, 1] < 0 := by
  rw [actual_quadratic_scalar]
  exact RawPlanePhaseParameterBounds.scalarQ_negative l hl

theorem not_three_point_nonnegative (l : ℝ) (hl : l ≠ 0) :
    ¬ RawGramGeometry.GramNonnegative (RawPlanePhaseParameterFamily.G l) 3 := by
  intro h
  have hn := h (preparations l) ![1, 1, 1]
  have hh := actual_quadratic_negative l hl
  linarith

theorem three_point_nonnegative_iff (l : ℝ) :
    RawGramGeometry.GramNonnegative (RawPlanePhaseParameterFamily.G l) 3 ↔ l = 0 := by
  constructor
  · intro h
    by_contra hl
    exact not_three_point_nonnegative l hl h
  · rintro rfl
    exact RawPlanePhaseParameterFamily.zero_parameter_gram_nonnegative 3

theorem triangle_iff_zero (l : ℝ) :
    RawGramGeometry.Triangle (RawPlanePhaseParameterFamily.d l) ↔ l = 0 := by
  rw [RawPlanePhaseParameterFamily.triangle_iff_three_point, three_point_nonnegative_iff]

end
end IDT.QMClosure.RawPlanePhaseParameterWall
