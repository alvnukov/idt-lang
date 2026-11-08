import Proofs.QMClosure.RawPlanePhaseGramControl
import Proofs.QMClosure.RawMidpointGramGeometry

/-!
# Exact midpoint obstruction for the actual plane control

The midpoint is computed from the supplied mixer and its native attenuation.
For one fixed input pair, all real scalings of a specified reference give an
exact affine squared-distance slack. The threshold below concerns this single
pair and reference orbit. These controls assert no physical primitive or
QM-closure claim.
-/

namespace IDT.QMClosure.RawPlanePhaseMidpointControl

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open RawPlanePhaseGramControl

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- The midpoint expression uses the actual operation. -/
def mid (x y : Vec) : Vec := b • RawPlanePhaseControl.m x (Complex.I • y)

/-- The selected reference orbit includes every real scalar. -/
def ref (t : ℝ) : Vec := (t : ℂ) • fourZ

theorem selected_pair_parameter : parameter fourX (Complex.I • fourY) = 0 := by
  norm_num [parameter, wedge, W, fourX, fourY, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

/-- Compute the actual midpoint, without supplying a separate averaging map. -/
theorem mid_fourX_fourY : mid fourX fourY = fourU := by
  unfold mid RawPlanePhaseControl.m
  rw [selected_pair_parameter, familyM_zero]
  funext i
  fin_cases i <;>
    apply Complex.ext <;>
    norm_num [native, a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      fourX, fourY, fourU, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem ref_fourX_sq (t : ℝ) :
    d (ref t) fourX ^ 2 = 2 * t ^ 2 + 1 - (8 / 5) * t := by
  rcases four_cross_entries with ⟨hxy, hxu, hxz, hyu, hyz, huz⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, huu, hzz⟩
  rw [d_sq]
  simp only [ref, G_real_smul_left, G_real_smul_right]
  rw [hzz, hxx, G_symmetric fourZ fourX, hxz]
  ring

theorem ref_fourY_sq (t : ℝ) :
    d (ref t) fourY ^ 2 = 2 * t ^ 2 + 1 := by
  rcases four_cross_entries with ⟨hxy, hxu, hxz, hyu, hyz, huz⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, huu, hzz⟩
  rw [d_sq]
  simp only [ref, G_real_smul_left, G_real_smul_right]
  rw [hzz, hyy, G_symmetric fourZ fourY, hyz]
  ring

theorem ref_fourU_sq (t : ℝ) :
    d (ref t) fourU ^ 2 = 2 * t ^ 2 + 1 / 2 - t := by
  rcases four_cross_entries with ⟨hxy, hxu, hxz, hyu, hyz, huz⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, huu, hzz⟩
  rw [d_sq]
  simp only [ref, G_real_smul_left, G_real_smul_right]
  rw [hzz, huu, G_symmetric fourZ fourU, huz]
  ring

/-- Exact weak midpoint slack on the selected pair and reference orbit. -/
theorem orbit_squared_midpoint_slack (t : ℝ) :
    (d (ref t) fourX ^ 2 + d (ref t) fourY ^ 2) / 2 -
      d (ref t) (mid fourX fourY) ^ 2 = 1 / 2 + t / 5 := by
  rw [mid_fourX_fourY, ref_fourX_sq, ref_fourY_sq, ref_fourU_sq]
  ring

/-- This threshold has no quantification over other endpoint pairs. -/
theorem orbit_squared_midpoint_iff (t : ℝ) :
    d (ref t) (mid fourX fourY) ^ 2 ≤
      (d (ref t) fourX ^ 2 + d (ref t) fourY ^ 2) / 2 ↔
        -(5 / 2 : ℝ) ≤ t := by
  have hs := orbit_squared_midpoint_slack t
  constructor <;> intro ht <;> linarith

theorem negative_three_squares :
    d (ref (-3)) (mid fourX fourY) ^ 2 = 43 / 2 ∧
    d (ref (-3)) fourX ^ 2 = 119 / 5 ∧
    d (ref (-3)) fourY ^ 2 = 19 := by
  rw [mid_fourX_fourY, ref_fourU_sq, ref_fourX_sq, ref_fourY_sq]
  norm_num

/-- The squared midpoint distance exceeds the endpoint mean by one tenth. -/
theorem negative_three_squared_defect :
    d (ref (-3)) (mid fourX fourY) ^ 2 -
      (d (ref (-3)) fourX ^ 2 + d (ref (-3)) fourY ^ 2) / 2 = 1 / 10 := by
  rcases negative_three_squares with ⟨hu, hx, hy⟩
  rw [hu, hx, hy]
  norm_num

theorem distance_square_eq (x y : Vec) :
    d x y ^ 2 = RawMidpointGramGeometry.squaredDistance G x y :=
  d_sq x y

theorem not_squaredMidpointConvex :
    ¬ RawMidpointGramGeometry.SquaredMidpointConvex G mid := by
  intro h
  have hh := h (ref (-3)) fourX fourY
  simp only [← distance_square_eq] at hh
  have ht := (orbit_squared_midpoint_iff (-3)).mp hh
  norm_num at ht

/-- A strict unsquared failure for the same actual operation and reference. -/
theorem strict_distance_midpoint_violation :
    d (ref (-3)) (mid fourX fourY) >
      (d (ref (-3)) fourX + d (ref (-3)) fourY) / 2 := by
  rcases negative_three_squares with ⟨hu, hx, hy⟩
  have hnu := d_nonnegative (ref (-3)) (mid fourX fourY)
  have hnx := d_nonnegative (ref (-3)) fourX
  have hny := d_nonnegative (ref (-3)) fourY
  by_contra hn
  push Not at hn
  have hdiff : 0 ≤ d (ref (-3)) fourX + d (ref (-3)) fourY -
      2 * d (ref (-3)) (mid fourX fourY) := by
    linarith
  have hsum : 0 ≤ d (ref (-3)) fourX + d (ref (-3)) fourY +
      2 * d (ref (-3)) (mid fourX fourY) := by
    linarith
  have hprod := mul_nonneg hdiff hsum
  nlinarith [sq_nonneg (d (ref (-3)) fourX - d (ref (-3)) fourY)]

theorem not_distanceMidpointConvex :
    ¬ RawMidpointGramGeometry.DistanceMidpointConvex d mid := by
  intro h
  exact (not_le_of_gt strict_distance_midpoint_violation)
    (h (ref (-3)) fourX fourY)

end
end IDT.QMClosure.RawPlanePhaseMidpointControl
