import Proofs.QMClosure.RawPlanePhaseGramKernel
import Proofs.QMClosure.RawPlanePhaseSparseWall

/-!
# Exact Gram and triangle countercontrols for the actual plane operation

Every entry below is computed from the response of the supplied continuous
operation, through its proved transport formula. The explicit quadratic
witnesses refute three-point and four-point positivity for that response.
The scaled three-point witness also gives a strict triangle violation for the
actual distance readout. These are mathematical controls and imply no physical
primitive or QM-closure claim.
-/

namespace IDT.QMClosure.RawPlanePhaseGramControl

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- The first explicit tuple has a negative four-point quadratic. -/
def fourX : Vec := ![1, 0, 0]
def fourY : Vec := ![0, 1, 0]
def fourU : Vec := ![1 / 2, 1 / 2, 0]
def fourZ : Vec := ![1, 0, 1]

/-- Off-diagonal entries of the actual response, with no free matrix supplied. -/
theorem four_cross_entries :
    G fourX fourY = 0 ∧
    G fourX fourU = 1 / 2 ∧
    G fourX fourZ = 4 / 5 ∧
    G fourY fourU = 1 / 2 ∧
    G fourY fourZ = 0 ∧
    G fourU fourZ = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [G_eq_nativeG_transport] <;>
    norm_num [nativeG, H, ratio, phase, RawSparsePhaseTwistControl.phase,
      parameter, wedge, W, fourX, fourY, fourU, fourZ,
      Pi.smul_apply, smul_eq_mul, Complex.normSq_apply,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem four_diagonal_entries :
    G fourX fourX = 1 ∧ G fourY fourY = 1 ∧
    G fourU fourU = 1 / 2 ∧ G fourZ fourZ = 2 := by
  norm_num [G_diagonal, W, fourX, fourY, fourU, fourZ, Complex.normSq_apply]

/-- The displayed coefficients are evaluated against the actual operation. -/
theorem four_quadratic :
    RawGramGeometry.quadratic G ![fourX, fourY, fourU, fourZ]
      ![-10, -10, 20, -1] = -2 := by
  rcases four_cross_entries with ⟨hxy, hxu, hxz, hyu, hyz, huz⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, huu, hzz⟩
  rw [RawGramGeometry.quadratic_four G_symmetric]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hxx, hyy, huu, hzz, hxy, hxu, hxz, hyu, hyz, huz]
  norm_num

theorem not_four_point_positive : ¬ RawGramGeometry.GramNonnegative G 4 := by
  intro h
  have hh := h ![fourX, fourY, fourU, fourZ] ![-10, -10, 20, -1]
  rw [four_quadratic] at hh
  norm_num at hh

/-- This separate tuple detects failure already at three points. -/
def threeX : Vec := ![0, 1, 1]
def threeY : Vec := ![1, 2, 1]
def threeZ : Vec := ![2, 2, 1]

/-- Exact pair entries computed through the actual mixer's transport. -/
theorem three_cross_entries :
    G threeX threeY = 120 / 41 ∧
    G threeX threeZ = 18483 / 6961 ∧
    G threeY threeZ = 12793837 / 1838941 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [G_eq_nativeG_transport] <;>
    norm_num [nativeG, H, ratio, phase, RawSparsePhaseTwistControl.phase,
      parameter, wedge, W, threeX, threeY, threeZ,
      Pi.smul_apply, smul_eq_mul, Complex.normSq_apply,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem three_diagonal_entries :
    G threeX threeX = 2 ∧ G threeY threeY = 6 ∧ G threeZ threeZ = 9 := by
  norm_num [G_diagonal, W, threeX, threeY, threeZ, Complex.normSq_apply]

/-- An exact negative value, with fixed integer coefficients. -/
theorem three_quadratic :
    RawGramGeometry.quadratic G ![threeX, threeY, threeZ] ![5, -7, 4] =
      -142257420744 / 524835600341 := by
  rcases three_cross_entries with ⟨hxy, hxz, hyz⟩
  rcases three_diagonal_entries with ⟨hxx, hyy, hzz⟩
  rw [RawGramGeometry.quadratic_three G_symmetric]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hxx, hyy, hzz, hxy, hxz, hyz]
  norm_num

theorem not_three_point_positive : ¬ RawGramGeometry.GramNonnegative G 3 := by
  intro h
  have hh := h ![threeX, threeY, threeZ] ![5, -7, 4]
  rw [three_quadratic] at hh
  norm_num at hh

/-- Actual scaled inputs for the strict triangle witness. -/
def triangleP : Vec := ((5 : ℝ) : ℂ) • threeX
def triangleQ : Vec := ((-7 : ℝ) : ℂ) • threeY
def triangleR : Vec := ((-2 : ℝ) : ℂ) • threeZ

theorem triangle_pr_sq : d triangleP triangleR ^ 2 = 968306 / 6961 := by
  rcases three_cross_entries with ⟨hxy, hxz, hyz⟩
  rcases three_diagonal_entries with ⟨hxx, hyy, hzz⟩
  rw [d_sq]
  simp only [triangleP, triangleR, G_real_smul_left, G_real_smul_right]
  rw [hxx, hzz, hxz]
  norm_num

theorem triangle_qr_sq : d triangleQ triangleR ^ 2 = 248623094 / 1838941 := by
  rcases three_cross_entries with ⟨hxy, hxz, hyz⟩
  rcases three_diagonal_entries with ⟨hxx, hyy, hzz⟩
  rw [d_sq]
  simp only [triangleQ, triangleR, G_real_smul_left, G_real_smul_right]
  rw [hyy, hzz, hyz]
  norm_num

theorem triangle_pq_sq : d triangleP triangleQ ^ 2 = 22504 / 41 := by
  rcases three_cross_entries with ⟨hxy, hxz, hyz⟩
  rcases three_diagonal_entries with ⟨hxx, hyy, hzz⟩
  rw [d_sq]
  simp only [triangleP, triangleQ, G_real_smul_left, G_real_smul_right]
  rw [hxx, hyy, hxy]
  norm_num

/-- Twice the two leg squares is already smaller than the opposite square. -/
theorem triangle_squared_defect :
    2 * d triangleP triangleR ^ 2 + 2 * d triangleQ triangleR ^ 2 -
      d triangleP triangleQ ^ 2 = -142257420744 / 524835600341 := by
  rw [triangle_pr_sq, triangle_qr_sq, triangle_pq_sq]
  norm_num

/-- A strict violation at three specified inputs of the actual readout. -/
theorem strict_triangle_violation :
    d triangleP triangleR + d triangleR triangleQ < d triangleP triangleQ := by
  rw [d_symmetric triangleR triangleQ]
  have hdef := triangle_squared_defect
  have hpq := d_nonnegative triangleP triangleQ
  have hpr := d_nonnegative triangleP triangleR
  have hqr := d_nonnegative triangleQ triangleR
  nlinarith [sq_nonneg (d triangleP triangleR - d triangleQ triangleR)]

theorem not_triangle : ¬ RawGramGeometry.Triangle d := by
  exact fun h => not_three_point_positive (triangle_iff_three_point.mp h)

/-- One continuous, faithful control has all raw tests and all displayed failures. -/
theorem constructed_continuous_countercontrol :
    RawSparseConservationTests.Tests RawPlanePhaseControl.contract ∧
    (∀ x y, RawSparseConservationTests.SparseAt RawPlanePhaseControl.contract x y
      (RawSparseConservationSelection.A RawPlanePhaseControl.contract x)) ∧
    (∀ x, 0 ≤ RawPlanePhaseControl.contract.weight x) ∧
    (∀ x, RawPlanePhaseControl.contract.weight x = 0 ↔
      x = RawPlanePhaseControl.contract.chosenZero) ∧
    RawSparseConservationSelection.PairConserved RawPlanePhaseControl.contract ∧
    (∀ (c : ℂ) (x y : Vec), RawPlanePhaseControl.m (c • x) (c • y) =
      c • RawPlanePhaseControl.m x y) ∧
    Continuous RawPlanePhaseControl.operation ∧
    ¬ RawSparseConservationSelection.SparseMarginalLaw RawPlanePhaseControl.contract ∧
    ¬ RawSparseConservationSelection.ObservedMedial RawPlanePhaseControl.contract ∧
    ¬ RawGramGeometry.GramNonnegative G 3 ∧
    ¬ RawGramGeometry.GramNonnegative G 4 ∧
    ¬ RawGramGeometry.Triangle d ∧
    d triangleP triangleR + d triangleR triangleQ < d triangleP triangleQ := by
  obtain ⟨ht, hs, hw, hf, hp, hh, hc, hn, hm⟩ :=
    RawPlanePhaseSparseWall.constructed_continuous_countermodel
  exact ⟨ht, hs, hw, hf, hp, hh, hc, hn, hm, not_three_point_positive,
    not_four_point_positive, not_triangle, strict_triangle_violation⟩

end
end IDT.QMClosure.RawPlanePhaseGramControl
