import Proofs.QMClosure.RawLocalMidpointCompatibility
import Proofs.QMClosure.RawPlanePhaseMidpointControl

/-!
# Local and second-order midpoint obstructions in the actual plane control

The midpoint and response below are computed from the existing supplied
lambda-one mathematical control. Every positive diagonal-weight ball fails
the restricted squared Jensen condition, and no second-order dyadic error
constant controls all contraction indices for every fixed triple.

The selected balanced orbit and the co-planar identity have the precise
restricted scopes stated below. No physical-origin or QM-closure claim is made.
-/

namespace IDT.QMClosure.RawPlanePhaseLocalMidpointControl

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open RawPlanePhaseGramControl RawPlanePhaseMidpointControl
open RawMidpointGramGeometry RawDyadicMidpointGram RawLocalMidpointCompatibility

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-- The actual preparation map used for row halving. -/
def half (x : Vec) : Vec := (1 / 2 : ℂ) • x

/-- Ordinary negation of the supplied mathematical preparation. -/
def antipode (x : Vec) : Vec := -x

theorem half_row (x z : Vec) : G (half x) z = G x z / 2 := by
  simpa [half, div_eq_mul_inv, mul_comm] using G_real_smul_left (1 / 2) x z

theorem antipode_row (x z : Vec) : G (antipode x) z = -G x z := by
  simpa [antipode] using G_real_smul_left (-1) x z

/-- Uniform complex covariance follows from covariance of the actual mixer. -/
theorem mid_smul (c : ℂ) (x y : Vec) :
    mid (c • x) (c • y) = c • mid x y := by
  have hI : Complex.I • (c • y) = c • (Complex.I • y) := by
    simp only [smul_smul]
    rw [mul_comm Complex.I c]
  unfold mid
  rw [hI, RawPlanePhaseControl.m_smul]
  simp only [smul_smul]
  rw [mul_comm b c]

theorem half_midpoint (x y : Vec) : mid (half x) (half y) = half (mid x y) :=
  mid_smul (1 / 2) x y

theorem halfMidpointCompatible : HalfMidpointCompatible G half mid :=
  halfMidpointCompatible_of_preparationEquality half half_row mid half_midpoint

theorem nonnegativeSquaredDistances : NonnegativeSquaredDistances G := by
  intro x y
  rw [← distance_square_eq]
  exact sq_nonneg _

theorem not_midpointRowAverage : ¬ MidpointRowAverage G mid := by
  intro hrow
  exact not_squaredMidpointConvex
    (squaredMidpointConvex_of_midpointRowAverage G_symmetric
      nonnegativeSquaredDistances mid hrow)

/-- Only the three input preparations are restricted to the ball. -/
theorem not_localSquaredMidpointConvex_weightBall (R : ℝ) (hR : 0 < R) :
    ¬ LocalSquaredMidpointConvex G mid (DiagonalWeightBall G R) := by
  intro hlocal
  exact not_midpointRowAverage
    (midpointRowAverage_of_weightBallSquaredMidpointConvex G_symmetric half antipode
      half_row antipode_row nonnegativeSquaredDistances mid halfMidpointCompatible
      R hR hlocal)

/-- For some fixed triple every constant fails at a dyadic index. -/
theorem not_secondOrderJensenControl : ¬ SecondOrderJensenControl G half mid := by
  intro hcontrol
  exact not_midpointRowAverage
    (midpointRowAverage_of_secondOrderJensenControl G_symmetric half antipode
      half_row antipode_row mid halfMidpointCompatible hcontrol)

def scale (r : ℝ) (x : Vec) : Vec := (r : ℂ) • x

theorem squaredDistance_scale (r s : ℝ) (x y : Vec) :
    squaredDistance G (scale r x) (scale s y) =
      r ^ 2 * G x x + s ^ 2 * G y y - 2 * r * s * G x y := by
  unfold squaredDistance scale
  simp only [G_real_smul_left, G_real_smul_right]
  ring

theorem mid_scaled_selected_pair (e : ℝ) :
    mid (scale e fourX) (scale e fourY) = scale e fourU := by
  rw [scale, scale, mid_smul, mid_fourX_fourY]
  rfl

/-- The slack uses actual distance squares and the actual midpoint. -/
def selectedSlack (t e : ℝ) : ℝ :=
  (d (scale t fourZ) (scale e fourX) ^ 2 +
      d (scale t fourZ) (scale e fourY) ^ 2) / 2 -
    d (scale t fourZ) (mid (scale e fourX) (scale e fourY)) ^ 2

/-- This formula concerns the displayed endpoint pair and reference orbit. -/
theorem selectedSlack_exact (t e : ℝ) :
    selectedSlack t e = e ^ 2 / 2 + t * e / 5 := by
  rcases four_cross_entries with ⟨hxy, hxu, hxz, hyu, hyz, huz⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, huu, hzz⟩
  unfold selectedSlack
  rw [mid_scaled_selected_pair]
  simp only [distance_square_eq, squaredDistance_scale]
  rw [hzz, hxx, hyy, huu, G_symmetric fourZ fourX, hxz,
    G_symmetric fourZ fourY, hyz, G_symmetric fourZ fourU, huz]
  ring

/-- Fixed reference, scaled endpoints, and the actual scaled midpoint. -/
theorem fixed_reference_excess (e : ℝ) :
    d (-fourZ) (mid (scale e fourX) (scale e fourY)) ^ 2 -
      (d (-fourZ) (scale e fourX) ^ 2 + d (-fourZ) (scale e fourY) ^ 2) / 2 =
        e / 5 - e ^ 2 / 2 := by
  have h := selectedSlack_exact (-1) e
  have href : scale (-1) fourZ = -fourZ := by simp [scale]
  unfold selectedSlack at h
  rw [href] at h
  linarith

theorem fixed_reference_excess_positive_iff (e : ℝ) :
    0 < d (-fourZ) (mid (scale e fourX) (scale e fourY)) ^ 2 -
      (d (-fourZ) (scale e fourX) ^ 2 + d (-fourZ) (scale e fourY) ^ 2) / 2 ↔
        0 < e ∧ e < 2 / 5 := by
  rw [fixed_reference_excess]
  constructor
  · intro h
    have he : 0 < e := by nlinarith [sq_nonneg e]
    refine ⟨he, ?_⟩
    by_contra hn
    have hp := mul_nonneg he.le (show 0 ≤ e - 2 / 5 by linarith)
    nlinarith
  · rintro ⟨he, hupper⟩
    have hp := mul_pos he (show 0 < 2 / 5 - e by linarith)
    nlinarith

/-- The two balanced rays are a selected passing orbit. -/
theorem balanced_selected_slacks (e : ℝ) :
    selectedSlack e e = e ^ 2 * (1 / 2 + 1 / 5) ∧
      selectedSlack (-e) e = e ^ 2 * (1 / 2 - 1 / 5) := by
  rw [selectedSlack_exact, selectedSlack_exact]
  constructor <;> ring

theorem balanced_selected_slacks_positive (e : ℝ) (he : e ≠ 0) :
    0 < selectedSlack e e ∧ 0 < selectedSlack (-e) e := by
  rcases balanced_selected_slacks e with ⟨hplus, hminus⟩
  rw [hplus, hminus]
  have hp := sq_pos_of_ne_zero he
  constructor <;> nlinarith

theorem inPlane_mid (x y : Vec) : InPlane x y (mid x y) :=
  inPlane_smul b (RawPlanePhaseControl.inPlane_m
    (inPlane_left x y) (inPlane_smul Complex.I (inPlane_right x y)))

theorem native_midpoint (x y : Vec) :
    b • native x (Complex.I • y) = ((1 / 2 : ℝ) : ℂ) • (x + y) := by
  funext i
  apply Complex.ext <;>
    norm_num [native, a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

/-- One fixed pair transport sends the actual midpoint to the coordinate mean. -/
theorem H_mid (x y : Vec) :
    H (-parameter x y) (mid x y) =
      ((1 / 2 : ℝ) : ℂ) • (H (-parameter x y) x + H (-parameter x y) y) := by
  unfold mid
  rw [H_smul, RawPlanePhaseControl.m_eq_family_of_inPlane
    (inPlane_left x y) (inPlane_smul Complex.I (inPlane_right x y)),
    familyM, H_neg_H, H_smul, native_midpoint]

theorem squaredDistance_inPlane {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    squaredDistance G z w =
      squaredDistance nativeG (H (-parameter x y) z) (H (-parameter x y) w) := by
  unfold squaredDistance
  rw [G_inPlane hz hz, G_inPlane hw hw, G_inPlane hz hw]

theorem native_squared_CN (z x y : Vec) :
    squaredDistance nativeG z (((1 / 2 : ℝ) : ℂ) • (x + y)) =
      (squaredDistance nativeG z x + squaredDistance nativeG z y) / 2 -
        squaredDistance nativeG x y / 4 := by
  unfold squaredDistance
  simp only [nativeG_real_smul_left, nativeG_real_smul_right,
    nativeG_add_left, nativeG_add_right]
  rw [nativeG_symmetric y x]
  ring

/-- Strong CN holds for every reference in the endpoints' ordinary complex plane. -/
theorem squared_CN_inPlane {x y z : Vec} (hz : InPlane x y z) :
    squaredDistance G z (mid x y) =
      (squaredDistance G z x + squaredDistance G z y) / 2 -
        squaredDistance G x y / 4 := by
  rw [squaredDistance_inPlane hz (inPlane_mid x y),
    squaredDistance_inPlane hz (inPlane_left x y),
    squaredDistance_inPlane hz (inPlane_right x y),
    squaredDistance_inPlane (inPlane_left x y) (inPlane_right x y), H_mid]
  exact native_squared_CN _ _ _

end
end IDT.QMClosure.RawPlanePhaseLocalMidpointControl
