import Proofs.QMClosure.RawPlanePhaseContinuity
import Proofs.QMClosure.RawFourPointGramBridge

/-!
# The actual response kernel of the continuous plane control

The response below is computed from the actual plane-dependent mixer. On each
ordinary complex two-plane it is the pullback of the elementary real coordinate
Gram form by one fixed phase transport. These statements concern the supplied
mathematical control and make no physical primitive or QM-closure claim.
-/

namespace IDT.QMClosure.RawPlanePhaseGramKernel

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry
open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-- The elementary real coordinate form, used only after proving transport. -/
def nativeG (x y : Vec) : ℝ :=
  (x 0).re * (y 0).re + (x 0).im * (y 0).im +
  (x 1).re * (y 1).re + (x 1).im * (y 1).im +
  (x 2).re * (y 2).re + (x 2).im * (y 2).im

/-- The response of the actual mixer to the prescribed quarter-turn input. -/
def G (x y : Vec) : ℝ :=
  (W x + W y - 2 * W (RawPlanePhaseControl.m x ((-Complex.I) • y))) / 2

/-- The distance readout computed from the actual response. -/
def d (x y : Vec) : ℝ := Real.sqrt (W x + W y - 2 * G x y)

theorem nativeG_symmetric (x y : Vec) : nativeG x y = nativeG y x := by
  unfold nativeG
  ring

theorem nativeG_diagonal (x : Vec) : nativeG x x = W x := by
  simp only [nativeG, W, Complex.normSq_apply]
  ring

@[simp] theorem nativeG_zero_left (x : Vec) : nativeG 0 x = 0 := by
  simp [nativeG]

@[simp] theorem nativeG_zero_right (x : Vec) : nativeG x 0 = 0 := by
  rw [nativeG_symmetric, nativeG_zero_left]

theorem nativeG_add_left (x y z : Vec) :
    nativeG (x + y) z = nativeG x z + nativeG y z := by
  simp only [nativeG, Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem nativeG_add_right (x y z : Vec) :
    nativeG x (y + z) = nativeG x y + nativeG x z := by
  rw [nativeG_symmetric, nativeG_add_left]
  rw [nativeG_symmetric y x, nativeG_symmetric z x]

theorem nativeG_real_smul_left (r : ℝ) (x y : Vec) :
    nativeG ((r : ℂ) • x) y = r * nativeG x y := by
  simp only [nativeG, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem nativeG_real_smul_right (r : ℝ) (x y : Vec) :
    nativeG x ((r : ℂ) • y) = r * nativeG x y := by
  rw [nativeG_symmetric, nativeG_real_smul_left, nativeG_symmetric y x]

/-- The specified native mixer response is exactly the coordinate Gram form. -/
theorem native_response (x y : Vec) :
    (W x + W y - 2 * W (native x ((-Complex.I) • y))) / 2 =
      nativeG x y := by
  norm_num [W, nativeG, native, a, b, NativeAttenuationCircuit.a,
    NativeAttenuationCircuit.b, Pi.smul_apply, smul_eq_mul, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

/-- All subpairs use the same fixed transport, including dependent subpairs. -/
theorem G_inPlane {x y z w : Vec} (hz : InPlane x y z) (hw : InPlane x y w) :
    G z w = nativeG (H (-parameter x y) z) (H (-parameter x y) w) := by
  calc
    G z w =
        (W (H (-parameter x y) z) + W (H (-parameter x y) w) -
          2 * W (native (H (-parameter x y) z)
            ((-Complex.I) • H (-parameter x y) w))) / 2 := by
      unfold G
      rw [RawPlanePhaseControl.m_eq_family_of_inPlane hz (inPlane_smul _ hw)]
      simp only [familyM, W_H, H_smul]
    _ = _ := native_response _ _

/-- A global formula retains the actual pair-selected transport. -/
theorem G_eq_nativeG_transport (x y : Vec) :
    G x y = nativeG (H (-parameter x y) x) (H (-parameter x y) y) :=
  G_inPlane (inPlane_left x y) (inPlane_right x y)

theorem G_symmetric (x y : Vec) : G x y = G y x := by
  rw [G_inPlane (inPlane_left x y) (inPlane_right x y),
    G_inPlane (inPlane_right x y) (inPlane_left x y), nativeG_symmetric]

theorem G_diagonal (x : Vec) : G x x = W x := by
  rw [G_eq_nativeG_transport, nativeG_diagonal, W_H]

@[simp] theorem G_zero_left (x : Vec) : G 0 x = 0 := by
  rw [G_eq_nativeG_transport, H_zero, nativeG_zero_left]

@[simp] theorem G_zero_right (x : Vec) : G x 0 = 0 := by
  rw [G_symmetric, G_zero_left]

/-- Real homogeneity is proved using the original pair's plane even at r=0. -/
theorem G_real_smul_left (r : ℝ) (x y : Vec) :
    G ((r : ℂ) • x) y = r * G x y := by
  rw [G_inPlane (inPlane_smul (r : ℂ) (inPlane_left x y)) (inPlane_right x y),
    H_smul, nativeG_real_smul_left,
    G_inPlane (inPlane_left x y) (inPlane_right x y)]

theorem G_real_smul_right (r : ℝ) (x y : Vec) :
    G x ((r : ℂ) • y) = r * G x y := by
  rw [G_symmetric, G_real_smul_left, G_symmetric y x]

theorem radicand_eq (x y : Vec) :
    W x + W y - 2 * G x y =
      2 * W (RawPlanePhaseControl.m x ((-Complex.I) • y)) := by
  unfold G
  ring

theorem radicand_nonnegative (x y : Vec) : 0 ≤ W x + W y - 2 * G x y := by
  rw [radicand_eq]
  exact mul_nonneg (by norm_num) (W_nonnegative _)

theorem d_nonnegative (x y : Vec) : 0 ≤ d x y := Real.sqrt_nonneg _

theorem d_symmetric (x y : Vec) : d x y = d y x := by
  unfold d
  rw [G_symmetric x y, add_comm (W x) (W y)]

theorem d_sq (x y : Vec) : d x y ^ 2 = G x x + G y y - 2 * G x y := by
  rw [d, Real.sq_sqrt (radicand_nonnegative x y), G_diagonal, G_diagonal]

/-- The fixed native attenuations are adjoints for the coordinate form. -/
theorem nativeG_adjoint (x z : Vec) : nativeG (a • x) z = nativeG x (b • z) := by
  norm_num [nativeG, a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem G_adjoint (x z : Vec) :
    G (RawSparseConservationSelection.A RawPlanePhaseControl.contract x) z =
      G x (RawSparseConservationSelection.B RawPlanePhaseControl.contract z) := by
  rw [RawPlanePhaseControl.A_eq, RawPlanePhaseControl.B_eq]
  rw [G_inPlane (inPlane_smul a (inPlane_left x z)) (inPlane_right x z),
    G_inPlane (inPlane_left x z) (inPlane_smul b (inPlane_right x z)),
    H_smul, H_smul, nativeG_adjoint]

theorem attenuations_commute (x : Vec) :
    RawSparseConservationSelection.A RawPlanePhaseControl.contract
        (RawSparseConservationSelection.B RawPlanePhaseControl.contract x) =
      RawSparseConservationSelection.B RawPlanePhaseControl.contract
        (RawSparseConservationSelection.A RawPlanePhaseControl.contract x) := by
  simp only [RawPlanePhaseControl.A_eq, RawPlanePhaseControl.B_eq, smul_smul]
  rw [mul_comm]

/-- An exact sum gives a null vector of its coordinate Gram matrix. -/
theorem nativeG_sum_null (u v : Vec) :
    RawGramGeometry.quadratic nativeG ![u, v, u + v] ![1, 1, -1] = 0 := by
  simp [RawGramGeometry.quadratic, Fin.sum_univ_succ, nativeG_add_left,
    nativeG_add_right]
  ring

/-- The local output is transported to the exact native sum in one fixed plane. -/
theorem H_m (x y : Vec) :
    H (-parameter x y) (RawPlanePhaseControl.m x y) =
      native (H (-parameter x y) x) (H (-parameter x y) y) := by
  rw [RawPlanePhaseControl.m_eq_family_of_inPlane
    (inPlane_left x y) (inPlane_right x y), familyM, H_neg_H]

theorem mixer_null (x y : Vec) :
    RawGramGeometry.quadratic G
      ![RawSparseConservationSelection.A RawPlanePhaseControl.contract x,
        RawSparseConservationSelection.B RawPlanePhaseControl.contract y,
        RawSparseConservationSelection.m RawPlanePhaseControl.contract x y]
      ![1, 1, -1] = 0 := by
  simp only [RawPlanePhaseControl.A_eq, RawPlanePhaseControl.B_eq,
    RawPlanePhaseControl.contract_m]
  have hp (i : Fin 3) :
      InPlane x y (![a • x, b • y, RawPlanePhaseControl.m x y] i) := by
    fin_cases i
    · exact inPlane_smul a (inPlane_left x y)
    · exact inPlane_smul b (inPlane_right x y)
    · exact RawPlanePhaseControl.inPlane_m (inPlane_left x y) (inPlane_right x y)
  unfold RawGramGeometry.quadratic
  simp_rw [G_inPlane (hp _) (hp _)]
  have hn := nativeG_sum_null (a • H (-parameter x y) x) (b • H (-parameter x y) y)
  simpa only [RawGramGeometry.quadratic, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, H_smul, H_m, native] using hn

/-- The actual response satisfies precisely the local kernel bridge contract. -/
theorem localKernel :
    RawFourPointGramBridge.LocalKernel RawPlanePhaseControl.contract G where
  symmetric := G_symmetric
  diagonal := G_diagonal
  adjoint := G_adjoint
  mixer_null := mixer_null

/-- For this actual response, triangle inequality is exactly three-point positivity. -/
theorem triangle_iff_three_point :
    RawGramGeometry.Triangle d ↔ RawGramGeometry.GramNonnegative G 3 := by
  exact RawGramGeometry.triangle_iff_three_point G_symmetric
    (fun r x => (r : ℂ) • x) G_real_smul_left d d_nonnegative d_sq

end
end IDT.QMClosure.RawPlanePhaseGramKernel
