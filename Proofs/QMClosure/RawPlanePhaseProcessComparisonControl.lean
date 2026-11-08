import Proofs.QMClosure.RawProcessComparisonBridge
import Proofs.QMClosure.RawPlanePhaseLocalMidpointControl

/-!
# Additive external comparison fails in the actual plane control

The supplied lambda-one operation preserves its complete scalar weight.
Its additive two-port comparison built from the external response kernel
nevertheless increases on an exact rational witness. The comparison calibration,
residual, and selected-orbit formulas concern this mathematical control only.
-/

namespace IDT.QMClosure.RawPlanePhaseProcessComparisonControl

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open RawPlanePhaseGramControl RawPlanePhaseMidpointControl
open RawPlanePhaseLocalMidpointControl RawMidpointGramGeometry
open RawProcessComparisonBridge

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

abbrev Q : Vec → Vec → ℝ := squaredDistance G

def quarter (x : Vec) : Vec := Complex.I • x

def attenuate (x : Vec) : Vec := b • x

def comparison (p q : Vec × Vec) : ℝ := pairComparison Q p q

theorem Q_symmetric (x y : Vec) : Q x y = Q y x := by
  unfold Q squaredDistance
  rw [G_symmetric x y]
  ring

theorem G_complex_smul (c : ℂ) (x y : Vec) :
    G (c • x) (c • y) = Complex.normSq c * G x y := by
  have hphase : (-Complex.I) • (c • y) = c • ((-Complex.I) • y) := by
    simp only [smul_smul]
    rw [mul_comm (-Complex.I) c]
  unfold G
  rw [hphase, RawPlanePhaseControl.m_smul]
  simp only [W_smul]
  ring

theorem Q_complex_smul (c : ℂ) (x y : Vec) :
    Q (c • x) (c • y) = Complex.normSq c * Q x y := by
  unfold Q squaredDistance
  rw [G_complex_smul, G_complex_smul, G_complex_smul]
  ring

theorem quarter_comparison (x y : Vec) : Q (quarter x) (quarter y) = Q x y := by
  simpa [quarter] using Q_complex_smul Complex.I x y

theorem attenuate_comparison (x y : Vec) :
    Q (attenuate x) (attenuate y) = Q x y / 2 := by
  rw [attenuate, attenuate, Q_complex_smul]
  norm_num [b, NativeAttenuationCircuit.b, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]
  ring

private theorem m_common_line (z : Vec) (c d : ℂ) :
    RawPlanePhaseControl.m (c • z) (d • z) = (a * c + b * d) • z := by
  have hw : wedge (c • z) (d • z) = 0 := by
    funext i
    fin_cases i <;> simp [wedge, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [RawPlanePhaseControl.m, familyM_of_dependent _ hw, native_smul_same]

theorem operation_reference (z : Vec) :
    RawPlanePhaseControl.operation (z, quarter z) = ((1 + Complex.I) • z, 0) := by
  have hfirst := m_common_line z 1 Complex.I
  have hsecond := m_common_line z Complex.I 1
  have hc : a * 1 + b * Complex.I = 1 + Complex.I := by
    apply Complex.ext <;>
      norm_num [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hd : a * Complex.I + b * 1 = 0 := by
    apply Complex.ext <;>
      norm_num [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  simp only [one_smul, hc, hd, zero_smul] at hfirst hsecond
  exact Prod.ext hfirst hsecond

theorem reference_calibration (z : Vec) :
    attenuate (RawPlanePhaseControl.operation (z, quarter z)).1 = z := by
  rw [operation_reference]
  unfold attenuate
  rw [smul_smul]
  have hc : b * (1 + Complex.I) = 1 := by
    apply Complex.ext <;>
      norm_num [b, NativeAttenuationCircuit.b, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  rw [hc, one_smul]

theorem midpoint_calibration (x y : Vec) :
    attenuate (RawPlanePhaseControl.operation (x, quarter y)).1 = mid x y := rfl

theorem Q_zero (x : Vec) : Q x 0 = W x := by
  simp [Q, squaredDistance, G_diagonal]

theorem Q_response (x y : Vec) :
    Q x y = 2 * W (RawPlanePhaseControl.m x ((-Complex.I) • y)) := by
  unfold Q squaredDistance
  rw [G_diagonal, G_diagonal, radicand_eq]

/-- The unused port carries half the endpoint comparison. -/
theorem residual_comparison (x y : Vec) :
    Q (RawPlanePhaseControl.operation (x, quarter y)).2 0 = Q x y / 2 := by
  have hi : Complex.I • ((-Complex.I) • x) = x := by
    simp only [smul_smul]
    simp
  have hm : RawPlanePhaseControl.m (quarter y) x =
      Complex.I • RawPlanePhaseControl.m y ((-Complex.I) • x) := by
    simpa only [quarter, hi] using
      RawPlanePhaseControl.m_smul Complex.I y ((-Complex.I) • x)
  change Q (RawPlanePhaseControl.m (quarter y) x) 0 = Q x y / 2
  rw [Q_zero, hm, W_smul]
  have hq := Q_response y x
  rw [Q_symmetric y x] at hq
  norm_num at *
  linarith

theorem comparison_input (x y z : Vec) :
    comparison (x, quarter y) (z, quarter z) = Q z x + Q z y := by
  simp only [comparison, pairComparison, quarter_comparison]
  rw [Q_symmetric x z, Q_symmetric y z]

theorem comparison_output (x y z : Vec) :
    comparison (RawPlanePhaseControl.operation (x, quarter y))
      (RawPlanePhaseControl.operation (z, quarter z)) =
        2 * Q z (mid x y) + Q x y / 2 := by
  have hfirst := attenuate_comparison
    (RawPlanePhaseControl.operation (x, quarter y)).1
    (RawPlanePhaseControl.operation (z, quarter z)).1
  rw [midpoint_calibration, reference_calibration, Q_symmetric (mid x y) z] at hfirst
  unfold comparison pairComparison
  rw [operation_reference]
  have hres := residual_comparison x y
  change Q (RawPlanePhaseControl.operation (x, quarter y)).2 0 = Q x y / 2 at hres
  rw [hres]
  have href := operation_reference z
  have hfst := congrArg Prod.fst href
  change (RawPlanePhaseControl.operation (z, quarter z)).1 = (1 + Complex.I) • z at hfst
  rw [hfst] at hfirst
  linarith

theorem comparison_defect (x y z : Vec) :
    comparison (RawPlanePhaseControl.operation (x, quarter y))
        (RawPlanePhaseControl.operation (z, quarter z)) -
      comparison (x, quarter y) (z, quarter z) =
        2 * (Q z (mid x y) - (Q z x + Q z y) / 2) + Q x y / 2 := by
  rw [comparison_output, comparison_input]
  ring

theorem selected_endpoint_comparison (e : ℝ) :
    Q (scale e fourX) (scale e fourY) = 2 * e ^ 2 := by
  rcases four_cross_entries with ⟨hxy, _, _, _, _, _⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, _, _⟩
  unfold Q
  rw [squaredDistance_scale, hxx, hyy, hxy]
  ring

theorem selected_input_exact (t e : ℝ) :
    comparison (scale e fourX, quarter (scale e fourY))
      (scale t fourZ, quarter (scale t fourZ)) =
        4 * t ^ 2 + 2 * e ^ 2 - (8 / 5) * t * e := by
  rcases four_cross_entries with ⟨_, _, hxz, _, hyz, _⟩
  rcases four_diagonal_entries with ⟨hxx, hyy, _, hzz⟩
  rw [comparison_input]
  simp only [Q, squaredDistance_scale]
  rw [hzz, hxx, hyy, G_symmetric fourZ fourX, hxz, G_symmetric fourZ fourY, hyz]
  ring

theorem selected_defect_exact (t e : ℝ) :
    comparison (RawPlanePhaseControl.operation (scale e fourX, quarter (scale e fourY)))
        (RawPlanePhaseControl.operation (scale t fourZ, quarter (scale t fourZ))) -
      comparison (scale e fourX, quarter (scale e fourY))
        (scale t fourZ, quarter (scale t fourZ)) = -(2 / 5) * t * e := by
  rw [comparison_defect, selected_endpoint_comparison]
  have hs := selectedSlack_exact t e
  unfold selectedSlack at hs
  simp only [distance_square_eq] at hs
  change (Q (scale t fourZ) (scale e fourX) + Q (scale t fourZ) (scale e fourY)) / 2 -
    Q (scale t fourZ) (mid (scale e fourX) (scale e fourY)) = e ^ 2 / 2 + t * e / 5 at hs
  linarith

theorem selected_output_exact (t e : ℝ) :
    comparison (RawPlanePhaseControl.operation (scale e fourX, quarter (scale e fourY)))
      (RawPlanePhaseControl.operation (scale t fourZ, quarter (scale t fourZ))) =
        4 * t ^ 2 + 2 * e ^ 2 - 2 * t * e := by
  have hi := selected_input_exact t e
  have hd := selected_defect_exact t e
  linarith

theorem rational_witness :
    comparison (scale (1 / 5) fourX, quarter (scale (1 / 5) fourY))
        (scale (-1) fourZ, quarter (scale (-1) fourZ)) = 22 / 5 ∧
      comparison (RawPlanePhaseControl.operation
          (scale (1 / 5) fourX, quarter (scale (1 / 5) fourY)))
        (RawPlanePhaseControl.operation
          (scale (-1) fourZ, quarter (scale (-1) fourZ))) = 112 / 25 := by
  rw [selected_input_exact, selected_output_exact]
  norm_num

theorem not_pairComparisonNonexpanding :
    ¬ PairComparisonNonexpanding Q RawPlanePhaseControl.operation := by
  intro hgate
  have h := hgate (scale (1 / 5) fourX, quarter (scale (1 / 5) fourY))
    (scale (-1) fourZ, quarter (scale (-1) fourZ))
  change comparison _ _ ≤ comparison _ _ at h
  rcases rational_witness with ⟨hi, ho⟩
  rw [hi, ho] at h
  norm_num at h

/-- Every positive endpoint scale fails at this fixed reference. -/
theorem fixed_reference_defect_positive (e : ℝ) (he : 0 < e) :
    0 < comparison
        (RawPlanePhaseControl.operation (scale e fourX, quarter (scale e fourY)))
        (RawPlanePhaseControl.operation (scale (-1) fourZ, quarter (scale (-1) fourZ))) -
      comparison (scale e fourX, quarter (scale e fourY))
        (scale (-1) fourZ, quarter (scale (-1) fourZ)) := by
  rw [selected_defect_exact]
  nlinarith

/-- The selected weak Jensen inequality can pass while comparison increases. -/
theorem balanced_pass_with_comparison_increase (e : ℝ) (he : e ≠ 0) :
    0 < selectedSlack (-e) e ∧
      0 < comparison
          (RawPlanePhaseControl.operation (scale e fourX, quarter (scale e fourY)))
          (RawPlanePhaseControl.operation (scale (-e) fourZ, quarter (scale (-e) fourZ))) -
        comparison (scale e fourX, quarter (scale e fourY))
          (scale (-e) fourZ, quarter (scale (-e) fourZ)) := by
  refine ⟨(balanced_selected_slacks_positive e he).2, ?_⟩
  rw [selected_defect_exact]
  nlinarith [sq_pos_of_ne_zero he]

end
end IDT.QMClosure.RawPlanePhaseProcessComparisonControl
