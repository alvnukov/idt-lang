import Proofs.QMClosure.RawPlanePhaseGramKernel

/-!
# Real amplitudes of the ordinary-plane phase deformation

The operation and its response are evaluated on the supplied mathematical
carrier. The parameter is a real coefficient of the pair's ordinary plane.
-/

namespace IDT.QMClosure.RawPlanePhaseParameterFamily

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def m (l : ℝ) (x y : Vec) : Vec := familyM (l * parameter x y) x y

def G (l : ℝ) (x y : Vec) : ℝ :=
  (W x + W y - 2 * W (m l x ((-Complex.I) • y))) / 2

def d (l : ℝ) (x y : Vec) : ℝ := Real.sqrt (W x + W y - 2 * G l x y)

theorem m_eq_family_of_inPlane (l : ℝ) {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    m l z w = familyM (l * parameter x y) z w := by
  unfold m
  rcases parameter_eq_or_dependent hz hw with hp | hd
  · rw [hp]
  · rw [familyM_of_dependent _ hd, familyM_of_dependent _ hd]

theorem G_inPlane (l : ℝ) {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    G l z w = nativeG (H (-(l * parameter x y)) z)
      (H (-(l * parameter x y)) w) := by
  calc
    G l z w =
        (W (H (-(l * parameter x y)) z) + W (H (-(l * parameter x y)) w) -
          2 * W (native (H (-(l * parameter x y)) z)
            ((-Complex.I) • H (-(l * parameter x y)) w))) / 2 := by
      unfold G
      rw [m_eq_family_of_inPlane l hz (inPlane_smul _ hw)]
      simp only [familyM, W_H, H_smul]
    _ = _ := native_response _ _

theorem G_eq_nativeG_transport (l : ℝ) (x y : Vec) :
    G l x y = nativeG (H (-(l * parameter x y)) x)
      (H (-(l * parameter x y)) y) :=
  G_inPlane l (inPlane_left x y) (inPlane_right x y)

theorem G_symmetric (l : ℝ) (x y : Vec) : G l x y = G l y x := by
  rw [G_inPlane l (inPlane_left x y) (inPlane_right x y),
    G_inPlane l (inPlane_right x y) (inPlane_left x y), nativeG_symmetric]

theorem G_diagonal (l : ℝ) (x : Vec) : G l x x = W x := by
  rw [G_eq_nativeG_transport, nativeG_diagonal, W_H]

theorem G_real_smul_left (l r : ℝ) (x y : Vec) :
    G l ((r : ℂ) • x) y = r * G l x y := by
  rw [G_inPlane l (inPlane_smul (r : ℂ) (inPlane_left x y)) (inPlane_right x y),
    H_smul, nativeG_real_smul_left,
    G_inPlane l (inPlane_left x y) (inPlane_right x y)]

theorem G_real_smul_right (l r : ℝ) (x y : Vec) :
    G l x ((r : ℂ) • y) = r * G l x y := by
  rw [G_symmetric, G_real_smul_left, G_symmetric l y x]

theorem radicand_eq (l : ℝ) (x y : Vec) :
    W x + W y - 2 * G l x y = 2 * W (m l x ((-Complex.I) • y)) := by
  unfold G
  ring

theorem radicand_nonnegative (l : ℝ) (x y : Vec) :
    0 ≤ W x + W y - 2 * G l x y := by
  rw [radicand_eq]
  exact mul_nonneg (by norm_num) (W_nonnegative _)

theorem d_nonnegative (l : ℝ) (x y : Vec) : 0 ≤ d l x y := Real.sqrt_nonneg _

theorem d_sq (l : ℝ) (x y : Vec) :
    d l x y ^ 2 = G l x x + G l y y - 2 * G l x y := by
  rw [d, Real.sq_sqrt (radicand_nonnegative l x y), G_diagonal, G_diagonal]

theorem triangle_iff_three_point (l : ℝ) :
    RawGramGeometry.Triangle (d l) ↔ RawGramGeometry.GramNonnegative (G l) 3 :=
  RawGramGeometry.triangle_iff_three_point (G_symmetric l)
    (fun r x => (r : ℂ) • x) (G_real_smul_left l) (d l) (d_nonnegative l) (d_sq l)

@[simp] theorem G_zero_parameter (x y : Vec) : G 0 x y = nativeG x y := by
  rw [G_eq_nativeG_transport]
  simp only [zero_mul, neg_zero, H_zero_parameter]

theorem nativeG_gram_nonnegative (n : ℕ) :
    RawGramGeometry.GramNonnegative nativeG n := by
  intro p c
  have he : RawGramGeometry.quadratic nativeG p c =
      (∑ i, c i * (p i 0).re) ^ 2 + (∑ i, c i * (p i 0).im) ^ 2 +
      (∑ i, c i * (p i 1).re) ^ 2 + (∑ i, c i * (p i 1).im) ^ 2 +
      (∑ i, c i * (p i 2).re) ^ 2 + (∑ i, c i * (p i 2).im) ^ 2 := by
    simp only [RawGramGeometry.quadratic, nativeG, pow_two]
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  positivity

theorem zero_parameter_gram_nonnegative (n : ℕ) :
    RawGramGeometry.GramNonnegative (G 0) n := by
  intro p c
  simpa only [RawGramGeometry.quadratic, G_zero_parameter] using
    nativeG_gram_nonnegative n p c

end
end IDT.QMClosure.RawPlanePhaseParameterFamily
