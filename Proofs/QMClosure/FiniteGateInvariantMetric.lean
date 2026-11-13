import Proofs.QMClosure.FiniteGateFrameCoordinates
import Proofs.QMClosure.FiniteGatePreparationBounds
import Proofs.QMClosure.BoundedPlaneTraceRigidity

/-!
# Positive spatial quadratic form assembled from finite gate premises

The coordinate package is constructed from the frame. Binary preparation
bounds supply the uniform reflected-matrix trace bound. The finite order-three
relation then fixes the transverse coefficients and gives a positive spatial
quadratic form invariant under all four actual gates. Its positivity statement
applies to the kernel of the supplied normalization functional. The quadratic
form vanishes on the normalization line in the full four-dimensional envelope.
No ball closure, physical origin, or quantum-mechanical completeness follows.
-/

namespace IDT.QMClosure.FiniteGateFrameCoordinates.AxisCoordinates

open FiniteGateFrameDimension FiniteGateFrameCoordinates BoundedPlaneTraceRigidity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable section

variable {F : Frame V} (C : FiniteGateFrameCoordinates.AxisCoordinates F)

def transverseMatrix : PlaneMatrix := !![C.a, C.b; C.c, C.d]

theorem transverseMatrix_action (w : Fin 2 → ℝ) :
    C.transverseMatrix.mulVec w = block C.a C.b C.c C.d w := by
  ext i
  fin_cases i <;>
    simp [transverseMatrix, block, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem transverseMatrix_cube : C.transverseMatrix ^ 3 = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [Matrix.one_mulVec]
  simp only [pow_succ', pow_zero, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transverseMatrix_action]
  exact C.transverse_cube w

theorem transverseMatrix_nontrivial : C.transverseMatrix ≠ 1 := by
  intro h
  apply C.transverse_nontrivial
  apply LinearMap.ext
  intro w
  change block C.a C.b C.c C.d w = w
  rw [← C.transverseMatrix_action, h, Matrix.one_mulVec]

def reflectedMatrix : PlaneMatrix := reflection * C.transverseMatrix

def planeEmbed (w : Fin 2 → ℝ) : V := C.equiv.symm (quad 0 (w 0) (w 1) 0)

def coordinateFunctional (i : Fin 4) : V →ₗ[ℝ] ℝ where
  toFun v := C.equiv v i
  map_add' v w := by simp
  map_smul' r v := by simp

abbrev reflectedGate : Module.End ℝ V := F.Jx.comp F.T

theorem reflected_gate_coordinates (v : V) :
    C.equiv (reflectedGate (F := F) v) =
      quad (C.equiv v 0) (C.a * C.equiv v 1 + C.b * C.equiv v 2)
        (-(C.c * C.equiv v 1 + C.d * C.equiv v 2)) (-C.equiv v 3) := by
  change C.equiv (F.Jx (F.T v)) = _
  rw [C.Jx_action]
  simp only [C.T_action, quad_zero, quad_one, quad_two, quad_three]

theorem planeEmbed_reflected_action (w : Fin 2 → ℝ) :
    reflectedGate (F := F) (C.planeEmbed w) =
      C.planeEmbed (C.reflectedMatrix.mulVec w) := by
  apply C.equiv.injective
  rw [C.reflected_gate_coordinates]
  ext i
  fin_cases i <;>
    simp [planeEmbed, reflectedMatrix, transverseMatrix, reflection,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

theorem planeEmbed_reflected_powers (n : ℕ) (w : Fin 2 → ℝ) :
    ((reflectedGate (F := F)) ^ n) (C.planeEmbed w) =
      C.planeEmbed ((C.reflectedMatrix ^ n).mulVec w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, C.planeEmbed_reflected_action]
    rw [pow_succ', ← Matrix.mulVec_mulVec]

/-- A single upper bound on every even trace is derived from the original
binary preparation premises and availability of the actual composed gate. -/
theorem reflected_trace_bound :
    ∃ B : ℝ, ∀ n : ℕ, Matrix.trace (C.reflectedMatrix ^ (2 * n)) ≤ B := by
  obtain ⟨B0, h0⟩ := FiniteGatePreparationBounds.Frame.JxT_orbit_bound F
    (C.coordinateFunctional 1) (C.planeEmbed ![1, 0])
  obtain ⟨B1, h1⟩ := FiniteGatePreparationBounds.Frame.JxT_orbit_bound F
    (C.coordinateFunctional 2) (C.planeEmbed ![0, 1])
  have hd0 (k : ℕ) : |(C.reflectedMatrix ^ k) 0 0| ≤ B0 := by
    have h := h0 k
    change |C.equiv (((reflectedGate (F := F)) ^ k) (C.planeEmbed ![1, 0])) 1| ≤ B0 at h
    rw [C.planeEmbed_reflected_powers] at h
    simpa [planeEmbed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hd1 (k : ℕ) : |(C.reflectedMatrix ^ k) 1 1| ≤ B1 := by
    have h := h1 k
    change |C.equiv (((reflectedGate (F := F)) ^ k) (C.planeEmbed ![0, 1])) 2| ≤ B1 at h
    rw [C.planeEmbed_reflected_powers] at h
    simpa [planeEmbed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  refine ⟨B0 + B1, fun n => ?_⟩
  rw [Matrix.trace_fin_two]
  have hb0 := hd0 (2 * n)
  have hb1 := hd1 (2 * n)
  linarith [le_abs_self ((C.reflectedMatrix ^ (2 * n)) 0 0),
    le_abs_self ((C.reflectedMatrix ^ (2 * n)) 1 1)]

/-- Shape, positive plane weight, and plane invariance all follow from the
frame. The reflected trace bound is an intermediate checked conclusion. -/
theorem transverse_metric_shape :
    C.a = -1 / 2 ∧ C.d = -1 / 2 ∧ C.b * C.c = -3 / 4 ∧ 0 < -C.b / C.c ∧
      (∀ w : Fin 2 → ℝ, w ≠ 0 → 0 < planeQuadratic C.b C.c w) ∧
      (∀ w : Fin 2 → ℝ,
        planeQuadratic C.b C.c (C.transverseMatrix.mulVec w) = planeQuadratic C.b C.c w) := by
  exact order_three_reflection_corollary C.a C.b C.c C.d
    C.transverseMatrix_cube C.transverseMatrix_nontrivial C.reflected_trace_bound

def planeWeight : ℝ := -C.b / C.c

theorem planeWeight_positive : 0 < C.planeWeight := C.transverse_metric_shape.2.2.2.1

theorem alphaWeight_positive : 0 < C.α ^ 2 := sq_pos_of_ne_zero C.alpha_ne_zero

/-- This spatial form is positive definite on the normalization kernel. -/
def spatialQuadratic (v : V) : ℝ :=
  (C.equiv v 1) ^ 2 + C.planeWeight * (C.equiv v 2) ^ 2 + C.α ^ 2 * (C.equiv v 3) ^ 2

theorem spatialQuadratic_nonnegative (v : V) : 0 ≤ C.spatialQuadratic v := by
  exact add_nonneg
    (add_nonneg (sq_nonneg (C.equiv v 1))
      (mul_nonneg C.planeWeight_positive.le (sq_nonneg (C.equiv v 2))))
    (mul_nonneg (sq_nonneg C.α) (sq_nonneg (C.equiv v 3)))

theorem spatialQuadratic_positive_on_kernel (v : V)
    (hu : F.normalization v = 0) (hv : v ≠ 0) : 0 < C.spatialQuadratic v := by
  have h0 : C.equiv v 0 = 0 := by rw [C.normalized, hu]
  have hw := C.planeWeight_positive
  have ha := C.alphaWeight_positive
  have hnx := sq_nonneg (C.equiv v 1)
  have hny := mul_nonneg hw.le (sq_nonneg (C.equiv v 2))
  have hnz := mul_nonneg ha.le (sq_nonneg (C.equiv v 3))
  by_contra h
  have hle : C.spatialQuadratic v ≤ 0 := le_of_not_gt h
  unfold spatialQuadratic at hle
  have hx : C.equiv v 1 = 0 := by nlinarith
  have hy : C.equiv v 2 = 0 := by
    by_contra hne
    have hpos := mul_pos hw (sq_pos_of_ne_zero hne)
    linarith
  have hz : C.equiv v 3 = 0 := by
    by_contra hne
    have hpos := mul_pos ha (sq_pos_of_ne_zero hne)
    linarith
  have hcoords : C.equiv v = 0 := by
    ext i
    fin_cases i <;> simp_all
  apply hv
  apply C.equiv.injective
  simpa only [map_zero] using hcoords

theorem spatialQuadratic_Jx (v : V) : C.spatialQuadratic (F.Jx v) = C.spatialQuadratic v := by
  simp [spatialQuadratic, C.Jx_action]

theorem spatialQuadratic_Jz (v : V) : C.spatialQuadratic (F.Jz v) = C.spatialQuadratic v := by
  simp [spatialQuadratic, C.Jz_action]

theorem spatialQuadratic_T (v : V) : C.spatialQuadratic (F.T v) = C.spatialQuadratic v := by
  have hplane := C.transverse_metric_shape.2.2.2.2.2 ![C.equiv v 1, C.equiv v 2]
  have hxy :
      (C.a * C.equiv v 1 + C.b * C.equiv v 2) ^ 2 +
        C.planeWeight * (C.c * C.equiv v 1 + C.d * C.equiv v 2) ^ 2 =
      (C.equiv v 1) ^ 2 + C.planeWeight * (C.equiv v 2) ^ 2 := by
    simpa [planeQuadratic, planeWeight, transverseMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, sub_eq_add_neg, neg_div] using hplane
  simp only [spatialQuadratic, C.T_action, quad_one, quad_two, quad_three]
  rw [hxy]

theorem spatialQuadratic_H (v : V) : C.spatialQuadratic (F.H v) = C.spatialQuadratic v := by
  have halpha : C.α ^ 2 * (C.α⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ C.alpha_ne_zero]
    norm_num
  simp only [spatialQuadratic, C.H_action, quad_one, quad_two, quad_three, mul_pow,
    C.beta_sq]
  linear_combination (C.equiv v 1) ^ 2 * halpha

end

end IDT.QMClosure.FiniteGateFrameCoordinates.AxisCoordinates

namespace IDT.QMClosure.FiniteGateInvariantMetric

open FiniteGateFrameDimension FiniteGateFrameCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable section

/-- The assembled metric data retain the constructed coordinates and the
explicit positivity domain. All invariance fields concern the actual gates. -/
structure InvariantMetricData (F : Frame V) where
  coordinates : FiniteGateFrameCoordinates.AxisCoordinates F
  a_eq : coordinates.a = -1 / 2
  d_eq : coordinates.d = -1 / 2
  bc_eq : coordinates.b * coordinates.c = -3 / 4
  plane_weight_positive : 0 < AxisCoordinates.planeWeight coordinates
  alpha_weight_positive : 0 < coordinates.α ^ 2
  nonnegative : ∀ v, 0 ≤ AxisCoordinates.spatialQuadratic coordinates v
  positive_on_kernel : ∀ v, F.normalization v = 0 → v ≠ 0 →
    0 < AxisCoordinates.spatialQuadratic coordinates v
  Jx_invariant : ∀ v,
    AxisCoordinates.spatialQuadratic coordinates (F.Jx v) = AxisCoordinates.spatialQuadratic coordinates v
  Jz_invariant : ∀ v,
    AxisCoordinates.spatialQuadratic coordinates (F.Jz v) = AxisCoordinates.spatialQuadratic coordinates v
  T_invariant : ∀ v,
    AxisCoordinates.spatialQuadratic coordinates (F.T v) = AxisCoordinates.spatialQuadratic coordinates v
  H_invariant : ∀ v,
    AxisCoordinates.spatialQuadratic coordinates (F.H v) = AxisCoordinates.spatialQuadratic coordinates v

end

end IDT.QMClosure.FiniteGateInvariantMetric

namespace IDT.QMClosure.FiniteGateFrameDimension.Frame

open IDT.QMClosure.FiniteGateInvariantMetric IDT.QMClosure.FiniteGateFrameCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The original frame premises construct positive spatial metric data without
any supplied coordinate basis, uniform trace bound, or finite-dimensional instance. -/
theorem exists_invariant_metric (F : Frame V) : Nonempty (InvariantMetricData F) := by
  obtain ⟨C⟩ := F.exists_axis_coordinates
  have hshape := AxisCoordinates.transverse_metric_shape C
  exact ⟨{
    coordinates := C
    a_eq := hshape.1
    d_eq := hshape.2.1
    bc_eq := hshape.2.2.1
    plane_weight_positive := AxisCoordinates.planeWeight_positive C
    alpha_weight_positive := AxisCoordinates.alphaWeight_positive C
    nonnegative := AxisCoordinates.spatialQuadratic_nonnegative C
    positive_on_kernel := AxisCoordinates.spatialQuadratic_positive_on_kernel C
    Jx_invariant := AxisCoordinates.spatialQuadratic_Jx C
    Jz_invariant := AxisCoordinates.spatialQuadratic_Jz C
    T_invariant := AxisCoordinates.spatialQuadratic_T C
    H_invariant := AxisCoordinates.spatialQuadratic_H C }⟩

end IDT.QMClosure.FiniteGateFrameDimension.Frame
