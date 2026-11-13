import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniformly bounded even traces on a real plane

These are conditional real two-dimensional matrix theorems. A single upper
bound on every even-power trace of a determinant-minus-one matrix forces its
trace to vanish. A subsequent algebraic corollary constructs a positive
invariant quadratic form from explicitly supplied trace and determinant data.
The hypotheses concern actual nonnegative integer powers and one uniform
upper bound. This module supplies no physical interpretation or state-space
boundedness premise.
-/

namespace IDT.QMClosure.BoundedPlaneTraceRigidity

noncomputable section

abbrev PlaneMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- A trace-type recurrence at parameter at least two grows at least linearly.
The same induction records positivity and a uniform lower bound on increments. -/
theorem recurrence_growth (c : ℕ → ℝ) (tau : ℝ)
    (htau : 2 ≤ tau) (hzero : c 0 = 2) (hone : c 1 = tau)
    (hrec : ∀ n, c (n + 2) = tau * c (n + 1) - c n) :
    ∀ n, 2 ≤ c n ∧ tau - 2 ≤ c (n + 1) - c n ∧
      2 + (n : ℝ) * (tau - 2) ≤ c n := by
  intro n
  induction n with
  | zero => simp [hzero, hone]
  | succ n ih =>
    obtain ⟨hcn, hdelta, hgrowth⟩ := ih
    have hnext : 2 ≤ c (n + 1) := by linarith
    have hmul : 0 ≤ (tau - 2) * c (n + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hdelta_next : tau - 2 ≤ c (n + 2) - c (n + 1) := by
      rw [hrec]
      nlinarith
    refine ⟨hnext, ?_, ?_⟩
    · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hdelta_next
    · push_cast
      nlinarith

/-- One upper bound for the entire recurrence forces the threshold parameter. -/
theorem bounded_recurrence_forces_two (c : ℕ → ℝ) (tau : ℝ)
    (htau : 2 ≤ tau) (hzero : c 0 = 2) (hone : c 1 = tau)
    (hrec : ∀ n, c (n + 2) = tau * c (n + 1) - c n)
    (hbounded : ∃ C : ℝ, ∀ n, c n ≤ C) : tau = 2 := by
  obtain ⟨C, hC⟩ := hbounded
  by_contra hne
  have hpos : 0 < tau - 2 := by
    by_contra h
    apply hne
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - 2) / (tau - 2))
  have hlarge : C - 2 < (n : ℝ) * (tau - 2) :=
    (div_lt_iff₀ hpos).mp hn
  have hsmall := (recurrence_growth c tau htau hzero hone hrec n).2.2
  have hupper := hC n
  linarith

/-- Cayley-Hamilton for real two-by-two matrices, checked entrywise. -/
theorem cayley_hamilton_two (A : PlaneMatrix) :
    A ^ 2 = Matrix.trace A • A - Matrix.det A • (1 : PlaneMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem trace_square (A : PlaneMatrix) :
    Matrix.trace (A ^ 2) = Matrix.trace A ^ 2 - 2 * Matrix.det A := by
  simp [pow_two, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- A nonidentity real two-by-two matrix of order three has its trace and
determinant forced by the finite power relation alone. -/
theorem trace_det_of_order_three (T : PlaneMatrix)
    (hcube : T ^ 3 = 1) (hnontrivial : T ≠ 1) :
    Matrix.trace T = -1 ∧ Matrix.det T = 1 := by
  have hdetcube : Matrix.det T ^ 3 = 1 := by
    simpa only [Matrix.det_pow, Matrix.det_one] using congrArg Matrix.det hcube
  have hdet : Matrix.det T = 1 :=
    (show Odd 3 from by decide).pow_injective (by simpa only [one_pow] using hdetcube)
  let tau := Matrix.trace T
  have hCH : T ^ 2 = tau • T - (1 : PlaneMatrix) := by
    simpa only [tau, hdet, one_smul] using cayley_hamilton_two T
  have hexpand : T ^ 3 = (tau ^ 2 - 1) • T - tau • (1 : PlaneMatrix) := by
    calc
      T ^ 3 = T ^ 2 * T := by rw [pow_succ]
      _ = (tau • T - 1) * T := by rw [hCH]
      _ = tau • (T * T) - T := by rw [sub_mul, smul_mul_assoc, one_mul]
      _ = tau • (tau • T - 1) - T := by rw [← pow_two, hCH]
      _ = (tau ^ 2 - 1) • T - tau • (1 : PlaneMatrix) := by module
  have hscalar : tau ^ 3 - 3 * tau = 2 := by
    have h := congrArg Matrix.trace hexpand
    rw [hcube] at h
    simp only [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_one, Fintype.card_fin] at h
    norm_num at h
    nlinarith
  have hfactor : (tau - 2) * (tau + 1) ^ 2 = 0 := by nlinarith [hscalar]
  have hnot_two : tau ≠ 2 := by
    intro htwo
    apply hnontrivial
    ext i j
    have hij := congrArg (fun M : PlaneMatrix => M i j) hexpand
    rw [hcube] at hij
    change (1 : PlaneMatrix) i j =
      (tau ^ 2 - 1) * T i j - tau * (1 : PlaneMatrix) i j at hij
    rw [htwo] at hij
    nlinarith
  have htrace : tau = -1 := by
    rcases mul_eq_zero.mp hfactor with htwo | hminus
    · exact False.elim (hnot_two (sub_eq_zero.mp htwo))
    · have hplus : tau + 1 = 0 := by nlinarith [sq_nonneg (tau + 1)]
      linarith
  exact ⟨htrace, hdet⟩

/-- Determinant one gives the scalar trace recurrence on nonnegative powers. -/
theorem det_one_trace_recurrence (B : PlaneMatrix) (hdet : Matrix.det B = 1)
    (n : ℕ) :
    Matrix.trace (B ^ (n + 2)) =
      Matrix.trace B * Matrix.trace (B ^ (n + 1)) - Matrix.trace (B ^ n) := by
  have hCH : B ^ 2 = Matrix.trace B • B - (1 : PlaneMatrix) := by
    simpa only [hdet, one_smul] using cayley_hamilton_two B
  have hp : B ^ (n + 2) = Matrix.trace B • B ^ (n + 1) - B ^ n := by
    calc
      B ^ (n + 2) = B ^ 2 * B ^ n := by rw [← pow_add]; congr 1; omega
      _ = (Matrix.trace B • B - 1) * B ^ n := by rw [hCH]
      _ = Matrix.trace B • (B * B ^ n) - B ^ n := by
        rw [sub_mul, smul_mul_assoc, one_mul]
      _ = Matrix.trace B • B ^ (n + 1) - B ^ n := by rw [← pow_succ']
  simpa only [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] using
    congrArg Matrix.trace hp

/-- A nonzero trace creates an explicit quadratic-in-trace linear growth rate. -/
theorem even_trace_growth_of_det_neg_one (A : PlaneMatrix)
    (hdet : Matrix.det A = -1) (n : ℕ) :
    2 + (n : ℝ) * Matrix.trace A ^ 2 ≤ Matrix.trace (A ^ (2 * n)) := by
  let B := A ^ 2
  have hBdet : Matrix.det B = 1 := by simp [B, Matrix.det_pow, hdet]
  have htau : Matrix.trace B = Matrix.trace A ^ 2 + 2 := by
    dsimp [B]
    rw [trace_square, hdet]
    ring
  have htau_ge : 2 ≤ Matrix.trace B := by
    rw [htau]
    nlinarith [sq_nonneg (Matrix.trace A)]
  have hzero : Matrix.trace (B ^ 0) = 2 := by simp [Matrix.trace_one]
  have hone : Matrix.trace (B ^ 1) = Matrix.trace B := by simp
  have hgrowth :=
    (recurrence_growth (fun k => Matrix.trace (B ^ k)) (Matrix.trace B)
      htau_ge hzero hone (det_one_trace_recurrence B hBdet) n).2.2
  simpa only [htau, add_sub_cancel_right, B, ← pow_mul] using hgrowth

/-- The upper bound is one constant shared by all even-power traces. -/
theorem trace_zero_of_bounded_even_powers (A : PlaneMatrix)
    (hdet : Matrix.det A = -1)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, Matrix.trace (A ^ (2 * n)) ≤ C) :
    Matrix.trace A = 0 := by
  let B := A ^ 2
  have hBdet : Matrix.det B = 1 := by simp [B, Matrix.det_pow, hdet]
  have htau : Matrix.trace B = Matrix.trace A ^ 2 + 2 := by
    dsimp [B]
    rw [trace_square, hdet]
    ring
  have htau_ge : 2 ≤ Matrix.trace B := by
    rw [htau]
    nlinarith [sq_nonneg (Matrix.trace A)]
  have hzero : Matrix.trace (B ^ 0) = 2 := by simp [Matrix.trace_one]
  have hone : Matrix.trace (B ^ 1) = Matrix.trace B := by simp
  have hBbounded : ∃ C : ℝ, ∀ n : ℕ, Matrix.trace (B ^ n) ≤ C := by
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, fun n => ?_⟩
    simpa only [B, ← pow_mul] using hC n
  have htwo := bounded_recurrence_forces_two
    (fun n => Matrix.trace (B ^ n)) (Matrix.trace B) htau_ge hzero hone
    (det_one_trace_recurrence B hBdet) hBbounded
  nlinarith [sq_nonneg (Matrix.trace A)]

/-- The same determinant and uniform bound force an involution. -/
theorem square_eq_one_of_bounded_even_powers (A : PlaneMatrix)
    (hdet : Matrix.det A = -1)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, Matrix.trace (A ^ (2 * n)) ≤ C) :
    A ^ 2 = 1 := by
  have htrace := trace_zero_of_bounded_even_powers A hdet hbounded
  simpa only [htrace, hdet, zero_smul, neg_smul, one_smul, sub_neg_eq_add,
    zero_add] using cayley_hamilton_two A

/-- Combining an order-three factor with the forced product involution gives
an exact reflected power relation. -/
theorem reflected_cube_relation_of_bounded_traces (J T : PlaneMatrix)
    (hcube : T ^ 3 = 1) (hdet : Matrix.det (J * T) = -1)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, Matrix.trace ((J * T) ^ (2 * n)) ≤ C) :
    J * T * J = T ^ 2 := by
  have hprod := square_eq_one_of_bounded_even_powers (J * T) hdet hbounded
  have h := congrArg (fun M : PlaneMatrix => M * T ^ 2) hprod
  change (J * T) ^ 2 * T ^ 2 = (1 : PlaneMatrix) * T ^ 2 at h
  have hassoc : (J * T) ^ 2 * T ^ 2 = (J * T * J) * T ^ 3 := by noncomm_ring
  rw [hassoc, hcube, mul_one, one_mul] at h
  exact h

def reflection : PlaneMatrix := !![1, 0; 0, -1]

def planeQuadratic (b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  v 0 ^ 2 - (b / c) * v 1 ^ 2

theorem positive_weight_of_product (b c : ℝ) (hbc : b * c = -3 / 4) :
    0 < -b / c := by
  have hc : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hbc
    norm_num at hbc
  have hc2 : 0 < c * c := mul_self_pos.mpr hc
  have hweight : (-b / c) * (c * c) = 3 / 4 := by
    calc
      (-b / c) * (c * c) = -(b * c) := by field_simp [hc]
      _ = 3 / 4 := by rw [hbc]; ring
  by_contra h
  have hnonpos : (-b / c) * (c * c) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_lt hc2)
  linarith

theorem planeQuadratic_positive (b c : ℝ) (hweight : 0 < -b / c)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) : 0 < planeQuadratic b c v := by
  have hQ : planeQuadratic b c v = v 0 ^ 2 + (-b / c) * v 1 ^ 2 := by
    unfold planeQuadratic
    ring
  rw [hQ]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp_all
    have hpos := mul_pos hweight (sq_pos_of_ne_zero h1)
    simpa [h0] using hpos
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0)
      (mul_nonneg (le_of_lt hweight) (sq_nonneg (v 1)))

theorem planeQuadratic_invariant_of_coefficients (b c : ℝ)
    (hbc : b * c = -3 / 4) (v : Fin 2 → ℝ) :
    planeQuadratic b c ((!![-1 / 2, b; c, -1 / 2] : PlaneMatrix).mulVec v) =
      planeQuadratic b c v := by
  have hc : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hbc
    norm_num at hbc
  have hfactor :
      planeQuadratic b c ((!![-1 / 2, b; c, -1 / 2] : PlaneMatrix).mulVec v) -
        planeQuadratic b c v =
      (b * c + 3 / 4) * (-(v 0 ^ 2) + (b / c) * v 1 ^ 2) := by
    simp [planeQuadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hc]
    ring
  have hzero : b * c + 3 / 4 = 0 := by rw [hbc]; norm_num
  rw [hzero, zero_mul] at hfactor
  exact sub_eq_zero.mp hfactor

/-- Supplied trace-minus-one and determinant-one data, together with bounded
reflection-product traces, determine the diagonal and an invariant positive form. -/
theorem trace_det_reflection_corollary (a b c d : ℝ)
    (htrace : Matrix.trace (!![a, b; c, d] : PlaneMatrix) = -1)
    (hdet : Matrix.det (!![a, b; c, d] : PlaneMatrix) = 1)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ,
      Matrix.trace ((reflection * (!![a, b; c, d] : PlaneMatrix)) ^ (2 * n)) ≤ C) :
    a = -1 / 2 ∧ d = -1 / 2 ∧ b * c = -3 / 4 ∧ 0 < -b / c ∧
      (∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < planeQuadratic b c v) ∧
      (∀ v : Fin 2 → ℝ,
        planeQuadratic b c ((!![a, b; c, d] : PlaneMatrix).mulVec v) =
          planeQuadratic b c v) := by
  have hprod_det : Matrix.det (reflection * (!![a, b; c, d] : PlaneMatrix)) = -1 := by
    rw [Matrix.det_mul, hdet]
    simp [reflection, Matrix.det_fin_two]
  have hprod_trace := trace_zero_of_bounded_even_powers
    (reflection * (!![a, b; c, d] : PlaneMatrix)) hprod_det hbounded
  have hsum : a + d = -1 := by simpa using htrace
  have hdiff : a - d = 0 := by
    simpa [reflection, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
      sub_eq_add_neg] using hprod_trace
  have ha : a = -1 / 2 := by linarith
  have hd : d = -1 / 2 := by linarith
  have hbc : b * c = -3 / 4 := by
    have hdetscalar : a * d - b * c = 1 := by simpa only [Matrix.det_fin_two_of] using hdet
    nlinarith
  have hweight := positive_weight_of_product b c hbc
  refine ⟨ha, hd, hbc, hweight, planeQuadratic_positive b c hweight, ?_⟩
  intro v
  rw [ha, hd]
  exact planeQuadratic_invariant_of_coefficients b c hbc v

/-- Finite order three and the uniform reflected even-trace bound suffice
for the positive invariant plane form. Trace and determinant are derived. -/
theorem order_three_reflection_corollary (a b c d : ℝ)
    (hcube : (!![a, b; c, d] : PlaneMatrix) ^ 3 = 1)
    (hnontrivial : (!![a, b; c, d] : PlaneMatrix) ≠ 1)
    (hbounded : ∃ C : ℝ, ∀ n : ℕ,
      Matrix.trace ((reflection * (!![a, b; c, d] : PlaneMatrix)) ^ (2 * n)) ≤ C) :
    a = -1 / 2 ∧ d = -1 / 2 ∧ b * c = -3 / 4 ∧ 0 < -b / c ∧
      (∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < planeQuadratic b c v) ∧
      (∀ v : Fin 2 → ℝ,
        planeQuadratic b c ((!![a, b; c, d] : PlaneMatrix).mulVec v) =
          planeQuadratic b c v) := by
  obtain ⟨htrace, hdet⟩ :=
    trace_det_of_order_three (!![a, b; c, d] : PlaneMatrix) hcube hnontrivial
  exact trace_det_reflection_corollary a b c d htrace hdet hbounded

end

end IDT.QMClosure.BoundedPlaneTraceRigidity
