import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar and finite-matrix consequences used by a proposed atomicity route.
The graph-preserver Lie-group, reductivity, and highest-weight classification
bridges remain unformalized. These kernels carry no full atomicity conclusion. -/

namespace IDT.QMClosure.AtomicitySpectralBoundary

/-- Three distinct roots of this quadratic force its linear coefficient to vanish. -/
theorem three_weight_polynomial {a b d k l c : ℝ}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a ^ 2 * k + l = c * a)
    (hb : b ^ 2 * k + l = c * b)
    (hd : d ^ 2 * k + l = c * d) : c = 0 := by
  have hp : (a - b) * (k * (a + b) - c) = 0 := by nlinarith [ha, hb]
  have hq : (a - d) * (k * (a + d) - c) = 0 := by nlinarith [ha, hd]
  have hp' : k * (a + b) = c := by
    have := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab)
    linarith
  have hq' : k * (a + d) = c := by
    have := (mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr had)
    linarith
  have hk : k * (b - d) = 0 := by nlinarith [hp', hq']
  have hk' : k = 0 := (mul_eq_zero.mp hk).resolve_right (sub_ne_zero.mpr hbd)
  simpa [hk'] using hp'.symm

/-- The inverse-weight equations reduce to a quadratic after multiplying by the weight. -/
theorem three_boost_weights {a b d k l c : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a * k + a⁻¹ * l = c)
    (hb : b * k + b⁻¹ * l = c)
    (hd : d * k + d⁻¹ * l = c) : c = 0 := by
  apply three_weight_polynomial hab had hbd
  · have h := congrArg (fun x : ℝ => a * x) ha
    simpa [mul_add, ← mul_assoc, ha0, pow_two, mul_comm c a] using h
  · have h := congrArg (fun x : ℝ => b * x) hb
    simpa [mul_add, ← mul_assoc, hb0, pow_two, mul_comm c b] using h
  · have h := congrArg (fun x : ℝ => d * x) hd
    simpa [mul_add, ← mul_assoc, hd0, pow_two, mul_comm c d] using h

/-- On a nonempty finite matrix space the three-weight law excludes c ≠ 0. -/
theorem matrix_three_boost_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K L : Matrix ι ι ℝ) {a b d c : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a • K + a⁻¹ • L = c • (1 : Matrix ι ι ℝ))
    (hb : b • K + b⁻¹ • L = c • (1 : Matrix ι ι ℝ))
    (hd : d • K + d⁻¹ • L = c • (1 : Matrix ι ι ℝ)) : c = 0 := by
  classical
  let i : ι := Classical.choice inferInstance
  apply three_boost_weights ha0 hb0 hd0 hab had hbd
    (k := K i i) (l := L i i)
  · simpa using congrArg (fun M : Matrix ι ι ℝ => M i i) ha
  · simpa using congrArg (fun M : Matrix ι ι ℝ => M i i) hb
  · simpa using congrArg (fun M : Matrix ι ι ℝ => M i i) hd

/-- Two reciprocal weights greater and less than one force equal coefficients. -/
theorem reciprocal_boost_weights {r k l c : ℝ} (hr : 1 < r)
    (h₁ : r * k + r⁻¹ * l = c) (h₂ : r⁻¹ * k + r * l = c) :
    k = c / (r + r⁻¹) ∧ l = c / (r + r⁻¹) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hi : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hdiff : r - r⁻¹ ≠ 0 := by linarith
  have heq : (r - r⁻¹) * (k - l) = 0 := by nlinarith [h₁, h₂]
  have hkl : k = l := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hdiff)
  have hsum : r + r⁻¹ ≠ 0 := ne_of_gt (add_pos hr0 (inv_pos.mpr hr0))
  have hk : k = c / (r + r⁻¹) := by
    apply (eq_div_iff hsum).mpr
    nlinarith [h₁]
  exact ⟨hk, hkl.symm.trans hk⟩

/-- Entrywise application gives the full two-weight matrix identity. -/
theorem matrix_reciprocal_boost_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : Matrix ι ι ℝ) {r c : ℝ} (hr : 1 < r)
    (h₁ : r • K + r⁻¹ • L = c • (1 : Matrix ι ι ℝ))
    (h₂ : r⁻¹ • K + r • L = c • (1 : Matrix ι ι ℝ)) :
    K = (c / (r + r⁻¹)) • (1 : Matrix ι ι ℝ) ∧
    L = (c / (r + r⁻¹)) • (1 : Matrix ι ι ℝ) := by
  have entry (i j : ι) :
      K i j = (c * (1 : Matrix ι ι ℝ) i j) / (r + r⁻¹) ∧
      L i j = (c * (1 : Matrix ι ι ℝ) i j) / (r + r⁻¹) := by
    apply reciprocal_boost_weights hr
    · simpa using congrArg (fun M : Matrix ι ι ℝ => M i j) h₁
    · simpa using congrArg (fun M : Matrix ι ι ℝ => M i j) h₂
  constructor
  · ext i j
    simpa [div_mul_eq_mul_div] using (entry i j).1
  · ext i j
    simpa [div_mul_eq_mul_div] using (entry i j).2

/-- Exact numerical calibration for p = 3/4, q = 1/4, c = sqrt(3)/2. -/
theorem spinor_calibration :
    (1 / 4 : ℝ) < (3 - Real.sqrt 3) / 4 ∧
    (3 / 4 : ℝ) < Real.sqrt 3 / 2 ∧
    2 * (1 / 4 : ℝ) < Real.sqrt 3 / 2 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A strictly larger positive eigenvalue defeats every fixed power envelope. -/
theorem power_envelope_impossible {eigenvalue q C : ℝ} (hq : 0 < q) (heigenvalue : q < eigenvalue)
    (bound : ∀ n : ℕ, eigenvalue ^ n ≤ C * q ^ n) : False := by
  have hratio : 1 < eigenvalue / q := (one_lt_div hq).mpr heigenvalue
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have hb := bound n
  have hqpow : 0 < q ^ n := pow_pos hq n
  have hupper : (eigenvalue / q) ^ n ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ hqpow).mpr hb
  exact (not_lt_of_ge hupper) hn

/-- The trivial-quotient scalar bounds force c ≤ 2q by the triangle inequality. -/
theorem trivial_quotient_scalar_bound {eigenvalue q c : ℝ}
    (heigenvalue : |eigenvalue| ≤ q) (hceigenvalue : |c - eigenvalue| ≤ q) : c ≤ 2 * q := by
  have h₁ := le_abs_self eigenvalue
  have h₂ := le_abs_self (c - eigenvalue)
  linarith

end IDT.QMClosure.AtomicitySpectralBoundary
