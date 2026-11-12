import Proofs.QMClosure.AtomicitySpectralBoundary
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! Field and complex spectral kernels for a conditional atomicity route.
The general normed-space operator conclusions require an actual nonzero
eigenvector and supplied operator-power bounds. In finite-dimensional nontrivial
complex spaces, eigenvector existence follows from algebraic closedness. Transfer
of bounds to a quotient and the Lie-theoretic classification remain separate
obligations. -/

namespace IDT.QMClosure.ComplexAtomicitySpectralBoundary

section Field

variable {F : Type*} [Field F]

/-- The three-weight quadratic elimination uses field algebra alone. -/
theorem three_weight_polynomial {a b d k l c : F}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a ^ 2 * k + l = c * a)
    (hb : b ^ 2 * k + l = c * b)
    (hd : d ^ 2 * k + l = c * d) : c = 0 := by
  have hp : (a - b) * (k * (a + b) - c) = 0 := by
    linear_combination ha - hb
  have hq : (a - d) * (k * (a + d) - c) = 0 := by
    linear_combination ha - hd
  have hp' : k * (a + b) = c :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab))
  have hq' : k * (a + d) = c :=
    sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr had))
  have hk : k * (b - d) = 0 := by linear_combination hp' - hq'
  have hk' : k = 0 := (mul_eq_zero.mp hk).resolve_right (sub_ne_zero.mpr hbd)
  simpa [hk'] using hp'.symm

/-- Three distinct nonzero inverse weights exclude a nonzero scalar right side. -/
theorem three_boost_weights {a b d k l c : F}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a * k + a⁻¹ * l = c)
    (hb : b * k + b⁻¹ * l = c)
    (hd : d * k + d⁻¹ * l = c) : c = 0 := by
  apply three_weight_polynomial hab had hbd
  · have h := congrArg (fun x : F => a * x) ha
    simpa [mul_add, ← mul_assoc, ha0, pow_two, mul_comm c a] using h
  · have h := congrArg (fun x : F => b * x) hb
    simpa [mul_add, ← mul_assoc, hb0, pow_two, mul_comm c b] using h
  · have h := congrArg (fun x : F => d * x) hd
    simpa [mul_add, ← mul_assoc, hd0, pow_two, mul_comm c d] using h

/-- A diagonal entry gives the corresponding finite-matrix exclusion. -/
theorem matrix_three_boost_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K L : Matrix ι ι F) {a b d c : F}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : a • K + a⁻¹ • L = c • (1 : Matrix ι ι F))
    (hb : b • K + b⁻¹ • L = c • (1 : Matrix ι ι F))
    (hd : d • K + d⁻¹ • L = c • (1 : Matrix ι ι F)) : c = 0 := by
  classical
  let i : ι := Classical.choice inferInstance
  apply three_boost_weights ha0 hb0 hd0 hab had hbd (k := K i i) (l := L i i)
  · simpa using congrArg (fun M : Matrix ι ι F => M i i) ha
  · simpa using congrArg (fun M : Matrix ι ι F => M i i) hb
  · simpa using congrArg (fun M : Matrix ι ι F => M i i) hd

/-- Reciprocal weights determine both coefficients when their difference and sum
are nonzero in the field. -/
theorem reciprocal_boost_weights {r k l c : F}
    (hdiff : r - r⁻¹ ≠ 0) (hsum : r + r⁻¹ ≠ 0)
    (h₁ : r * k + r⁻¹ * l = c) (h₂ : r⁻¹ * k + r * l = c) :
    k = c / (r + r⁻¹) ∧ l = c / (r + r⁻¹) := by
  have heq : (r - r⁻¹) * (k - l) = 0 := by linear_combination h₁ - h₂
  have hkl : k = l := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hdiff)
  rw [← hkl] at h₁
  have hk : k = c / (r + r⁻¹) := by
    apply (eq_div_iff hsum).mpr
    linear_combination h₁
  exact ⟨hk, hkl.symm.trans hk⟩

end Field

/-- A positive real boost supplies the required two nonzero complex coefficients. -/
theorem complex_reciprocal_boost_weights {r : ℝ} {k l c : ℂ} (hr : 1 < r)
    (h₁ : (r : ℂ) * k + (r : ℂ)⁻¹ * l = c)
    (h₂ : (r : ℂ)⁻¹ * k + (r : ℂ) * l = c) :
    k = c / ((r : ℂ) + (r : ℂ)⁻¹) ∧
    l = c / ((r : ℂ) + (r : ℂ)⁻¹) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hi : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hdiff : r - r⁻¹ ≠ 0 := by linarith
  have hsum : r + r⁻¹ ≠ 0 := ne_of_gt (add_pos hr0 (inv_pos.mpr hr0))
  apply reciprocal_boost_weights (r := (r : ℂ)) _ _ h₁ h₂
  · exact_mod_cast hdiff
  · exact_mod_cast hsum

/-- Real boosts act on complex matrices without requiring real matrix entries. -/
theorem complex_matrix_reciprocal_boost_weights
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : Matrix ι ι ℂ) {r : ℝ} {c : ℂ} (hr : 1 < r)
    (h₁ : r • K + r⁻¹ • L = c • (1 : Matrix ι ι ℂ))
    (h₂ : r⁻¹ • K + r • L = c • (1 : Matrix ι ι ℂ)) :
    K = (c / ((r : ℂ) + (r : ℂ)⁻¹)) • (1 : Matrix ι ι ℂ) ∧
    L = (c / ((r : ℂ) + (r : ℂ)⁻¹)) • (1 : Matrix ι ι ℂ) := by
  have entry (i j : ι) :
      K i j = (c * (1 : Matrix ι ι ℂ) i j) / ((r : ℂ) + (r : ℂ)⁻¹) ∧
      L i j = (c * (1 : Matrix ι ι ℂ) i j) / ((r : ℂ) + (r : ℂ)⁻¹) := by
    apply complex_reciprocal_boost_weights hr
    · simpa [Complex.real_smul] using congrArg (fun M : Matrix ι ι ℂ => M i j) h₁
    · simpa [Complex.real_smul] using congrArg (fun M : Matrix ι ι ℂ => M i j) h₂
  constructor
  · ext i j
    simpa [div_mul_eq_mul_div] using (entry i j).1
  · ext i j
    simpa [div_mul_eq_mul_div] using (entry i j).2

/-- The scalar quotient estimate allows a complex spectral parameter. -/
theorem complex_triangle_bound {z : ℂ} {q c : ℝ}
    (hz : ‖z‖ ≤ q) (hcz : ‖(c : ℂ) - z‖ ≤ q) : c ≤ 2 * q := by
  calc
    c ≤ |c| := le_abs_self c
    _ = ‖(c : ℂ)‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((c : ℂ) - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖(c : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 2 * q := by linarith

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A supplied eigenvector remains an eigenvector of every operator power. -/
theorem eigenvector_power (T : E →L[ℂ] E) {v : E} {z : ℂ}
    (eigen : T v = z • v) (n : ℕ) : (T ^ n) v = z ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, eigen,
        smul_smul, pow_succ]

/-- Operator-power bounds control the modulus of an actual eigenvalue. -/
theorem eigenvalue_norm_le_of_power_bound (T : E →L[ℂ] E)
    {v : E} {z : ℂ} {q C : ℝ} (hv : v ≠ 0) (eigen : T v = z • v)
    (hq : 0 < q) (bound : ∀ n : ℕ, ‖T ^ n‖ ≤ C * q ^ n) : ‖z‖ ≤ q := by
  by_contra h
  have hlarge : q < ‖z‖ := lt_of_not_ge h
  apply AtomicitySpectralBoundary.power_envelope_impossible hq hlarge
    (C := C)
  intro n
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm : ‖z‖ ^ n * ‖v‖ ≤ (C * q ^ n) * ‖v‖ := by
    calc
      ‖z‖ ^ n * ‖v‖ = ‖(T ^ n) v‖ := by
        rw [eigenvector_power T eigen n, norm_smul, norm_pow]
      _ ≤ ‖T ^ n‖ * ‖v‖ := (T ^ n).le_opNorm v
      _ ≤ (C * q ^ n) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (bound n) (norm_nonneg v)
  exact (mul_le_mul_iff_left₀ hvnorm).mp hnorm

/-- Complementary operators sharing the supplied eigenvector obey the scalar bound.
Each operator has its own fixed power-envelope constant. -/
theorem complementary_operator_scalar_bound (A B : E →L[ℂ] E)
    {v : E} {z : ℂ} {q c CA CB : ℝ}
    (hv : v ≠ 0) (eigen : A v = z • v)
    (complement : A + B = (c : ℂ) • (1 : E →L[ℂ] E))
    (hq : 0 < q)
    (boundA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * q ^ n)
    (boundB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * q ^ n) : c ≤ 2 * q := by
  have heq : A v + B v = (c : ℂ) • v := by
    simpa using DFunLike.congr_fun complement v
  have eigenB : B v = ((c : ℂ) - z) • v := by
    rw [sub_smul]
    apply eq_sub_iff_add_eq.mpr
    calc
      B v + z • v = A v + B v := by rw [eigen, add_comm]
      _ = (c : ℂ) • v := heq
  exact complex_triangle_bound
    (eigenvalue_norm_le_of_power_bound A hv eigen hq boundA)
    (eigenvalue_norm_le_of_power_bound B hv eigenB hq boundB)

/-- Finite-dimensional complex spectral existence removes the supplied-eigenvector
premise while retaining both uniform operator-power bounds. -/
theorem finite_dimensional_complementary_operator_scalar_bound
    [FiniteDimensional ℂ E] [Nontrivial E]
    (A B : E →L[ℂ] E) {q c CA CB : ℝ}
    (complement : A + B = (c : ℂ) • (1 : E →L[ℂ] E))
    (hq : 0 < q)
    (boundA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * q ^ n)
    (boundB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * q ^ n) : c ≤ 2 * q := by
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue A.toLinearMap
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  exact complementary_operator_scalar_bound A B hv.2 hv.apply_eq_smul
    complement hq boundA boundB

end Operator

end IDT.QMClosure.ComplexAtomicitySpectralBoundary
