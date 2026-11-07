import Proofs.QMClosure.NativeMixerInfiniteOrder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Exact denominators for one repeated native three-wire word

The selected squared norm of the existing word `cK`, repeated `n > 0` times
from the first basis vector, has reduced denominator `2^(2*n-1)`.
This is an exact result about the supplied complex circuit semantics. Calling
that squared norm a detector frequency still requires an explicit readout law.
No actualization, probability-law derivation, or QM closure is asserted.
-/

namespace IDT.QMClosure.NativeThreeWireProbabilityDenominator

noncomputable section

open NativeMixerInfiniteOrder NativeMixerEventConeExclusion MixerGeneratedProcessWall
open scoped Matrix BigOperators

attribute [local simp] Matrix.cons_val_two

def source : Fin 3 → ℂ := Pi.single 0 1

theorem source_eq_single : source = MixerGeneratedProcessWall.single 0 1 := by
  ext i
  simp [source, MixerGeneratedProcessWall.single, Pi.single_apply]

/-- Literal repetition in the existing native syntax. -/
def repeatedWord : ℕ → NativeCircuit
  | 0 => .identity
  | n + 1 => .seq (repeatedWord n) cK

def orbit : ℕ → (Fin 3 → ℂ)
  | 0 => source
  | n + 1 => K.mulVec (orbit n)

def selectedAmplitude (n : ℕ) : ℂ := orbit n 0
def selectedWeight (n : ℕ) : ℝ := Complex.normSq (selectedAmplitude n)

theorem repeatedWord_eval (n : ℕ) : (repeatedWord n).eval source = orbit n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change cK.eval ((repeatedWord n).eval source) = K.mulVec (orbit n)
      rw [ih, native_word_action]

theorem orbit_eq_matrix_power (n : ℕ) : orbit n = (K ^ n).mulVec source := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      rw [orbit, ih, Matrix.mulVec_mulVec, ← pow_succ']

theorem K_preserves_sum (v : Fin 3 → ℂ) :
    (K.mulVec v) 0 + (K.mulVec v) 1 + (K.mulVec v) 2 = v 0 + v 1 + v 2 := by
  apply Complex.ext <;>
    norm_num [K, A, B, a, b, pow_succ, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

theorem orbit_sum (n : ℕ) : orbit n 0 + orbit n 1 + orbit n 2 = 1 := by
  induction n with
  | zero => norm_num [orbit, source, Pi.single_apply, Fin.ext_iff]
  | succ n ih => simpa only [orbit, K_preserves_sum] using ih

theorem K_twice_selected (v : Fin 3 → ℂ) :
    (K.mulVec (K.mulVec v)) 0 =
      (K.mulVec v) 0 / 2 - v 0 + (v 0 + v 1 + v 2) / 2 := by
  apply Complex.ext <;>
    norm_num [K, A, B, a, b, pow_succ, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

theorem selectedAmplitude_zero : selectedAmplitude 0 = 1 := by
  simp [selectedAmplitude, orbit, source]

theorem selectedAmplitude_one : selectedAmplitude 1 = (1 + Complex.I) / 2 := by
  apply Complex.ext <;>
    norm_num [selectedAmplitude, orbit, source, Pi.single_apply, K, A, B, a, b,
      pow_succ, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem selectedAmplitude_recurrence (n : ℕ) :
    selectedAmplitude (n + 2) =
      selectedAmplitude (n + 1) / 2 - selectedAmplitude n + 1 / 2 := by
  change (K.mulVec (K.mulVec (orbit n))) 0 = _
  rw [K_twice_selected, orbit_sum]
  rfl

def realNumerator : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => realNumerator (n + 1) - 4 * realNumerator n + 2 ^ (n + 1)

def imagNumerator : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => imagNumerator (n + 1) - 4 * imagNumerator n

theorem realNumerator_odd (n : ℕ) : realNumerator (n + 1) % 2 = 1 := by
  induction n with
  | zero => norm_num [realNumerator]
  | succ n ih =>
      rw [show n.succ + 1 = n + 2 by omega, realNumerator, pow_succ]
      omega

theorem imagNumerator_odd (n : ℕ) : imagNumerator (n + 1) % 2 = 1 := by
  induction n with
  | zero => norm_num [imagNumerator]
  | succ n ih =>
      rw [show n.succ + 1 = n + 2 by omega, imagNumerator]
      omega

/-- Both integer coordinates use the exact scale `2^n`. -/
theorem selectedAmplitude_gaussian (n : ℕ) :
    selectedAmplitude n =
      ((realNumerator n : ℂ) + (imagNumerator n : ℂ) * Complex.I) / (2 : ℂ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [selectedAmplitude_zero, realNumerator, imagNumerator]
  | one => simp [selectedAmplitude_one, realNumerator, imagNumerator]
  | more n ih₀ ih₁ =>
      rw [selectedAmplitude_recurrence, ih₀, ih₁, realNumerator, imagNumerator]
      push_cast
      simp only [pow_succ]
      field_simp
      ring

theorem selectedWeight_formula (n : ℕ) :
    selectedWeight n =
      ((realNumerator n : ℝ) ^ 2 + (imagNumerator n : ℝ) ^ 2) / (2 : ℝ) ^ (2 * n) := by
  rw [selectedWeight, selectedAmplitude_gaussian, Complex.normSq_div, map_pow]
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_mul, pow_two]

theorem odd_square_mod_eight (z : ℤ) (hz : z % 2 = 1) : z ^ 2 % 8 = 1 := by
  have hz8 : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by omega
  have he : z ^ 2 % 8 = ((z % 8) * (z % 8)) % 8 := by
    rw [pow_two, Int.mul_emod]
  rw [he]
  rcases hz8 with h | h | h | h <;> norm_num [h]

def squareSum (n : ℕ) : ℤ := realNumerator n ^ 2 + imagNumerator n ^ 2

theorem squareSum_mod_eight (n : ℕ) (hn : 0 < n) : squareSum n % 8 = 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [squareSum, Int.add_emod,
    odd_square_mod_eight _ (realNumerator_odd m),
    odd_square_mod_eight _ (imagNumerator_odd m)]
  norm_num

theorem squareSum_nonnegative (n : ℕ) : 0 ≤ squareSum n :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The numerator after cancelling exactly one factor of two. -/
def numerator (n : ℕ) : ℕ := (squareSum n / 2).toNat

theorem numerator_spec (n : ℕ) (hn : 0 < n) :
    0 < numerator n ∧ Odd (numerator n) ∧ squareSum n = 2 * (numerator n : ℤ) := by
  have hmod := squareSum_mod_eight n hn
  have hnonneg := squareSum_nonnegative n
  have hcast : (numerator n : ℤ) = squareSum n / 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hodd : numerator n % 2 = 1 := by omega
  exact ⟨by omega, Nat.odd_iff.mpr hodd, by omega⟩

/-- A positive odd numerator exhibits the reduced power-of-two denominator. -/
theorem selectedWeight_reduced (n : ℕ) (hn : 0 < n) :
    selectedWeight n = (numerator n : ℝ) / (2 : ℝ) ^ (2 * n - 1) := by
  rw [selectedWeight_formula]
  have hs : (realNumerator n : ℝ) ^ 2 + (imagNumerator n : ℝ) ^ 2 =
      2 * (numerator n : ℝ) := by
    exact_mod_cast (numerator_spec n hn).2.2
  rw [hs]
  have he : 2 * n = (2 * n - 1) + 1 := by omega
  conv_lhs => rw [he, pow_succ]
  field_simp

theorem selectedWeight_positive_odd_fraction (n : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, 0 < N ∧ Odd N ∧ selectedWeight n = (N : ℝ) / (2 : ℝ) ^ (2 * n - 1) :=
  ⟨numerator n, (numerator_spec n hn).1, (numerator_spec n hn).2.1,
    selectedWeight_reduced n hn⟩

/-- Every natural-number fraction for this weight has the stated denominator divisor. -/
theorem denominator_dvd (n : ℕ) (hn : 0 < n) (k ell : ℕ) (hell : 0 < ell)
    (h : selectedWeight n = (k : ℝ) / (ell : ℝ)) :
    2 ^ (2 * n - 1) ∣ ell := by
  have hp : Nat.Coprime (2 ^ (2 * n - 1)) (numerator n) :=
    ((numerator_spec n hn).2.1.coprime_two_left).pow_left _
  have hd : (2 : ℝ) ^ (2 * n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
  have hcross : (numerator n : ℝ) * (ell : ℝ) =
      (k : ℝ) * (2 : ℝ) ^ (2 * n - 1) := by
    exact (div_eq_div_iff hd he).mp ((selectedWeight_reduced n hn).symm.trans h)
  have hnat : numerator n * ell = k * 2 ^ (2 * n - 1) := by exact_mod_cast hcross
  apply hp.dvd_of_dvd_mul_left
  rw [hnat]
  exact dvd_mul_left _ _

theorem repeatedWord_selectedWeight (n : ℕ) :
    Complex.normSq ((repeatedWord n).eval source 0) = selectedWeight n := by
  rw [repeatedWord_eval]
  rfl

end

end IDT.QMClosure.NativeThreeWireProbabilityDenominator
