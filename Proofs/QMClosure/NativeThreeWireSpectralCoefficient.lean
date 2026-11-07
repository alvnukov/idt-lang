import Proofs.QMClosure.NativeThreeWireProbabilityDenominator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Field.GeomSum

/-!
# A nonzero spectral coefficient of the repeated native three-wire word

The source and word are those of `NativeThreeWireProbabilityDenominator`.
This module proves an exact algebraic expansion and a twisted Cesaro limit in
the supplied complex circuit semantics. It supplies no stochastic realization,
physical finite-memory premise, probability-law derivation, or QM closure.
-/

namespace IDT.QMClosure.NativeThreeWireSpectralCoefficient

noncomputable section

open Filter Finset NativeThreeWireProbabilityDenominator
open scoped Topology ComplexConjugate

def lambda : ℂ := (1 + (Real.sqrt 15 : ℂ) * Complex.I) / 4

private theorem sqrt_fifteen_sq : (Real.sqrt 15) ^ 2 = 15 := by
  norm_num

theorem lambda_normSq : Complex.normSq lambda = 1 := by
  norm_num [lambda, Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem lambda_ne_zero : lambda ≠ 0 := by
  intro h
  have hnorm := lambda_normSq
  rw [h] at hnorm
  norm_num at hnorm

theorem lambda_add_conj : lambda + conj lambda = 1 / 2 := by
  apply Complex.ext <;>
    norm_num [lambda, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  ring

theorem lambda_mul_conj : lambda * conj lambda = 1 := by
  rw [Complex.mul_conj, lambda_normSq]
  norm_num

theorem lambda_conj_eq_inv : conj lambda = lambda⁻¹ := by
  apply (mul_left_cancel₀ lambda_ne_zero)
  rw [lambda_mul_conj, mul_inv_cancel₀ lambda_ne_zero]

theorem lambda_quadratic : lambda ^ 2 = lambda / 2 - 1 := by
  have h := congrArg (fun z : ℂ => lambda * z) lambda_add_conj
  dsimp only at h
  rw [mul_add, lambda_mul_conj] at h
  linear_combination h

theorem conj_lambda_quadratic : (conj lambda) ^ 2 = conj lambda / 2 - 1 := by
  simpa only [map_pow, map_sub, map_div₀, map_one, Complex.conj_ofNat] using
    congrArg (starRingEnd ℂ) lambda_quadratic

/-- The existing integer trace recurrence detects every possible finite order. -/
theorem traceSequence_spectral (n : ℕ) :
    (NativeMixerInfiniteOrder.traceSequence n : ℂ) =
      (2 : ℂ) ^ n * (lambda ^ n + (conj lambda) ^ n) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [NativeMixerInfiniteOrder.traceSequence]
  | one =>
      norm_num only [NativeMixerInfiniteOrder.traceSequence, Int.cast_one, pow_one]
      rw [lambda_add_conj]
      norm_num
  | more n ih₀ ih₁ =>
      rw [NativeMixerInfiniteOrder.traceSequence]
      push_cast
      rw [ih₀, ih₁, pow_add lambda n 2, pow_add (conj lambda) n 2,
        lambda_quadratic, conj_lambda_quadratic]
      simp only [pow_succ]
      ring

theorem lambda_pow_ne_one (q : ℕ) (hq : 0 < q) : lambda ^ q ≠ 1 := by
  intro h
  have hc : (conj lambda) ^ q = 1 := by
    simpa using congrArg (starRingEnd ℂ) h
  have ht := traceSequence_spectral q
  rw [h, hc] at ht
  have hz : NativeMixerInfiniteOrder.traceSequence q = (2 : ℤ) ^ (q + 1) := by
    have he : (NativeMixerInfiniteOrder.traceSequence q : ℂ) =
        ((2 : ℤ) ^ (q + 1) : ℤ) := by
      push_cast
      simpa only [pow_succ, one_add_one_eq_two] using ht
    exact_mod_cast he
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have ho := NativeMixerInfiniteOrder.traceSequence_odd m
  rw [hz, pow_succ] at ho
  omega

private def coefficientPlus : ℝ := 1 / 3 + Real.sqrt 15 / 15
private def coefficientMinus : ℝ := 1 / 3 - Real.sqrt 15 / 15

private theorem coefficient_sum : coefficientPlus + coefficientMinus = 2 / 3 := by
  unfold coefficientPlus coefficientMinus
  ring

private theorem coefficient_product : coefficientPlus * coefficientMinus = 2 / 45 := by
  unfold coefficientPlus coefficientMinus
  nlinarith [sqrt_fifteen_sq]

private theorem coefficient_square_sum :
    1 / 9 + coefficientPlus ^ 2 + coefficientMinus ^ 2 = 7 / 15 := by
  unfold coefficientPlus coefficientMinus
  nlinarith [sqrt_fifteen_sq]

/-- An exact expansion of the selected amplitude of the actual repeated word. -/
theorem selectedAmplitude_spectral (n : ℕ) :
    selectedAmplitude n = 1 / 3 + (coefficientPlus : ℂ) * lambda ^ n +
      (coefficientMinus : ℂ) * (conj lambda) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [selectedAmplitude_zero]
      norm_num [coefficientPlus, coefficientMinus]
      ring
  | one =>
      rw [selectedAmplitude_one]
      apply Complex.ext <;>
        norm_num [coefficientPlus, coefficientMinus, lambda, Complex.div_re,
          Complex.div_im, Complex.mul_re, Complex.mul_im] <;>
        nlinarith [sqrt_fifteen_sq]
  | more n ih₀ ih₁ =>
      rw [selectedAmplitude_recurrence, ih₀, ih₁,
        pow_add lambda n 2, pow_add (conj lambda) n 2,
        lambda_quadratic, conj_lambda_quadratic]
      simp only [pow_succ]
      ring

private theorem selectedWeight_spectral_powers (n : ℕ) :
    (selectedWeight n : ℂ) = 7 / 15 +
      (2 / 9 : ℂ) * (lambda ^ n + (conj lambda) ^ n) +
      (2 / 45 : ℂ) * ((lambda ^ n) ^ 2 + ((conj lambda) ^ n) ^ 2) := by
  rw [selectedWeight, selectedAmplitude_spectral, ← Complex.mul_conj]
  have hprod : lambda ^ n * (conj lambda) ^ n = 1 := by
    rw [← mul_pow, lambda_mul_conj, one_pow]
  have hsum : (coefficientPlus : ℂ) + (coefficientMinus : ℂ) = 2 / 3 := by
    simpa using congrArg Complex.ofReal coefficient_sum
  have hcoef : (coefficientPlus : ℂ) * (coefficientMinus : ℂ) = 2 / 45 := by
    simpa using congrArg Complex.ofReal coefficient_product
  have hsquares : (1 / 9 : ℂ) + (coefficientPlus : ℂ) ^ 2 +
      (coefficientMinus : ℂ) ^ 2 = 7 / 15 := by
    simpa using congrArg Complex.ofReal coefficient_square_sum
  simp only [map_add, map_mul, map_div₀, map_pow, map_one, map_ofNat,
    Complex.conj_ofReal, starRingEnd_self_apply]
  linear_combination
    ((coefficientPlus : ℂ) ^ 2 + (coefficientMinus : ℂ) ^ 2) * hprod +
    ((lambda ^ n + (conj lambda) ^ n) / 3) * hsum +
    ((lambda ^ n) ^ 2 + ((conj lambda) ^ n) ^ 2) * hcoef + hsquares

/-- Exact squared-weight expansion; no trigonometric or physical interpretation is needed. -/
theorem selectedWeight_spectral (n : ℕ) :
    (selectedWeight n : ℂ) = 7 / 15 +
      (2 / 9 : ℂ) * (lambda ^ n + (conj lambda) ^ n) +
      (2 / 45 : ℂ) * (lambda ^ (2 * n) + (conj lambda) ^ (2 * n)) := by
  simpa only [pow_mul'] using selectedWeight_spectral_powers n

def geometricCesaro (ζ : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, ζ ^ n

/-- A nonconstant unit-modulus geometric sequence has zero Cesaro limit. -/
theorem geometricCesaro_zero (ζ : ℂ) (hζ : Complex.normSq ζ = 1) (hne : ζ ≠ 1) :
    Tendsto (geometricCesaro ζ) atTop (𝓝 0) := by
  have hn : ‖ζ‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hζ
    nlinarith [norm_nonneg ζ]
  have hbound (N : ℕ) : ‖∑ n ∈ range N, ζ ^ n‖ ≤ 2 / ‖ζ - 1‖ := by
    rw [geom_sum_eq hne, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hn]
  apply squeeze_zero_norm (a := fun N : ℕ => (2 / ‖ζ - 1‖) / (N : ℝ))
  · intro N
    calc
      ‖geometricCesaro ζ N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N, ζ ^ n‖ := by
        simp [geometricCesaro]
      _ ≤ (N : ℝ)⁻¹ * (2 / ‖ζ - 1‖) :=
        mul_le_mul_of_nonneg_left (hbound N) (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = (2 / ‖ζ - 1‖) / (N : ℝ) := by ring
  · exact tendsto_const_div_atTop_nhds_zero_nat _

theorem geometricCesaro_one : Tendsto (geometricCesaro 1) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simp [geometricCesaro, Nat.ne_of_gt hN]

private theorem inverse_power_normSq (q : ℕ) : Complex.normSq ((lambda⁻¹) ^ q) = 1 := by
  rw [map_pow, Complex.normSq_inv, lambda_normSq]
  simp

private theorem inverse_power_ne_one (q : ℕ) (hq : 0 < q) : (lambda⁻¹) ^ q ≠ 1 := by
  intro h
  apply lambda_pow_ne_one q hq
  have h' := congrArg (fun z : ℂ => z⁻¹) h
  simpa using h'

private theorem twistedTerm_formula (n : ℕ) :
    (lambda⁻¹) ^ n * (selectedWeight n : ℂ) =
      (7 / 15 : ℂ) * (lambda⁻¹) ^ n +
      (2 / 9 : ℂ) * (1 + ((lambda⁻¹) ^ 2) ^ n) +
      (2 / 45 : ℂ) * (lambda ^ n + ((lambda⁻¹) ^ 3) ^ n) := by
  rw [selectedWeight_spectral_powers, lambda_conj_eq_inv]
  rw [show ((lambda⁻¹) ^ 2) ^ n = ((lambda⁻¹) ^ n) ^ 2 by rw [← pow_mul, ← pow_mul]; congr 1; omega]
  rw [show ((lambda⁻¹) ^ 3) ^ n = ((lambda⁻¹) ^ n) ^ 3 by rw [← pow_mul, ← pow_mul]; congr 1; omega]
  simp only [inv_pow]
  field_simp [pow_ne_zero n lambda_ne_zero]

private theorem twistedCesaro_formula (N : ℕ) :
    (N : ℂ)⁻¹ * ∑ n ∈ range N, (lambda⁻¹) ^ n * (selectedWeight n : ℂ) =
      (7 / 15 : ℂ) * geometricCesaro (lambda⁻¹) N +
      (2 / 9 : ℂ) * (geometricCesaro 1 N + geometricCesaro ((lambda⁻¹) ^ 2) N) +
      (2 / 45 : ℂ) * (geometricCesaro lambda N + geometricCesaro ((lambda⁻¹) ^ 3) N) := by
  simp_rw [twistedTerm_formula]
  simp only [geometricCesaro, sum_add_distrib, ← mul_sum, one_pow]
  ring

/-- The actual native squared weight has a nonzero coefficient at its infinite-order frequency. -/
theorem selectedWeight_twistedCesaro_limit :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, (lambda⁻¹) ^ n * (selectedWeight n : ℂ))
      atTop (𝓝 ((2 : ℂ) / 9)) := by
  have h₁ := geometricCesaro_zero (lambda⁻¹)
    (by simpa using inverse_power_normSq 1)
    (by simpa using inverse_power_ne_one 1 (by decide))
  have h₂ := geometricCesaro_zero ((lambda⁻¹) ^ 2)
    (inverse_power_normSq 2) (inverse_power_ne_one 2 (by decide))
  have h₃ := geometricCesaro_zero ((lambda⁻¹) ^ 3)
    (inverse_power_normSq 3) (inverse_power_ne_one 3 (by decide))
  have hlambda := geometricCesaro_zero lambda lambda_normSq
    (by simpa using lambda_pow_ne_one 1 (by decide))
  have h := (h₁.const_mul (7 / 15 : ℂ)).add
    (((geometricCesaro_one.add h₂).const_mul (2 / 9 : ℂ)).add
      ((hlambda.add h₃).const_mul (2 / 45 : ℂ)))
  norm_num at h
  apply h.congr
  intro N
  dsimp only
  rw [twistedCesaro_formula]
  simp only [inv_pow]
  ac_rfl

end

end IDT.QMClosure.NativeThreeWireSpectralCoefficient
