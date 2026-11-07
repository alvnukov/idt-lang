import Proofs.QMClosure.NativeFixedStateFiniteWindow

/-!
# A finite algebraic obstruction for stochastic characteristic polynomials

The exact native readout contains a nonzero geometric mode at the supplied
infinite-order phase `lambda`. A polynomial annihilating that readout must
vanish at `lambda`: a four-factor polynomial filter isolates this mode from
the other four modes. A stochastic characteristic polynomial cannot vanish
there. Its native readout residual is therefore nonzero at one of the first
four depths.

This is a finite algebraic statement about the supplied native complex model
and fixed finite row-stochastic preparation kernels. It does not derive a
physical state bound, probability actualization, detector frequency, or QM.
-/

namespace IDT.QMClosure.NativeReadoutPolynomialObstruction

open Polynomial Finset
open FiniteReadoutRecurrence NativeFixedStateFiniteWindow
open NativeThreeWireProbabilityDenominator NativeThreeWireSpectralCoefficient

noncomputable section

/-- A geometric sequence is an eigenvector of every polynomial in the shift. -/
theorem applyPolynomial_geometric (q : ℂ[X]) (z : ℂ) (n : ℕ) :
    applyPolynomial q (fun k => z ^ k) n = q.eval z * z ^ n := by
  rw [applyPolynomial_eq_sum, Polynomial.eval_eq_sum_range, sum_mul]
  apply sum_congr rfl
  intro k _hk
  rw [pow_add]
  ring

private theorem applyPolynomial_add_sequence (q : ℂ[X]) (u v : ℕ → ℂ) :
    applyPolynomial q (u + v) = applyPolynomial q u + applyPolynomial q v := by
  simp only [applyPolynomial, map_add]

private theorem applyPolynomial_smul_sequence (q : ℂ[X]) (c : ℂ) (u : ℕ → ℂ) :
    applyPolynomial q (c • u) = c • applyPolynomial q u := by
  simp only [applyPolynomial, map_smul]

private theorem native_sequence_spectral :
    (fun n => (selectedWeight n : ℂ)) =
      (fun _ => (7 / 15 : ℂ)) +
      (2 / 9 : ℂ) • ((fun n => lambda ^ n) + (fun n => (lambda⁻¹) ^ n)) +
      (2 / 45 : ℂ) • ((fun n => (lambda ^ 2) ^ n) +
        (fun n => ((lambda⁻¹) ^ 2) ^ n)) := by
  funext n
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    lambda_conj_eq_inv, pow_mul] using selectedWeight_spectral n

/-- The exact five native modes after applying an arbitrary polynomial. -/
theorem applyPolynomial_selectedWeight (q : ℂ[X]) (n : ℕ) :
    applyPolynomial q (fun k => (selectedWeight k : ℂ)) n =
      (7 / 15 : ℂ) * q.eval 1 +
      (2 / 9 : ℂ) * (q.eval lambda * lambda ^ n +
        q.eval (lambda⁻¹) * (lambda⁻¹) ^ n) +
      (2 / 45 : ℂ) * (q.eval (lambda ^ 2) * (lambda ^ 2) ^ n +
        q.eval ((lambda⁻¹) ^ 2) * ((lambda⁻¹) ^ 2) ^ n) := by
  rw [native_sequence_spectral]
  simp only [applyPolynomial_add_sequence, applyPolynomial_smul_sequence,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, applyPolynomial_const,
    applyPolynomial_geometric]
  ring

private def separatingPolynomial : ℂ[X] :=
  (X - C 1) * (X - C (lambda⁻¹)) * (X - C (lambda ^ 2)) *
    (X - C ((lambda⁻¹) ^ 2))

private theorem separatingPolynomial_eval_lambda_ne_zero :
    separatingPolynomial.eval lambda ≠ 0 := by
  have h₁ : lambda ≠ 1 := by simpa using lambda_pow_ne_one 1 (by decide)
  have h₂ : lambda ≠ lambda⁻¹ := by
    intro h
    apply lambda_pow_ne_one 2 (by decide)
    calc
      lambda ^ 2 = lambda * lambda := pow_two _
      _ = lambda * lambda⁻¹ := congrArg (lambda * ·) h
      _ = 1 := mul_inv_cancel₀ lambda_ne_zero
  have h₃ : lambda ≠ lambda ^ 2 := by
    intro h
    apply h₁
    have heq : lambda * 1 = lambda * lambda := by simpa only [mul_one, ← pow_two] using h
    exact (mul_left_cancel₀ lambda_ne_zero heq).symm
  have h₄ : lambda ≠ (lambda⁻¹) ^ 2 := by
    intro h
    apply lambda_pow_ne_one 3 (by decide)
    calc
      lambda ^ 3 = lambda * lambda ^ 2 := by ring
      _ = (lambda⁻¹) ^ 2 * lambda ^ 2 := congrArg (· * lambda ^ 2) h
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ lambda_ne_zero, one_pow]
  simpa only [separatingPolynomial, eval_mul, eval_sub, eval_X, eval_C] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂))
      (sub_ne_zero.mpr h₃)) (sub_ne_zero.mpr h₄)

/-- Every polynomial annihilator of the native weight vanishes at its nonzero mode. -/
theorem annihilator_eval_lambda_zero (q : ℂ[X])
    (hq : applyPolynomial q (fun n => (selectedWeight n : ℂ)) = 0) :
    q.eval lambda = 0 := by
  have hzero : applyPolynomial (separatingPolynomial * q)
      (fun n => (selectedWeight n : ℂ)) = 0 := by
    rw [applyPolynomial_mul, hq, applyPolynomial_zero_sequence]
  have h₁ : separatingPolynomial.eval 1 = 0 := by simp [separatingPolynomial]
  have h₂ : separatingPolynomial.eval (lambda⁻¹) = 0 := by simp [separatingPolynomial]
  have h₃ : separatingPolynomial.eval (lambda ^ 2) = 0 := by simp [separatingPolynomial]
  have h₄ : separatingPolynomial.eval ((lambda⁻¹) ^ 2) = 0 := by simp [separatingPolynomial]
  have h := congrFun hzero 0
  rw [applyPolynomial_selectedWeight] at h
  simp only [eval_mul, h₁, h₂, h₃, h₄, pow_zero, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, Pi.zero_apply] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))).resolve_left
    separatingPolynomial_eval_lambda_ne_zero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The native infinite-order phase is not a stochastic characteristic root. -/
theorem charpoly_eval_lambda_ne_zero {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) :
    (FiniteStochasticPeripheral.complexify P).charpoly.eval lambda ≠ 0 := by
  intro hroot
  apply FiniteStochasticTwistedReadout.shifted_det_ne_zero hP lambda_normSq lambda_pow_ne_one
  have hdet : (Matrix.scalar S lambda - FiniteStochasticPeripheral.complexify P).det = 0 := by
    simpa only [Matrix.eval_charpoly] using hroot
  have hscalar : Matrix.scalar S lambda = lambda • (1 : Matrix S S ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  rw [hscalar] at hdet
  rw [show FiniteStochasticPeripheral.complexify P - lambda • (1 : Matrix S S ℂ) =
    -(lambda • (1 : Matrix S S ℂ) - FiniteStochasticPeripheral.complexify P) by abel,
    Matrix.det_neg, hdet, mul_zero]

/-- A stochastic characteristic polynomial has a nonzero native residual in four slots. -/
theorem exists_charpoly_residual_before_four {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) :
    ∃ k : ℕ, k < 4 ∧
      applyPolynomial (FiniteStochasticPeripheral.complexify P).charpoly
        (fun n => (selectedWeight n : ℂ)) k ≠ 0 := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · refine ⟨0, by omega, ?_⟩
    simp [applyPolynomial, selectedWeight, selectedAmplitude_zero]
  · by_contra h
    push Not at h
    let q := (FiniteStochasticPeripheral.complexify P).charpoly
    let residual := applyPolynomial q (fun n => (selectedWeight n : ℂ))
    have hrec : applyPolynomial nativePolynomial residual = 0 := by
      change applyPolynomial nativePolynomial
        (applyPolynomial q (fun n => (selectedWeight n : ℂ))) = 0
      rw [← applyPolynomial_mul, mul_comm nativePolynomial q, applyPolynomial_mul,
        nativePolynomial_forcing, applyPolynomial_const]
      change (fun _ => q.eval 1 * (21 / 8 : ℂ)) = 0
      have hq1 : q.eval 1 = 0 := charpoly_eval_one hP
      rw [hq1]
      funext n
      simp
    have hzero : residual = 0 := eq_zero_of_initial nativePolynomial
      nativePolynomial_monic residual hrec (by
        intro n hn
        exact h n (by simpa only [nativePolynomial_natDegree] using hn))
    exact charpoly_eval_lambda_ne_zero hP (annihilator_eval_lambda_zero q hzero)

end

end IDT.QMClosure.NativeReadoutPolynomialObstruction
