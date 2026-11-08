import Proofs.QMClosure.GaussianSignedSmoothingMoments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology ComplexConjugate NNReal

namespace IDT.QMClosure.GaussianSignedSmoothingCharacterization

/-- The signed four-copy smoothing transform on a scalar characteristic value. -/
def signedSmoothing (z : ℂ) : ℂ := z ^ 3 * conj z

/-- On the closed unit disk the signed smoothing transform is `4`-Lipschitz. -/
theorem norm_signedSmoothing_sub_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖signedSmoothing z - signedSmoothing w‖ ≤ 4 * ‖z - w‖ := by
  have hz0 := norm_nonneg z
  have hw0 := norm_nonneg w
  have hsum : ‖z ^ 2 + z * w + w ^ 2‖ ≤ 3 := by
    calc
      _ ≤ ‖z ^ 2‖ + ‖z * w‖ + ‖w ^ 2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]
      _ ≤ 3 := by
        have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ hz0 hz
        have hw2 : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ hw0 hw
        have hzw : ‖z‖ * ‖w‖ ≤ 1 := by
          simpa using mul_le_mul hz hw hw0 (by norm_num : (0 : ℝ) ≤ 1)
        linarith
  have hcube : ‖z ^ 3 - w ^ 3‖ ≤ 3 * ‖z - w‖ := by
    calc
      _ = ‖(z - w) * (z ^ 2 + z * w + w ^ 2)‖ := by congr 1; ring
      _ = ‖z - w‖ * ‖z ^ 2 + z * w + w ^ 2‖ := norm_mul _ _
      _ ≤ ‖z - w‖ * 3 := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = _ := by ring
  have hw3 : ‖w‖ ^ 3 ≤ 1 := pow_le_one₀ hw0 hw
  calc
    _ = ‖(z ^ 3 - w ^ 3) * conj z + w ^ 3 * conj (z - w)‖ := by
      simp only [signedSmoothing, map_sub]
      congr 1
      ring
    _ ≤ ‖(z ^ 3 - w ^ 3) * conj z‖ + ‖w ^ 3 * conj (z - w)‖ := norm_add_le _ _
    _ = ‖z ^ 3 - w ^ 3‖ * ‖z‖ + ‖w‖ ^ 3 * ‖z - w‖ := by
      simp only [norm_mul, norm_pow, norm_conj]
    _ ≤ (3 * ‖z - w‖) * 1 + 1 * ‖z - w‖ :=
      add_le_add (mul_le_mul hcube hz hz0 (by positivity))
        (mul_le_mul_of_nonneg_right hw3 (norm_nonneg _))
    _ = _ := by ring

/-- A quadratic little-o difference makes two bounded smoothing fixed points identical. -/
theorem fixedPoint_eq_of_isLittleO {f g : ℝ → ℂ}
    (hf : ∀ t, f t = signedSmoothing (f (t / 2)))
    (hg : ∀ t, g t = signedSmoothing (g (t / 2)))
    (hfnorm : ∀ t, ‖f t‖ ≤ 1) (hgnorm : ∀ t, ‖g t‖ ≤ 1)
    (hsmall : (fun t => f t - g t) =o[𝓝 (0 : ℝ)] (fun t => t ^ 2)) : f = g := by
  have hstep (t : ℝ) : ‖f t - g t‖ ≤ 4 * ‖f (t / 2) - g (t / 2)‖ := by
    rw [hf t, hg t]
    exact norm_signedSmoothing_sub_le (hfnorm _) (hgnorm _)
  have hiter (n : ℕ) (t : ℝ) :
      ‖f t - g t‖ ≤ (4 : ℝ) ^ n * ‖f (t * (1 / 2 : ℝ) ^ n) - g (t * (1 / 2 : ℝ) ^ n)‖ := by
    induction n generalizing t with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ 4 * ‖f (t / 2) - g (t / 2)‖ := hstep t
        _ ≤ 4 * ((4 : ℝ) ^ n *
            ‖f ((t / 2) * (1 / 2 : ℝ) ^ n) - g ((t / 2) * (1 / 2 : ℝ) ^ n)‖) :=
          mul_le_mul_of_nonneg_left (ih (t / 2)) (by norm_num)
        _ = _ := by
          have harg : (t / 2) * (1 / 2 : ℝ) ^ n = t * (1 / 2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
          rw [harg, pow_succ]
          ring
  funext t
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hbound (c : ℝ) (hc : 0 < c) : ‖f t - g t‖ ≤ c * t ^ 2 := by
    have ht : Tendsto (fun n : ℕ => t * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
    obtain ⟨n, hn⟩ := (ht.eventually (hsmall.bound hc)).exists
    have hscale : (4 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow]
      norm_num
    calc
      _ ≤ (4 : ℝ) ^ n * ‖f (t * (1 / 2 : ℝ) ^ n) - g (t * (1 / 2 : ℝ) ^ n)‖ := hiter n t
      _ ≤ (4 : ℝ) ^ n * (c * ‖(t * (1 / 2 : ℝ) ^ n) ^ 2‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = c * t ^ 2 * ((4 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        ring
      _ = _ := by rw [hscale, mul_one]
  by_contra hne
  have hpos : 0 < ‖f t - g t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hden : 0 < t ^ 2 + 1 := by positivity
  have hb := hbound (‖f t - g t‖ / (t ^ 2 + 1)) (div_pos hpos hden)
  have heq : (‖f t - g t‖ / (t ^ 2 + 1)) * (t ^ 2 + 1) = ‖f t - g t‖ :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  nlinarith [div_pos hpos hden]

/-- Every real Gaussian, including its zero-variance Dirac case, satisfies signed smoothing. -/
theorem gaussianReal_fixedPoint (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    charFun (gaussianReal m v) t = signedSmoothing (charFun (gaussianReal m v) (t / 2)) := by
  simp only [charFun_gaussianReal, signedSmoothing, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- Finite second moments and matching mean and variance identify smoothing fixed points. -/
theorem eq_of_fixedPoint_of_memLp {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν)
    (hfμ : ∀ t, charFun μ t = signedSmoothing (charFun μ (t / 2)))
    (hfν : ∀ t, charFun ν t = signedSmoothing (charFun ν (t / 2)))
    (hmean : (∫ x : ℝ, x ∂μ) = ∫ x : ℝ, x ∂ν)
    (hvariance : variance id μ = variance id ν) : μ = ν := by
  have hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [variance_eq_sub hμ, variance_eq_sub hν] at hvariance
    change (∫ x : ℝ, x ^ 2 ∂μ) - (∫ x : ℝ, x ∂μ) ^ 2 =
      (∫ x : ℝ, x ^ 2 ∂ν) - (∫ x : ℝ, x ∂ν) ^ 2 at hvariance
    rw [hmean] at hvariance
    linarith
  have htaylor (t : ℝ) :
      taylorWithinEval (charFun μ) 2 univ 0 t = taylorWithinEval (charFun ν) 2 univ 0 t := by
    have hμt := taylorWithinEval_charFun_two_zero (P := μ) (X := id)
      measurable_id.aemeasurable (by simpa using hμ) t
    have hνt := taylorWithinEval_charFun_two_zero (P := ν) (X := id)
      measurable_id.aemeasurable (by simpa using hν) t
    simp only [Measure.map_id, id_eq, Pi.pow_apply] at hμt hνt
    rw [hμt, hνt, hmean, hsecond]
  have hsmall : (fun t => charFun μ t - charFun ν t) =o[𝓝 (0 : ℝ)] (fun t => t ^ 2) := by
    have hrem := (taylor_isLittleO_univ (x₀ := (0 : ℝ)) (contDiff_charFun (n := 2) hμ)).sub
      (taylor_isLittleO_univ (x₀ := (0 : ℝ)) (contDiff_charFun (n := 2) hν))
    convert hrem using 1
    · funext t
      rw [htaylor]
      ring
    · simp only [sub_zero]
  exact Measure.ext_of_charFun (fixedPoint_eq_of_isLittleO hfμ hfν
    (norm_charFun_le_one) (norm_charFun_le_one) hsmall)

/-- A finite-second-moment scalar signed-smoothing law is Gaussian with its own mean and variance. -/
theorem eq_gaussianReal_of_memLp {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ)
    (hf : ∀ t, charFun μ t = (charFun μ (t / 2)) ^ 3 * conj (charFun μ (t / 2))) :
    μ = gaussianReal (∫ x : ℝ, x ∂μ) (variance id μ).toNNReal := by
  apply eq_of_fixedPoint_of_memLp hμ (memLp_id_gaussianReal 2) hf
    (gaussianReal_fixedPoint _ _)
  · simp
  · simp [Real.toNNReal_of_nonneg (variance_nonneg id μ)]

/-- Every scalar probability law satisfying signed smoothing is Gaussian with its own moments.
The fixed-point equation supplies the finite second moment used by the uniqueness argument. -/
theorem eq_gaussianReal_of_fixedPoint {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hf : ∀ t, charFun μ t = (charFun μ (t / 2)) ^ 3 * conj (charFun μ (t / 2))) :
    μ = gaussianReal (∫ x : ℝ, x ∂μ) (variance id μ).toNNReal :=
  eq_gaussianReal_of_memLp
    (GaussianSignedSmoothingMoments.memLp_two_of_fixedPoint μ hf) hf

end IDT.QMClosure.GaussianSignedSmoothingCharacterization
