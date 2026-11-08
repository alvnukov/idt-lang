import Proofs.QMClosure.RelativeEntropyDataProcessing
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Relative entropy of a Gaussian location family

The sample space is the ordinary measurable product of two real coordinates.
Each coordinate has supplied unit variance. The Gaussian law and its scale are
supplied inputs of this concrete classical statistical model.
-/

namespace IDT.QMClosure.GaussianLocationEntropy

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-- Independent unit-variance real Gaussian coordinates with complex location. -/
def preparation (z : ℂ) : Measure (ℝ × ℝ) :=
  (gaussianReal z.re 1).prod (gaussianReal z.im 1)

instance preparation_isProbabilityMeasure (z : ℂ) : IsProbabilityMeasure (preparation z) := by
  unfold preparation
  infer_instance

/-- Nondegenerate Gaussian location laws are mutually absolutely continuous. -/
theorem gaussianReal_ac (a b : ℝ) : gaussianReal a 1 ≪ gaussianReal b 1 :=
  (gaussianReal_absolutelyContinuous a one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' b one_ne_zero)

private theorem log_gaussianPDFReal (a t : ℝ) :
    Real.log (gaussianPDFReal a 1 t) =
      Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - (t - a) ^ 2 / 2 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The actual likelihood ratio is affine after the equal-variance cancellation. -/
theorem llr_gaussianReal (a b : ℝ) :
    llr (gaussianReal a 1) (gaussianReal b 1) =ᵐ[gaussianReal a 1]
      fun t => (a - b) * t + (b ^ 2 - a ^ 2) / 2 := by
  have ha := gaussianReal_absolutelyContinuous a (v := 1) one_ne_zero
  have hb := gaussianReal_absolutelyContinuous b (v := 1) one_ne_zero
  have hr := (gaussianReal_ac a b).ae_le (Measure.rnDeriv_eq_div ha hb)
  filter_upwards [hr, ha.ae_le (rnDeriv_gaussianReal a 1),
    ha.ae_le (rnDeriv_gaussianReal b 1)] with t ht hat hbt
  simp only [llr, ht, hat, hbt, ENNReal.toReal_div, toReal_gaussianPDF]
  rw [Real.log_div (gaussianPDFReal_pos a 1 t one_ne_zero).ne'
    (gaussianPDFReal_pos b 1 t one_ne_zero).ne',
    log_gaussianPDFReal, log_gaussianPDFReal]
  ring

/-- Equal-variance Gaussian log-likelihood ratios have a finite first moment. -/
theorem integrable_llr_gaussianReal (a b : ℝ) :
    Integrable (llr (gaussianReal a 1) (gaussianReal b 1)) (gaussianReal a 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal a 1) :=
    (memLp_one_iff_integrable).mp (memLp_id_gaussianReal (μ := a) (v := 1) 1)
  exact ((hid.const_mul (a - b)).add (integrable_const ((b ^ 2 - a ^ 2) / 2))).congr
    (llr_gaussianReal a b).symm

/-- KL is computed from the actual Gaussian Radon–Nikodym derivative. -/
theorem klDiv_gaussianReal (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1) =
      ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal a 1) :=
    (memLp_one_iff_integrable).mp (memLp_id_gaussianReal (μ := a) (v := 1) 1)
  rw [klDiv_of_ac_of_integrable (gaussianReal_ac a b) (integrable_llr_gaussianReal a b)]
  rw [integral_congr_ae (llr_gaussianReal a b),
    integral_add (hid.const_mul (a - b)) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  ring

/-- Every ordered pair in the scalar location family has finite KL. -/
theorem gaussianReal_klDiv_ne_top (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1) ≠ ∞ := by
  rw [klDiv_gaussianReal]
  exact ENNReal.ofReal_ne_top

/-- Independent coordinates add their actual KL values. -/
theorem klDiv_preparation (x y : ℂ) :
    klDiv (preparation x) (preparation y) =
      ENNReal.ofReal (Complex.normSq (x - y) / 2) := by
  rw [preparation, preparation, RelativeEntropyDataProcessing.klDiv_prod,
    klDiv_gaussianReal, klDiv_gaussianReal, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- Finiteness is established before using the real-valued comparison. -/
theorem klDiv_preparation_ne_top (x y : ℂ) :
    klDiv (preparation x) (preparation y) ≠ ∞ := by
  rw [klDiv_preparation]
  exact ENNReal.ofReal_ne_top

/-- The ordinary Jeffreys comparison is squared Euclidean location separation. -/
theorem jeffreys_preparation (x y : ℂ) :
    (klDiv (preparation x) (preparation y)).toReal +
      (klDiv (preparation y) (preparation x)).toReal = Complex.normSq (x - y) := by
  rw [klDiv_preparation, klDiv_preparation,
    ENNReal.toReal_ofReal (div_nonneg (Complex.normSq_nonneg _) (by norm_num)),
    ENNReal.toReal_ofReal (div_nonneg (Complex.normSq_nonneg _) (by norm_num))]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The supplied normalization gives a nonzero, finite unit-location comparison. -/
theorem jeffreys_zero_one :
    (klDiv (preparation 0) (preparation 1)).toReal +
      (klDiv (preparation 1) (preparation 0)).toReal = 1 := by
  simpa using jeffreys_preparation 0 1

/-- The actual measure family is nonconstant. -/
theorem preparation_zero_ne_one : preparation 0 ≠ preparation 1 := by
  intro h
  have hk := klDiv_preparation 0 1
  rw [h, klDiv_self] at hk
  norm_num at hk

end
end IDT.QMClosure.GaussianLocationEntropy
