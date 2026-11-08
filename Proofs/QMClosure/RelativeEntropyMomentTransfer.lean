import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Relative entropy transfer from a reciprocal density moment

Finite relative entropy with respect to one reference measure transfers to an
equivalent probability measure whose reciprocal quarter density is integrable.
The reciprocal moment is an explicit analytic hypothesis.
-/

namespace IDT.QMClosure.RelativeEntropyMomentTransfer

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

private theorem entropy_young (a b : ℝ) (ha : 0 ≤ a) :
    a * b ≤ klFun a + Real.exp b := by
  by_cases hzero : a = 0
  · simp only [hzero, zero_mul, klFun_zero]
    positivity
  have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
  have hexp : a * Real.exp (b - Real.log a) = Real.exp b := by
    rw [Real.exp_sub, Real.exp_log hpos]
    field_simp
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b - Real.log a)) ha
  rw [hexp] at h
  unfold klFun
  nlinarith

/-- An exponential absolute quarter moment follows from the reciprocal quarter
moment and normalization of the forward density. -/
theorem integrable_exp_abs_llr_quarter (Q α : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure α] (hαQ : α ≪ Q)
    (hmoment : Integrable (fun x => Real.exp (-llr Q α x / 4)) α) :
    Integrable (fun x => Real.exp (|llr Q α x| / 4)) α := by
  have hdensity : Integrable (fun x => (Q.rnDeriv α x).toReal) α :=
    Measure.integrable_toReal_rnDeriv
  apply (hdensity.add hmoment).mono' (by fun_prop)
  filter_upwards [exp_llr_of_ac' Q α hαQ] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hsign : 0 ≤ llr Q α x
  · have hle : Real.exp (|llr Q α x| / 4) ≤ (Q.rnDeriv α x).toReal := by
      rw [← hx]
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg hsign]
      linarith
    exact le_add_of_le_of_nonneg hle (le_of_lt (Real.exp_pos _))
  · rw [abs_of_nonpos (le_of_not_ge hsign)]
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg

/-- Finite entropy controls cross-log integrability under the explicit
reciprocal quarter moment of the second reference density. -/
theorem integrable_llr_of_reciprocal_quarter_moment (P Q α : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure α]
    (hP : klDiv P α ≠ ∞) (hαQ : α ≪ Q)
    (hmoment : Integrable (fun x => Real.exp (-llr Q α x / 4)) α) :
    Integrable (llr Q α) P := by
  obtain ⟨hPα, hlog⟩ := klDiv_ne_top_iff.mp hP
  have hentropy := (integrable_klFun_rnDeriv_iff hPα).mpr hlog
  have hexp := integrable_exp_abs_llr_quarter Q α hαQ hmoment
  have hweighted : Integrable
      (fun x => (P.rnDeriv α x).toReal * (llr Q α x / 4)) α := by
    apply (hentropy.add hexp).mono' (by fun_prop)
    filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact entropy_young _ _ ENNReal.toReal_nonneg
  have hquarter : Integrable (fun x => llr Q α x / 4) P :=
    (integrable_toReal_rnDeriv_mul_iff hPα).mp hweighted
  convert hquarter.const_mul 4 using 1
  ext x
  ring

/-- The likelihood-ratio chain identity under a common dominating measure. -/
theorem llr_sub_of_equivalent_reference (P Q α : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure α]
    (hPα : P ≪ α) (hQα : Q ≪ α) (hαQ : α ≪ Q) :
    llr P Q =ᵐ[P] fun x => llr P α x - llr Q α x := by
  have hPQ : P ≪ Q := hPα.trans hαQ
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_eq_div hPα hQα),
    Measure.rnDeriv_pos hPα, hPα.ae_le (Measure.rnDeriv_ne_top P α),
    hPα.ae_le (Measure.rnDeriv_pos' hαQ),
    hPα.ae_le (Measure.rnDeriv_ne_top Q α)] with x hratio hppos hpfin hqpos hqfin
  have hp : (P.rnDeriv α x).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hppos.ne' hpfin)
  have hq : (Q.rnDeriv α x).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hqpos.ne' hqfin)
  simp only [llr, hratio, ENNReal.toReal_div, Real.log_div hp hq]

/-- A reciprocal quarter density moment transfers finite relative entropy
between equivalent reference probability measures. -/
theorem klDiv_ne_top_of_reciprocal_quarter_moment (P Q α : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure α]
    (hP : klDiv P α ≠ ∞) (hQα : Q ≪ α) (hαQ : α ≪ Q)
    (hmoment : Integrable (fun x => Real.exp (-llr Q α x / 4)) α) :
    klDiv P Q ≠ ∞ := by
  obtain ⟨hPα, hlog⟩ := klDiv_ne_top_iff.mp hP
  apply klDiv_ne_top (hPα.trans hαQ)
  exact (hlog.sub (integrable_llr_of_reciprocal_quarter_moment P Q α hP hαQ hmoment)).congr
    (llr_sub_of_equivalent_reference P Q α hPα hQα hαQ).symm

end
end IDT.QMClosure.RelativeEntropyMomentTransfer
