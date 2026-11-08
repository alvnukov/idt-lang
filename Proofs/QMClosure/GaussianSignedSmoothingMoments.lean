import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Second moments forced by the signed smoothing equation

For an arbitrary probability law on the real line, the characteristic-function
fixed-point equation for three positive and one negative half-scale summands
forces a finite second moment. No moment, density, or nondegeneracy hypothesis
is imposed. The proof uses the symmetrized law and nonnegative cosine kernels.
-/

open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace IDT.QMClosure.GaussianSignedSmoothingMoments

noncomputable section

/-- The exact characteristic-function equation of signed half-scale smoothing. -/
def FixedPoint (μ : Measure ℝ) : Prop :=
  ∀ t : ℝ, charFun μ t = (charFun μ (t / 2)) ^ 3 * conj (charFun μ (t / 2))

private def psi (μ : Measure ℝ) (t : ℝ) : ℝ := Complex.normSq (charFun μ t)

private lemma psi_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ psi μ t :=
  Complex.normSq_nonneg _

private lemma psi_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    psi μ t ≤ 1 := by
  rw [psi, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (charFun μ t), norm_charFun_le_one (μ := μ) t]

private lemma psi_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : psi μ 0 = 1 := by
  simp [psi]

private lemma continuous_psi (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Continuous (psi μ) := by
  exact Complex.continuous_normSq.comp continuous_charFun

private lemma psi_half (μ : Measure ℝ) (h : FixedPoint μ) (t : ℝ) :
    psi μ t = (psi μ (t / 2)) ^ 4 := by
  unfold psi
  rw [h t, Complex.normSq_mul, map_pow, Complex.normSq_conj]
  ring

private lemma dyadic_pow (μ : Measure ℝ) (h : FixedPoint μ) (n : ℕ) :
    (psi μ ((1 / 2 : ℝ) ^ n)) ^ (4 ^ n) = psi μ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2 := by
      rw [pow_succ]
      ring
    rw [hs, pow_succ', pow_mul, ← psi_half μ h]
    exact ih

private lemma psi_one_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : FixedPoint μ) : 0 < psi μ 1 := by
  by_contra hp
  have hz : psi μ 1 = 0 := le_antisymm (le_of_not_gt hp) (psi_nonneg μ 1)
  have hall (n : ℕ) : psi μ ((1 / 2 : ℝ) ^ n) = 0 := by
    have hn := dyadic_pow μ h n
    rw [hz] at hn
    exact eq_zero_of_pow_eq_zero hn
  have ht : Tendsto (fun n : ℕ => psi μ ((1 / 2 : ℝ) ^ n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [psi_zero] using (continuous_psi μ).continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have : (0 : ℝ) = 1 := tendsto_nhds_unique (by simpa only [hall] using tendsto_const_nhds) ht
  norm_num at this

private lemma geometric_bound {q c : ℝ} {N : ℕ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hpow : q ^ N = c) : (N : ℝ) * (1 - q) ≤ (1 - c) / c := by
  have hsum : (N : ℝ) * c ≤ ∑ i ∈ Finset.range N, q ^ i := by
    calc
      (N : ℝ) * c = ∑ i ∈ Finset.range N, c := by simp
      _ ≤ ∑ i ∈ Finset.range N, q ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← hpow]
        exact pow_le_pow_of_le_one hq hq1 (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hgeom := geom_sum_mul_neg q N
  rw [hpow] at hgeom
  have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hq1)
  apply (le_div_iff₀ hc).2
  nlinarith

private def symLaw (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)

private instance symLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symLaw μ) := by
  unfold symLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma symLaw_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (symLaw μ) t = (psi μ t : ℂ) := by
  rw [charFun_apply_real, symLaw, integral_map (by fun_prop) (by fun_prop)]
  calc
    (∫ p : ℝ × ℝ, Complex.exp ((t : ℂ) * ↑(p.1 - p.2) * Complex.I) ∂μ.prod μ) =
        ∫ p : ℝ × ℝ,
          Complex.exp ((t : ℂ) * p.1 * Complex.I) *
            Complex.exp ((-t : ℂ) * p.2 * Complex.I) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = charFun μ t * charFun μ (-t) := by
      simpa only [charFun_apply_real, Complex.ofReal_neg] using
        (integral_prod_mul (μ := μ) (ν := μ)
          (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I))
          (fun x : ℝ => Complex.exp ((-t : ℂ) * x * Complex.I)))
    _ = (psi μ t : ℂ) := by rw [charFun_neg, Complex.mul_conj]; rfl

private lemma integrable_cos (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => Real.cos (t * x)) ν := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  exact Real.abs_cos_le_one _

private lemma integral_cos_symLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) ∂symLaw μ = psi μ t := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I))
      (symLaw μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with x
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  calc
    (∫ x : ℝ, Real.cos (t * x) ∂symLaw μ) =
        ∫ x : ℝ, (Complex.exp ((t : ℂ) * x * Complex.I)).re ∂symLaw μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]
    _ = (∫ x : ℝ, Complex.exp ((t : ℂ) * x * Complex.I) ∂symLaw μ).re := integral_re hi
    _ = psi μ t := by
      rw [← charFun_apply_real, symLaw_charFun, Complex.ofReal_re]

private def cosineKernel (n : ℕ) (x : ℝ) : ℝ :=
  (4 : ℝ) ^ n * (1 - Real.cos (((1 / 2 : ℝ) ^ n) * x))

private lemma cosineKernel_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cosineKernel n x := by
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))

private lemma cosineKernel_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    Integrable (cosineKernel n) ν := by
  exact ((integrable_const (1 : ℝ)).sub (integrable_cos ν _)).const_mul _

private lemma integral_cosineKernel (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ x, cosineKernel n x ∂symLaw μ =
      (4 : ℝ) ^ n * (1 - psi μ ((1 / 2 : ℝ) ^ n)) := by
  unfold cosineKernel
  rw [integral_const_mul,
    integral_sub (integrable_const _) (integrable_cos _ _), integral_const,
    integral_cos_symLaw]
  simp

private lemma sinc_mul_arg (x : ℝ) : Real.sinc x * x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx, div_mul_cancel₀ _ hx]

private lemma cosineKernel_eq_sinc (n : ℕ) (x : ℝ) :
    cosineKernel n x = x ^ 2 / 2 * (Real.sinc (((1 / 2 : ℝ) ^ n) * x / 2)) ^ 2 := by
  have hscale : (4 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow]
    norm_num
  have hcos := Real.cos_two_mul_eq_one_sub (((1 / 2 : ℝ) ^ n) * x / 2)
  have harg : 2 * (((1 / 2 : ℝ) ^ n) * x / 2) = ((1 / 2 : ℝ) ^ n) * x := by ring
  rw [harg] at hcos
  unfold cosineKernel
  rw [hcos, ← sinc_mul_arg]
  calc
    (4 : ℝ) ^ n * (1 - (1 - 2 * (Real.sinc (((1 / 2 : ℝ) ^ n) * x / 2) *
        (((1 / 2 : ℝ) ^ n) * x / 2)) ^ 2)) =
      ((4 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ 2) *
        (x ^ 2 / 2 * Real.sinc (((1 / 2 : ℝ) ^ n) * x / 2) ^ 2) := by ring
    _ = _ := by rw [hscale, one_mul]

private lemma cosineKernel_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => cosineKernel n x) atTop (𝓝 (x ^ 2 / 2)) := by
  simp_rw [cosineKernel_eq_sinc]
  have ht : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n) * x / 2) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const x |>.div_const 2
      using 1
    simp
  convert ((Real.continuous_sinc.continuousAt.tendsto.comp ht).pow 2).const_mul (x ^ 2 / 2)
    using 1
  simp

private lemma symLaw_integrable_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : FixedPoint μ) : Integrable (fun x : ℝ => x ^ 2) (symLaw μ) := by
  have hc := psi_one_pos μ h
  let C : ℝ := (1 - psi μ 1) / psi μ 1
  have hbound (n : ℕ) : ∫ x, cosineKernel n x ∂symLaw μ ≤ C := by
    rw [integral_cosineKernel]
    have hb := geometric_bound (psi_nonneg μ ((1 / 2 : ℝ) ^ n))
      (psi_le_one μ ((1 / 2 : ℝ) ^ n)) hc (dyadic_pow μ h n)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hb
  have hlin (n : ℕ) : ∫⁻ x, ‖cosineKernel n x‖ₑ ∂symLaw μ ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (cosineKernel_integrable (symLaw μ) n)]
    have hn : (fun x => ‖cosineKernel n x‖) = cosineKernel n := by
      funext x
      exact Real.norm_of_nonneg (cosineKernel_nonneg n x)
    rw [hn]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlim : liminf (fun n : ℕ => ∫⁻ x, ‖cosineKernel n x‖ₑ ∂symLaw μ) atTop ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt
      (liminf_le_of_frequently_le' (Frequently.of_forall hlin)) ENNReal.ofReal_lt_top
  have hi : Integrable (fun x : ℝ => x ^ 2 / 2) (symLaw μ) :=
    integrable_of_tendsto (ae_of_all _ cosineKernel_tendsto)
      (fun n => (cosineKernel_integrable (symLaw μ) n).aestronglyMeasurable) hlim
  convert hi.const_mul 2 using 1
  funext x
  ring

/-- The signed smoothing equation alone forces a finite second moment. -/
theorem integrable_sq_of_fixedPoint (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ t : ℝ, charFun μ t = (charFun μ (t / 2)) ^ 3 * conj (charFun μ (t / 2))) :
    Integrable (fun x : ℝ => x ^ 2) μ := by
  have hi := symLaw_integrable_sq μ h
  have hp : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) :=
    hi.comp_aemeasurable (by fun_prop)
  obtain ⟨y, hy⟩ := hp.prod_left_ae.exists
  apply ((hy.const_mul 2).add (integrable_const (2 * y ^ 2))).mono_nonneg
    (by fun_prop) (ae_of_all _ fun x => sq_nonneg x)
  filter_upwards [] with x
  dsimp
  nlinarith [sq_nonneg (x - 2 * y)]

/-- No finite-moment premise is needed to enter the `L²` Gaussian analysis. -/
theorem memLp_two_of_fixedPoint (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ t : ℝ, charFun μ t = (charFun μ (t / 2)) ^ 3 * conj (charFun μ (t / 2))) :
    MemLp (fun x : ℝ => x) 2 μ := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 (integrable_sq_of_fixedPoint μ h)

end

end IDT.QMClosure.GaussianSignedSmoothingMoments
