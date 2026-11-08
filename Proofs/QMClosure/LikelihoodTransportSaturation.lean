import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace IDT.QMClosure.LikelihoodTransportSaturation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u v
variable {Ω : Type u} {Ξ : Type v} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]

/-- A nonnegative integrable density has integrable square root over a finite measure. -/
theorem integrable_sqrt {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    Integrable (fun x => Real.sqrt (f x)) μ := by
  apply (hf.add (integrable_const (1 : ℝ))).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [hpos] with x hx
  change 0 ≤ f x at hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_left (by linarith : 0 ≤ f x + 1)).mpr
  nlinarith [sq_nonneg (f x)]

/-- Conditional square-root Jensen on an arbitrary sub-sigma-algebra. -/
theorem condExp_sqrt_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    μ[fun x => Real.sqrt (f x) | m] ≤ᵐ[μ]
      fun x => Real.sqrt (μ[f | m] x) := by
  letI : MeasurableSpace Ω := mΩ
  simpa only [Function.comp_apply] using
    Real.strictConcaveOn_sqrt.concaveOn.condExp_map_le hm
      Real.continuous_sqrt.continuousOn.upperSemicontinuousOn hpos
      isClosed_Ici hf (integrable_sqrt hf hpos)

/-- Equality of square-root averages forces equality with the conditional mean.
The proof uses strict concavity at the midpoint, without conditional distributions. -/
theorem ae_eq_condExp_of_integral_sqrt_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f)
    (heq : (∫ x, Real.sqrt (f x) ∂μ) =
      ∫ x, Real.sqrt (μ[f | m] x) ∂μ) :
    f =ᵐ[μ] μ[f | m] := by
  letI : MeasurableSpace Ω := mΩ
  let q : Ω → ℝ := μ[f | m]
  let r : Ω → ℝ := (1 / 2 : ℝ) • (f + q)
  have hq : Integrable q μ := integrable_condExp
  have hqpos : 0 ≤ᵐ[μ] q := condExp_nonneg hpos
  have hr : Integrable r μ := (hf.add hq).const_mul (1 / 2 : ℝ)
  have hrpos : 0 ≤ᵐ[μ] r := by
    filter_upwards [hpos, hqpos] with x hx hqx
    change 0 ≤ f x at hx
    change 0 ≤ q x at hqx
    change 0 ≤ (1 / 2 : ℝ) * (f x + q x)
    positivity
  have hqr : μ[r | m] =ᵐ[μ] q := by
    have hqq : μ[q | m] = q :=
      condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp hq
    filter_upwards [condExp_smul (μ := μ) (1 / 2 : ℝ) (f + q) m,
      condExp_add hf hq m] with x hx hy
    dsimp [r]
    rw [hx]
    change (1 / 2 : ℝ) * μ[f + q | m] x = q x
    rw [hy]
    simp only [Pi.add_apply, hqq]
    dsimp [q]
    ring
  have hsf := integrable_sqrt hf hpos
  have hsq := integrable_sqrt hq hqpos
  have hsr := integrable_sqrt hr hrpos
  have hupper : (∫ x, Real.sqrt (r x) ∂μ) ≤ ∫ x, Real.sqrt (q x) ∂μ := by
    have hj := condExp_sqrt_le hm hr hrpos
    have hj' : μ[fun x => Real.sqrt (r x) | m] ≤ᵐ[μ]
        fun x => Real.sqrt (q x) := by
      filter_upwards [hj, hqr] with x hx hqx
      simpa only [hqx] using hx
    calc
      (∫ x, Real.sqrt (r x) ∂μ)
          = ∫ x, μ[fun y => Real.sqrt (r y) | m] x ∂μ := (integral_condExp hm).symm
      _ ≤ ∫ x, Real.sqrt (q x) ∂μ := integral_mono_ae integrable_condExp hsq hj'
  let s : Ω → ℝ := fun x => (1 / 2 : ℝ) * (Real.sqrt (f x) + Real.sqrt (q x))
  have hs : Integrable s μ := (hsf.add hsq).const_mul (1 / 2 : ℝ)
  have hpoint : s ≤ᵐ[μ] fun x => Real.sqrt (r x) := by
    filter_upwards [hpos, hqpos] with x hx hqx
    have hc := Real.strictConcaveOn_sqrt.concaveOn.2 hx hqx
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    dsimp [s, r]
    simpa only [smul_eq_mul, mul_add] using hc
  have hsint : (∫ x, s x ∂μ) = ∫ x, Real.sqrt (q x) ∂μ := by
    dsimp [s]
    rw [integral_const_mul, integral_add hsf hsq, heq]
    ring
  have hsame : s =ᵐ[μ] fun x => Real.sqrt (r x) := by
    apply (integral_eq_iff_of_ae_le hs hsr hpoint).mp
    apply le_antisymm (integral_mono_ae hs hsr hpoint)
    rw [hsint]
    exact hupper
  filter_upwards [hpos, hqpos, hsame] with x hx hqx hsx
  by_contra hne
  have hstrict := Real.strictConcaveOn_sqrt.2 hx hqx hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  dsimp [s, r] at hsx
  simp only [mul_add] at hsx
  simp only [smul_eq_mul] at hstrict
  linarith

/-- Square-root affinity of an absolutely continuous measure relative to its reference. -/
def affinity (P Q : Measure Ω) : ℝ := ∫ x, Real.sqrt ((P.rnDeriv Q x).toReal) ∂Q

/-- Statistical processing increases square-root affinity on arbitrary measurable spaces. -/
theorem affinity_map_le (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : P ≪ Q) (g : Ω → Ξ) (hg : Measurable g) :
    affinity P Q ≤ affinity (P.map g) (Q.map g) := by
  letI : IsProbabilityMeasure (Q.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let m := MeasurableSpace.comap g mΞ
  letI : MeasurableSpace Ω := mΩ
  let f : Ω → ℝ := fun x => (P.rnDeriv Q x).toReal
  have hf : Integrable f Q := Measure.integrable_toReal_rnDeriv
  have hpos : 0 ≤ᵐ[Q] f := Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hout := toReal_rnDeriv_map hac hg
  have hsi : Integrable (fun y => Real.sqrt (((P.map g).rnDeriv (Q.map g) y).toReal))
      (Q.map g) := integrable_sqrt (Ω := Ξ) Measure.integrable_toReal_rnDeriv
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have htarget : (fun x => Real.sqrt (Q[f | m] x)) =ᵐ[Q]
      fun x => Real.sqrt (((P.map g).rnDeriv (Q.map g) (g x)).toReal) :=
    hout.symm.fun_comp Real.sqrt
  calc
    affinity P Q = ∫ x, Q[fun y => Real.sqrt (f y) | m] x ∂Q := (integral_condExp hg.comap_le).symm
    _ ≤ ∫ x, Real.sqrt (Q[f | m] x) ∂Q :=
      integral_mono_ae integrable_condExp (integrable_sqrt integrable_condExp (condExp_nonneg hpos))
        (condExp_sqrt_le hg.comap_le hf hpos)
    _ = ∫ x, Real.sqrt (((P.map g).rnDeriv (Q.map g) (g x)).toReal) ∂Q :=
      integral_congr_ae htarget
    _ = affinity (P.map g) (Q.map g) := (integral_map hg.aemeasurable hsi.aestronglyMeasurable).symm

/-- Equality in square-root affinity processing transports the likelihood along the map. -/
theorem likelihood_map_of_affinity_eq (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : P ≪ Q) (g : Ω → Ξ) (hg : Measurable g)
    (heq : affinity P Q = affinity (P.map g) (Q.map g)) :
    (fun x => (P.rnDeriv Q x).toReal) =ᵐ[Q]
      fun x => ((P.map g).rnDeriv (Q.map g) (g x)).toReal := by
  letI : IsProbabilityMeasure (Q.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let m := MeasurableSpace.comap g mΞ
  letI : MeasurableSpace Ω := mΩ
  let f : Ω → ℝ := fun x => (P.rnDeriv Q x).toReal
  have hout := toReal_rnDeriv_map hac hg
  have hsi : Integrable (fun y => Real.sqrt (((P.map g).rnDeriv (Q.map g) y).toReal))
      (Q.map g) := integrable_sqrt (Ω := Ξ) Measure.integrable_toReal_rnDeriv
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have heq' : (∫ x, Real.sqrt (f x) ∂Q) = ∫ x, Real.sqrt (Q[f | m] x) ∂Q := by
    calc
      _ = affinity (P.map g) (Q.map g) := heq
      _ = ∫ x, Real.sqrt (((P.map g).rnDeriv (Q.map g) (g x)).toReal) ∂Q :=
        integral_map hg.aemeasurable hsi.aestronglyMeasurable
      _ = _ := integral_congr_ae (hout.fun_comp Real.sqrt)
  exact (ae_eq_condExp_of_integral_sqrt_eq hg.comap_le
    Measure.integrable_toReal_rnDeriv
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) heq').trans hout.symm

/-- Adding one common Markov kernel preserves square-root affinity. -/
theorem affinity_compProd (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel Ω Ξ) [IsMarkovKernel κ] :
    affinity (P ⊗ₘ κ) (Q ⊗ₘ κ) = affinity P Q := by
  have hd := rnDeriv_measure_compProd_left P Q κ
  calc
    affinity (P ⊗ₘ κ) (Q ⊗ₘ κ)
        = ∫ z, Real.sqrt ((P.rnDeriv Q z.1).toReal) ∂(Q ⊗ₘ κ) := by
            apply integral_congr_ae
            filter_upwards [hd] with z hz
            rw [hz]
    _ = ∫ x, Real.sqrt ((P.rnDeriv Q x).toReal) ∂(Q ⊗ₘ κ).fst := by
      exact (integral_map (μ := Q ⊗ₘ κ) (φ := Prod.fst)
        measurable_fst.aemeasurable
        (f := fun x => Real.sqrt ((P.rnDeriv Q x).toReal))
        (Real.continuous_sqrt.measurable.comp
          (Measure.measurable_rnDeriv P Q).ennreal_toReal).aestronglyMeasurable).symm
    _ = affinity P Q := by rw [Measure.fst_compProd]; rfl

/-- A common Markov channel increases square-root affinity. -/
theorem affinity_markov_le (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : P ≪ Q) (κ : Kernel Ω Ξ) [IsMarkovKernel κ] :
    affinity P Q ≤ affinity (κ ∘ₘ P) (κ ∘ₘ Q) := by
  have h := affinity_map_le (P ⊗ₘ κ) (Q ⊗ₘ κ)
    (hac.compProd_left κ) Prod.snd measurable_snd
  change affinity (P ⊗ₘ κ) (Q ⊗ₘ κ) ≤
    affinity (P ⊗ₘ κ).snd (Q ⊗ₘ κ).snd at h
  simpa only [affinity_compProd, Measure.snd_compProd] using h

/-- Saturation transports input likelihood to output likelihood along the actual channel.
No conditional distribution for the reverse channel is selected. -/
theorem likelihood_markov_of_affinity_eq (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : P ≪ Q) (κ : Kernel Ω Ξ) [IsMarkovKernel κ]
    (heq : affinity P Q = affinity (κ ∘ₘ P) (κ ∘ₘ Q)) :
    (fun z : Ω × Ξ => (P.rnDeriv Q z.1).toReal) =ᵐ[Q ⊗ₘ κ]
      fun z => ((κ ∘ₘ P).rnDeriv (κ ∘ₘ Q) z.2).toReal := by
  have heq' : affinity (P ⊗ₘ κ) (Q ⊗ₘ κ) =
      affinity ((P ⊗ₘ κ).map Prod.snd) ((Q ⊗ₘ κ).map Prod.snd) := by
    change affinity (P ⊗ₘ κ) (Q ⊗ₘ κ) =
      affinity (P ⊗ₘ κ).snd (Q ⊗ₘ κ).snd
    simpa only [affinity_compProd, Measure.snd_compProd] using heq
  have h := likelihood_map_of_affinity_eq (P ⊗ₘ κ) (Q ⊗ₘ κ)
    (hac.compProd_left κ) Prod.snd measurable_snd heq'
  have hd := (rnDeriv_measure_compProd_left P Q κ).fun_comp ENNReal.toReal
  change (fun z => ((P ⊗ₘ κ).rnDeriv (Q ⊗ₘ κ) z).toReal) =ᵐ[Q ⊗ₘ κ]
    fun z => ((P ⊗ₘ κ).snd.rnDeriv (Q ⊗ₘ κ).snd z.2).toReal at h
  simpa only [Measure.snd_compProd] using hd.symm.trans h

end
end IDT.QMClosure.LikelihoodTransportSaturation
