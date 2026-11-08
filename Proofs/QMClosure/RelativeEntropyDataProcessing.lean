import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Classical relative entropy under statistical processing

These results concern ordinary probability measures on arbitrary measurable spaces.
Conditional Jensen supplies the pushforward inequality. Common-kernel joint invariance
then supplies Markov data processing. No conditional distribution or disintegration
is selected. Product additivity follows from the KL chain rule and measurable swap.
The inequalities are proved in ENNReal before any finite-entropy real comparison is used.
-/

namespace IDT.QMClosure.RelativeEntropyDataProcessing

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

universe u v
variable {Ω : Type u} {Ξ : Type v} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]

/-- Deterministic statistical processing cannot increase relative entropy. -/
theorem klDiv_map_le (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (g : Ω → Ξ) (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  by_cases hfin : klDiv μ ν = ∞
  · simp [hfin]
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfin
  let m := MeasurableSpace.comap g mΞ
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hg.comap_le
  let r : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hr : Integrable r ν := Measure.integrable_toReal_rnDeriv
  have hφ : Integrable (klFun ∘ r) ν :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hj := convexOn_klFun.map_condExp_le (f := r) (μ := ν) (m := m) hm
    continuous_klFun.continuousOn.lowerSemicontinuousOn
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    isClosed_Ici hr hφ
  have hd := toReal_rnDeriv_map hac hg
  have hnonneg : 0 ≤ᵐ[ν] klFun ∘ r :=
    Filter.Eventually.of_forall fun x => klFun_nonneg ENNReal.toReal_nonneg
  calc
    klDiv (μ.map g) (ν.map g)
        = ∫⁻ x, ENNReal.ofReal (klFun (((μ.map g).rnDeriv (ν.map g) x).toReal))
            ∂(ν.map g) := klDiv_eq_lintegral_klFun_of_ac (hac.map hg)
    _ = ∫⁻ x, ENNReal.ofReal (klFun (((μ.map g).rnDeriv (ν.map g) (g x)).toReal))
            ∂ν := lintegral_map (by fun_prop) hg
    _ ≤ ∫⁻ x, ENNReal.ofReal (ν[klFun ∘ r | m] x) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hd, hj] with x hdx hjx
      apply ENNReal.ofReal_le_ofReal
      simpa only [hdx, Function.comp_apply] using hjx
    _ = ENNReal.ofReal (∫ x, ν[klFun ∘ r | m] x ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_condExp
        (condExp_nonneg hnonneg)).symm
    _ = ENNReal.ofReal (∫ x, klFun (r x) ∂ν) := by
      rw [integral_condExp hm]
      rfl
    _ = klDiv μ ν := by
      rw [klDiv_eq_integral_klFun, if_pos ⟨hac, hint⟩]

/-- This consequence justifies subsequent uses of the real-valued divergence. -/
theorem klDiv_map_ne_top (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (g : Ω → Ξ) (hg : Measurable g)
    (hfin : klDiv μ ν ≠ ∞) : klDiv (μ.map g) (ν.map g) ≠ ∞ :=
  ne_top_of_le_ne_top hfin (klDiv_map_le μ ν g hg)

/-- Coordinate invariance uses both measurable inverse maps. -/
theorem klDiv_map_measurableEquiv (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (e : Ω ≃ᵐ Ξ) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  letI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  apply le_antisymm (klDiv_map_le μ ν e e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm e.symm.measurable
  simpa only [MeasurableEquiv.map_symm_map] using h

/-- Relabelling the two product coordinates leaves the divergence unchanged. -/
theorem klDiv_prod_swap (μ ν : Measure Ω) (ρ σ : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    klDiv (ρ.prod μ) (σ.prod ν) = klDiv (μ.prod ρ) (ν.prod σ) := by
  have h := klDiv_map_measurableEquiv (μ.prod ρ) (ν.prod σ)
    (MeasurableEquiv.prodComm : Ω × Ξ ≃ᵐ Ξ × Ω)
  change klDiv (Measure.map Prod.swap (μ.prod ρ))
    (Measure.map Prod.swap (ν.prod σ)) = _ at h
  simpa only [Measure.prod_swap] using h

/-- Relative entropy is additive on independent products, including infinite values. -/
theorem klDiv_prod (μ ν : Measure Ω) (ρ σ : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    klDiv (μ.prod ρ) (ν.prod σ) = klDiv μ ν + klDiv ρ σ := by
  have hchain := klDiv_compProd_eq_add μ ν (Kernel.const Ω ρ) (Kernel.const Ω σ)
  simp only [Measure.compProd_const] at hchain
  rw [hchain, ← klDiv_prod_swap μ μ ρ σ]
  have hleft := klDiv_compProd_left ρ σ (Kernel.const Ξ μ)
  simpa only [Measure.compProd_const] using congrArg (fun z => klDiv μ ν + z) hleft

/-- One common Markov kernel contracts KL on arbitrary measurable spaces. -/
theorem klDiv_markov_le (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : Kernel Ω Ξ) [IsMarkovKernel T] :
    klDiv (T ∘ₘ μ) (T ∘ₘ ν) ≤ klDiv μ ν := by
  have h := klDiv_map_le (μ ⊗ₘ T) (ν ⊗ₘ T) Prod.snd measurable_snd
  change klDiv (μ ⊗ₘ T).snd (ν ⊗ₘ T).snd ≤ _ at h
  simpa only [Measure.snd_compProd, klDiv_compProd_left] using h

end
end IDT.QMClosure.RelativeEntropyDataProcessing
