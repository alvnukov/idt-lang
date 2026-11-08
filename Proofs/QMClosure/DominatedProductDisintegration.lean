import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Dominated product disintegration on arbitrary measurable spaces

A probability joint dominated by a probability product admits an explicit
Markov disintegration relative to the second reference measure. The construction
normalizes the joint Radon–Nikodym density row by row and uses the supplied
second reference on zero or infinite rows.
-/

namespace IDT.QMClosure.DominatedProductDisintegration

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

universe u v
variable {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]

/-- Integrating a product density in the second coordinate gives its first marginal. -/
theorem fst_withDensity_prod (α : Measure A) (β : Measure B) [SFinite β]
    (f : A × B → ℝ≥0∞) (hf : Measurable f) :
    ((α.prod β).withDensity f).fst =
      α.withDensity (fun x => ∫⁻ y, f (x, y) ∂β) := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs]
  rw [lintegral_prod _ (hf.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [hx]

/-- A dominated probability joint has a Markov disintegration whose rows remain
absolutely continuous with respect to the second reference. -/
theorem exists_markov_disintegration_of_ac
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hac : ν ≪ α.prod β) :
    ∃ κ : Kernel A B, IsMarkovKernel κ ∧ ν.fst ⊗ₘ κ = ν ∧
      ∀ x, κ x ≪ β := by
  classical
  let f : A × B → ℝ≥0∞ := ν.rnDeriv (α.prod β)
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hν : (α.prod β).withDensity f = ν :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  let r : A → ℝ≥0∞ := fun x => ∫⁻ y, f (x, y) ∂β
  have hr : Measurable r := hf.lintegral_prod_right'
  have hfst : α.withDensity r = ν.fst := by
    rw [← hν, fst_withDensity_prod α β f hf]
  have htotal : ∫⁻ x, r x ∂α = 1 := by
    have h := congrArg (fun μ : Measure A => μ univ) hfst
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      measure_univ] using h
  have hfinite : ∀ᵐ x ∂α, r x < ∞ := ae_lt_top hr (by rw [htotal]; simp)
  let g : A × B → ℝ≥0∞ := fun p =>
    if r p.1 = 0 ∨ r p.1 = ∞ then 1 else (r p.1)⁻¹ * f p
  have hg : Measurable g := by
    apply Measurable.ite
      ((measurableSet_eq_fun (hr.comp measurable_fst) measurable_const).union
        (measurableSet_eq_fun (hr.comp measurable_fst) measurable_const))
    · exact measurable_const
    · exact (hr.comp measurable_fst).inv.mul hf
  have hrow : ∀ x, ∫⁻ y, g (x, y) ∂β = 1 := by
    intro x
    by_cases hx : r x = 0 ∨ r x = ∞
    · simp [g, hx]
    · simp only [g, hx, if_false]
      rw [lintegral_const_mul (r x)⁻¹
        (f := fun y : B => f (x, y)) (hf.comp measurable_prodMk_left)]
      exact ENNReal.inv_mul_cancel (not_or.mp hx).1 (not_or.mp hx).2
  let κ : Kernel A B := (Kernel.const A β).withDensity (fun x y => g (x, y))
  have hg' : Measurable (Function.uncurry (fun x y => g (x, y))) := hg
  letI : IsMarkovKernel κ := ⟨fun x => ⟨by
    change ((Kernel.const A β).withDensity (fun x y => g (x, y)) x) univ = 1
    rw [Kernel.withDensity_apply' _ hg', Kernel.const_apply, Measure.restrict_univ]
    exact hrow x⟩⟩
  have hcancel : (fun p : A × B => r p.1 * g p) =ᵐ[α.prod β] f := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun ((hr.comp measurable_fst).mul hg) hf)).mpr
    filter_upwards [hfinite] with x hx
    by_cases hz : r x = 0
    · have hzrow : (fun y => f (x, y)) =ᵐ[β] 0 :=
        (lintegral_eq_zero_iff (hf.comp measurable_prodMk_left)).mp hz
      filter_upwards [hzrow] with y hy
      simp [g, hz, hy]
    · exact Filter.Eventually.of_forall fun y => by
        simp only [g, if_neg (not_or.mpr ⟨hz, ne_of_lt hx⟩)]
        exact ENNReal.mul_inv_cancel_left hz (ne_of_lt hx)
  refine ⟨κ, inferInstance, ?_, ?_⟩
  · change ν.fst ⊗ₘ (Kernel.const A β).withDensity (fun x y => g (x, y)) = ν
    rw [Measure.compProd_withDensity hg', Measure.compProd_const, ← hfst,
      prod_withDensity_left hr]
    change ((α.prod β).withDensity (fun p => r p.1)).withDensity g = ν
    rw [← withDensity_mul (α.prod β) (f := fun p : A × B => r p.1)
      (g := g) (hr.comp measurable_fst) hg]
    exact (withDensity_congr_ae hcancel).trans hν
  · intro x
    exact Kernel.withDensity_absolutelyContinuous _ x

end
end IDT.QMClosure.DominatedProductDisintegration
