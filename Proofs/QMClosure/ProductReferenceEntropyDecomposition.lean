import Proofs.QMClosure.DominatedProductDisintegration
import Proofs.QMClosure.RelativeEntropyDataProcessing

/-!
# Product-reference relative entropy decomposition

For a joint probability measure, extended relative entropy against a supplied
probability product separates into its mutual-information term and the two
marginal relative entropies. The dominated case uses an explicit normalized
density construction on arbitrary measurable spaces. The nondominated case is
resolved by an infinite term. Finite readouts retain explicit finiteness premises.
-/

namespace IDT.QMClosure.ProductReferenceEntropyDecomposition

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open IDT.QMClosure.RelativeEntropyDataProcessing
open IDT.QMClosure.DominatedProductDisintegration

universe u v
variable {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]

private theorem joint_ac_marginal_prod_right
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hac : ν ≪ α.prod β) : ν ≪ ν.fst.prod β := by
  obtain ⟨κ, hκ, hdis, hrow⟩ := exists_markov_disintegration_of_ac ν α β hac
  letI : IsMarkovKernel κ := hκ
  have hrows : ∀ᵐ x ∂ν.fst, κ x ≪ (Kernel.const A β) x :=
    Filter.Eventually.of_forall hrow
  have h := Measure.AbsolutelyContinuous.compProd_right hrows
  simpa only [hdis, Measure.compProd_const] using h

private theorem product_reference_chain
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hac : ν ≪ α.prod β) :
    klDiv ν (α.prod β) = klDiv ν.fst α + klDiv ν (ν.fst.prod β) := by
  obtain ⟨κ, hκ, hdis, _⟩ := exists_markov_disintegration_of_ac ν α β hac
  letI : IsMarkovKernel κ := hκ
  have h := klDiv_compProd_eq_add ν.fst α κ (Kernel.const A β)
  simpa only [hdis, Measure.compProd_const] using h

/-- The extended-valued decomposition in the dominated case. -/
theorem product_reference_decomposition_of_ac
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hac : ν ≪ α.prod β) :
    klDiv ν (α.prod β) = klDiv ν (ν.fst.prod ν.snd) +
      klDiv ν.fst α + klDiv ν.snd β := by
  have hfirst := product_reference_chain ν α β hac
  let σ : Measure (B × A) := ν.map Prod.swap
  letI : IsProbabilityMeasure σ :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hswap : klDiv σ (β.prod ν.fst) = klDiv ν (ν.fst.prod β) := by
    have h := klDiv_map_measurableEquiv ν (ν.fst.prod β)
      (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
    change klDiv (ν.map Prod.swap) ((ν.fst.prod β).map Prod.swap) = _ at h
    simpa only [σ, Measure.prod_swap] using h
  have hresac : σ ≪ β.prod ν.fst := by
    have h := (joint_ac_marginal_prod_right ν α β hac).map measurable_swap
    simpa only [σ, Measure.prod_swap] using h
  have hsecond := product_reference_chain σ β ν.fst hresac
  have hmi : klDiv σ (σ.fst.prod ν.fst) = klDiv ν (ν.fst.prod ν.snd) := by
    have h := klDiv_map_measurableEquiv ν (ν.fst.prod ν.snd)
      (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
    change klDiv (ν.map Prod.swap) ((ν.fst.prod ν.snd).map Prod.swap) = _ at h
    simpa only [σ, Measure.fst_map_swap, Measure.prod_swap] using h
  have hres : klDiv ν (ν.fst.prod β) =
      klDiv ν.snd β + klDiv ν (ν.fst.prod ν.snd) := by
    rw [← hswap, hsecond, hmi]
    simp only [σ, Measure.fst_map_swap]
  rw [hfirst, hres]
  simp only [add_assoc, add_left_comm, add_comm]

/-- Relative entropy against a product reference is mutual information plus the
two marginal reference divergences, including infinite values. -/
theorem product_reference_decomposition
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    klDiv ν (α.prod β) = klDiv ν (ν.fst.prod ν.snd) +
      klDiv ν.fst α + klDiv ν.snd β := by
  by_cases hac : ν ≪ α.prod β
  · exact product_reference_decomposition_of_ac ν α β hac
  · rw [klDiv_of_not_ac hac]
    by_cases hfst : ν.fst ≪ α
    · by_cases hsnd : ν.snd ≪ β
      · have hmi : ¬ ν ≪ ν.fst.prod ν.snd := by
          intro h
          exact hac (h.trans (hfst.prod hsnd))
        simp only [klDiv_of_not_ac hmi, top_add]
      · simp only [klDiv_of_not_ac hsnd, add_top]
    · simp only [klDiv_of_not_ac hfst, add_top, top_add]

/-- Finite joint reference divergence makes all three decomposition terms finite. -/
theorem product_reference_terms_ne_top
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hfin : klDiv ν (α.prod β) ≠ ∞) :
    klDiv ν (ν.fst.prod ν.snd) ≠ ∞ ∧
      klDiv ν.fst α ≠ ∞ ∧ klDiv ν.snd β ≠ ∞ := by
  rw [product_reference_decomposition ν α β] at hfin
  obtain ⟨hleft, hsnd⟩ := ENNReal.add_ne_top.mp hfin
  obtain ⟨hmi, hfst⟩ := ENNReal.add_ne_top.mp hleft
  exact ⟨hmi, hfst, hsnd⟩

/-- Finite reference divergence permits a faithful real-valued decomposition. -/
theorem product_reference_decomposition_toReal
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hfin : klDiv ν (α.prod β) ≠ ∞) :
    (klDiv ν (α.prod β)).toReal = (klDiv ν (ν.fst.prod ν.snd)).toReal +
      (klDiv ν.fst α).toReal + (klDiv ν.snd β).toReal := by
  obtain ⟨hmi, hfst, hsnd⟩ := product_reference_terms_ne_top ν α β hfin
  rw [product_reference_decomposition ν α β,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hmi, hfst⟩) hsnd,
    ENNReal.toReal_add hmi hfst]

/-- The sum of marginal reference divergences is bounded by joint divergence. -/
theorem marginal_kl_sum_le
    (ν : Measure (A × B)) (α : Measure A) (β : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    klDiv ν.fst α + klDiv ν.snd β ≤ klDiv ν (α.prod β) := by
  rw [product_reference_decomposition ν α β, add_assoc]
  exact le_add_of_nonneg_left (zero_le _)

/-- Zero divergence from the marginal product is exactly factorization. -/
theorem marginal_product_kl_eq_zero_iff (ν : Measure (A × B))
    [IsProbabilityMeasure ν] :
    klDiv ν (ν.fst.prod ν.snd) = 0 ↔ ν = ν.fst.prod ν.snd :=
  klDiv_eq_zero_iff

end
end IDT.QMClosure.ProductReferenceEntropyDecomposition
