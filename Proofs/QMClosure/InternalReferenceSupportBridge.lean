import Proofs.QMClosure.TransparentSwapRootOrderWall
import Proofs.QMClosure.ReferenceEntropyFactorization
import Proofs.QMClosure.DetectorEndpointSupportWall

/-!
# Internal reference and support symmetry

A common statistical channel with full independent-product covariance makes the
raw operation monotone for preparation absolute continuity. A transparent square
root of swap therefore makes that preorder symmetric on comparable pairs.

In a reference-entropy factorization contract, a reference that is itself one of
the preparations, together with a fixed raw diagonal, then forces mutual absolute
continuity throughout the preparation family. Common effects inherit endpoint
rigidity. These statements do not infer pairwise finite KL from absolute
continuity, and do not remove the finite-entropy input of the process adapter.
-/

namespace IDT.QMClosure.InternalReferenceSupportBridge

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open InvariantEffectReadoutBridge
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- For probability products, absolute continuity is equivalent to coordinatewise
absolute continuity. No standard-Borel hypothesis is needed. -/
theorem product_absolutelyContinuous_iff (μ₁ μ₂ ν₁ ν₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    μ₁.prod μ₂ ≪ ν₁.prod ν₂ ↔ μ₁ ≪ ν₁ ∧ μ₂ ≪ ν₂ := by
  constructor
  · intro h
    constructor
    · have hf := h.map measurable_fst
      change (μ₁.prod μ₂).fst ≪ (ν₁.prod ν₂).fst at hf
      simpa only [Measure.fst_prod] using hf
    · have hs := h.map measurable_snd
      change (μ₁.prod μ₂).snd ≪ (ν₁.prod ν₂).snd at hs
      simpa only [Measure.snd_prod] using hs
  · rintro ⟨h₁, h₂⟩
    exact h₁.prod h₂

/-- Full covariance through one common kernel preserves the preparation support
preorder in each coordinate. -/
theorem covariance_preserves_absolutelyContinuous
    (K : V → Measure Ω) (probability : ∀ x, IsProbabilityMeasure (K x))
    (F : V × V → V × V) (κ : Kernel (Ω × Ω) (Ω × Ω))
    (covariance : ∀ p, κ ∘ₘ ((K p.1).prod (K p.2)) =
      (K (F p).1).prod (K (F p).2))
    {p q : V × V} (h₁ : K p.1 ≪ K q.1) (h₂ : K p.2 ≪ K q.2) :
    K (F p).1 ≪ K (F q).1 ∧ K (F p).2 ≪ K (F q).2 := by
  letI (x : V) : IsProbabilityMeasure (K x) := probability x
  have h := (h₁.prod h₂).comp_right κ
  rw [covariance p, covariance q] at h
  exact (product_absolutelyContinuous_iff _ _ _ _).mp h

/-- The statistical support preorder has no strictly comparable pairs under a
transparent square root of swap. This generic theorem uses no KL hypothesis. -/
theorem reverse_absolutelyContinuous
    (K : V → Measure Ω) (probability : ∀ x, IsProbabilityMeasure (K x))
    (F : V × V → V × V) (square : ∀ p, F (F p) = p.swap)
    (diagonal : ∀ x, F (x, x) = (x, x))
    (κ : Kernel (Ω × Ω) (Ω × Ω))
    (covariance : ∀ p, κ ∘ₘ ((K p.1).prod (K p.2)) =
      (K (F p).1).prod (K (F p).2))
    {x y : V} (hxy : K x ≪ K y) : K y ≪ K x := by
  letI : Preorder V :=
    { le := fun x y => K x ≪ K y
      le_refl := fun _ => Measure.AbsolutelyContinuous.rfl
      le_trans := fun _ _ _ hxy hyz => hxy.trans hyz }
  have monotone : Monotone F := by
    intro p q hpq
    exact covariance_preserves_absolutelyContinuous K probability F κ covariance hpq.1 hpq.2
  exact TransparentSwapRootOrderWall.reverse_le F monotone square diagonal hxy

namespace ReferenceContract

variable (D : ReferenceEntropyFactorization.Contract V Ω)

/-- An internal preparation reference and raw transparency make all preparations
mutually absolutely continuous. Reference-relative entropy finiteness is supplied
by the factorization contract. Pairwise entropy finiteness is not concluded. -/
theorem mutually_absolutelyContinuous (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (diagonal : ∀ x, D.operation (x, x) = (x, x)) (x y : V) :
    D.preparation x ≪ D.preparation y := by
  have hreference (z : V) : D.preparation z ≪ D.preparation x₀ := by
    rw [← internal]
    exact (klDiv_ne_top_iff.mp (D.finiteReferenceEntropy z)).1
  have hreverse : D.preparation x₀ ≪ D.preparation y :=
    reverse_absolutelyContinuous D.preparation D.probability D.operation D.square
      diagonal D.channel D.covariance (hreference y)
  exact (hreference x).trans hreverse

/-- Every common effect is identically zero, identically one, or pointwise
strictly interior on a transparent internal-reference contract. -/
theorem acceptance_trichotomy (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (diagonal : ∀ x, D.operation (x, x) = (x, x)) (g : Effect Ω) :
    (∀ x, g.acceptance (D.preparation x) = 0) ∨
      (∀ x, g.acceptance (D.preparation x) = 1) ∨
      (∀ x, 0 < g.acceptance (D.preparation x) ∧ g.acceptance (D.preparation x) < 1) :=
  DetectorEndpointSupportWall.acceptance_trichotomy D.preparation D.probability
    (mutually_absolutelyContinuous D x₀ internal diagonal) g

end ReferenceContract
end
end IDT.QMClosure.InternalReferenceSupportBridge
