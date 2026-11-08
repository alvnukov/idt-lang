import Proofs.QMClosure.BoundedDominationProcess
import Proofs.QMClosure.BoundedLogProcessRigidity

/-!
# Bounded likelihood rigidity for a transparent statistical process

One finite domination bound between two preparation laws forces their equality.
Each preparation in the resulting closed component has its own finite log
range. Finite entropy and log integrability are derived within that component.
-/

namespace IDT.QMClosure.BoundedLikelihoodProcessRigidity

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open BoundedDominationProcess
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

namespace Contract

variable (D : BoundedDominationProcess.Contract V Ω)

local instance (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x

/-- One-way bounded domination collapses to equality under the common channel,
full product covariance, square-swap, and raw transparency hypotheses. -/
theorem eq_of_boundedDom {x y : V}
    (hxy : boundedDom (D.preparation x) (D.preparation y)) :
    D.preparation x = D.preparation y := by
  let L := D.logDensityProcess y
  have hbounded : ∀ z : D.Component y, ∃ lo hi : ℝ, ∀ᵐ s ∂L.reference,
      lo ≤ L.logDensity z s ∧ L.logDensity z s ≤ hi := by
    intro z
    obtain ⟨B, _, hB⟩ := D.component_bounded_logDensity y z
    refine ⟨-B, B, ?_⟩
    filter_upwards [hB] with s hs
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hs)
  obtain ⟨c, hc⟩ :=
    BoundedLogProcessRigidity.Contract.ae_constant_of_individually_bounded
      L hbounded (⟨x, hxy⟩ : D.Component y)
  have hactual : llr (D.preparation x) (D.preparation y) =ᵐ[D.preparation y]
      fun _ => c := hc
  exact eq_of_llr_ae_const _ _ hxy.absolutelyContinuous
    (D.reverse_boundedDom hxy).absolutelyContinuous hactual

/-- The same conclusion with its scalar bound supplied directly. -/
theorem eq_of_le_smul {x y : V} {C : ℝ≥0∞}
    (hC : 0 < C) (hCfin : C ≠ ∞)
    (hxy : D.preparation x ≤ C • D.preparation y) :
    D.preparation x = D.preparation y :=
  eq_of_boundedDom D ⟨C, hC, hCfin, hxy⟩

theorem boundedDom_iff_eq (x y : V) :
    boundedDom (D.preparation x) (D.preparation y) ↔ D.preparation x = D.preparation y := by
  constructor
  · exact eq_of_boundedDom D
  · intro h
    rw [h]
    exact boundedDom.refl _

/-- Distinct preparations admit no finite positive one-way domination bound. -/
theorem not_boundedDom_of_ne {x y : V} (hne : D.preparation x ≠ D.preparation y) :
    ¬ boundedDom (D.preparation x) (D.preparation y) := by
  intro hxy
  exact hne (eq_of_boundedDom D hxy)

end Contract
end
end IDT.QMClosure.BoundedLikelihoodProcessRigidity
