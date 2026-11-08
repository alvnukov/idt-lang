import Proofs.QMClosure.RawPlanePhaseControl
import Mathlib.Topology.Compactness.Compact

/-!
# Global continuity of the actual plane-dependent operation

The plane parameter is continuous away from the dependent locus. At a dependent
pair, all members of the compactly parameterized continuous family agree.
The tube lemma therefore supplies continuity even though the parameter selector
itself need not be continuous there.
-/

namespace IDT.QMClosure.RawPlanePhaseContinuity

noncomputable section

open Topology Set
open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseControl

/-- A compact family with one common fibre value permits an arbitrary selector
at that fibre. This is a pointwise continuity statement at `x₀`. -/
theorem continuousAt_compact_selection
    {K X Y : Type*} [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set K) (hS : IsCompact S) (G : K × X → Y) (hG : Continuous G)
    (s : X → K) (hs : ∀ x, s x ∈ S) (x₀ : X) (y₀ : Y)
    (hconstant : ∀ k ∈ S, G (k, x₀) = y₀) :
    ContinuousAt (fun x => G (s x, x)) x₀ := by
  change Filter.Tendsto (fun x => G (s x, x)) (𝓝 x₀) (𝓝 (G (s x₀, x₀)))
  rw [hconstant (s x₀) (hs x₀)]
  apply tendsto_nhds.mpr
  intro U hU hy₀
  have hfibre : S ×ˢ ({x₀} : Set X) ⊆ G ⁻¹' U := by
    rintro ⟨k, x⟩ ⟨hk, hx⟩
    have hx₀ : x = x₀ := Set.mem_singleton_iff.mp hx
    subst x
    change G (k, x₀) ∈ U
    rw [hconstant k hk]
    exact hy₀
  obtain ⟨u, v, _hu, hv, hSu, hx₀v, huv⟩ :=
    generalized_tube_lemma hS isCompact_singleton (hU.preimage hG) hfibre
  apply Filter.mem_of_superset (hv.mem_nhds (hx₀v (by simp)))
  intro x hx
  exact huv ⟨hSu (hs x), hx⟩

/-- The actual plane-dependent operation is globally continuous in the ordinary
product topology, including zero and all other dependent pairs. -/
theorem continuous_operation : Continuous RawPlanePhaseControl.operation := by
  have hop : RawPlanePhaseControl.operation =
      (fun p : Vec × Vec => familyOperation (parameter p.1 p.2) p) :=
    funext operation_eq_family
  rw [hop]
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : wedge p.1 p.2 = 0
  · exact continuousAt_compact_selection (Set.Icc (0 : ℝ) 1) isCompact_Icc
      (fun z : ℝ × (Vec × Vec) => familyOperation z.1 z.2)
      jointcontinuous_family (fun q : Vec × Vec => parameter q.1 q.2)
      (fun q => ⟨parameter_nonnegative q.1 q.2, parameter_le_one q.1 q.2⟩)
      p (native p.1 p.2, native p.2 p.1)
      (fun t _ => familyOperation_of_dependent t hp)
  · have hpair : ContinuousAt
        (fun q : Vec × Vec => (parameter q.1 q.2, q)) p :=
      (continuous_parameter_at p hp).prodMk continuousAt_id
    exact jointcontinuous_family.continuousAt.comp'
      (f := fun q : Vec × Vec => (parameter q.1 q.2, q)) hpair

/-- The first output of the actual plane-dependent operation is continuous. -/
theorem continuous_m :
    Continuous (fun p : Vec × Vec => RawPlanePhaseControl.m p.1 p.2) :=
  continuous_fst.comp continuous_operation

end
end IDT.QMClosure.RawPlanePhaseContinuity
