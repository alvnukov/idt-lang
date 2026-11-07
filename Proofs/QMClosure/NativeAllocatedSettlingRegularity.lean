import Proofs.QMClosure.NativeAllocatedContextAttenuation
import Proofs.QMClosure.NativeAllocatedSingleTraceLaw

/-!
# An open constant patch supplies a changed native reference tail

Fixed-reference iteration converges in the existing ordinary complex scalar
backend and the canonical inherited topology on the allocated generated carrier.
A nonempty open constant patch therefore supplies exact eventual reference-label
agreement for every generated input. The threshold may depend on that input;
neither a uniform threshold nor global continuity of the signature is assumed.
The label type has no topology.

Together with nonconstancy this gives the existing changed-constant-tail witness,
which can be passed to the existing single-trace law adapter. No law adapter or
probability field is changed here, and no probability provenance follows.
Every fixed known generated reference occurrence is separately allocated and
charged. Companion wires remain retained; this is not global information erasure,
unknown-token cloning, a finite observation certificate, physical reference
availability, detector construction, actualization, or QM closure.
-/

namespace IDT.QMClosure.NativeAllocatedSettlingRegularity

noncomputable section

open OperationalContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedStableObservation NativeAllocatedSingleTraceLaw
open Filter Topology

variable {Ω : Type*}

private def referenceContext (z : G) : ℕ → Context G
  | 0 => .hole
  | n + 1 => .left .first (referenceContext z n) z

private theorem referenceContext_depth (z : G) (n : ℕ) :
    NativeAllocatedContextAttenuation.depth (referenceContext z n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [referenceContext, NativeAllocatedContextAttenuation.depth, ih]

private theorem referenceContext_eval (z x : G) (n : ℕ) :
    (referenceContext z n).eval operationG x = (referenceStep z)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [referenceContext, Context.eval, select, Function.iterate_succ_apply',
      referenceStep, ih]

/-- Literal complex values of actual fixed-reference iterates converge. -/
theorem referenceStep_iterate_coe_tendsto (z x : G) :
    Tendsto (fun n => ((referenceStep z)^[n] x).val) atTop (𝓝 z.val) := by
  have hfixed : Tendsto (fun n => ((referenceContext z n).eval operationG z).val)
      atTop (𝓝 z.val) := by
    simpa only [referenceContext_eval, referenceStep_iterate_coe, sub_self,
      mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z.val) atTop (𝓝 z.val))
  have hdepth : Tendsto
      (fun n => NativeAllocatedContextAttenuation.depth (referenceContext z n))
      atTop atTop := by
    simpa only [referenceContext_depth] using (tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop)
  simpa only [referenceContext_eval] using
    NativeAllocatedContextAttenuation.eval_tendsto_of_one (referenceContext z)
      hdepth z x z.val hfixed

/-- The topology is the already installed canonical inherited topology on G. -/
theorem referenceStep_iterate_tendsto (z x : G) :
    Tendsto (fun n => (referenceStep z)^[n] x) atTop (𝓝 z) :=
  tendsto_subtype_rng.mpr (referenceStep_iterate_coe_tendsto z x)

/-- No continuity or topology on the signature codomain is needed. -/
theorem referenceSettles_of_openConstantPatch (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) : ReferenceSettles σ := by
  obtain ⟨U, hU, ⟨z, hz⟩, c, hc⟩ := hpatch
  refine ⟨z, ?_⟩
  intro x
  have hevent := (referenceStep_iterate_tendsto z x).eventually (hU.mem_nhds hz)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨N, fun n hn => (hc _ (hN n hn)).trans (hc z hz).symm⟩

theorem changedConstantTail_of_referenceSettles_nonconstant (σ : G → Ω)
    (hsettles : ReferenceSettles σ) (hnonconstant : ∃ x y : G, σ x ≠ σ y) :
    HasChangedConstantReferenceTail σ := by
  classical
  obtain ⟨z, hz⟩ := hsettles
  obtain ⟨u, v, huv⟩ := hnonconstant
  have hex : ∃ x : G, σ x ≠ σ z := by
    by_cases hu : σ u = σ z
    · exact ⟨v, fun hv => huv (hu.trans hv.symm)⟩
    · exact ⟨u, hu⟩
  obtain ⟨x, hx⟩ := hex
  obtain ⟨N, hN⟩ := hz x
  exact ⟨z, x, σ z, hx, N, hN⟩

/-- This witness feeds the existing single-trace law adapter unchanged. -/
theorem changedConstantTail_of_openConstantPatch_nonconstant (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) (hnonconstant : ∃ x y : G, σ x ≠ σ y) :
    HasChangedConstantReferenceTail σ :=
  changedConstantTail_of_referenceSettles_nonconstant σ
    (referenceSettles_of_openConstantPatch σ hpatch) hnonconstant

end
end IDT.QMClosure.NativeAllocatedSettlingRegularity
