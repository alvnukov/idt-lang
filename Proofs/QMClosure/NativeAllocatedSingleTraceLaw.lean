import Proofs.QMClosure.NativeAllocatedStableObservation
import Proofs.QMClosure.NativeAllocatedResidueObservation

/-!
# A single reference trace can suffice for the existing response law

A trace with no period valid from time zero suffices for full contextual
separation. Eventual avoidance of its initial answer is a stronger sufficient
witness; an eventual constant answer different from its initial answer is a
still stronger witness. That changed constant tail is eventually periodic:
only periodicity from time zero is excluded here.

These are infinite-time predicates on supplied observations of actual generated
values under the existing native gate. No topology, finite codomain, existing
law, necessity, finite observation certificate, or physical settling premise
is supplied. Known references remain separately allocated and charged. Law
transport preserves any supplied scalar family's entire probability field;
it gives no probability provenance, detector construction, physical reference
availability, multi-source probability extension, actualization, or QM closure.
-/

namespace IDT.QMClosure.NativeAllocatedSingleTraceLaw

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedStableObservation NativeAllocatedSignatureLaw

variable {Ω : Type*}

/-- One reference trace has no positive period valid from its initial time. -/
def HasNonperiodicReferenceTrace (σ : G → Ω) : Prop :=
  ∃ z x : G, ∀ L : ℕ, 0 < L → ∃ n : ℕ,
    σ ((referenceStep z)^[n + L] x) ≠ σ ((referenceStep z)^[n] x)

/-- One trace eventually avoids its own initial signature at every later time. -/
def HasEventuallyAvoidingReferenceTrace (σ : G → Ω) : Prop :=
  ∃ z x : G, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → σ ((referenceStep z)^[n] x) ≠ σ x

/-- The eventual answer need not equal the reference's answer. -/
def HasChangedConstantReferenceTail (σ : G → Ω) : Prop :=
  ∃ z x : G, ∃ c : Ω, σ x ≠ c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → σ ((referenceStep z)^[n] x) = c

theorem eventuallyAvoiding_of_changedConstantTail (σ : G → Ω)
    (h : HasChangedConstantReferenceTail σ) : HasEventuallyAvoidingReferenceTrace σ := by
  obtain ⟨z, x, c, hxc, N, hN⟩ := h
  refine ⟨z, x, N, ?_⟩
  intro n hn he
  exact hxc (he.symm.trans (hN n hn))

theorem nonperiodic_of_eventuallyAvoiding (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) : HasNonperiodicReferenceTrace σ := by
  obtain ⟨z, x, N, hN⟩ := h
  refine ⟨z, x, ?_⟩
  intro L hL
  by_contra hp
  have hperiod : ∀ n : ℕ,
      σ ((referenceStep z)^[n + L] x) = σ ((referenceStep z)^[n] x) := by
    intro n
    by_contra hn
    exact hp ⟨n, hn⟩
  have hmultiple : ∀ m : ℕ, σ ((referenceStep z)^[L * m] x) = σ x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simpa only [Nat.mul_succ] using (hperiod (L * m)).trans ih
  have hlarge : N ≤ L * (N + 1) :=
    (Nat.le_succ N).trans (by
      simpa only [Nat.succ_eq_add_one, Nat.zero_add, one_mul] using
        Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hL))
  exact hN (L * (N + 1)) hlarge (hmultiple (N + 1))

/-- A collapsed response pair forces a common period on every reference trace,
which contradicts the supplied single trace. -/
theorem separates_of_nonperiodicReferenceTrace (σ : G → Ω)
    (h : HasNonperiodicReferenceTrace σ) : Separates σ := by
  intro u v huv
  by_contra hne
  obtain ⟨L, hL, hret⟩ := common_contextual_return_of_distinct_responseEq σ hne huv
  obtain ⟨z, x, htrace⟩ := h
  obtain ⟨n, hn⟩ := htrace L hL
  have hr := signature_eq (hret z ((referenceStep z)^[n] x))
  apply hn
  rw [Nat.add_comm n L, Function.iterate_add_apply]
  exact hr.symm

theorem separates_of_eventuallyAvoidingReferenceTrace (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) : Separates σ :=
  separates_of_nonperiodicReferenceTrace σ (nonperiodic_of_eventuallyAvoiding σ h)

theorem separates_of_changedConstantTail (σ : G → Ω)
    (h : HasChangedConstantReferenceTail σ) : Separates σ :=
  separates_of_eventuallyAvoidingReferenceTrace σ (eventuallyAvoiding_of_changedConstantTail σ h)

theorem nonconstant_of_nonperiodicReferenceTrace (σ : G → Ω)
    (h : HasNonperiodicReferenceTrace σ) : ∃ x y : G, σ x ≠ σ y := by
  obtain ⟨z, x, htrace⟩ := h
  obtain ⟨n, hn⟩ := htrace 1 (by decide)
  exact ⟨(referenceStep z)^[n + 1] x, (referenceStep z)^[n] x, hn⟩

theorem nonconstant_of_eventuallyAvoidingReferenceTrace (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) : ∃ x y : G, σ x ≠ σ y :=
  nonconstant_of_nonperiodicReferenceTrace σ (nonperiodic_of_eventuallyAvoiding σ h)

theorem nonconstant_of_changedConstantTail (σ : G → Ω)
    (h : HasChangedConstantReferenceTail σ) : ∃ x y : G, σ x ≠ σ y :=
  nonconstant_of_eventuallyAvoidingReferenceTrace σ (eventuallyAvoiding_of_changedConstantTail σ h)

def lawOfScalarOfNonperiodicTrace (σ : G → Ω) (h : HasNonperiodicReferenceTrace σ)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  NativeAllocatedSignatureLaw.lawOfScalar σ (separates_of_nonperiodicReferenceTrace σ h) L

theorem lawOfScalarOfNonperiodicTrace_probability (σ : G → Ω)
    (h : HasNonperiodicReferenceTrace σ) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
        (lawOfScalarOfNonperiodicTrace σ h L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_nonperiodicTrace (σ : G → Ω) (h : HasNonperiodicReferenceTrace σ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) :=
  ⟨lawOfScalarOfNonperiodicTrace σ h NativeVacuumProbabilityFamily.canonicalLaw⟩

def lawOfScalarOfEventuallyAvoidingTrace (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  NativeAllocatedSignatureLaw.lawOfScalar σ (separates_of_eventuallyAvoidingReferenceTrace σ h) L

theorem lawOfScalarOfEventuallyAvoidingTrace_probability (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
        (lawOfScalarOfEventuallyAvoidingTrace σ h L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_eventuallyAvoidingTrace (σ : G → Ω)
    (h : HasEventuallyAvoidingReferenceTrace σ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) :=
  ⟨lawOfScalarOfEventuallyAvoidingTrace σ h NativeVacuumProbabilityFamily.canonicalLaw⟩

def lawOfScalarOfChangedConstantTail (σ : G → Ω) (h : HasChangedConstantReferenceTail σ)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  NativeAllocatedSignatureLaw.lawOfScalar σ (separates_of_changedConstantTail σ h) L

theorem lawOfScalarOfChangedConstantTail_probability (σ : G → Ω)
    (h : HasChangedConstantReferenceTail σ) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
        (lawOfScalarOfChangedConstantTail σ h L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_changedConstantTail (σ : G → Ω) (h : HasChangedConstantReferenceTail σ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) :=
  ⟨lawOfScalarOfChangedConstantTail σ h NativeVacuumProbabilityFamily.canonicalLaw⟩

/-- Arbitrarily late changes from the initial answer alone are insufficient. -/
theorem arbitrarily_late_change_without_law :
    (∃ z x : G, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      NativeAllocatedResidueObservation.hitSignature ((referenceStep z)^[n] x) ≠
        NativeAllocatedResidueObservation.hitSignature x) ∧
    ¬ Separates NativeAllocatedResidueObservation.hitSignature ∧
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law
      (signatureData NativeAllocatedResidueObservation.hitSignature) unitG) := by
  refine ⟨⟨zeroG, NativeAllocatedResidueObservation.twoG, ?_⟩,
    NativeAllocatedResidueObservation.hitSignature_not_separates,
    NativeAllocatedResidueObservation.hitSignature_no_law⟩
  intro N
  obtain ⟨n, hn, _, hanswer⟩ :=
    NativeAllocatedResidueObservation.hitSignature_zero_reference_recurrence
      NativeAllocatedResidueObservation.twoG N
  refine ⟨n, hn, ?_⟩
  rw [hanswer, NativeAllocatedResidueObservation.hitSignature_zeroG,
    NativeAllocatedResidueObservation.hitSignature_twoG]
  decide

theorem one_change_without_law :
    (∃ z x : G, ∃ n : ℕ,
      NativeAllocatedResidueObservation.hitSignature ((referenceStep z)^[n] x) ≠
        NativeAllocatedResidueObservation.hitSignature x) ∧
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law
      (signatureData NativeAllocatedResidueObservation.hitSignature) unitG) := by
  obtain ⟨⟨z, x, h⟩, _, hL⟩ := arbitrarily_late_change_without_law
  obtain ⟨n, _, hn⟩ := h 0
  exact ⟨⟨z, x, n, hn⟩, hL⟩

end
end IDT.QMClosure.NativeAllocatedSingleTraceLaw
