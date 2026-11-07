import Proofs.QMClosure.NativeAllocatedSingleTraceLaw
import Proofs.QMClosure.ResponseAllocatedStableBridge

/-!
# Original-operation single-trace witnesses and sufficient response laws

The witness predicates mention only the original operation and signature,
actual allocated ScalarPrograms, and infinite iteration. Both source-local
diagonal-fixed hypotheses remain explicit. Audited one-hole compilation
equates each raw observation with the induced scalar observation; no bare
signature equality is propagated through a further gate.

The conclusion is induced scalar separation and a sufficient ambient
single-basis law, with the entire probability field of any supplied scalar law
unchanged. No ambient literal-state separation, ambient iff, necessity, finite
observation certificate, or eventual-aperiodicity claim is asserted. The
existing Native-indexed complex backend remains supplied. Each time-n context
retains its single unknown hole and charges Bp+n*Br for the allocated input and
known references. No uniform resource bound, physical availability, detector,
probability provenance, unknown cloning, multi-source probability extension,
actualization, or QM closure is established.
-/

namespace IDT.QMClosure.ResponseAllocatedSingleTraceBridge

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient ResponseSourceLocalProbability ResponseAllocatedFaithfulness
open NativeAllocatedSourceArithmetic NativeAllocatedObservationBoundary
open NativeAllocatedSingleTraceLaw NativeAllocatedSignatureLaw ResponseAllocatedStableBridge

variable {V Ω : Type*}

def RawNonperiodicReferenceTrace (d : Data V Ω) (v : V) : Prop :=
  ∃ r p : ScalarProgram, ∀ L : ℕ, 0 < L → ∃ n : ℕ,
    d.signature ((rawReferenceStep d v r)^[n + L] (rawValue d v p)) ≠
      d.signature ((rawReferenceStep d v r)^[n] (rawValue d v p))

def RawEventuallyAvoidingReferenceTrace (d : Data V Ω) (v : V) : Prop :=
  ∃ r p : ScalarProgram, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    d.signature ((rawReferenceStep d v r)^[n] (rawValue d v p)) ≠
      d.signature (rawValue d v p)

def RawChangedConstantReferenceTail (d : Data V Ω) (v : V) : Prop :=
  ∃ r p : ScalarProgram, ∃ c : Ω, d.signature (rawValue d v p) ≠ c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      d.signature ((rawReferenceStep d v r)^[n] (rawValue d v p)) = c

theorem induced_nonperiodic_of_rawNonperiodic (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNonperiodicReferenceTrace d v) :
    HasNonperiodicReferenceTrace (inducedSignature d v) := by
  obtain ⟨r, p, hp⟩ := h
  refine ⟨ofProgram r, ofProgram p, ?_⟩
  intro L hL
  obtain ⟨n, hn⟩ := hp L hL
  refine ⟨n, ?_⟩
  rw [signature_reference_iterate d v hz hv r p (n + L),
    signature_reference_iterate d v hz hv r p n]
  exact hn

theorem induced_eventuallyAvoiding_of_rawEventuallyAvoiding (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawEventuallyAvoidingReferenceTrace d v) :
    HasEventuallyAvoidingReferenceTrace (inducedSignature d v) := by
  obtain ⟨r, p, N, hN⟩ := h
  refine ⟨ofProgram r, ofProgram p, N, ?_⟩
  intro n hn
  rw [signature_reference_iterate d v hz hv r p n,
    inducedSignature_ofProgram d v hz hv p]
  exact hN n hn

theorem induced_changedConstantTail_of_rawChangedConstantTail (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawChangedConstantReferenceTail d v) :
    HasChangedConstantReferenceTail (inducedSignature d v) := by
  obtain ⟨r, p, c, hpc, N, hN⟩ := h
  refine ⟨ofProgram r, ofProgram p, c, ?_, N, ?_⟩
  · rw [inducedSignature_ofProgram d v hz hv p]
    exact hpc
  · intro n hn
    rw [signature_reference_iterate d v hz hv r p n]
    exact hN n hn

theorem separates_of_rawNonperiodicTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNonperiodicReferenceTrace d v) : Separates (inducedSignature d v) :=
  separates_of_nonperiodicReferenceTrace (inducedSignature d v)
    (induced_nonperiodic_of_rawNonperiodic d v hz hv h)

theorem separates_of_rawEventuallyAvoidingTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawEventuallyAvoidingReferenceTrace d v) : Separates (inducedSignature d v) :=
  separates_of_eventuallyAvoidingReferenceTrace (inducedSignature d v)
    (induced_eventuallyAvoiding_of_rawEventuallyAvoiding d v hz hv h)

theorem separates_of_rawChangedConstantTail (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawChangedConstantReferenceTail d v) : Separates (inducedSignature d v) :=
  separates_of_changedConstantTail (inducedSignature d v)
    (induced_changedConstantTail_of_rawChangedConstantTail d v hz hv h)

def lawOfScalarOfRawNonperiodicTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNonperiodicReferenceTrace d v) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv (separates_of_rawNonperiodicTrace d v hz hv h) L

theorem lawOfScalarOfRawNonperiodicTrace_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNonperiodicReferenceTrace d v) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
        (lawOfScalarOfRawNonperiodicTrace d v hz hv h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_rawNonperiodicTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNonperiodicReferenceTrace d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfRawNonperiodicTrace d v hz hv h NativeVacuumProbabilityFamily.canonicalLaw⟩

def lawOfScalarOfRawEventuallyAvoidingTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawEventuallyAvoidingReferenceTrace d v) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv (separates_of_rawEventuallyAvoidingTrace d v hz hv h) L

theorem lawOfScalarOfRawEventuallyAvoidingTrace_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawEventuallyAvoidingReferenceTrace d v) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
        (lawOfScalarOfRawEventuallyAvoidingTrace d v hz hv h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_rawEventuallyAvoidingTrace (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawEventuallyAvoidingReferenceTrace d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfRawEventuallyAvoidingTrace d v hz hv h NativeVacuumProbabilityFamily.canonicalLaw⟩

def lawOfScalarOfRawChangedConstantTail (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawChangedConstantReferenceTail d v) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv (separates_of_rawChangedConstantTail d v hz hv h) L

theorem lawOfScalarOfRawChangedConstantTail_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawChangedConstantReferenceTail d v) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
        (lawOfScalarOfRawChangedConstantTail d v hz hv h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_rawChangedConstantTail (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawChangedConstantReferenceTail d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfRawChangedConstantTail d v hz hv h NativeVacuumProbabilityFamily.canonicalLaw⟩

end
end IDT.QMClosure.ResponseAllocatedSingleTraceBridge
