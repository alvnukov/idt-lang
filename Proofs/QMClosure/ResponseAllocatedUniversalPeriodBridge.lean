import Proofs.QMClosure.NativeAllocatedUniversalPeriodLaw
import Proofs.QMClosure.ResponseAllocatedStableBridge

/-!
# Original-operation no-common-period witnesses and sufficient ambient laws

The predicate retains original signature/operation iteration, actual allocated
programs, and all positive time lengths. With both diagonal-fixed hypotheses,
the exact checked per-length signature correspondence gives induced scalar
separation and a sufficient original single-basis law. The whole polymorphic
probability field of any supplied scalar family remains unchanged.

No ambient iff, full ambient-state separation, individually nonperiodic-orbit
necessity, or finite empirical certification is asserted. No scalar coordinates
or topology are added as observation data; the Native-indexed backend remains
supplied. Each time-L one-hole context retains the charged Bp+L*Br tagged-source occurrence
count, without a uniform bound, physical reference guarantee, unknown cloning,
detector, probability provenance, multi-source probability extension,
actualization, or QM closure.
-/

namespace IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient ResponseSourceLocalProbability ResponseAllocatedFaithfulness
open NativeAllocatedSourceArithmetic NativeAllocatedObservationBoundary
open NativeAllocatedUniversalPeriodLaw NativeAllocatedSignatureLaw ResponseAllocatedStableBridge

variable {V Ω : Type*}

def RawNoCommonPositivePeriod (d : Data V Ω) (v : V) : Prop :=
  ∀ L : ℕ, 0 < L → ∃ r p : ScalarProgram,
    d.signature ((rawReferenceStep d v r)^[L] (rawValue d v p)) ≠
      d.signature (rawValue d v p)

theorem induced_noCommonPositivePeriod_of_raw (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNoCommonPositivePeriod d v) : NoCommonPositivePeriod (inducedSignature d v) := by
  intro L hL
  obtain ⟨r, p, hrp⟩ := h L hL
  refine ⟨ofProgram r, ofProgram p, ?_⟩
  rw [signature_reference_iterate d v hz hv r p L,
    inducedSignature_ofProgram d v hz hv p]
  exact hrp

theorem separates_of_rawNoCommonPositivePeriod (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNoCommonPositivePeriod d v) : Separates (inducedSignature d v) :=
  (separates_iff_noCommonPositivePeriod (inducedSignature d v)).mpr
    (induced_noCommonPositivePeriod_of_raw d v hz hv h)

def lawOfScalarOfRawNoCommonPositivePeriod (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNoCommonPositivePeriod d v) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv (separates_of_rawNoCommonPositivePeriod d v hz hv h) L

theorem lawOfScalarOfRawNoCommonPositivePeriod_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNoCommonPositivePeriod d v) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
        (lawOfScalarOfRawNoCommonPositivePeriod d v hz hv h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_rawNoCommonPositivePeriod (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (h : RawNoCommonPositivePeriod d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfRawNoCommonPositivePeriod d v hz hv h NativeVacuumProbabilityFamily.canonicalLaw⟩

end
end IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge
