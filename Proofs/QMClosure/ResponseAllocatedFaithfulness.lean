import Proofs.QMClosure.NativeAllocatedSourceArithmetic
import Proofs.QMClosure.ResponseSourceLocalProbability
import Proofs.QMClosure.ResponsePhaseQuotientWall

/-!
# Response faithfulness of explicitly allocated source programs

The raw value uses the original operation. Its scalar coordinate uses the
concrete native mixer. The supplied response data include observed square-swap
and medial laws. Full contextual diagonal fixedness of the chosen zero and
reference suffices to correlate these two evaluations in the response quotient.
No global transparency is assumed.

Equal scalar coordinates imply response equivalence without a probability law.
A supplied original single-basis probability family makes the converse hold by
forcing faithful Gaussian action on this reference's orbit. This does not
extend that probability family to allocated multi-source arrays.

All conclusions concern full ambient contextual equivalence or response
classes. They do not assert literal raw equality, comparator soundness, or a
law descended to contexts of a generated subcarrier. Such a restriction needs
its own response data and law on that carrier. Stock, a common raw frame, and
joint availability of tagged input arrays remain supplied hypotheses about
preparation. No actualization or QM closure is established.
-/

namespace IDT.QMClosure.ResponseAllocatedFaithfulness

noncomputable section

open ResponseContextQuotient ResponseSourceLocalProbability
open AllocatedPreparation
open WeightFreeRawProbability (evalRaw)
open RawNativeDyadicSemantics
open NativeAllocatedSourceArithmetic (ScalarProgram)

variable {V Ω : Type*}

/-- Evaluate the allocated array with the original operation and supplied source. -/
def rawValue (d : Data V Ω) (v : V) (p : ScalarProgram) : V :=
  AllocatedPreparation.eval d.operation d.chosenZero (fun _ : Unit => v) p

/-- The coordinate of the same complete program under the concrete mixer. -/
def scalarValue (p : ScalarProgram) : ℂ := NativeAllocatedSourceArithmetic.value p

/-- Correlation holds for arbitrary allocated programs. Every initial tag is
either the contextually fixed zero or the contextually fixed reference. The
correlation theorem accepts the complete array without an independence premise. -/
theorem allocated_class_related (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p : ScalarProgram) :
    Related d.quotientData.zeroWeightData (d.classOf v)
      (scalarValue p) (d.classOf (rawValue d v p)) := by
  let r := d.quotientData
  let D := r.zeroWeightData
  let z : p.Wires → ℂ := inputState 0 (fun _ : Unit => 1) p
  let a : p.Wires → V := inputState d.chosenZero (fun _ : Unit => v) p
  let x : p.Wires → d.Space :=
    inputState (d.classOf d.chosenZero) (fun _ : Unit => d.classOf v) p
  have hzq : SourceLocalOriginalSemantics.g r (d.classOf d.chosenZero) =
      d.classOf d.chosenZero := (diagonalFixed_iff_quotient_fixed d _).mp hz
  have hvq : SourceLocalOriginalSemantics.g r (d.classOf v) = d.classOf v :=
    (diagonalFixed_iff_quotient_fixed d _).mp hv
  have hfixed : ∀ i, SourceLocalOriginalSemantics.g r (x i) = x i := by
    intro i
    cases hi : p.input i with
    | none => simpa [x, inputState, hi] using hzq
    | some label => simpa [x, inputState, hi] using hvq
  have hinput : x = fun i => d.classOf (a i) := by
    funext i
    cases hi : p.input i <;> simp [x, a, inputState, hi]
  have hinit : ∀ i, Related D (d.classOf v) (z i) (x i) := by
    intro i
    cases hi : p.input i with
    | none =>
      simpa [z, x, inputState, hi, RawOperationalHilbert.Data.carrier_zero]
        using related_zero D (d.classOf v)
    | some label =>
      simpa [z, x, inputState, hi] using related_one D (d.classOf v)
  have hclass : evalRaw r.operation p.circuit x =
      fun i => d.classOf (evalRaw d.operation p.circuit a i) := by
    change evalRaw d.quotientOperation p.circuit x = _
    rw [hinput]
    exact evalRaw_class d p.circuit a
  have hnormalized : evalRaw r.operation p.circuit x =
      (RawNativeScalarCircuitBridge.liftCircuit D p.circuit).eval x := by
    rw [SourceLocalOriginalSemantics.evalRaw_eq_on_fixed r p.circuit x hfixed]
    exact WeightFreeRawProbability.evalRaw_eq_lift D p.circuit x
  have houtput : (RawNativeScalarCircuitBridge.liftCircuit D p.circuit).eval x p.cursor =
      d.classOf (rawValue d v p) := by
    exact (congrFun hnormalized p.cursor).symm.trans (congrFun hclass p.cursor)
  have hscalar : p.circuit.eval z p.cursor = scalarValue p := by
    change p.circuit.eval z p.cursor =
      evalRaw NativeMixerEventConeExclusion.mixer p.circuit z p.cursor
    exact (congrFun (NativeAllocatedSourceArithmetic.evalRaw_eq_native p.circuit z)
      p.cursor).symm
  have h := circuit_related D (d.classOf v) p.circuit z x hinit p.cursor
  rw [hscalar, houtput] at h
  exact h

/-- Scalar equality determines the response class even for a null reference.
No probability family or faithful-action premise is used in this direction. -/
theorem scalar_eq_implies_responseEq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p q : ScalarProgram) (h : scalarValue p = scalarValue q) :
    ResponseEq d.operation d.signature (rawValue d v p) (rawValue d v q) := by
  apply (d.classOf_eq_iff_responseEq _ _).mp
  apply related_raw_unique d.quotientData.zeroWeightData (d.classOf v)
    (allocated_class_related d v hz hv p)
  rw [h]
  exact allocated_class_related d v hz hv q

/-- A supplied single-basis response law forces faithful reference action, so
the scalar coordinate classifies response equivalence of allocated programs.
This is not a multi-source probability assignment or literal raw equality. -/
theorem responseEq_iff_scalar_eq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v) (p q : ScalarProgram) :
    ResponseEq d.operation d.signature (rawValue d v p) (rawValue d v q) ↔
      scalarValue p = scalarValue q := by
  constructor
  · intro h
    have hclass := (d.classOf_eq_iff_responseEq _ _).mpr h
    have hp := allocated_class_related d v hz hv p
    have hq := allocated_class_related d v hz hv q
    rw [← hclass] at hq
    have hfaithful := RawNativeProbabilityExistence.gaussianAction_injective_of_rawLaw
      d.quotientData.zeroWeightData (d.classOf v) (normalizedLawEquiv d v hz hv L)
    exact RawNativeProbabilityExistence.related_scalar_unique
      d.quotientData.zeroWeightData (d.classOf v) hfaithful hp hq
  · exact scalar_eq_implies_responseEq d v hz hv p q

/-- With a zero reference, source and zero identity programs agree as raw
values despite distinct scalar coordinates. A response law for that reference
is impossible, so this does not contradict the conditional converse. -/
theorem null_reference_control (d : Data V Ω) :
    ResponseEq d.operation d.signature
      (rawValue d d.chosenZero (sourceProgram ()))
      (rawValue d d.chosenZero (zeroProgram : ScalarProgram)) ∧
    scalarValue (sourceProgram ()) ≠ scalarValue (zeroProgram : ScalarProgram) ∧
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law d d.chosenZero) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C
    rfl
  · change (1 : ℂ) ≠ 0
    exact one_ne_zero
  · exact ResponsePhaseQuotientWall.no_law_of_reference_response_zero d d.chosenZero
      (fun C => rfl)

end

end IDT.QMClosure.ResponseAllocatedFaithfulness
