import Proofs.QMClosure.ResponseRecipeContextReflection
import Proofs.QMClosure.NativeReferenceSeparation

/-!
# Algebraic recipe comparison and supplied vacuum-response soundness

The difference event retains the existing paired-setting circuit certificate.
Its quotient value is reconstructed phase after reconstructed half of a
difference. Injectivity is algebraic, with no scalar recovery, numerical
signature, positive weight, infinite-order reference or probability law.

ComparatorVacuumSound is supplied observation soundness restricted to these
comparison events. It is equivalent to correctness of each baseline comparison
and sufficient for full profile reflection; necessity for profile reflection is
not asserted. Outer ResponseEq still uses arbitrary fixed raw references.
This factors algebra from observation soundness; it derives no minimal physical
primitive, detector, unknown-token processing, standalone native phase,
amplification, physical availability, actualization or origin claim.
-/

namespace IDT.QMClosure.ResponseRecipeComparison

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeRecipeContextRealization
open ResponseSourceLocalProbability ResponseRecipeContextReflection
open RawNativeDyadicSemantics

variable {V Ω : Type*}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def comparisonEvent (s : ι) (e f : Event ι) : Event ι :=
  (NativeReferenceSeparation.pairedSetting s e f).differenceEvent

def vacuumEvent (s : ι) : Event ι := ⟨1, .identity, .inr s⟩

theorem comparisonEvent_amplitude (s : ι) (e f : Event ι) :
    amplitude s (comparisonEvent s e f) =
      NativeReferenceSeparation.differenceOutput (amplitude s e) (amplitude s f) :=
  (NativeReferenceSeparation.pairedSetting s e f).difference_amplitude

/-- The identity circuit retains the marked source and its unused vacuum wire. -/
theorem vacuumEvent_original (d : Data V Ω) (v : V) (s : ι) :
    originalEvent d v s (vacuumEvent s) = d.chosenZero := by
  simp [originalEvent, vacuumEvent, ResponseNativeProbabilitySelection.prepared,
    ResponseNativeProbabilitySelection.basisInput, WeightFreeRawProbability.evalRaw,
    sourceAt]

theorem exists_vacuumEvent (d : Data V Ω) (v : V) (s : ι) :
    ∃ e : Event ι, originalEvent d v s e = d.chosenZero :=
  ⟨vacuumEvent s, vacuumEvent_original d v s⟩

/-- Correlated scalar certificates transfer directly to raw equality without
recovering scalar coordinates from the raw carrier. -/
theorem rawEvent_comparison (r : WeightFreeRawProbability.RawOperationalData V)
    (v : r.Carrier) (s : ι) (e f : Event ι) :
    rawEvent r v s (comparisonEvent s e f) =
      r.zeroWeightData.phase.J (RawOperationalSeparation.half r.zeroWeightData
        (rawEvent r v s e - rawEvent r v s f)) := by
  have he := rawEvent_related r v s e
  have hf := rawEvent_related r v s f
  have hrel := related_phase r.zeroWeightData v
    (related_half r.zeroWeightData v (related_sub r.zeroWeightData v he hf))
  have hc := rawEvent_related r v s (comparisonEvent s e f)
  rw [comparisonEvent_amplitude] at hc
  have hs : NativeReferenceSeparation.differenceOutput (amplitude s e) (amplitude s f) =
      Complex.I * ((amplitude s e - amplitude s f) / 2) := by
    unfold NativeReferenceSeparation.differenceOutput
    ring
  rw [hs] at hc
  exact related_raw_unique r.zeroWeightData v hc hrel

theorem comparisonEvent_class (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (e f : Event ι) :
    d.classOf (originalEvent d v s (comparisonEvent s e f)) =
      d.quotientData.zeroWeightData.phase.J
        (RawOperationalSeparation.half d.quotientData.zeroWeightData
          (@Sub.sub d.quotientData.Carrier inferInstance
            (d.classOf (originalEvent d v s e)) (d.classOf (originalEvent d v s f)))) := by
  rw [originalEvent_class d v hz hv, originalEvent_class d v hz hv,
    originalEvent_class d v hz hv]
  exact rawEvent_comparison d.quotientData (d.classOf v) s e f

theorem phase_injective (r : WeightFreeRawProbability.RawOperationalData V) :
    Function.Injective r.zeroWeightData.phase.J := by
  intro x y h
  have hh := congrArg r.zeroWeightData.phase.J h
  rw [r.zeroWeightData.phase.square, r.zeroWeightData.phase.square] at hh
  exact neg_injective hh

theorem half_injective (r : WeightFreeRawProbability.RawOperationalData V) :
    Function.Injective (RawOperationalSeparation.half r.zeroWeightData) := by
  intro x y h
  calc
    x = RawOperationalSeparation.half r.zeroWeightData x +
        RawOperationalSeparation.half r.zeroWeightData x :=
      (r.zeroWeightData.reconstruction.halves x).symm
    _ = RawOperationalSeparation.half r.zeroWeightData y +
        RawOperationalSeparation.half r.zeroWeightData y := congrArg (fun t => t + t) h
    _ = y := r.zeroWeightData.reconstruction.halves y

/-- Full contextual equality, not merely equality of the supplied signature. -/
theorem comparison_responseEq_zero_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (e f : Event ι) :
    ResponseEq d.operation d.signature
      (originalEvent d v s (comparisonEvent s e f)) d.chosenZero ↔
      ResponseEq d.operation d.signature (originalEvent d v s e) (originalEvent d v s f) := by
  letI : AddCommGroup d.Space := d.quotientData.zeroWeightData.derivedGroup
  rw [← d.classOf_eq_iff_responseEq, ← d.classOf_eq_iff_responseEq,
    comparisonEvent_class d v hz hv]
  change d.quotientData.zeroWeightData.phase.J
    (RawOperationalSeparation.half d.quotientData.zeroWeightData
      (@Sub.sub d.quotientData.Carrier inferInstance
        (d.classOf (originalEvent d v s e)) (d.classOf (originalEvent d v s f)))) = 0 ↔
      d.classOf (originalEvent d v s e) = d.classOf (originalEvent d v s f)
  constructor
  · intro h
    have hJ : d.quotientData.zeroWeightData.phase.J
        (RawOperationalSeparation.half d.quotientData.zeroWeightData
          (@Sub.sub d.quotientData.Carrier inferInstance
            (d.classOf (originalEvent d v s e)) (d.classOf (originalEvent d v s f)))) =
        d.quotientData.zeroWeightData.phase.J 0 := by simpa only [map_zero] using h
    have hH := phase_injective d.quotientData hJ
    have hH0 : RawOperationalSeparation.half d.quotientData.zeroWeightData
        (@Sub.sub d.quotientData.Carrier inferInstance
          (d.classOf (originalEvent d v s e)) (d.classOf (originalEvent d v s f))) =
        RawOperationalSeparation.half d.quotientData.zeroWeightData 0 := by
      simpa only [map_zero] using hH
    exact sub_eq_zero.mp (half_injective d.quotientData hH0)
  · intro h
    have hsub : @Sub.sub d.quotientData.Carrier inferInstance
        (d.classOf (originalEvent d v s e)) (d.classOf (originalEvent d v s f)) = 0 :=
      sub_eq_zero.mpr h
    exact (congrArg (fun x : d.quotientData.Carrier =>
      d.quotientData.zeroWeightData.phase.J
        (RawOperationalSeparation.half d.quotientData.zeroWeightData x)) hsub).trans
      (by simp only [map_zero])

def ComparatorVacuumSound (d : Data V Ω) (v : V) (s : ι) : Prop :=
  ∀ e f : Event ι,
    d.signature (originalEvent d v s (comparisonEvent s e f)) = d.signature d.chosenZero →
      ResponseEq d.operation d.signature
        (originalEvent d v s (comparisonEvent s e f)) d.chosenZero

def responseProfile (d : Data V Ω) (v : V) (s : ι) (e : Event ι) : Event ι → Ω :=
  fun r => d.signature (originalEvent d v s (comparisonEvent s e r))

theorem comparison_signature_eq_zero_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (sound : ComparatorVacuumSound d v s) (e f : Event ι) :
    d.signature (originalEvent d v s (comparisonEvent s e f)) = d.signature d.chosenZero ↔
      ResponseEq d.operation d.signature (originalEvent d v s e) (originalEvent d v s f) := by
  constructor
  · intro h
    exact (comparison_responseEq_zero_iff d v hz hv s e f).mp (sound e f h)
  · intro h
    exact signature_eq ((comparison_responseEq_zero_iff d v hz hv s e f).mpr h)

/-- Exactly the soundness needed for every individual baseline comparison. -/
theorem comparatorVacuumSound_iff_comparison_correct (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v) (s : ι) :
    ComparatorVacuumSound d v s ↔
      ∀ e f : Event ι,
        (d.signature (originalEvent d v s (comparisonEvent s e f)) = d.signature d.chosenZero ↔
          ResponseEq d.operation d.signature (originalEvent d v s e) (originalEvent d v s f)) := by
  constructor
  · intro sound e f
    exact comparison_signature_eq_zero_iff d v hz hv s sound e f
  · intro correct e f h
    exact (comparison_responseEq_zero_iff d v hz hv s e f).mpr ((correct e f).mp h)

/-- Source-recipe equality implies equality of every comparison response
without any observation-soundness premise. -/
theorem responseProfile_eq_of_responseEq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (e f : Event ι)
    (h : ResponseEq d.operation d.signature (originalEvent d v s e) (originalEvent d v s f)) :
    responseProfile d v s e = responseProfile d v s f := by
  funext r
  change d.signature (originalEvent d v s (comparisonEvent s e r)) =
    d.signature (originalEvent d v s (comparisonEvent s f r))
  apply ResponseContextQuotient.signature_eq
  apply (d.classOf_eq_iff_responseEq _ _).mp
  rw [comparisonEvent_class d v hz hv, comparisonEvent_class d v hz hv,
    (d.classOf_eq_iff_responseEq _ _).mpr h]

/-- Soundness is sufficient for full-profile reflection; no necessity claim
for full-profile injectivity is made. The self-reference e detects equality. -/
theorem responseProfile_eq_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (sound : ComparatorVacuumSound d v s) (e f : Event ι) :
    responseProfile d v s e = responseProfile d v s f ↔
      ResponseEq d.operation d.signature (originalEvent d v s e) (originalEvent d v s f) := by
  constructor
  · intro h
    have hself : d.signature (originalEvent d v s (comparisonEvent s e e)) =
        d.signature d.chosenZero :=
      (comparison_signature_eq_zero_iff d v hz hv s sound e e).mpr (fun _ => rfl)
    have hfe : d.signature (originalEvent d v s (comparisonEvent s f e)) =
        d.signature d.chosenZero := (congrFun h e).symm.trans hself
    have heq := (comparison_signature_eq_zero_iff d v hz hv s sound f e).mp hfe
    exact fun c => (heq c).symm
  · exact responseProfile_eq_of_responseEq d v hz hv s e f

end
end IDT.QMClosure.ResponseRecipeComparison
