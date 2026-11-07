import Proofs.QMClosure.NativeAllocatedObservationBoundary
import Proofs.QMClosure.ResponseAllocatedFaithfulness

/-!
# Signature laws on the explicitly allocated scalar carrier

For an arbitrary supplied signature, a native single-basis response probability
family exists exactly when full contextual response equivalence separates the
generated scalar carrier. Separation concerns all stated contexts and is weaker
than requiring the bare signature itself to be injective. No topology, numeric
readout, or decidable equality on the signature codomain is supplied.

The structural response data are defined for every signature, independently of
separation. Sufficiency transports any supplied scalar family's probability
field unchanged; the canonical scalar family is used only for the separate
existence statement. Necessity uses only the supplied response law.

Programs allocate known source occurrences. A common frame and joint input
availability remain supplied. These results do not assert a physical ray-state
ontology, a normalized probability extension to multi-source arrays, provenance
or availability of a probability family, actualization, or QM closure.
-/

namespace IDT.QMClosure.NativeAllocatedSignatureLaw

noncomputable section

open ResponseContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedSourceArithmetic
open NativeVacuumProbabilityFamily MixerGeneratedProcessWall
open NativeMixerEventConeExclusion (mixer)

variable {Ω : Type*}

private theorem responseEq_of_eq (σ : G → Ω) {x y : G} (h : x = y) :
    ResponseEq operationG σ x y := by
  subst y
  intro C
  rfl

/-- Literal scalar structural laws supply response data for every signature. -/
def signatureData (σ : G → Ω) : Data G Ω where
  chosenZero := zeroG
  operation := operationG
  signature := σ
  square p := ⟨responseEq_of_eq σ (congrArg Prod.fst (operationG_square p)),
    responseEq_of_eq σ (congrArg Prod.snd (operationG_square p))⟩
  medial w x y z := responseEq_of_eq σ (operationG_medial w x y z)

/-- Full contextual separation; no bare-signature injectivity is assumed. -/
def Separates (σ : G → Ω) : Prop :=
  ∀ x y : G, ResponseEq operationG σ x y → x = y

theorem signatureData_observedTransparent (σ : G → Ω) :
    ObservedTransparent (signatureData σ) := by
  intro x
  apply responseEq_of_eq σ
  apply Subtype.ext
  exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_transparent x.val)

/-- Original evaluation on the generated carrier denotes the same supplied
program, without a probability law or a separation premise. -/
theorem rawValue_eq_ofProgram (σ : G → Ω) (p : ScalarProgram) :
    ResponseAllocatedFaithfulness.rawValue (signatureData σ) unitG p = ofProgram p := by
  apply Subtype.ext
  change (WeightFreeRawProbability.evalRaw operationG p.circuit
    (AllocatedPreparation.inputState zeroG (fun _ : Unit => unitG) p) p.cursor).val =
      value p
  have hinput :
      (fun i => (AllocatedPreparation.inputState zeroG (fun _ : Unit => unitG) p i).val) =
      AllocatedPreparation.inputState (0 : ℂ) (fun _ : Unit => (1 : ℂ)) p := by
    funext i
    cases hi : p.input i <;> simp [AllocatedPreparation.inputState, hi]
  have h := congrFun (evalRaw_coe p.circuit
    (AllocatedPreparation.inputState zeroG (fun _ : Unit => unitG) p)) p.cursor
  rw [hinput] at h
  exact h

/-- Complete original single-basis prepared arrays preserve scalar evaluation.
The input-coercion lemma used here depends only on the common zero and gate. -/
theorem signature_prepared_coe (σ : G → Ω)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) :
    (fun i => (ResponseNativeProbabilitySelection.prepared (signatureData σ) unitG s c i).val) =
      c.eval (source s) := by
  unfold ResponseNativeProbabilitySelection.prepared
  change (fun i => (WeightFreeRawProbability.evalRaw operationG c
    (ResponseNativeProbabilitySelection.basisInput (signatureData σ) unitG s) i).val) = _
  rw [evalRaw_coe]
  have hinput :
      (fun i => (ResponseNativeProbabilitySelection.basisInput (signatureData σ) unitG s i).val) =
      source s := basisInput_coe (0 : ℂ) s
  rw [hinput]
  exact NativeAllocatedSourceArithmetic.evalRaw_eq_native c (source s)

/-- Under full contextual separation, transport any supplied scalar family.
The probability field is unchanged; the six family contracts are transported. -/
def lawOfScalar (σ : G → Ω) (hsep : Separates σ)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    funext i
    have hraw := hsep _ _ (h i)
    have hv := congrArg Subtype.val hraw
    exact (congrFun (signature_prepared_coe σ s c) i).symm.trans
      (hv.trans (congrFun (signature_prepared_coe σ s e) i))
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem lawOfScalar_probability (σ : G → Ω) (hsep : Separates σ)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
      (lawOfScalar σ hsep L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

/-- A response law alone forces full contextual separation on all generated
values. No independent scalar probability family is used in this direction. -/
theorem responseEq_eq_of_law (σ : G → Ω)
    (L : ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) :
    Separates σ := by
  intro x y h
  obtain ⟨p, rfl⟩ := ofProgram_surjective x
  obtain ⟨q, rfl⟩ := ofProgram_surjective y
  apply Subtype.ext
  have hraw : ResponseEq operationG σ
      (ResponseAllocatedFaithfulness.rawValue (signatureData σ) unitG p)
      (ResponseAllocatedFaithfulness.rawValue (signatureData σ) unitG q) := by
    rw [rawValue_eq_ofProgram, rawValue_eq_ofProgram]
    exact h
  have hscalar := (ResponseAllocatedFaithfulness.responseEq_iff_scalar_eq
    (signatureData σ) unitG (signatureData_observedTransparent σ zeroG)
    (signatureData_observedTransparent σ unitG) L p q).mp hraw
  exact hscalar

/-- Canonical scalar consistency supplies sufficiency; necessity still uses
only the given response law. No probability provenance is inferred. -/
theorem law_nonempty_iff_separates (σ : G → Ω) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) ↔
      Separates σ := by
  constructor
  · rintro ⟨L⟩
    exact responseEq_eq_of_law σ L
  · intro hsep
    exact ⟨lawOfScalar σ hsep NativeVacuumProbabilityFamily.canonicalLaw⟩

/-- The criterion also holds for exact preservation of any supplied scalar
probability field, including its complete finite-width polymorphic interface. -/
theorem same_probability_law_exists_iff_separates (σ : G → Ω)
    (L : NativeVacuumProbabilityFamily.Law) :
    (∃ M : ResponseNativeProbabilitySelection.Law (signatureData σ) unitG,
      @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG M =
        @NativeVacuumProbabilityFamily.Law.prob L) ↔ Separates σ := by
  constructor
  · rintro ⟨M, _⟩
    exact responseEq_eq_of_law σ M
  · intro hsep
    exact ⟨lawOfScalar σ hsep L, lawOfScalar_probability σ hsep L⟩

end

end IDT.QMClosure.NativeAllocatedSignatureLaw
