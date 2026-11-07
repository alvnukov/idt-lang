import Proofs.QMClosure.AllocatedGeneratedContexts
import Proofs.QMClosure.NativeAllocatedSourceArithmetic
import Proofs.QMClosure.NativeRecipeObservationBoundary
import Proofs.QMClosure.ResponsePhaseQuotientWall

/-!
# Point observations on the allocated scalar generated carrier

The scalar carrier contains the selected values of
all finite explicitly allocated 0/1 preparations, with no uniform resource
ceiling. Both outputs and every ancillary wire are retained by those recipes.

Each ambient exact point test defines response data on this carrier. If the
tested point is generated, explicit charged comparison references separate
literal values and every supplied scalar six-field law transports with its
probability field unchanged. If the tested point is not generated, its test is
constant false on the carrier and its six-field law contract has no inhabitant.

The laws here remain single-basis-reference laws. This is not an extension to
joint allocated input arrays. A common scalar frame and the physical joint
availability of supplied recipes remain hypotheses outside these mathematical
constructions. No physical detector, unknown-token cloning, tomography,
actualization, tensor structure, independence, or QM closure is established.
-/

namespace IDT.QMClosure.NativeAllocatedObservationBoundary

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient ResponseContextQuotient
open NativeVacuumProbabilityFamily MixerGeneratedProcessWall
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b)
open NativeAllocatedSourceArithmetic
open NativeRecipeObservationBoundary

abbrev G := AllocatedGeneratedContexts.G mixer (0 : ℂ) (fun _ : Unit => (1 : ℂ))

def operationG : G × G → G × G :=
  AllocatedGeneratedContexts.operationG mixer 0 (fun _ : Unit => (1 : ℂ))

def zeroG : G := AllocatedGeneratedContexts.zeroG mixer 0 (fun _ : Unit => (1 : ℂ))
def unitG : G := AllocatedGeneratedContexts.sourceG mixer 0 (fun _ : Unit => (1 : ℂ)) ()

def ofProgram (p : ScalarProgram) : G :=
  AllocatedGeneratedContexts.value mixer 0 (fun _ : Unit => (1 : ℂ)) p

@[simp] theorem val_ofProgram (p : ScalarProgram) : (ofProgram p).val = value p := rfl
@[simp] theorem val_zeroG : zeroG.val = 0 := rfl
@[simp] theorem val_unitG : unitG.val = 1 := rfl

theorem generated_iff_reachable (q : ℂ) :
    AllocatedGeneratedContexts.Generated mixer (0 : ℂ) (fun _ : Unit => (1 : ℂ)) q ↔
      Reachable q := Iff.rfl

theorem ofProgram_surjective : Function.Surjective ofProgram :=
  AllocatedGeneratedContexts.value_surjective mixer 0 (fun _ : Unit => (1 : ℂ))

/-- Literal structural laws hold before selecting a point signature. -/
theorem operationG_square (p : G × G) : operationG (operationG p) = p.swap := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_square (p.1.val, p.2.val))
  · apply Subtype.ext
    exact congrArg Prod.snd (NativeMixerEventConeExclusion.mixer_square (p.1.val, p.2.val))

theorem operationG_medial (w x y z : G) :
    MedialSwapRoot.firstChannel operationG
      (MedialSwapRoot.firstChannel operationG w x)
      (MedialSwapRoot.firstChannel operationG y z) =
    MedialSwapRoot.firstChannel operationG
      (MedialSwapRoot.firstChannel operationG w y)
      (MedialSwapRoot.firstChannel operationG x z) := by
  apply Subtype.ext
  exact ResponseSignatureControls.native_medial w.val x.val y.val z.val

def pointSignature (q : ℂ) (x : G) : Bool := pointTest q x.val

theorem responseEq_of_eq (q : ℂ) {x y : G} (h : x = y) :
    ResponseEq operationG (pointSignature q) x y := by
  subst y
  intro C
  rfl

/-- Defined for every ambient q, independently of q's generated membership. -/
def pointGeneratedData (q : ℂ) : Data G Bool where
  chosenZero := zeroG
  operation := operationG
  signature := pointSignature q
  square p := ⟨responseEq_of_eq q (congrArg Prod.fst (operationG_square p)),
    responseEq_of_eq q (congrArg Prod.snd (operationG_square p))⟩
  medial w x y z := responseEq_of_eq q (operationG_medial w x y z)

/-- Each repeated known preparation is allocated and charged again. -/
def pointReferenceProgram (qProg xProg : ScalarProgram) : ScalarProgram :=
  add (mix qProg (phasePlus qProg)) (phaseMinus xProg)

theorem value_pointReferenceProgram (qProg xProg : ScalarProgram) :
    value (pointReferenceProgram qProg xProg) =
      pointReference (value qProg) (value xProg) := by
  rw [pointReferenceProgram, value_add, value_mix, value_phasePlus, value_phaseMinus]
  apply Complex.ext <;>
    norm_num [pointReference, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

theorem budget_pointReferenceProgram (qProg xProg : ScalarProgram) :
    AllocatedPreparation.budget (pointReferenceProgram qProg xProg) =
      25 * AllocatedPreparation.budget qProg + 20 * AllocatedPreparation.budget xProg := by
  simp only [pointReferenceProgram, budget_add, budget_mix, budget_phasePlus, budget_phaseMinus]
  omega

/-- A reachable tested point supplies reachable fixed references for separation. -/
theorem pointGenerated_responseEq_iff_eq (q : ℂ) (hq : Reachable q) (x y : G) :
    ResponseEq operationG (pointSignature q) x y ↔ x = y := by
  constructor
  · intro h
    obtain ⟨qProg, hqProg⟩ := hq
    obtain ⟨xProg, hxProg⟩ := x.property
    change value xProg = x.val at hxProg
    let r : G := ofProgram (pointReferenceProgram qProg xProg)
    have hr : r.val = pointReference q x.val := by
      change value (pointReferenceProgram qProg xProg) = pointReference q x.val
      rw [value_pointReferenceProgram, hqProg, hxProg]
    have ht := h (.left .first .hole r)
    change pointTest q (mixer (x.val, r.val)).1 =
      pointTest q (mixer (y.val, r.val)).1 at ht
    rw [hr, first_point_reference, first_point_reference, sub_self, mul_zero,
      add_zero, pointTest_self] at ht
    have hz : q + a * (y.val - x.val) = q := (pointTest_eq_true_iff _ _).mp ht.symm
    have hz' : a * (y.val - x.val) = 0 := by
      have hh := congrArg (fun z : ℂ => z - q) hz
      simpa only [add_sub_cancel_left, sub_self] using hh
    apply Subtype.ext
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left
      ResponseSignatureControls.native_a_ne_zero)).symm
  · exact responseEq_of_eq q

theorem pointSignature_false_of_not_reachable (q : ℂ) (hq : ¬ Reachable q) (x : G) :
    pointSignature q x = false := by
  have hne : x.val ≠ q := by
    intro he
    apply hq
    obtain ⟨p, hp⟩ := x.property
    exact ⟨p, hp.trans he⟩
  classical
  simp [pointSignature, pointTest, hne]

/-- Every finite context still lands in G, where an absent point is never hit. -/
theorem pointGenerated_responseEq_of_not_reachable (q : ℂ) (hq : ¬ Reachable q)
    (x y : G) : ResponseEq operationG (pointSignature q) x y := by
  intro C
  rw [pointSignature_false_of_not_reachable q hq,
    pointSignature_false_of_not_reachable q hq]

theorem pointGenerated_responseEq_classification (q : ℂ) (x y : G) :
    ResponseEq operationG (pointSignature q) x y ↔ ¬ Reachable q ∨ x = y := by
  classical
  by_cases hq : Reachable q
  · rw [pointGenerated_responseEq_iff_eq q hq]
    simp only [hq, not_true_eq_false, false_or]
  · constructor
    · intro _
      exact Or.inl hq
    · intro _
      exact pointGenerated_responseEq_of_not_reachable q hq x y

/-- The zero-reference wall uses four fields of the existing six-field contract. -/
theorem pointGenerated_no_law_of_not_reachable (q : ℂ) (hq : ¬ Reachable q) :
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData q) unitG) :=
  ResponsePhaseQuotientWall.no_law_of_reference_response_zero (pointGeneratedData q) unitG
    (pointGenerated_responseEq_of_not_reachable q hq unitG zeroG)

/-! Full prepared arrays, not only selected coordinates, preserve scalar semantics. -/

theorem evalRaw_coe {ι : Type} [DecidableEq ι] (c : Native ι) (x : ι → G) :
    (fun i => (WeightFreeRawProbability.evalRaw operationG c x i).val) =
      WeightFreeRawProbability.evalRaw mixer c (fun i => (x i).val) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    funext k
    simp only [WeightFreeRawProbability.evalRaw]
    split_ifs <;> rfl
  | permute => rfl
  | seq c d hc hd =>
    change (fun i => (WeightFreeRawProbability.evalRaw operationG d
      (WeightFreeRawProbability.evalRaw operationG c x) i).val) = _
    rw [hd, hc]
    rfl

theorem basisInput_coe (q : ℂ) {ι : Type} [DecidableEq ι] (s : ι) :
    (fun i => (ResponseNativeProbabilitySelection.basisInput (pointGeneratedData q) unitG s i).val) =
      source s := by
  funext i
  by_cases hi : i = s
  · simp only [ResponseNativeProbabilitySelection.basisInput, if_pos hi]
    change (1 : ℂ) = source s i
    simp [source, single, hi]
  · simp only [ResponseNativeProbabilitySelection.basisInput, if_neg hi]
    change (0 : ℂ) = source s i
    simp [source, single, hi]

theorem pointGenerated_prepared_coe (q : ℂ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) :
    (fun i => (ResponseNativeProbabilitySelection.prepared (pointGeneratedData q) unitG s c i).val) =
      c.eval (source s) := by
  unfold ResponseNativeProbabilitySelection.prepared
  change (fun i => (WeightFreeRawProbability.evalRaw operationG c
    (ResponseNativeProbabilitySelection.basisInput (pointGeneratedData q) unitG s) i).val) = _
  rw [evalRaw_coe, basisInput_coe]
  exact NativeAllocatedSourceArithmetic.evalRaw_eq_native c (source s)

/-! Transport any supplied scalar law; canonical consistency is separate. -/

def pointGeneratedLawOfScalar (q : ℂ) (hq : Reachable q)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (pointGeneratedData q) unitG where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    funext i
    have hraw := (pointGenerated_responseEq_iff_eq q hq _ _).mp (h i)
    have hv := congrArg Subtype.val hraw
    exact (congrFun (pointGenerated_prepared_coe q s c) i).symm.trans
      (hv.trans (congrFun (pointGenerated_prepared_coe q s e) i))
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem pointGeneratedLawOfScalar_probability (q : ℂ) (hq : Reachable q)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Bool (pointGeneratedData q) unitG
      (pointGeneratedLawOfScalar q hq L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

def canonicalPointGeneratedLaw (q : ℂ) (hq : Reachable q) :
    ResponseNativeProbabilitySelection.Law (pointGeneratedData q) unitG :=
  pointGeneratedLawOfScalar q hq NativeVacuumProbabilityFamily.canonicalLaw

theorem pointGenerated_law_nonempty_iff_reachable (q : ℂ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData q) unitG) ↔
      Reachable q := by
  classical
  constructor
  · intro hL
    by_contra hq
    exact pointGenerated_no_law_of_not_reachable q hq hL
  · intro hq
    exact ⟨canonicalPointGeneratedLaw q hq⟩

theorem pointGenerated_law_nonempty_iff_gaussian_dyadic (q : ℂ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData q) unitG) ↔
      GaussianDyadic q :=
  (pointGenerated_law_nonempty_iff_reachable q).trans (reachable_iff_gaussian_dyadic q)

/-- The original ambient pointData and its supplied law remain untouched. -/
theorem third_ambient_generated_boundary :
    (∀ x y : ℂ, ResponseEq mixer (pointTest (1 / 3 : ℂ)) x y ↔ x = y) ∧
    Nonempty (ResponseNativeProbabilitySelection.Law (pointData (1 / 3 : ℂ)) 1) ∧
    (∀ x y : G, ResponseEq operationG (pointSignature (1 / 3 : ℂ)) x y) ∧
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData (1 / 3 : ℂ)) unitG) :=
  ⟨point_responseEq_iff_eq (1 / 3 : ℂ), point_law_nonempty (1 / 3 : ℂ),
    pointGenerated_responseEq_of_not_reachable (1 / 3 : ℂ) third_not_reachable,
    pointGenerated_no_law_of_not_reachable (1 / 3 : ℂ) third_not_reachable⟩

theorem pointGenerated_law_two :
    Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData 2) unitG) :=
  ⟨canonicalPointGeneratedLaw 2 ⟨targetTwo, targetTwo_value⟩⟩

theorem pointGenerated_law_zero :
    Nonempty (ResponseNativeProbabilitySelection.Law (pointGeneratedData 0) unitG) :=
  ⟨canonicalPointGeneratedLaw 0 ⟨zero, value_zero⟩⟩

inductive BoundaryRole where
  | suppliedConcreteScalarModelAndExactPointTest
  | noUniformResourceCeiling
  | everyRepeatedReferenceAllocatedAndCharged
  | structuralDataDefinedForEveryAmbientPoint
  | generatedPointExactlyControlsThisLawDomain
  | arbitrarySuppliedScalarProbabilityFieldPreserved
  | fullPreparedArrayCoercionBeforeLawTransport
  | canonicalConsistencyWitnessSeparate
  | originalAmbientDataAndLawUnchanged
  | singleBasisLawNotJointAllocatedInputExtension
  | retainedOutputsAndSuppliedCommonFrame
  | noPhysicalAvailabilityDetectorOrUnknownTokenCloning
  | noTomographyActualizationOrQMClosure
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .suppliedConcreteScalarModelAndExactPointTest,
  .noUniformResourceCeiling,
  .everyRepeatedReferenceAllocatedAndCharged,
  .structuralDataDefinedForEveryAmbientPoint,
  .generatedPointExactlyControlsThisLawDomain,
  .arbitrarySuppliedScalarProbabilityFieldPreserved,
  .fullPreparedArrayCoercionBeforeLawTransport,
  .canonicalConsistencyWitnessSeparate,
  .originalAmbientDataAndLawUnchanged,
  .singleBasisLawNotJointAllocatedInputExtension,
  .retainedOutputsAndSuppliedCommonFrame,
  .noPhysicalAvailabilityDetectorOrUnknownTokenCloning,
  .noTomographyActualizationOrQMClosure]

end
end IDT.QMClosure.NativeAllocatedObservationBoundary
