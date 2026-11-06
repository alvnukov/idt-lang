import Proofs.QMClosure.MedialPortLocalization
import Proofs.QMClosure.CanonicalQuadraticHilbert

namespace IDT.QMClosure.RawOperationalHilbert

open MedialSwapRoot QuadraticRecordRefinement QuadraticHermitianKernel

noncomputable section

/-!
An explicit facade from a raw complete operation to the constructed Hilbert
space. The raw carrier has a chosen zero, but no supplied addition, inverse,
scalar action, topology, phase, half, quadratic law, or Gram-positivity premise.
All reconstructed algebra refers to the canonical diagonal-normalized operation.
Neither normalization nor mathematical completion asserts physical availability.
-/

/-- Exact raw hypotheses, with the chosen zero explicit in the data. -/
structure Data (V : Type*) where
  chosenZero : V
  operation : (V × V) → (V × V)
  square : ∀ p, operation (operation p) = p.swap
  medial : ∀ a b c d,
    firstChannel operation (firstChannel operation a b) (firstChannel operation c d) =
      firstChannel operation (firstChannel operation a c) (firstChannel operation b d)
  weight : V → ℝ
  vacuum : weight chosenZero = 0
  nonnegative : ∀ x, 0 ≤ weight x
  conserved : ∀ x y,
    weight (operation (x, y)).1 + weight (operation (x, y)).2 = weight x + weight y

namespace Data

variable {V : Type*} (d : Data V)

private def normalizedLaws : Laws (DiagonalNormalization.normalized (firstChannel d.operation)) :=
  CompleteOperation.normalizedLaws d.operation d.square d.medial

/-- The group is an output, with its zero fixed by the raw chosen zero. -/
@[reducible] def derivedGroup : AddCommGroup V :=
  letI : Zero V := ⟨d.chosenZero⟩
  CompleteOperation.group d.operation d.square d.medial

set_option linter.unusedVariables false in
/-- Data-indexed carrier used only to install the reconstructed algebra. -/
def Carrier (d : Data V) := V

instance : AddCommGroup (Carrier d) := d.derivedGroup

private def normalizedOperation : (Carrier d × Carrier d) →+ (Carrier d × Carrier d) :=
  letI : Zero V := ⟨d.chosenZero⟩
  canonicalOperation d.normalizedLaws

private theorem reconstruction :
    OperationalQuadraticReconstruction.Reconstruction (V := Carrier d)
      d.normalizedOperation d.weight := by
  letI : Zero V := ⟨d.chosenZero⟩
  exact CompleteOperation.positive_readout d.operation d.square d.medial d.weight
    d.vacuum d.nonnegative d.conserved

/-- Canonical addition as an explicit term in the normalized raw operation. -/
def addition (x y : V) : V :=
  letI : Zero V := ⟨d.chosenZero⟩
  canonicalAdd (DiagonalNormalization.normalized (firstChannel d.operation)) x y

/-- The reconstructed phase, expressed without requiring algebra on raw V. -/
def phaseTerm (x : V) : V :=
  letI : Zero V := ⟨d.chosenZero⟩
  canonicalPhase d.normalizedLaws x

theorem carrier_add (x y : Carrier d) : x + y = d.addition x y := by
  letI : Zero V := ⟨d.chosenZero⟩
  exact canonical_add_raw d.normalizedLaws x y

theorem carrier_zero : (0 : Carrier d) = d.chosenZero := rfl

private def phaseHom : Carrier d →+ Carrier d :=
  OperationalQuadraticReconstruction.phase d.normalizedOperation

private theorem phaseHom_apply (x : Carrier d) : d.phaseHom x = d.phaseTerm x := rfl

private theorem phase_square (x : Carrier d) : d.phaseHom (d.phaseHom x) = -x := by
  letI : Zero V := ⟨d.chosenZero⟩
  exact canonical_phase_square_neg d.normalizedLaws x

/-- Positive quadratic readout derived from the raw conserved weight. -/
def quadratic : PositiveQuadratic (fun x : Carrier d => d.weight x) where
  nonnegative := d.nonnegative
  parallelogram x y := by
    have hp := d.reconstruction.parallelogram x y
    change d.weight (x + y) + d.weight (x + d.phaseHom (d.phaseHom y)) = _ at hp
    simpa only [d.phase_square, sub_eq_add_neg] using hp

/-- The quarter-turn and its readout invariance are reconstructed outputs. -/
def phase : QuadraticPhase (fun x : Carrier d => d.weight x) where
  J := d.phaseHom
  square := d.phase_square
  preserves := d.reconstruction.phase_invariant

private def half : Carrier d →+ Carrier d :=
  OperationalQuadraticReconstruction.half d.normalizedOperation

private theorem halves (x : Carrier d) : d.half x + d.half x = x :=
  d.reconstruction.halves x

/-- Actual separated complete complex inner product space constructed from raw data. -/
abbrev Hilbert := CanonicalQuadraticHilbert.Hilbert d.quadratic d.phase

/-- Feature map whose domain is the original raw carrier. -/
def feature (x : V) : Hilbert d := CanonicalQuadraticHilbert.feature d.quadratic d.phase x

theorem inner_feature (x y : V) :
    inner ℂ (d.feature x) (d.feature y) = kernel d.phase x y :=
  CanonicalQuadraticHilbert.inner_feature d.quadratic d.phase x y

theorem norm_feature_sq (x : V) : ‖d.feature x‖ ^ 2 = d.weight x :=
  CanonicalQuadraticHilbert.norm_feature_sq d.quadratic d.phase x

theorem feature_zero : d.feature d.chosenZero = 0 :=
  CanonicalQuadraticHilbert.feature_zero d.quadratic d.phase

theorem feature_add (x y : V) :
    d.feature (d.addition x y) = d.feature x + d.feature y := by
  rw [← d.carrier_add x y]
  exact CanonicalQuadraticHilbert.feature_add d.quadratic d.phase x y

theorem feature_phase (x : V) : d.feature (d.phaseTerm x) = Complex.I • d.feature x :=
  CanonicalQuadraticHilbert.feature_phase d.quadratic d.phase x

/-- The difference is in the derived group, not in a supplied raw group. -/
def difference (x y : V) : V := @Sub.sub (Carrier d) inferInstance x y

theorem feature_eq_iff (x y : V) :
    d.feature x = d.feature y ↔ d.weight (d.difference x y) = 0 :=
  CanonicalQuadraticHilbert.feature_eq_iff d.quadratic d.phase x y

theorem feature_eq_iff_all_reference_tests (x y : V) :
    d.feature x = d.feature y ↔
      ∀ z, d.weight (d.addition x z) = d.weight (d.addition y z) := by
  simpa only [d.carrier_add] using
    CanonicalQuadraticHilbert.feature_eq_iff_all_reference_tests d.quadratic d.phase x y

/-- Density uses the operational half derived from the raw laws. -/
theorem denseRange_feature : DenseRange d.feature :=
  CanonicalQuadraticHilbert.denseRange_feature d.quadratic d.phase d.half d.halves

end Data

/-- Scope of the facade; these roles do not assert physical closure. -/
inductive BoundaryRole where
  | explicitChosenZeroAndRawCompleteOperation
  | suppliedExactSquareSwapAndGlobalMediality
  | suppliedNonnegativeRealVacuumZeroWeightAndGlobalConservation
  | derivedNormalizedGroupPhaseHalfAndQuadraticReadout
  | constructedComplexHilbertOutputAndDenseFeatureImage
  | noRawCarrierAlgebraScalarOrTopologyPremise
  | zeroWeightAndNoninjectiveFeaturesAllowed
  | mathematicalNormalizationDoesNotProvePhysicalControl
  | normCompletionDoesNotProvePhysicalStateAvailabilityOrCompleteness
  | doesNotProveEventsProbabilityDynamicsCompositeScaleOrFullQM
  | unitaryUniquenessNotEstablishedHere
  | doesNotUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .explicitChosenZeroAndRawCompleteOperation,
  .suppliedExactSquareSwapAndGlobalMediality,
  .suppliedNonnegativeRealVacuumZeroWeightAndGlobalConservation,
  .derivedNormalizedGroupPhaseHalfAndQuadraticReadout,
  .constructedComplexHilbertOutputAndDenseFeatureImage,
  .noRawCarrierAlgebraScalarOrTopologyPremise,
  .zeroWeightAndNoninjectiveFeaturesAllowed,
  .mathematicalNormalizationDoesNotProvePhysicalControl,
  .normCompletionDoesNotProvePhysicalStateAvailabilityOrCompleteness,
  .doesNotProveEventsProbabilityDynamicsCompositeScaleOrFullQM,
  .unitaryUniquenessNotEstablishedHere,
  .doesNotUpgradeManifestStatus]

end

end IDT.QMClosure.RawOperationalHilbert
