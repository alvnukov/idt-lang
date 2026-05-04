import Proofs.QMClosure.FullQMAssemblyFromGroundedSources

namespace IDT
namespace QMClosure

def toyChecked : CheckedProp :=
  {
    statement := True,
    proof := True.intro
  }

def toyB0CandidateBase : B0CandidateBase :=
  {
    finiteGeneration := toyChecked,
    facticizableSeparation := toyChecked,
    importBoundary := toyChecked,
    noPrimitiveGlobalSection := toyChecked,
    noHilbertPrimitive := toyChecked,
    noBornPrimitive := toyChecked,
    noUnitaryPrimitive := toyChecked,
    noTensorPrimitive := toyChecked,
    noStonePrimitive := toyChecked,
    noSpectralPrimitive := toyChecked
  }

def toyBoolPair : DistinctPair Bool :=
  {
    left := false,
    right := true,
    distinct := by decide
  }

def toyExposedIn : Bool → Bool → Prop
  | false, false => True
  | _, _ => False

def toyCompleteExposedContextPartitionGround :
    CompleteExposedContextPartitionGround :=
  {
    Context := Bool,
    Fact := Unit,
    Block := Bool,
    contexts := toyBoolPair,
    factWitness := (),
    blockOf := fun _ => false,
    exposedIn := toyExposedIn,
    exposedWitness := True.intro,
    exposureBoundary := by
      exact ⟨true, false, fun impossible => impossible⟩
  }

def toyReversibleContextAutomorphismClosureGround :
    ReversibleContextAutomorphismClosureGround :=
  {
    Context := Bool,
    Route := Unit,
    contexts := toyBoolPair,
    routeWitness := (),
    forward := fun value => !value,
    backward := fun value => !value,
    roundTripLeft := rfl,
    roundTripRight := rfl,
    nontrivialForward := rfl
  }

def toyCoherentRefinementCompactnessGround :
    CoherentRefinementCompactnessGround :=
  {
    Refinement := Unit,
    State := Bool,
    refinementWitness := (),
    states := toyBoolPair,
    compactBound := 1,
    compactBoundPositive := by decide
  }

def toyGenerates : Bool → Bool → Prop :=
  fun generator route => generator = route

def toyGeneratorBookkeepingWithoutStoneGround :
    GeneratorBookkeepingWithoutStoneGround :=
  {
    Generator := Bool,
    Route := Bool,
    generatorWitness := false,
    routeWitness := false,
    generates := toyGenerates,
    generationWitness := rfl,
    generationBoundary := by
      exact ⟨false, true, fun impossible => nomatch impossible⟩
  }

def toyProductContextGenerationClosureGround :
    ProductContextGenerationClosureGround :=
  {
    LocalContext := Bool,
    ProductContext := Bool × Bool,
    localContexts := toyBoolPair,
    productWitness := (false, true),
    productOf := fun left right => (left, right),
    productWitnessMatches := rfl,
    productOrderBoundary := by decide
  }

def toyWitnesses : Bool → Bool → Prop :=
  fun product joint => product = joint

def toyNoHiddenJointOnlyGenerationGround :
    NoHiddenJointOnlyGenerationGround :=
  {
    LocalFact := Bool,
    JointFact := Bool,
    ProductWitness := Bool,
    localFacts := toyBoolPair,
    jointFactWitness := false,
    productWitness := false,
    witnesses := toyWitnesses,
    witnessedJointFact := rfl,
    witnessBoundary := by
      exact ⟨false, true, fun impossible => nomatch impossible⟩
  }

def toyGroundedCGSCSemanticExtensionBase :
    GroundedCGSCSemanticExtensionBase :=
  {
    b0 := toyB0CandidateBase,
    exposed := toyCompleteExposedContextPartitionGround,
    reversible := toyReversibleContextAutomorphismClosureGround,
    refinement := toyCoherentRefinementCompactnessGround,
    generator := toyGeneratorBookkeepingWithoutStoneGround,
    product := toyProductContextGenerationClosureGround,
    noHiddenJoint := toyNoHiddenJointOnlyGenerationGround
  }

theorem grounded_kernel_admits_toy_full_qm_obligation_bundle :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase) :=
  grounded_semantic_sources_yield_full_qm_obligation_bundle
    toyGroundedCGSCSemanticExtensionBase

theorem grounded_kernel_toy_model_keeps_import_guards :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        toyGroundedCGSCSemanticExtensionBase).compositeClosure.noHilbertImport.statement :=
  grounded_semantic_sources_yield_full_qm_import_guards
    toyGroundedCGSCSemanticExtensionBase

end QMClosure
end IDT
