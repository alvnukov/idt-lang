import Proofs.QMClosure.UniversalPrimitiveSourceKernel

namespace IDT
namespace QMClosure

inductive Triad where
  | first
  | second
  | third

open Triad

theorem triad_first_ne_second : first ≠ second := by
  intro impossible
  cases impossible

theorem triad_first_ne_third : first ≠ third := by
  intro impossible
  cases impossible

theorem triad_second_ne_third : second ≠ third := by
  intro impossible
  cases impossible

def triadAtLeastThree : AtLeastThree Triad :=
  ⟨first, second, third,
    triad_first_ne_second,
    triad_first_ne_third,
    triad_second_ne_third⟩

def triadPair : DistinctPair Triad :=
  {
    left := first,
    right := second,
    distinct := triad_first_ne_second
  }

def triadChecked : CheckedProp :=
  {
    statement := True,
    proof := True.intro
  }

def triadB0CandidateBase : B0CandidateBase :=
  {
    finiteGeneration := triadChecked,
    facticizableSeparation := triadChecked,
    importBoundary := triadChecked,
    noPrimitiveGlobalSection := triadChecked,
    noHilbertPrimitive := triadChecked,
    noBornPrimitive := triadChecked,
    noUnitaryPrimitive := triadChecked,
    noTensorPrimitive := triadChecked,
    noStonePrimitive := triadChecked,
    noSpectralPrimitive := triadChecked
  }

def triadExposedIn : Triad → Triad → Prop
  | first, first => True
  | _, _ => False

def triadCompleteExposedContextPartitionGround :
    CompleteExposedContextPartitionGround :=
  {
    Context := Triad,
    Fact := Unit,
    Block := Triad,
    contexts := triadPair,
    factWitness := (),
    blockOf := fun _ => first,
    exposedIn := triadExposedIn,
    exposedWitness := True.intro,
    exposureBoundary := by
      exact ⟨second, first, fun impossible => impossible⟩
  }

def triadCycle : Triad → Triad
  | first => second
  | second => third
  | third => first

def triadCycleBackward : Triad → Triad
  | first => third
  | second => first
  | third => second

def triadReversibleContextAutomorphismClosureGround :
    ReversibleContextAutomorphismClosureGround :=
  {
    Context := Triad,
    Route := Unit,
    contexts := triadPair,
    routeWitness := (),
    forward := triadCycle,
    backward := triadCycleBackward,
    roundTripLeft := rfl,
    roundTripRight := rfl,
    nontrivialForward := rfl
  }

def triadCoherentRefinementCompactnessGround :
    CoherentRefinementCompactnessGround :=
  {
    Refinement := Unit,
    State := Triad,
    refinementWitness := (),
    states := triadPair,
    compactBound := 1,
    compactBoundPositive := by decide
  }

def triadGenerates : Triad → Triad → Prop :=
  fun generator route => generator = route

def triadGeneratorBookkeepingWithoutStoneGround :
    GeneratorBookkeepingWithoutStoneGround :=
  {
    Generator := Triad,
    Route := Triad,
    generatorWitness := first,
    routeWitness := first,
    generates := triadGenerates,
    generationWitness := rfl,
    generationBoundary := by
      exact ⟨first, second, triad_first_ne_second⟩
  }

def triadProductContextGenerationClosureGround :
    ProductContextGenerationClosureGround :=
  {
    LocalContext := Triad,
    ProductContext := Triad × Triad,
    localContexts := triadPair,
    productWitness := (first, second),
    productOf := fun left right => (left, right),
    productWitnessMatches := rfl,
    productOrderBoundary := by
      intro impossible
      exact triad_first_ne_second (Prod.ext_iff.mp impossible).left
  }

def triadWitnesses : Triad → Triad → Prop :=
  fun product joint => product = joint

def triadNoHiddenJointOnlyGenerationGround :
    NoHiddenJointOnlyGenerationGround :=
  {
    LocalFact := Triad,
    JointFact := Triad,
    ProductWitness := Triad,
    localFacts := triadPair,
    jointFactWitness := first,
    productWitness := first,
    witnesses := triadWitnesses,
    witnessedJointFact := rfl,
    witnessBoundary := by
      exact ⟨first, second, triad_first_ne_second⟩
  }

def triadGroundedCGSCSemanticExtensionBase :
    GroundedCGSCSemanticExtensionBase :=
  {
    b0 := triadB0CandidateBase,
    exposed := triadCompleteExposedContextPartitionGround,
    reversible := triadReversibleContextAutomorphismClosureGround,
    refinement := triadCoherentRefinementCompactnessGround,
    generator := triadGeneratorBookkeepingWithoutStoneGround,
    product := triadProductContextGenerationClosureGround,
    noHiddenJoint := triadNoHiddenJointOnlyGenerationGround
  }

def triadUniversalPrimitiveSourceKernel :
    UniversalPrimitiveSourceKernel :=
  {
    grounded := triadGroundedCGSCSemanticExtensionBase,
    primitiveGeneratedScope := triadChecked,
    admissibleContextUniverse := triadChecked,
    exposedContextRank := triadAtLeastThree,
    reversibleContextRank := triadAtLeastThree,
    localProductContextRank := triadAtLeastThree,
    localFactRank := triadAtLeastThree
  }

theorem universal_kernel_admits_three_point_toy_full_qm_obligation_bundle :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)) :=
  universal_primitive_source_kernel_yields_full_qm_obligation_bundle
    triadUniversalPrimitiveSourceKernel

theorem universal_kernel_three_point_toy_keeps_import_guards :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
      (universalPrimitiveSourceKernelToGrounded
        triadUniversalPrimitiveSourceKernel)).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          triadUniversalPrimitiveSourceKernel)).compositeClosure.noHilbertImport.statement :=
  universal_primitive_source_kernel_yields_import_guards
    triadUniversalPrimitiveSourceKernel

end QMClosure
end IDT
