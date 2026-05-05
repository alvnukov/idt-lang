import Proofs.QMClosure.PrimitiveGeneratedSourceKernel

namespace IDT
namespace QMClosure

inductive FreePrimitiveAtom where
  | contextLeft
  | contextRight
  | contextThird
  | factWitness
  | blockWitness
  | blockedBlock
  | routeWitness
  | routeBoundary
  | refinementWitness
  | stateLeft
  | stateRight
  | generatorWitness
  | generatorBoundary
  | localFactLeft
  | localFactRight
  | localFactThird
deriving DecidableEq

open FreePrimitiveAtom

def freeIsContext : FreePrimitiveAtom → Prop
  | contextLeft | contextRight | contextThird => True
  | _ => False

def freeIsFact : FreePrimitiveAtom → Prop
  | factWitness => True
  | _ => False

def freeIsBlock : FreePrimitiveAtom → Prop
  | blockWitness | blockedBlock => True
  | _ => False

def freeIsRoute : FreePrimitiveAtom → Prop
  | routeWitness | routeBoundary => True
  | _ => False

def freeIsRefinement : FreePrimitiveAtom → Prop
  | refinementWitness => True
  | _ => False

def freeIsState : FreePrimitiveAtom → Prop
  | stateLeft | stateRight => True
  | _ => False

def freeIsGenerator : FreePrimitiveAtom → Prop
  | generatorWitness | generatorBoundary => True
  | _ => False

def freeIsLocalFact : FreePrimitiveAtom → Prop
  | localFactLeft | localFactRight | localFactThird => True
  | _ => False

def freeExposedIn (block _context : FreePrimitiveAtom) : Prop :=
  block = blockWitness

def freeForwardContext : FreePrimitiveAtom → FreePrimitiveAtom
  | contextLeft => contextRight
  | contextRight => contextLeft
  | contextThird => contextThird
  | value => value

def freeBackwardContext : FreePrimitiveAtom → FreePrimitiveAtom :=
  freeForwardContext

theorem freeForwardContextClosed :
    ∀ value : FreePrimitiveAtom, freeIsContext value → freeIsContext (freeForwardContext value) := by
  intro value witness
  cases value <;> simp [freeIsContext, freeForwardContext] at witness ⊢

theorem freeBackwardContextClosed :
    ∀ value : FreePrimitiveAtom, freeIsContext value → freeIsContext (freeBackwardContext value) := by
  intro value witness
  cases value <;> simp [freeIsContext, freeBackwardContext, freeForwardContext] at witness ⊢

def freeGenerates (generator route : FreePrimitiveAtom) : Prop :=
  generator = generatorWitness ∧ route = routeWitness

def freeWitnessesJoint (product : FreePrimitiveAtom × FreePrimitiveAtom)
    (localFact : FreePrimitiveAtom) : Prop :=
  product = (contextLeft, contextRight) ∧ localFact = localFactLeft

def freePrimitiveGeneratedAdmissibility
    (b0 : B0CandidateBase) :
    PrimitiveGeneratedAdmissibility :=
  {
    Atom := FreePrimitiveAtom,
    b0 := b0,
    primitiveGeneratedScope := groundedChecked True True.intro,
    admissibleContextUniverse := groundedChecked True True.intro,
    isContext := freeIsContext,
    isFact := freeIsFact,
    isBlock := freeIsBlock,
    isRoute := freeIsRoute,
    isRefinement := freeIsRefinement,
    isState := freeIsState,
    isGenerator := freeIsGenerator,
    isLocalFact := freeIsLocalFact,
    contextLeft := contextLeft,
    contextRight := contextRight,
    contextThird := contextThird,
    contextLeftIsContext := trivial,
    contextRightIsContext := trivial,
    contextThirdIsContext := trivial,
    contextLeftNeRight := by decide,
    contextLeftNeThird := by decide,
    contextRightNeThird := by decide,
    factWitness := factWitness,
    factWitnessIsFact := trivial,
    blockWitness := blockWitness,
    blockWitnessIsBlock := trivial,
    blockedBlockWitness := blockedBlock,
    blockedBlockWitnessIsBlock := trivial,
    exposedIn := freeExposedIn,
    exposedWitness := rfl,
    exposureBoundary := (by
      intro exposure
      cases exposure),
    routeWitness := routeWitness,
    routeWitnessIsRoute := trivial,
    forwardContext := freeForwardContext,
    backwardContext := freeBackwardContext,
    forwardContextClosed := freeForwardContextClosed,
    backwardContextClosed := freeBackwardContextClosed,
    roundTripLeft := rfl,
    roundTripRight := rfl,
    nontrivialForward := rfl,
    refinementWitness := refinementWitness,
    refinementWitnessIsRefinement := trivial,
    stateLeft := stateLeft,
    stateRight := stateRight,
    stateLeftIsState := trivial,
    stateRightIsState := trivial,
    stateLeftNeRight := by decide,
    compactBound := 1,
    compactBoundPositive := by decide,
    generatorWitness := generatorWitness,
    generatorWitnessIsGenerator := trivial,
    generatorBoundaryWitness := generatorBoundary,
    generatorBoundaryWitnessIsGenerator := trivial,
    routeBoundaryWitness := routeBoundary,
    routeBoundaryWitnessIsRoute := trivial,
    generates := freeGenerates,
    generationWitness := And.intro rfl rfl,
    generationBoundary := (by
      intro generation
      cases generation.left),
    localFactLeft := localFactLeft,
    localFactRight := localFactRight,
    localFactThird := localFactThird,
    localFactLeftIsLocalFact := trivial,
    localFactRightIsLocalFact := trivial,
    localFactThirdIsLocalFact := trivial,
    localFactLeftNeRight := by decide,
    localFactLeftNeThird := by decide,
    localFactRightNeThird := by decide,
    witnessesJoint := freeWitnessesJoint,
    witnessedJointFact := And.intro rfl rfl,
    witnessBoundary := (by
      intro witness
      cases witness.right)
  }

theorem b0_alone_admits_free_primitive_generated_admissibility
    (b0 : B0CandidateBase) :
    Nonempty PrimitiveGeneratedAdmissibility :=
  ⟨freePrimitiveGeneratedAdmissibility b0⟩

theorem b0_alone_can_feed_free_primitive_generated_source_kernel
    (b0 : B0CandidateBase) :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))) :=
  primitive_generated_admissibility_yields_full_qm_obligation_bundle
    (freePrimitiveGeneratedAdmissibility b0)

theorem free_primitive_generated_admissibility_keeps_import_guards
    (b0 : B0CandidateBase) :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
      (universalPrimitiveSourceKernelToGrounded
        (primitiveGeneratedUniversalSourceKernel
          (freePrimitiveGeneratedAdmissibility b0)))).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel
            (freePrimitiveGeneratedAdmissibility b0)))).compositeClosure.noHilbertImport.statement :=
  primitive_generated_admissibility_yields_import_guards
    (freePrimitiveGeneratedAdmissibility b0)

end QMClosure
end IDT
