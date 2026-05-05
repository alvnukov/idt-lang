import Proofs.QMClosure.UniversalPrimitiveToyWall

namespace IDT
namespace QMClosure

def subtypeNe {alpha : Type} {predicate : alpha → Prop}
    {left right : alpha}
    {leftProof : predicate left}
    {rightProof : predicate right}
    (notEqual : left ≠ right) :
    (⟨left, leftProof⟩ : { value : alpha // predicate value }) ≠
      ⟨right, rightProof⟩ :=
  fun equality => notEqual (congrArg Subtype.val equality)

structure PrimitiveGeneratedAdmissibility where
  Atom : Type
  b0 : B0CandidateBase
  primitiveGeneratedScope : CheckedProp
  admissibleContextUniverse : CheckedProp
  isContext : Atom → Prop
  isFact : Atom → Prop
  isBlock : Atom → Prop
  isRoute : Atom → Prop
  isRefinement : Atom → Prop
  isState : Atom → Prop
  isGenerator : Atom → Prop
  isLocalFact : Atom → Prop
  contextLeft : Atom
  contextRight : Atom
  contextThird : Atom
  contextLeftIsContext : isContext contextLeft
  contextRightIsContext : isContext contextRight
  contextThirdIsContext : isContext contextThird
  contextLeftNeRight : contextLeft ≠ contextRight
  contextLeftNeThird : contextLeft ≠ contextThird
  contextRightNeThird : contextRight ≠ contextThird
  factWitness : Atom
  factWitnessIsFact : isFact factWitness
  blockWitness : Atom
  blockWitnessIsBlock : isBlock blockWitness
  blockedBlockWitness : Atom
  blockedBlockWitnessIsBlock : isBlock blockedBlockWitness
  exposedIn : Atom → Atom → Prop
  exposedWitness : exposedIn blockWitness contextLeft
  exposureBoundary : ¬ exposedIn blockedBlockWitness contextLeft
  routeWitness : Atom
  routeWitnessIsRoute : isRoute routeWitness
  forwardContext : Atom → Atom
  backwardContext : Atom → Atom
  forwardContextClosed : ∀ value : Atom, isContext value → isContext (forwardContext value)
  backwardContextClosed : ∀ value : Atom, isContext value → isContext (backwardContext value)
  roundTripLeft : backwardContext (forwardContext contextLeft) = contextLeft
  roundTripRight : forwardContext (backwardContext contextRight) = contextRight
  nontrivialForward : forwardContext contextLeft = contextRight
  refinementWitness : Atom
  refinementWitnessIsRefinement : isRefinement refinementWitness
  stateLeft : Atom
  stateRight : Atom
  stateLeftIsState : isState stateLeft
  stateRightIsState : isState stateRight
  stateLeftNeRight : stateLeft ≠ stateRight
  compactBound : Nat
  compactBoundPositive : compactBound > 0
  generatorWitness : Atom
  generatorWitnessIsGenerator : isGenerator generatorWitness
  generatorBoundaryWitness : Atom
  generatorBoundaryWitnessIsGenerator : isGenerator generatorBoundaryWitness
  routeBoundaryWitness : Atom
  routeBoundaryWitnessIsRoute : isRoute routeBoundaryWitness
  generates : Atom → Atom → Prop
  generationWitness : generates generatorWitness routeWitness
  generationBoundary : ¬ generates generatorBoundaryWitness routeBoundaryWitness
  localFactLeft : Atom
  localFactRight : Atom
  localFactThird : Atom
  localFactLeftIsLocalFact : isLocalFact localFactLeft
  localFactRightIsLocalFact : isLocalFact localFactRight
  localFactThirdIsLocalFact : isLocalFact localFactThird
  localFactLeftNeRight : localFactLeft ≠ localFactRight
  localFactLeftNeThird : localFactLeft ≠ localFactThird
  localFactRightNeThird : localFactRight ≠ localFactThird
  witnessesJoint : Atom × Atom → Atom → Prop
  witnessedJointFact : witnessesJoint (contextLeft, contextRight) localFactLeft
  witnessBoundary : ¬ witnessesJoint (contextLeft, contextRight) localFactRight

abbrev PrimitiveGeneratedAdmissibility.Context
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isContext value }

abbrev PrimitiveGeneratedAdmissibility.Fact
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isFact value }

abbrev PrimitiveGeneratedAdmissibility.Block
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isBlock value }

abbrev PrimitiveGeneratedAdmissibility.Route
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isRoute value }

abbrev PrimitiveGeneratedAdmissibility.Refinement
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isRefinement value }

abbrev PrimitiveGeneratedAdmissibility.State
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isState value }

abbrev PrimitiveGeneratedAdmissibility.Generator
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isGenerator value }

abbrev PrimitiveGeneratedAdmissibility.LocalFact
    (admissibility : PrimitiveGeneratedAdmissibility) : Type :=
  { value : admissibility.Atom // admissibility.isLocalFact value }

def primitiveContextLeft
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Context :=
  ⟨admissibility.contextLeft, admissibility.contextLeftIsContext⟩

def primitiveContextRight
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Context :=
  ⟨admissibility.contextRight, admissibility.contextRightIsContext⟩

def primitiveContextThird
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Context :=
  ⟨admissibility.contextThird, admissibility.contextThirdIsContext⟩

def primitiveContextPair
    (admissibility : PrimitiveGeneratedAdmissibility) :
    DistinctPair admissibility.Context :=
  {
    left := primitiveContextLeft admissibility,
    right := primitiveContextRight admissibility,
    distinct := subtypeNe admissibility.contextLeftNeRight
  }

def primitiveContextRank
    (admissibility : PrimitiveGeneratedAdmissibility) :
    AtLeastThree admissibility.Context :=
  ⟨primitiveContextLeft admissibility,
    primitiveContextRight admissibility,
    primitiveContextThird admissibility,
    subtypeNe admissibility.contextLeftNeRight,
    subtypeNe admissibility.contextLeftNeThird,
    subtypeNe admissibility.contextRightNeThird⟩

def primitiveLocalFactLeft
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.LocalFact :=
  ⟨admissibility.localFactLeft, admissibility.localFactLeftIsLocalFact⟩

def primitiveLocalFactRight
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.LocalFact :=
  ⟨admissibility.localFactRight, admissibility.localFactRightIsLocalFact⟩

def primitiveLocalFactThird
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.LocalFact :=
  ⟨admissibility.localFactThird, admissibility.localFactThirdIsLocalFact⟩

def primitiveLocalFactPair
    (admissibility : PrimitiveGeneratedAdmissibility) :
    DistinctPair admissibility.LocalFact :=
  {
    left := primitiveLocalFactLeft admissibility,
    right := primitiveLocalFactRight admissibility,
    distinct := subtypeNe admissibility.localFactLeftNeRight
  }

def primitiveLocalFactRank
    (admissibility : PrimitiveGeneratedAdmissibility) :
    AtLeastThree admissibility.LocalFact :=
  ⟨primitiveLocalFactLeft admissibility,
    primitiveLocalFactRight admissibility,
    primitiveLocalFactThird admissibility,
    subtypeNe admissibility.localFactLeftNeRight,
    subtypeNe admissibility.localFactLeftNeThird,
    subtypeNe admissibility.localFactRightNeThird⟩

def primitiveBlockWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Block :=
  ⟨admissibility.blockWitness, admissibility.blockWitnessIsBlock⟩

def primitiveBlockedBlockWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Block :=
  ⟨admissibility.blockedBlockWitness, admissibility.blockedBlockWitnessIsBlock⟩

def primitiveFactWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Fact :=
  ⟨admissibility.factWitness, admissibility.factWitnessIsFact⟩

def primitiveExposedIn
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Block → admissibility.Context → Prop :=
  fun block context => admissibility.exposedIn block.val context.val

def primitiveCompleteExposedContextPartitionGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    CompleteExposedContextPartitionGround :=
  {
    Context := admissibility.Context,
    Fact := admissibility.Fact,
    Block := admissibility.Block,
    contexts := primitiveContextPair admissibility,
    factWitness := primitiveFactWitness admissibility,
    blockOf := fun _ => primitiveBlockWitness admissibility,
    exposedIn := primitiveExposedIn admissibility,
    exposedWitness := admissibility.exposedWitness,
    exposureBoundary := by
      exact ⟨primitiveBlockedBlockWitness admissibility,
        primitiveContextLeft admissibility,
        admissibility.exposureBoundary⟩
  }

def primitiveRouteWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Route :=
  ⟨admissibility.routeWitness, admissibility.routeWitnessIsRoute⟩

def primitiveForwardContext
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Context → admissibility.Context :=
  fun context =>
    ⟨admissibility.forwardContext context.val,
      admissibility.forwardContextClosed context.val context.property⟩

def primitiveBackwardContext
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Context → admissibility.Context :=
  fun context =>
    ⟨admissibility.backwardContext context.val,
      admissibility.backwardContextClosed context.val context.property⟩

def primitiveReversibleContextAutomorphismClosureGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    ReversibleContextAutomorphismClosureGround :=
  {
    Context := admissibility.Context,
    Route := admissibility.Route,
    contexts := primitiveContextPair admissibility,
    routeWitness := primitiveRouteWitness admissibility,
    forward := primitiveForwardContext admissibility,
    backward := primitiveBackwardContext admissibility,
    roundTripLeft := by
      apply Subtype.ext
      exact admissibility.roundTripLeft,
    roundTripRight := by
      apply Subtype.ext
      exact admissibility.roundTripRight,
    nontrivialForward := by
      apply Subtype.ext
      exact admissibility.nontrivialForward
  }

def primitiveRefinementWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Refinement :=
  ⟨admissibility.refinementWitness, admissibility.refinementWitnessIsRefinement⟩

def primitiveStateLeft
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.State :=
  ⟨admissibility.stateLeft, admissibility.stateLeftIsState⟩

def primitiveStateRight
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.State :=
  ⟨admissibility.stateRight, admissibility.stateRightIsState⟩

def primitiveStatePair
    (admissibility : PrimitiveGeneratedAdmissibility) :
    DistinctPair admissibility.State :=
  {
    left := primitiveStateLeft admissibility,
    right := primitiveStateRight admissibility,
    distinct := subtypeNe admissibility.stateLeftNeRight
  }

def primitiveCoherentRefinementCompactnessGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    CoherentRefinementCompactnessGround :=
  {
    Refinement := admissibility.Refinement,
    State := admissibility.State,
    refinementWitness := primitiveRefinementWitness admissibility,
    states := primitiveStatePair admissibility,
    compactBound := admissibility.compactBound,
    compactBoundPositive := admissibility.compactBoundPositive
  }

def primitiveGeneratorWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Generator :=
  ⟨admissibility.generatorWitness, admissibility.generatorWitnessIsGenerator⟩

def primitiveGeneratorBoundaryWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Generator :=
  ⟨admissibility.generatorBoundaryWitness,
    admissibility.generatorBoundaryWitnessIsGenerator⟩

def primitiveRouteBoundaryWitness
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Route :=
  ⟨admissibility.routeBoundaryWitness, admissibility.routeBoundaryWitnessIsRoute⟩

def primitiveGenerates
    (admissibility : PrimitiveGeneratedAdmissibility) :
    admissibility.Generator → admissibility.Route → Prop :=
  fun generator route => admissibility.generates generator.val route.val

def primitiveGeneratorBookkeepingWithoutStoneGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    GeneratorBookkeepingWithoutStoneGround :=
  {
    Generator := admissibility.Generator,
    Route := admissibility.Route,
    generatorWitness := primitiveGeneratorWitness admissibility,
    routeWitness := primitiveRouteWitness admissibility,
    generates := primitiveGenerates admissibility,
    generationWitness := admissibility.generationWitness,
    generationBoundary := by
      exact ⟨primitiveGeneratorBoundaryWitness admissibility,
        primitiveRouteBoundaryWitness admissibility,
        admissibility.generationBoundary⟩
  }

def primitiveProductContextGenerationClosureGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    ProductContextGenerationClosureGround :=
  {
    LocalContext := admissibility.Context,
    ProductContext := admissibility.Context × admissibility.Context,
    localContexts := primitiveContextPair admissibility,
    productWitness := (primitiveContextLeft admissibility, primitiveContextRight admissibility),
    productOf := fun left right => (left, right),
    productWitnessMatches := rfl,
    productOrderBoundary := by
      intro equality
      exact (primitiveContextPair admissibility).distinct
        (Prod.ext_iff.mp equality).left
  }

def primitiveWitnessesJoint
    (admissibility : PrimitiveGeneratedAdmissibility) :
    (admissibility.Context × admissibility.Context) →
      admissibility.LocalFact → Prop :=
  fun product localFact =>
    admissibility.witnessesJoint (product.fst.val, product.snd.val) localFact.val

def primitiveNoHiddenJointOnlyGenerationGround
    (admissibility : PrimitiveGeneratedAdmissibility) :
    NoHiddenJointOnlyGenerationGround :=
  {
    LocalFact := admissibility.LocalFact,
    JointFact := admissibility.LocalFact,
    ProductWitness := admissibility.Context × admissibility.Context,
    localFacts := primitiveLocalFactPair admissibility,
    jointFactWitness := primitiveLocalFactLeft admissibility,
    productWitness := (primitiveContextLeft admissibility, primitiveContextRight admissibility),
    witnesses := primitiveWitnessesJoint admissibility,
    witnessedJointFact := admissibility.witnessedJointFact,
    witnessBoundary := by
      exact ⟨(primitiveContextLeft admissibility, primitiveContextRight admissibility),
        primitiveLocalFactRight admissibility,
        admissibility.witnessBoundary⟩
  }

def primitiveGeneratedGroundedSemanticExtensionBase
    (admissibility : PrimitiveGeneratedAdmissibility) :
    GroundedCGSCSemanticExtensionBase :=
  {
    b0 := admissibility.b0,
    exposed := primitiveCompleteExposedContextPartitionGround admissibility,
    reversible := primitiveReversibleContextAutomorphismClosureGround admissibility,
    refinement := primitiveCoherentRefinementCompactnessGround admissibility,
    generator := primitiveGeneratorBookkeepingWithoutStoneGround admissibility,
    product := primitiveProductContextGenerationClosureGround admissibility,
    noHiddenJoint := primitiveNoHiddenJointOnlyGenerationGround admissibility
  }

def primitiveGeneratedUniversalSourceKernel
    (admissibility : PrimitiveGeneratedAdmissibility) :
    UniversalPrimitiveSourceKernel :=
  {
    grounded := primitiveGeneratedGroundedSemanticExtensionBase admissibility,
    primitiveGeneratedScope := admissibility.primitiveGeneratedScope,
    admissibleContextUniverse := admissibility.admissibleContextUniverse,
    exposedContextRank := primitiveContextRank admissibility,
    reversibleContextRank := primitiveContextRank admissibility,
    localProductContextRank := primitiveContextRank admissibility,
    localFactRank := primitiveLocalFactRank admissibility
  }

theorem primitive_generated_admissibility_yields_full_qm_obligation_bundle
    (admissibility : PrimitiveGeneratedAdmissibility) :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))) :=
  universal_primitive_source_kernel_yields_full_qm_obligation_bundle
    (primitiveGeneratedUniversalSourceKernel admissibility)

theorem primitive_generated_admissibility_yields_import_guards
    (admissibility : PrimitiveGeneratedAdmissibility) :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
      (universalPrimitiveSourceKernelToGrounded
        (primitiveGeneratedUniversalSourceKernel admissibility))).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (primitiveGeneratedUniversalSourceKernel admissibility))).compositeClosure.noHilbertImport.statement :=
  universal_primitive_source_kernel_yields_import_guards
    (primitiveGeneratedUniversalSourceKernel admissibility)

theorem primitive_generated_source_slots_share_one_atom_universe
    (admissibility : PrimitiveGeneratedAdmissibility) :
    (primitiveGeneratedGroundedSemanticExtensionBase admissibility).exposed.Context =
        admissibility.Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase admissibility).reversible.Context =
        admissibility.Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase admissibility).product.LocalContext =
        admissibility.Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase admissibility).noHiddenJoint.LocalFact =
        admissibility.LocalFact :=
  And.intro rfl (And.intro rfl (And.intro rfl rfl))

end QMClosure
end IDT
