import Proofs.QMClosure.CGSCTypedSemanticExtensions

namespace IDT
namespace QMClosure

def groundedChecked (source : Prop) (proof : source) : CheckedProp :=
  {
    statement := source,
    proof := proof
  }

structure CompleteExposedContextPartitionGround where
  Context : Type
  Fact : Type
  Block : Type
  contexts : DistinctPair Context
  factWitness : Fact
  blockOf : Fact → Block
  exposedIn : Block → Context → Prop
  exposedWitness : exposedIn (blockOf factWitness) contexts.left
  exposureBoundary : ∃ block : Block, ∃ context : Context, ¬ exposedIn block context

def completeExposedSource
    (ground : CompleteExposedContextPartitionGround) : Prop :=
  ground.exposedIn (ground.blockOf ground.factWitness) ground.contexts.left
    ∧ ∃ block : ground.Block, ∃ context : ground.Context,
      ¬ ground.exposedIn block context

def completeExposedSourceProof
    (ground : CompleteExposedContextPartitionGround) :
    completeExposedSource ground :=
  And.intro ground.exposedWitness ground.exposureBoundary

def completeExposedExtensionFromGround
    (ground : CompleteExposedContextPartitionGround) :
    CompleteExposedContextPartitionExtension :=
  let checked := groundedChecked
    (completeExposedSource ground)
    (completeExposedSourceProof ground)
  {
    completeExposedContextPartition := checked,
    finiteProjectionDeterminacy := checked,
    projectiveConsistency := checked,
    nonunitalStableDistinguishability := checked,
    conservativeProjectiveGluing := checked,
    spectralDecomposition := checked,
    contextNormalization := checked,
    exclusivityAdditivity := checked,
    coarseGrainingConsistency := checked,
    operationalEquivalenceProbability := checked,
    physicalPhaseScaleBoundary := checked
  }

def completeExposedSemanticFromGround
    (ground : CompleteExposedContextPartitionGround) :
    CompleteExposedContextPartitionSemantic :=
  {
    Context := ground.Context,
    Fact := ground.Fact,
    Block := ground.Block,
    contexts := ground.contexts,
    factWitness := ground.factWitness,
    blockOf := ground.blockOf,
    exposedIn := ground.exposedIn,
    exposedWitness := ground.exposedWitness,
    extension := completeExposedExtensionFromGround ground
  }

structure ReversibleContextAutomorphismClosureGround where
  Context : Type
  Route : Type
  contexts : DistinctPair Context
  routeWitness : Route
  forward : Context → Context
  backward : Context → Context
  roundTripLeft : backward (forward contexts.left) = contexts.left
  roundTripRight : forward (backward contexts.right) = contexts.right
  nontrivialForward : forward contexts.left = contexts.right

def reversibleSource
    (ground : ReversibleContextAutomorphismClosureGround) : Prop :=
  ground.backward (ground.forward ground.contexts.left) = ground.contexts.left
    ∧ ground.forward (ground.backward ground.contexts.right) = ground.contexts.right
    ∧ ground.forward ground.contexts.left = ground.contexts.right
    ∧ ground.contexts.left ≠ ground.contexts.right

def reversibleSourceProof
    (ground : ReversibleContextAutomorphismClosureGround) :
    reversibleSource ground :=
  And.intro
    ground.roundTripLeft
    (And.intro
      ground.roundTripRight
      (And.intro ground.nontrivialForward ground.contexts.distinct))

def reversibleExtensionFromGround
    (ground : ReversibleContextAutomorphismClosureGround) :
    ReversibleContextAutomorphismClosureExtension :=
  let checked := groundedChecked (reversibleSource ground) (reversibleSourceProof ground)
  {
    reversibleContextAutomorphismClosure := checked,
    richDclReversibleSymmetry := checked,
    dclAutomorphismDynamics := checked,
    overlapPreservationDynamics := checked,
    projectiveAction := checked
  }

def reversibleSemanticFromGround
    (ground : ReversibleContextAutomorphismClosureGround) :
    ReversibleContextAutomorphismClosureSemantic :=
  {
    Context := ground.Context,
    Route := ground.Route,
    contexts := ground.contexts,
    routeWitness := ground.routeWitness,
    forward := ground.forward,
    backward := ground.backward,
    roundTripLeft := ground.roundTripLeft,
    roundTripRight := ground.roundTripRight,
    extension := reversibleExtensionFromGround ground
  }

structure CoherentRefinementCompactnessGround where
  Refinement : Type
  State : Type
  refinementWitness : Refinement
  states : DistinctPair State
  compactBound : Nat
  compactBoundPositive : compactBound > 0

def refinementSource
    (ground : CoherentRefinementCompactnessGround) : Prop :=
  ground.states.left ≠ ground.states.right ∧ ground.compactBound > 0

def refinementSourceProof
    (ground : CoherentRefinementCompactnessGround) :
    refinementSource ground :=
  And.intro ground.states.distinct ground.compactBoundPositive

def refinementExtensionFromGround
    (ground : CoherentRefinementCompactnessGround) :
    CoherentRefinementCompactnessExtension :=
  let checked := groundedChecked (refinementSource ground) (refinementSourceProof ground)
  {
    coherentRefinementCompactness := checked,
    continuousInheritanceFamily := checked
  }

def refinementSemanticFromGround
    (ground : CoherentRefinementCompactnessGround) :
    CoherentRefinementCompactnessSemantic :=
  {
    Refinement := ground.Refinement,
    State := ground.State,
    refinementWitness := ground.refinementWitness,
    states := ground.states,
    compactBound := ground.compactBound,
    compactBoundPositive := ground.compactBoundPositive,
    extension := refinementExtensionFromGround ground
  }

structure GeneratorBookkeepingWithoutStoneGround where
  Generator : Type
  Route : Type
  generatorWitness : Generator
  routeWitness : Route
  generates : Generator → Route → Prop
  generationWitness : generates generatorWitness routeWitness
  generationBoundary : ∃ generator : Generator, ∃ route : Route, ¬ generates generator route

def generatorSource
    (ground : GeneratorBookkeepingWithoutStoneGround) : Prop :=
  ground.generates ground.generatorWitness ground.routeWitness
    ∧ ∃ generator : ground.Generator, ∃ route : ground.Route,
      ¬ ground.generates generator route

def generatorSourceProof
    (ground : GeneratorBookkeepingWithoutStoneGround) :
    generatorSource ground :=
  And.intro ground.generationWitness ground.generationBoundary

def generatorExtensionFromGround
    (ground : GeneratorBookkeepingWithoutStoneGround) :
    GeneratorBookkeepingWithoutStoneExtension :=
  let checked := groundedChecked (generatorSource ground) (generatorSourceProof ground)
  {
    generatorBookkeepingWithoutStone := checked,
    generatorClosure := checked
  }

def generatorSemanticFromGround
    (ground : GeneratorBookkeepingWithoutStoneGround) :
    GeneratorBookkeepingWithoutStoneSemantic :=
  {
    Generator := ground.Generator,
    Route := ground.Route,
    generatorWitness := ground.generatorWitness,
    routeWitness := ground.routeWitness,
    generates := ground.generates,
    generationWitness := ground.generationWitness,
    extension := generatorExtensionFromGround ground
  }

structure ProductContextGenerationClosureGround where
  LocalContext : Type
  ProductContext : Type
  localContexts : DistinctPair LocalContext
  productWitness : ProductContext
  productOf : LocalContext → LocalContext → ProductContext
  productWitnessMatches :
    productOf localContexts.left localContexts.right = productWitness
  productOrderBoundary :
    productOf localContexts.left localContexts.right ≠
      productOf localContexts.right localContexts.left

def productSource
    (ground : ProductContextGenerationClosureGround) : Prop :=
  ground.localContexts.left ≠ ground.localContexts.right
    ∧ ground.productOf ground.localContexts.left ground.localContexts.right =
      ground.productWitness
    ∧ ground.productOf ground.localContexts.left ground.localContexts.right ≠
      ground.productOf ground.localContexts.right ground.localContexts.left

def productSourceProof
    (ground : ProductContextGenerationClosureGround) :
    productSource ground :=
  And.intro
    ground.localContexts.distinct
    (And.intro ground.productWitnessMatches ground.productOrderBoundary)

def productExtensionFromGround
    (ground : ProductContextGenerationClosureGround) :
    ProductContextGenerationClosureExtension :=
  let checked := groundedChecked (productSource ground) (productSourceProof ground)
  {
    productContextGenerationClosure := checked,
    productContextExhaustion := checked,
    localTomography := checked,
    monoidalAssociativity := checked,
    entanglementClosure := checked,
    projectiveLimitConsistency := checked
  }

def productSemanticFromGround
    (ground : ProductContextGenerationClosureGround) :
    ProductContextGenerationClosureSemantic :=
  {
    LocalContext := ground.LocalContext,
    ProductContext := ground.ProductContext,
    localContexts := ground.localContexts,
    productWitness := ground.productWitness,
    productOf := ground.productOf,
    productWitnessMatches := ground.productWitnessMatches,
    extension := productExtensionFromGround ground
  }

structure NoHiddenJointOnlyGenerationGround where
  LocalFact : Type
  JointFact : Type
  ProductWitness : Type
  localFacts : DistinctPair LocalFact
  jointFactWitness : JointFact
  productWitness : ProductWitness
  witnesses : ProductWitness → JointFact → Prop
  witnessedJointFact : witnesses productWitness jointFactWitness
  witnessBoundary :
    ∃ product : ProductWitness, ∃ joint : JointFact, ¬ witnesses product joint

def noHiddenJointSource
    (ground : NoHiddenJointOnlyGenerationGround) : Prop :=
  ground.localFacts.left ≠ ground.localFacts.right
    ∧ ground.witnesses ground.productWitness ground.jointFactWitness
    ∧ ∃ product : ground.ProductWitness, ∃ joint : ground.JointFact,
      ¬ ground.witnesses product joint

def noHiddenJointSourceProof
    (ground : NoHiddenJointOnlyGenerationGround) :
    noHiddenJointSource ground :=
  And.intro
    ground.localFacts.distinct
    (And.intro ground.witnessedJointFact ground.witnessBoundary)

def noHiddenJointExtensionFromGround
    (ground : NoHiddenJointOnlyGenerationGround) :
    NoHiddenJointOnlyGenerationExtension :=
  let checked := groundedChecked (noHiddenJointSource ground) (noHiddenJointSourceProof ground)
  {
    noHiddenJointOnlyGenerationExtension := checked,
    constructiveCarrierWitness := checked,
    noHiddenJointOnlyGeneration := checked
  }

def noHiddenJointSemanticFromGround
    (ground : NoHiddenJointOnlyGenerationGround) :
    NoHiddenJointOnlyGenerationSemantic :=
  {
    LocalFact := ground.LocalFact,
    JointFact := ground.JointFact,
    ProductWitness := ground.ProductWitness,
    localFacts := ground.localFacts,
    jointFactWitness := ground.jointFactWitness,
    productWitness := ground.productWitness,
    witnesses := ground.witnesses,
    witnessedJointFact := ground.witnessedJointFact,
    extension := noHiddenJointExtensionFromGround ground
  }

structure GroundedCGSCSemanticExtensionBase where
  b0 : B0CandidateBase
  exposed : CompleteExposedContextPartitionGround
  reversible : ReversibleContextAutomorphismClosureGround
  refinement : CoherentRefinementCompactnessGround
  generator : GeneratorBookkeepingWithoutStoneGround
  product : ProductContextGenerationClosureGround
  noHiddenJoint : NoHiddenJointOnlyGenerationGround

def groundedSemanticExtensionBaseToTyped
    (base : GroundedCGSCSemanticExtensionBase) :
    TypedCGSCSemanticExtensionBase :=
  {
    b0 := base.b0,
    exposed := completeExposedSemanticFromGround base.exposed,
    reversible := reversibleSemanticFromGround base.reversible,
    refinement := refinementSemanticFromGround base.refinement,
    generator := generatorSemanticFromGround base.generator,
    product := productSemanticFromGround base.product,
    noHiddenJoint := noHiddenJointSemanticFromGround base.noHiddenJoint
  }

def groundedSemanticExtensionBaseToCGSCPackageClosure
    (base : GroundedCGSCSemanticExtensionBase) :
    CGSCPackageClosure :=
  typedSemanticExtensionBaseToCGSCPackageClosure
    (groundedSemanticExtensionBaseToTyped base)

theorem grounded_semantic_extension_base_yields_six_extension_statements
    (base : GroundedCGSCSemanticExtensionBase) :
    (completeExposedSource base.exposed)
      ∧ (reversibleSource base.reversible)
      ∧ (refinementSource base.refinement)
      ∧ (generatorSource base.generator)
      ∧ (productSource base.product)
      ∧ (noHiddenJointSource base.noHiddenJoint)
      ∧ (groundedSemanticExtensionBaseToTyped base).exposed.extension.completeExposedContextPartition.statement
      ∧ (groundedSemanticExtensionBaseToTyped base).reversible.extension.reversibleContextAutomorphismClosure.statement
      ∧ (groundedSemanticExtensionBaseToTyped base).refinement.extension.coherentRefinementCompactness.statement
      ∧ (groundedSemanticExtensionBaseToTyped base).generator.extension.generatorBookkeepingWithoutStone.statement
      ∧ (groundedSemanticExtensionBaseToTyped base).product.extension.productContextGenerationClosure.statement
      ∧ (groundedSemanticExtensionBaseToTyped base).noHiddenJoint.extension.noHiddenJointOnlyGenerationExtension.statement :=
  And.intro
    (completeExposedSourceProof base.exposed)
    (And.intro
      (reversibleSourceProof base.reversible)
      (And.intro
        (refinementSourceProof base.refinement)
        (And.intro
          (generatorSourceProof base.generator)
          (And.intro
            (productSourceProof base.product)
            (And.intro
              (noHiddenJointSourceProof base.noHiddenJoint)
              (typed_semantic_extension_base_yields_six_extension_statements
                (groundedSemanticExtensionBaseToTyped base)))))))

theorem grounded_semantic_extension_base_blocks_decorative_relations
    (base : GroundedCGSCSemanticExtensionBase) :
    (∃ block : base.exposed.Block, ∃ context : base.exposed.Context,
      ¬ base.exposed.exposedIn block context)
      ∧ (∃ generator : base.generator.Generator, ∃ route : base.generator.Route,
        ¬ base.generator.generates generator route)
      ∧ (∃ product : base.noHiddenJoint.ProductWitness,
        ∃ joint : base.noHiddenJoint.JointFact,
          ¬ base.noHiddenJoint.witnesses product joint) :=
  And.intro
    base.exposed.exposureBoundary
    (And.intro base.generator.generationBoundary base.noHiddenJoint.witnessBoundary)

theorem grounded_semantic_extension_base_yields_package_import_guards
    (base : GroundedCGSCSemanticExtensionBase) :
    (groundedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noHilbertImport.statement :=
  typed_semantic_extension_base_yields_package_import_guards
    (groundedSemanticExtensionBaseToTyped base)

/-!
Claim-source aliasing boundary.

The grounded extension constructors intentionally reuse a small ground witness
to populate larger package slots.  That is useful for migration scaffolding, but
it is not a semantic proof that every slot has been independently derived.  The
equalities below make this boundary explicit: a package field can currently be
Lean-checked because it shares the same source proposition, not because the
field name itself has been reconstructed from primitives.
-/

def CompleteExposedExtensionClaimSourceAliasing
    (ground : CompleteExposedContextPartitionGround) : Prop :=
  let extension := completeExposedExtensionFromGround ground
  extension.completeExposedContextPartition.statement =
      extension.spectralDecomposition.statement
    ∧ extension.completeExposedContextPartition.statement =
      extension.contextNormalization.statement
    ∧ extension.completeExposedContextPartition.statement =
      extension.operationalEquivalenceProbability.statement
    ∧ extension.completeExposedContextPartition.statement =
      extension.physicalPhaseScaleBoundary.statement

theorem complete_exposed_extension_claim_source_aliasing
    (ground : CompleteExposedContextPartitionGround) :
    CompleteExposedExtensionClaimSourceAliasing ground := by
  simp [
    CompleteExposedExtensionClaimSourceAliasing,
    completeExposedExtensionFromGround,
    groundedChecked,
  ]

def ReversibleExtensionClaimSourceAliasing
    (ground : ReversibleContextAutomorphismClosureGround) : Prop :=
  let extension := reversibleExtensionFromGround ground
  extension.reversibleContextAutomorphismClosure.statement =
      extension.richDclReversibleSymmetry.statement
    ∧ extension.reversibleContextAutomorphismClosure.statement =
      extension.dclAutomorphismDynamics.statement
    ∧ extension.reversibleContextAutomorphismClosure.statement =
      extension.overlapPreservationDynamics.statement
    ∧ extension.reversibleContextAutomorphismClosure.statement =
      extension.projectiveAction.statement

theorem reversible_extension_claim_source_aliasing
    (ground : ReversibleContextAutomorphismClosureGround) :
    ReversibleExtensionClaimSourceAliasing ground := by
  simp [
    ReversibleExtensionClaimSourceAliasing,
    reversibleExtensionFromGround,
    groundedChecked,
  ]

def ProductExtensionClaimSourceAliasing
    (ground : ProductContextGenerationClosureGround) : Prop :=
  let extension := productExtensionFromGround ground
  extension.productContextGenerationClosure.statement =
      extension.productContextExhaustion.statement
    ∧ extension.productContextGenerationClosure.statement =
      extension.localTomography.statement
    ∧ extension.productContextGenerationClosure.statement =
      extension.monoidalAssociativity.statement
    ∧ extension.productContextGenerationClosure.statement =
      extension.entanglementClosure.statement
    ∧ extension.productContextGenerationClosure.statement =
      extension.projectiveLimitConsistency.statement

theorem product_extension_claim_source_aliasing
    (ground : ProductContextGenerationClosureGround) :
    ProductExtensionClaimSourceAliasing ground := by
  simp [
    ProductExtensionClaimSourceAliasing,
    productExtensionFromGround,
    groundedChecked,
  ]

def NoHiddenJointExtensionClaimSourceAliasing
    (ground : NoHiddenJointOnlyGenerationGround) : Prop :=
  let extension := noHiddenJointExtensionFromGround ground
  extension.noHiddenJointOnlyGenerationExtension.statement =
      extension.constructiveCarrierWitness.statement
    ∧ extension.noHiddenJointOnlyGenerationExtension.statement =
      extension.noHiddenJointOnlyGeneration.statement

theorem no_hidden_joint_extension_claim_source_aliasing
    (ground : NoHiddenJointOnlyGenerationGround) :
    NoHiddenJointExtensionClaimSourceAliasing ground := by
  simp [
    NoHiddenJointExtensionClaimSourceAliasing,
    noHiddenJointExtensionFromGround,
    groundedChecked,
  ]

def GroundedCGSCClaimSourceAliasing
    (base : GroundedCGSCSemanticExtensionBase) : Prop :=
  CompleteExposedExtensionClaimSourceAliasing base.exposed
    ∧ ReversibleExtensionClaimSourceAliasing base.reversible
    ∧ ProductExtensionClaimSourceAliasing base.product
    ∧ NoHiddenJointExtensionClaimSourceAliasing base.noHiddenJoint

theorem grounded_cgsc_claim_source_aliasing_boundary
    (base : GroundedCGSCSemanticExtensionBase) :
    GroundedCGSCClaimSourceAliasing base := by
  exact And.intro
    (complete_exposed_extension_claim_source_aliasing base.exposed)
    (And.intro
      (reversible_extension_claim_source_aliasing base.reversible)
      (And.intro
        (product_extension_claim_source_aliasing base.product)
        (no_hidden_joint_extension_claim_source_aliasing base.noHiddenJoint)))

end QMClosure
end IDT
