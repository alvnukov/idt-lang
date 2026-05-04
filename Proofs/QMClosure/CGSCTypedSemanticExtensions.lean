import Proofs.QMClosure.CGSCPrimitiveBridge

namespace IDT
namespace QMClosure

structure DistinctPair (alpha : Type) where
  left : alpha
  right : alpha
  distinct : left ≠ right

structure CompleteExposedContextPartitionSemantic where
  Context : Type
  Fact : Type
  Block : Type
  contexts : DistinctPair Context
  factWitness : Fact
  blockOf : Fact → Block
  exposedIn : Block → Context → Prop
  exposedWitness : exposedIn (blockOf factWitness) contexts.left
  extension : CompleteExposedContextPartitionExtension

structure ReversibleContextAutomorphismClosureSemantic where
  Context : Type
  Route : Type
  contexts : DistinctPair Context
  routeWitness : Route
  forward : Context → Context
  backward : Context → Context
  roundTripLeft : backward (forward contexts.left) = contexts.left
  roundTripRight : forward (backward contexts.right) = contexts.right
  extension : ReversibleContextAutomorphismClosureExtension

structure CoherentRefinementCompactnessSemantic where
  Refinement : Type
  State : Type
  refinementWitness : Refinement
  states : DistinctPair State
  compactBound : Nat
  compactBoundPositive : compactBound > 0
  extension : CoherentRefinementCompactnessExtension

structure GeneratorBookkeepingWithoutStoneSemantic where
  Generator : Type
  Route : Type
  generatorWitness : Generator
  routeWitness : Route
  generates : Generator → Route → Prop
  generationWitness : generates generatorWitness routeWitness
  extension : GeneratorBookkeepingWithoutStoneExtension

structure ProductContextGenerationClosureSemantic where
  LocalContext : Type
  ProductContext : Type
  localContexts : DistinctPair LocalContext
  productWitness : ProductContext
  productOf : LocalContext → LocalContext → ProductContext
  productWitnessMatches :
    productOf localContexts.left localContexts.right = productWitness
  extension : ProductContextGenerationClosureExtension

structure NoHiddenJointOnlyGenerationSemantic where
  LocalFact : Type
  JointFact : Type
  ProductWitness : Type
  localFacts : DistinctPair LocalFact
  jointFactWitness : JointFact
  productWitness : ProductWitness
  witnesses : ProductWitness → JointFact → Prop
  witnessedJointFact : witnesses productWitness jointFactWitness
  extension : NoHiddenJointOnlyGenerationExtension

structure TypedCGSCSemanticExtensionBase where
  b0 : B0CandidateBase
  exposed : CompleteExposedContextPartitionSemantic
  reversible : ReversibleContextAutomorphismClosureSemantic
  refinement : CoherentRefinementCompactnessSemantic
  generator : GeneratorBookkeepingWithoutStoneSemantic
  product : ProductContextGenerationClosureSemantic
  noHiddenJoint : NoHiddenJointOnlyGenerationSemantic

def typedSemanticExtensionBaseToPrimitiveExtensionBase
    (base : TypedCGSCSemanticExtensionBase) :
    CGSCPrimitiveExtensionBase :=
  {
    b0 := base.b0,
    exposed := base.exposed.extension,
    reversible := base.reversible.extension,
    refinement := base.refinement.extension,
    generator := base.generator.extension,
    product := base.product.extension,
    noHiddenJoint := base.noHiddenJoint.extension
  }

def typedSemanticExtensionBaseToCGSCPackageClosure
    (base : TypedCGSCSemanticExtensionBase) :
    CGSCPackageClosure :=
  cgscPackageClosureFromPrimitiveExtensionBase
    (typedSemanticExtensionBaseToPrimitiveExtensionBase base)

theorem typed_semantic_extension_base_yields_six_extension_statements
    (base : TypedCGSCSemanticExtensionBase) :
    base.exposed.extension.completeExposedContextPartition.statement
      ∧ base.reversible.extension.reversibleContextAutomorphismClosure.statement
      ∧ base.refinement.extension.coherentRefinementCompactness.statement
      ∧ base.generator.extension.generatorBookkeepingWithoutStone.statement
      ∧ base.product.extension.productContextGenerationClosure.statement
      ∧ base.noHiddenJoint.extension.noHiddenJointOnlyGenerationExtension.statement :=
  primitive_extension_base_contains_all_six_extension_witnesses
    (typedSemanticExtensionBaseToPrimitiveExtensionBase base)

theorem typed_semantic_extension_base_has_no_vacuity
    (base : TypedCGSCSemanticExtensionBase) :
    base.exposed.contexts.left ≠ base.exposed.contexts.right
      ∧ base.exposed.exposedIn
        (base.exposed.blockOf base.exposed.factWitness)
        base.exposed.contexts.left
      ∧ base.reversible.contexts.left ≠ base.reversible.contexts.right
      ∧ base.reversible.backward
        (base.reversible.forward base.reversible.contexts.left)
          = base.reversible.contexts.left
      ∧ base.refinement.states.left ≠ base.refinement.states.right
      ∧ base.refinement.compactBound > 0
      ∧ base.generator.generates
        base.generator.generatorWitness
        base.generator.routeWitness
      ∧ base.product.localContexts.left ≠ base.product.localContexts.right
      ∧ base.product.productOf
        base.product.localContexts.left
        base.product.localContexts.right
          = base.product.productWitness
      ∧ base.noHiddenJoint.localFacts.left ≠ base.noHiddenJoint.localFacts.right
      ∧ base.noHiddenJoint.witnesses
        base.noHiddenJoint.productWitness
        base.noHiddenJoint.jointFactWitness :=
  And.intro
    base.exposed.contexts.distinct
    (And.intro
      base.exposed.exposedWitness
      (And.intro
        base.reversible.contexts.distinct
        (And.intro
          base.reversible.roundTripLeft
          (And.intro
            base.refinement.states.distinct
            (And.intro
              base.refinement.compactBoundPositive
              (And.intro
                base.generator.generationWitness
                (And.intro
                  base.product.localContexts.distinct
                  (And.intro
                    base.product.productWitnessMatches
                    (And.intro
                      base.noHiddenJoint.localFacts.distinct
                      base.noHiddenJoint.witnessedJointFact)))))))))

theorem typed_semantic_extension_base_preserves_import_boundary
    (base : TypedCGSCSemanticExtensionBase) :
    base.b0.noHilbertPrimitive.statement
      ∧ base.b0.noBornPrimitive.statement
      ∧ base.b0.noUnitaryPrimitive.statement
      ∧ base.b0.noTensorPrimitive.statement
      ∧ base.b0.noStonePrimitive.statement
      ∧ base.b0.noSpectralPrimitive.statement :=
  primitive_extension_base_preserves_target_import_boundary
    (typedSemanticExtensionBaseToPrimitiveExtensionBase base)

theorem typed_semantic_extension_base_yields_package_import_guards
    (base : TypedCGSCSemanticExtensionBase) :
    (typedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noSpectralImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noBornImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).finiteExposed.noHilbertImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noUnitaryImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noStoneImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).routeCoherence.noGeneratorImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noTensorImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noBornImport.statement
      ∧ (typedSemanticExtensionBaseToCGSCPackageClosure base).compositeClosure.noHilbertImport.statement :=
  primitive_bridge_yields_all_package_import_guards
    (typedSemanticExtensionBaseToPrimitiveExtensionBase base)

end QMClosure
end IDT
