import Proofs.QMClosure.CGSCPackageClosure

namespace IDT
namespace QMClosure

structure B0CandidateBase where
  finiteGeneration : CheckedProp
  facticizableSeparation : CheckedProp
  importBoundary : CheckedProp
  noPrimitiveGlobalSection : CheckedProp
  noHilbertPrimitive : CheckedProp
  noBornPrimitive : CheckedProp
  noUnitaryPrimitive : CheckedProp
  noTensorPrimitive : CheckedProp
  noStonePrimitive : CheckedProp
  noSpectralPrimitive : CheckedProp

structure CompleteExposedContextPartitionExtension where
  completeExposedContextPartition : CheckedProp
  finiteProjectionDeterminacy : CheckedProp
  projectiveConsistency : CheckedProp
  nonunitalStableDistinguishability : CheckedProp
  conservativeProjectiveGluing : CheckedProp
  spectralDecomposition : CheckedProp
  contextNormalization : CheckedProp
  exclusivityAdditivity : CheckedProp
  coarseGrainingConsistency : CheckedProp
  operationalEquivalenceProbability : CheckedProp
  physicalPhaseScaleBoundary : CheckedProp

structure ReversibleContextAutomorphismClosureExtension where
  reversibleContextAutomorphismClosure : CheckedProp
  richDclReversibleSymmetry : CheckedProp
  dclAutomorphismDynamics : CheckedProp
  overlapPreservationDynamics : CheckedProp
  projectiveAction : CheckedProp

structure CoherentRefinementCompactnessExtension where
  coherentRefinementCompactness : CheckedProp
  continuousInheritanceFamily : CheckedProp

structure GeneratorBookkeepingWithoutStoneExtension where
  generatorBookkeepingWithoutStone : CheckedProp
  generatorClosure : CheckedProp

structure ProductContextGenerationClosureExtension where
  productContextGenerationClosure : CheckedProp
  productContextExhaustion : CheckedProp
  localTomography : CheckedProp
  monoidalAssociativity : CheckedProp
  entanglementClosure : CheckedProp
  projectiveLimitConsistency : CheckedProp

structure NoHiddenJointOnlyGenerationExtension where
  noHiddenJointOnlyGenerationExtension : CheckedProp
  constructiveCarrierWitness : CheckedProp
  noHiddenJointOnlyGeneration : CheckedProp

structure CGSCPrimitiveExtensionBase where
  b0 : B0CandidateBase
  exposed : CompleteExposedContextPartitionExtension
  reversible : ReversibleContextAutomorphismClosureExtension
  refinement : CoherentRefinementCompactnessExtension
  generator : GeneratorBookkeepingWithoutStoneExtension
  product : ProductContextGenerationClosureExtension
  noHiddenJoint : NoHiddenJointOnlyGenerationExtension

def finiteExposedContextPackageFromPrimitiveExtension
    (base : CGSCPrimitiveExtensionBase) :
    FiniteExposedContextPackage :=
  {
    finiteProjectionDeterminacy := base.exposed.finiteProjectionDeterminacy,
    projectiveConsistency := base.exposed.projectiveConsistency,
    nonunitalStableDistinguishability := base.exposed.nonunitalStableDistinguishability,
    conservativeProjectiveGluing := base.exposed.conservativeProjectiveGluing,
    spectralDecomposition := base.exposed.spectralDecomposition,
    contextNormalization := base.exposed.contextNormalization,
    exclusivityAdditivity := base.exposed.exclusivityAdditivity,
    coarseGrainingConsistency := base.exposed.coarseGrainingConsistency,
    operationalEquivalenceProbability := base.exposed.operationalEquivalenceProbability,
    physicalPhaseScaleBoundary := base.exposed.physicalPhaseScaleBoundary,
    noSpectralImport := base.b0.noSpectralPrimitive,
    noBornImport := base.b0.noBornPrimitive,
    noHilbertImport := base.b0.noHilbertPrimitive
  }

def routeAutomorphismRefinementPackageFromPrimitiveExtension
    (base : CGSCPrimitiveExtensionBase) :
    RouteAutomorphismRefinementPackage :=
  {
    richDclReversibleSymmetry := base.reversible.richDclReversibleSymmetry,
    dclAutomorphismDynamics := base.reversible.dclAutomorphismDynamics,
    overlapPreservationDynamics := base.reversible.overlapPreservationDynamics,
    projectiveAction := base.reversible.projectiveAction,
    continuousInheritanceFamily := base.refinement.continuousInheritanceFamily,
    generatorClosure := base.generator.generatorClosure,
    noUnitaryImport := base.b0.noUnitaryPrimitive,
    noStoneImport := base.b0.noStonePrimitive,
    noGeneratorImport := base.generator.generatorBookkeepingWithoutStone
  }

def generatedCompositePackageFromPrimitiveExtension
    (base : CGSCPrimitiveExtensionBase) :
    GeneratedCompositePackage :=
  {
    productContextExhaustion := base.product.productContextExhaustion,
    localTomography := base.product.localTomography,
    monoidalAssociativity := base.product.monoidalAssociativity,
    entanglementClosure := base.product.entanglementClosure,
    projectiveLimitConsistency := base.product.projectiveLimitConsistency,
    constructiveCarrierWitness := base.noHiddenJoint.constructiveCarrierWitness,
    noHiddenJointOnlyGeneration := base.noHiddenJoint.noHiddenJointOnlyGeneration,
    noTensorImport := base.b0.noTensorPrimitive,
    noBornImport := base.b0.noBornPrimitive,
    noHilbertImport := base.b0.noHilbertPrimitive
  }

def cgscPackageClosureFromPrimitiveExtensionBase
    (base : CGSCPrimitiveExtensionBase) :
    CGSCPackageClosure :=
  {
    finiteExposed := finiteExposedContextPackageFromPrimitiveExtension base,
    routeCoherence := routeAutomorphismRefinementPackageFromPrimitiveExtension base,
    compositeClosure := generatedCompositePackageFromPrimitiveExtension base
  }

theorem primitive_extension_base_contains_all_six_extension_witnesses
    (base : CGSCPrimitiveExtensionBase) :
    base.exposed.completeExposedContextPartition.statement
      ∧ base.reversible.reversibleContextAutomorphismClosure.statement
      ∧ base.refinement.coherentRefinementCompactness.statement
      ∧ base.generator.generatorBookkeepingWithoutStone.statement
      ∧ base.product.productContextGenerationClosure.statement
      ∧ base.noHiddenJoint.noHiddenJointOnlyGenerationExtension.statement :=
  And.intro
    base.exposed.completeExposedContextPartition.proof
    (And.intro
      base.reversible.reversibleContextAutomorphismClosure.proof
      (And.intro
        base.refinement.coherentRefinementCompactness.proof
        (And.intro
          base.generator.generatorBookkeepingWithoutStone.proof
          (And.intro
            base.product.productContextGenerationClosure.proof
            base.noHiddenJoint.noHiddenJointOnlyGenerationExtension.proof))))

theorem primitive_extension_base_preserves_target_import_boundary
    (base : CGSCPrimitiveExtensionBase) :
    base.b0.noHilbertPrimitive.statement
      ∧ base.b0.noBornPrimitive.statement
      ∧ base.b0.noUnitaryPrimitive.statement
      ∧ base.b0.noTensorPrimitive.statement
      ∧ base.b0.noStonePrimitive.statement
      ∧ base.b0.noSpectralPrimitive.statement :=
  And.intro
    base.b0.noHilbertPrimitive.proof
    (And.intro
      base.b0.noBornPrimitive.proof
      (And.intro
        base.b0.noUnitaryPrimitive.proof
        (And.intro
          base.b0.noTensorPrimitive.proof
          (And.intro
            base.b0.noStonePrimitive.proof
            base.b0.noSpectralPrimitive.proof))))

theorem primitive_bridge_yields_all_package_import_guards
    (base : CGSCPrimitiveExtensionBase) :
    (cgscPackageClosureFromPrimitiveExtensionBase base).finiteExposed.noSpectralImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).finiteExposed.noBornImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).finiteExposed.noHilbertImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).routeCoherence.noUnitaryImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).routeCoherence.noStoneImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).routeCoherence.noGeneratorImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).compositeClosure.noTensorImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).compositeClosure.noBornImport.statement
      ∧ (cgscPackageClosureFromPrimitiveExtensionBase base).compositeClosure.noHilbertImport.statement :=
  And.intro
    base.b0.noSpectralPrimitive.proof
    (And.intro
      base.b0.noBornPrimitive.proof
      (And.intro
        base.b0.noHilbertPrimitive.proof
        (And.intro
          base.b0.noUnitaryPrimitive.proof
          (And.intro
            base.b0.noStonePrimitive.proof
            (And.intro
              base.generator.generatorBookkeepingWithoutStone.proof
              (And.intro
                base.b0.noTensorPrimitive.proof
                (And.intro base.b0.noBornPrimitive.proof base.b0.noHilbertPrimitive.proof)))))))

end QMClosure
end IDT
