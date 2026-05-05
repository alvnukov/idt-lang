import Proofs.QMClosure.B1PrimitiveBase

namespace IDT
namespace QMClosure

structure ResidualProjectiveKernel where
  finiteProjectionDeterminacy : CheckedProp
  projectiveConsistency : CheckedProp
  nonunitalStableDistinguishability : CheckedProp
  conservativeProjectiveGluing : CheckedProp

structure RepresentationKernel where
  spectralDecomposition : CheckedProp
  richDclReversibleSymmetry : CheckedProp

structure ReadoutKernel where
  contextNormalization : CheckedProp
  exclusivityAdditivity : CheckedProp
  coarseGrainingConsistency : CheckedProp
  operationalEquivalenceProbability : CheckedProp

structure DynamicsKernel where
  dclAutomorphismDynamics : CheckedProp
  overlapPreservationDynamics : CheckedProp
  projectiveAction : CheckedProp
  continuousInheritanceFamily : CheckedProp
  generatorClosure : CheckedProp

structure CompositeKernel where
  productContextExhaustion : CheckedProp
  localTomography : CheckedProp
  monoidalAssociativity : CheckedProp
  entanglementClosure : CheckedProp
  projectiveLimitConsistency : CheckedProp
  constructiveCarrierWitness : CheckedProp
  noHiddenJointOnlyGeneration : CheckedProp

structure PhysicalScaleKernel where
  physicalPhaseScaleBoundary : CheckedProp

structure NoTargetImportKernel where
  noSpectralImport : CheckedProp
  noBornImport : CheckedProp
  noHilbertImport : CheckedProp
  noUnitaryImport : CheckedProp
  noStoneImport : CheckedProp
  noGeneratorImport : CheckedProp
  noTensorImport : CheckedProp

structure FullQMSemanticKernel where
  residualProjective : ResidualProjectiveKernel
  representation : RepresentationKernel
  readout : ReadoutKernel
  dynamics : DynamicsKernel
  composite : CompositeKernel
  scale : PhysicalScaleKernel
  imports : NoTargetImportKernel

def semanticKernelToPackageClosure
    (kernel : FullQMSemanticKernel) :
    CGSCPackageClosure :=
  {
    finiteExposed := {
      finiteProjectionDeterminacy :=
        kernel.residualProjective.finiteProjectionDeterminacy,
      projectiveConsistency :=
        kernel.residualProjective.projectiveConsistency,
      nonunitalStableDistinguishability :=
        kernel.residualProjective.nonunitalStableDistinguishability,
      conservativeProjectiveGluing :=
        kernel.residualProjective.conservativeProjectiveGluing,
      spectralDecomposition :=
        kernel.representation.spectralDecomposition,
      contextNormalization :=
        kernel.readout.contextNormalization,
      exclusivityAdditivity :=
        kernel.readout.exclusivityAdditivity,
      coarseGrainingConsistency :=
        kernel.readout.coarseGrainingConsistency,
      operationalEquivalenceProbability :=
        kernel.readout.operationalEquivalenceProbability,
      physicalPhaseScaleBoundary :=
        kernel.scale.physicalPhaseScaleBoundary,
      noSpectralImport :=
        kernel.imports.noSpectralImport,
      noBornImport :=
        kernel.imports.noBornImport,
      noHilbertImport :=
        kernel.imports.noHilbertImport
    },
    routeCoherence := {
      richDclReversibleSymmetry :=
        kernel.representation.richDclReversibleSymmetry,
      dclAutomorphismDynamics :=
        kernel.dynamics.dclAutomorphismDynamics,
      overlapPreservationDynamics :=
        kernel.dynamics.overlapPreservationDynamics,
      projectiveAction :=
        kernel.dynamics.projectiveAction,
      continuousInheritanceFamily :=
        kernel.dynamics.continuousInheritanceFamily,
      generatorClosure :=
        kernel.dynamics.generatorClosure,
      noUnitaryImport :=
        kernel.imports.noUnitaryImport,
      noStoneImport :=
        kernel.imports.noStoneImport,
      noGeneratorImport :=
        kernel.imports.noGeneratorImport
    },
    compositeClosure := {
      productContextExhaustion :=
        kernel.composite.productContextExhaustion,
      localTomography :=
        kernel.composite.localTomography,
      monoidalAssociativity :=
        kernel.composite.monoidalAssociativity,
      entanglementClosure :=
        kernel.composite.entanglementClosure,
      projectiveLimitConsistency :=
        kernel.composite.projectiveLimitConsistency,
      constructiveCarrierWitness :=
        kernel.composite.constructiveCarrierWitness,
      noHiddenJointOnlyGeneration :=
        kernel.composite.noHiddenJointOnlyGeneration,
      noTensorImport :=
        kernel.imports.noTensorImport,
      noBornImport :=
        kernel.imports.noBornImport,
      noHilbertImport :=
        kernel.imports.noHilbertImport
    }
  }

theorem semantic_kernel_yields_full_qm_obligation_bundle
    (kernel : FullQMSemanticKernel) :
    FullQMObligationBundle
      (semanticKernelToPackageClosure kernel) :=
  fullQMObligationBundleFromPackage
    (semanticKernelToPackageClosure kernel)

theorem semantic_kernel_preserves_import_boundaries
    (kernel : FullQMSemanticKernel) :
    (semanticKernelToPackageClosure kernel).finiteExposed.noSpectralImport.statement
      ∧ (semanticKernelToPackageClosure kernel).finiteExposed.noBornImport.statement
      ∧ (semanticKernelToPackageClosure kernel).finiteExposed.noHilbertImport.statement
      ∧ (semanticKernelToPackageClosure kernel).routeCoherence.noUnitaryImport.statement
      ∧ (semanticKernelToPackageClosure kernel).routeCoherence.noStoneImport.statement
      ∧ (semanticKernelToPackageClosure kernel).routeCoherence.noGeneratorImport.statement
      ∧ (semanticKernelToPackageClosure kernel).compositeClosure.noTensorImport.statement
      ∧ (semanticKernelToPackageClosure kernel).compositeClosure.noBornImport.statement
      ∧ (semanticKernelToPackageClosure kernel).compositeClosure.noHilbertImport.statement :=
  And.intro
    kernel.imports.noSpectralImport.proof
    (And.intro
      kernel.imports.noBornImport.proof
      (And.intro
        kernel.imports.noHilbertImport.proof
        (And.intro
          kernel.imports.noUnitaryImport.proof
          (And.intro
            kernel.imports.noStoneImport.proof
            (And.intro
              kernel.imports.noGeneratorImport.proof
              (And.intro
                kernel.imports.noTensorImport.proof
                (And.intro
                  kernel.imports.noBornImport.proof
                  kernel.imports.noHilbertImport.proof)))))))

theorem semantic_kernel_rejects_unwitnessed_composite_residual
    (kernel : FullQMSemanticKernel) :
    (semanticKernelToPackageClosure kernel).compositeClosure.constructiveCarrierWitness.statement
      ∧ (semanticKernelToPackageClosure kernel).compositeClosure.noHiddenJointOnlyGeneration.statement :=
  And.intro
    kernel.composite.constructiveCarrierWitness.proof
    kernel.composite.noHiddenJointOnlyGeneration.proof

structure B1ToFullQMSemanticKernelRoute where
  base : B1PrimitiveBase
  kernel : FullQMSemanticKernel
  kernelDerivedFromB1 : CheckedProp

theorem b1_semantic_kernel_route_yields_full_qm_obligation_bundle
    (route : B1ToFullQMSemanticKernelRoute) :
    FullQMObligationBundle
      (semanticKernelToPackageClosure route.kernel) :=
  semantic_kernel_yields_full_qm_obligation_bundle route.kernel

theorem b1_semantic_kernel_route_keeps_b1_bundle_available
    (route : B1ToFullQMSemanticKernelRoute) :
    FullQMObligationBundle
      (b1PrimitiveGeneratedCGSCPackageClosure route.base) :=
  b1_primitive_base_yields_full_qm_obligation_bundle route.base

theorem b1_semantic_kernel_route_requires_b1_derivation_witness
    (route : B1ToFullQMSemanticKernelRoute) :
    route.kernelDerivedFromB1.statement :=
  route.kernelDerivedFromB1.proof

end QMClosure
end IDT
