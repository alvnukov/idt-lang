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
  finiteNoSpectralImport : CheckedProp
  finiteNoBornImport : CheckedProp
  finiteNoHilbertImport : CheckedProp
  routeNoUnitaryImport : CheckedProp
  routeNoStoneImport : CheckedProp
  routeNoGeneratorImport : CheckedProp
  compositeNoTensorImport : CheckedProp
  compositeNoBornImport : CheckedProp
  compositeNoHilbertImport : CheckedProp

structure FullQMSemanticKernel where
  residualProjective : ResidualProjectiveKernel
  representation : RepresentationKernel
  readout : ReadoutKernel
  dynamics : DynamicsKernel
  composite : CompositeKernel
  scale : PhysicalScaleKernel
  imports : NoTargetImportKernel

def packageClosureToSemanticKernel
    (pkg : CGSCPackageClosure) :
    FullQMSemanticKernel :=
  {
    residualProjective := {
      finiteProjectionDeterminacy :=
        pkg.finiteExposed.finiteProjectionDeterminacy,
      projectiveConsistency :=
        pkg.finiteExposed.projectiveConsistency,
      nonunitalStableDistinguishability :=
        pkg.finiteExposed.nonunitalStableDistinguishability,
      conservativeProjectiveGluing :=
        pkg.finiteExposed.conservativeProjectiveGluing
    },
    representation := {
      spectralDecomposition :=
        pkg.finiteExposed.spectralDecomposition,
      richDclReversibleSymmetry :=
        pkg.routeCoherence.richDclReversibleSymmetry
    },
    readout := {
      contextNormalization :=
        pkg.finiteExposed.contextNormalization,
      exclusivityAdditivity :=
        pkg.finiteExposed.exclusivityAdditivity,
      coarseGrainingConsistency :=
        pkg.finiteExposed.coarseGrainingConsistency,
      operationalEquivalenceProbability :=
        pkg.finiteExposed.operationalEquivalenceProbability
    },
    dynamics := {
      dclAutomorphismDynamics :=
        pkg.routeCoherence.dclAutomorphismDynamics,
      overlapPreservationDynamics :=
        pkg.routeCoherence.overlapPreservationDynamics,
      projectiveAction :=
        pkg.routeCoherence.projectiveAction,
      continuousInheritanceFamily :=
        pkg.routeCoherence.continuousInheritanceFamily,
      generatorClosure :=
        pkg.routeCoherence.generatorClosure
    },
    composite := {
      productContextExhaustion :=
        pkg.compositeClosure.productContextExhaustion,
      localTomography :=
        pkg.compositeClosure.localTomography,
      monoidalAssociativity :=
        pkg.compositeClosure.monoidalAssociativity,
      entanglementClosure :=
        pkg.compositeClosure.entanglementClosure,
      projectiveLimitConsistency :=
        pkg.compositeClosure.projectiveLimitConsistency,
      constructiveCarrierWitness :=
        pkg.compositeClosure.constructiveCarrierWitness,
      noHiddenJointOnlyGeneration :=
        pkg.compositeClosure.noHiddenJointOnlyGeneration
    },
    scale := {
      physicalPhaseScaleBoundary :=
        pkg.finiteExposed.physicalPhaseScaleBoundary
    },
    imports := {
      finiteNoSpectralImport :=
        pkg.finiteExposed.noSpectralImport,
      finiteNoBornImport :=
        pkg.finiteExposed.noBornImport,
      finiteNoHilbertImport :=
        pkg.finiteExposed.noHilbertImport,
      routeNoUnitaryImport :=
        pkg.routeCoherence.noUnitaryImport,
      routeNoStoneImport :=
        pkg.routeCoherence.noStoneImport,
      routeNoGeneratorImport :=
        pkg.routeCoherence.noGeneratorImport,
      compositeNoTensorImport :=
        pkg.compositeClosure.noTensorImport,
      compositeNoBornImport :=
        pkg.compositeClosure.noBornImport,
      compositeNoHilbertImport :=
        pkg.compositeClosure.noHilbertImport
    }
  }

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
        kernel.imports.finiteNoSpectralImport,
      noBornImport :=
        kernel.imports.finiteNoBornImport,
      noHilbertImport :=
        kernel.imports.finiteNoHilbertImport
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
        kernel.imports.routeNoUnitaryImport,
      noStoneImport :=
        kernel.imports.routeNoStoneImport,
      noGeneratorImport :=
        kernel.imports.routeNoGeneratorImport
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
        kernel.imports.compositeNoTensorImport,
      noBornImport :=
        kernel.imports.compositeNoBornImport,
      noHilbertImport :=
        kernel.imports.compositeNoHilbertImport
    }
  }

theorem semantic_kernel_yields_full_qm_obligation_bundle
    (kernel : FullQMSemanticKernel) :
    FullQMObligationBundle
    (semanticKernelToPackageClosure kernel) :=
  fullQMObligationBundleFromPackage
    (semanticKernelToPackageClosure kernel)

theorem package_closure_to_semantic_kernel_roundtrip
    (pkg : CGSCPackageClosure) :
    semanticKernelToPackageClosure
      (packageClosureToSemanticKernel pkg) = pkg := by
  cases pkg
  rfl

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
    kernel.imports.finiteNoSpectralImport.proof
    (And.intro
      kernel.imports.finiteNoBornImport.proof
      (And.intro
        kernel.imports.finiteNoHilbertImport.proof
        (And.intro
          kernel.imports.routeNoUnitaryImport.proof
          (And.intro
            kernel.imports.routeNoStoneImport.proof
            (And.intro
              kernel.imports.routeNoGeneratorImport.proof
              (And.intro
                kernel.imports.compositeNoTensorImport.proof
                (And.intro
                  kernel.imports.compositeNoBornImport.proof
                  kernel.imports.compositeNoHilbertImport.proof)))))))

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

def b1PrimitiveBaseToFullQMSemanticKernel
    (base : B1PrimitiveBase) :
    FullQMSemanticKernel :=
  packageClosureToSemanticKernel
    (b1PrimitiveGeneratedCGSCPackageClosure base)

theorem b1_primitive_base_projects_to_semantic_kernel
    (base : B1PrimitiveBase) :
    semanticKernelToPackageClosure
      (b1PrimitiveBaseToFullQMSemanticKernel base) =
        b1PrimitiveGeneratedCGSCPackageClosure base :=
  package_closure_to_semantic_kernel_roundtrip
    (b1PrimitiveGeneratedCGSCPackageClosure base)

theorem b1_projected_semantic_kernel_yields_full_qm_obligation_bundle
    (base : B1PrimitiveBase) :
    FullQMObligationBundle
      (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)) := by
  rw [b1_primitive_base_projects_to_semantic_kernel]
  exact b1_primitive_base_yields_full_qm_obligation_bundle base

theorem b1_projected_residual_projective_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.finiteProjectionDeterminacy.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.projectiveConsistency.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.nonunitalStableDistinguishability.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.conservativeProjectiveGluing.statement :=
  And.intro
    (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.finiteProjectionDeterminacy.proof
    (And.intro
      (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.projectiveConsistency.proof
      (And.intro
        (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.nonunitalStableDistinguishability.proof
        (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.conservativeProjectiveGluing.proof))

theorem b1_projected_representation_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).representation.spectralDecomposition.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).representation.richDclReversibleSymmetry.statement :=
  And.intro
    (b1PrimitiveBaseToFullQMSemanticKernel base).representation.spectralDecomposition.proof
    (b1PrimitiveBaseToFullQMSemanticKernel base).representation.richDclReversibleSymmetry.proof

theorem b1_projected_readout_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).readout.contextNormalization.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).readout.exclusivityAdditivity.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).readout.coarseGrainingConsistency.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).readout.operationalEquivalenceProbability.statement :=
  And.intro
    (b1PrimitiveBaseToFullQMSemanticKernel base).readout.contextNormalization.proof
    (And.intro
      (b1PrimitiveBaseToFullQMSemanticKernel base).readout.exclusivityAdditivity.proof
      (And.intro
        (b1PrimitiveBaseToFullQMSemanticKernel base).readout.coarseGrainingConsistency.proof
        (b1PrimitiveBaseToFullQMSemanticKernel base).readout.operationalEquivalenceProbability.proof))

theorem b1_projected_dynamics_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.dclAutomorphismDynamics.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.overlapPreservationDynamics.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.projectiveAction.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.continuousInheritanceFamily.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.generatorClosure.statement :=
  And.intro
    (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.dclAutomorphismDynamics.proof
    (And.intro
      (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.overlapPreservationDynamics.proof
      (And.intro
        (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.projectiveAction.proof
        (And.intro
          (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.continuousInheritanceFamily.proof
          (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.generatorClosure.proof)))

theorem b1_projected_composite_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).composite.productContextExhaustion.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.localTomography.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.monoidalAssociativity.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.entanglementClosure.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.projectiveLimitConsistency.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.constructiveCarrierWitness.statement
      ∧ (b1PrimitiveBaseToFullQMSemanticKernel base).composite.noHiddenJointOnlyGeneration.statement :=
  And.intro
    (b1PrimitiveBaseToFullQMSemanticKernel base).composite.productContextExhaustion.proof
    (And.intro
      (b1PrimitiveBaseToFullQMSemanticKernel base).composite.localTomography.proof
      (And.intro
        (b1PrimitiveBaseToFullQMSemanticKernel base).composite.monoidalAssociativity.proof
        (And.intro
          (b1PrimitiveBaseToFullQMSemanticKernel base).composite.entanglementClosure.proof
          (And.intro
            (b1PrimitiveBaseToFullQMSemanticKernel base).composite.projectiveLimitConsistency.proof
            (And.intro
              (b1PrimitiveBaseToFullQMSemanticKernel base).composite.constructiveCarrierWitness.proof
              (b1PrimitiveBaseToFullQMSemanticKernel base).composite.noHiddenJointOnlyGeneration.proof)))))

theorem b1_projected_physical_scale_kernel
    (base : B1PrimitiveBase) :
    (b1PrimitiveBaseToFullQMSemanticKernel base).scale.physicalPhaseScaleBoundary.statement :=
  (b1PrimitiveBaseToFullQMSemanticKernel base).scale.physicalPhaseScaleBoundary.proof

theorem b1_projected_semantic_kernel_preserves_import_boundaries
    (base : B1PrimitiveBase) :
    (semanticKernelToPackageClosure
      (b1PrimitiveBaseToFullQMSemanticKernel base)).finiteExposed.noSpectralImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).finiteExposed.noBornImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).finiteExposed.noHilbertImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).routeCoherence.noUnitaryImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).routeCoherence.noStoneImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).routeCoherence.noGeneratorImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).compositeClosure.noTensorImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).compositeClosure.noBornImport.statement
      ∧ (semanticKernelToPackageClosure
        (b1PrimitiveBaseToFullQMSemanticKernel base)).compositeClosure.noHilbertImport.statement :=
  semantic_kernel_preserves_import_boundaries
    (b1PrimitiveBaseToFullQMSemanticKernel base)

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
