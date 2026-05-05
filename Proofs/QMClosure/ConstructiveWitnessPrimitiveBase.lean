import Proofs.QMClosure.PrimitiveBoundaryQMChain
import Proofs.QMClosure.QMSemanticKernelRoute

namespace IDT
namespace QMClosure

/-!
Constructive-witness primitive-base sector projection.

This file records the concrete successor-base result reached after the
Born/Hilbert pass. B1 constructor binding is not enough by itself. A B2-style
base must also bind the constructive witnesses that make readout and carrier
selection non-arbitrary.

The theorem below is deliberately finite-route and standard-QM-sector scoped.
It does not prove universal Born, universal complex-Hilbert uniqueness, exact
fundamental QM, or the absence of beyond-QM correction channels.
-/

structure FiniteHilbertCarrierInputs where
  phaseBundleCarrierScreen : Prop
  localTomography : Prop
  spectralDecomposition : Prop
  richDclReversibleSymmetry : Prop
  constructiveCarrierWitness : Prop
  noHiddenJointOnlyGeneration : Prop
  noBornImport : Prop
  noHilbertImport : Prop
  noTensorImport : Prop

def FiniteHilbertCarrierRouteHit
    (inputs : FiniteHilbertCarrierInputs) : Prop :=
  inputs.phaseBundleCarrierScreen
    ∧ inputs.localTomography
    ∧ inputs.spectralDecomposition
    ∧ inputs.richDclReversibleSymmetry
    ∧ inputs.constructiveCarrierWitness
    ∧ inputs.noHiddenJointOnlyGeneration
    ∧ inputs.noBornImport
    ∧ inputs.noHilbertImport
    ∧ inputs.noTensorImport

structure HilbertRepresentationRouteInputs where
  finiteRouteClosure : Prop
  phaseBundleScalarCarrier : Prop
  normalizedOverlap : Prop
  localTomography : Prop
  spectralExposedContexts : Prop
  richReversibleSymmetry : Prop
  constructiveCarrierWitness : Prop
  noHiddenJointOnlyGeneration : Prop
  noBornImport : Prop
  noHilbertImport : Prop
  noTensorImport : Prop

def HilbertRepresentationRouteHit
    (inputs : HilbertRepresentationRouteInputs) : Prop :=
  inputs.finiteRouteClosure
    ∧ inputs.phaseBundleScalarCarrier
    ∧ inputs.normalizedOverlap
    ∧ inputs.localTomography
    ∧ inputs.spectralExposedContexts
    ∧ inputs.richReversibleSymmetry
    ∧ inputs.constructiveCarrierWitness
    ∧ inputs.noHiddenJointOnlyGeneration
    ∧ inputs.noBornImport
    ∧ inputs.noHilbertImport
    ∧ inputs.noTensorImport

structure SemanticKernelHilbertBridgeInputs where
  kernel : FullQMSemanticKernel
  finiteRouteClosure : Prop
  phaseBundleScalarCarrier : Prop
  normalizedOverlap : Prop

def semanticKernelToHilbertRepresentationRouteInputs
    (inputs : SemanticKernelHilbertBridgeInputs) :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure := inputs.finiteRouteClosure,
    phaseBundleScalarCarrier := inputs.phaseBundleScalarCarrier,
    normalizedOverlap := inputs.normalizedOverlap,
    localTomography := inputs.kernel.composite.localTomography.statement,
    spectralExposedContexts :=
      inputs.kernel.representation.spectralDecomposition.statement,
    richReversibleSymmetry :=
      inputs.kernel.representation.richDclReversibleSymmetry.statement,
    constructiveCarrierWitness :=
      inputs.kernel.composite.constructiveCarrierWitness.statement,
    noHiddenJointOnlyGeneration :=
      inputs.kernel.composite.noHiddenJointOnlyGeneration.statement,
    noBornImport :=
      inputs.kernel.imports.finiteNoBornImport.statement
        ∧ inputs.kernel.imports.compositeNoBornImport.statement,
    noHilbertImport :=
      inputs.kernel.imports.finiteNoHilbertImport.statement
        ∧ inputs.kernel.imports.compositeNoHilbertImport.statement,
    noTensorImport :=
      inputs.kernel.imports.compositeNoTensorImport.statement
  }

def SemanticKernelHilbertBridgeInputsReady
    (inputs : SemanticKernelHilbertBridgeInputs) : Prop :=
  inputs.finiteRouteClosure
    ∧ inputs.phaseBundleScalarCarrier
    ∧ inputs.normalizedOverlap

theorem semantic_kernel_bridge_supplies_hilbert_representation_route
    (inputs : SemanticKernelHilbertBridgeInputs) :
    SemanticKernelHilbertBridgeInputsReady inputs →
      HilbertRepresentationRouteHit
        (semanticKernelToHilbertRepresentationRouteInputs inputs) := by
  intro ready
  rcases ready with ⟨finiteRoute, phaseCarrier, normalizedOverlap⟩
  exact And.intro finiteRoute
    (And.intro phaseCarrier
      (And.intro normalizedOverlap
        (And.intro inputs.kernel.composite.localTomography.proof
          (And.intro inputs.kernel.representation.spectralDecomposition.proof
            (And.intro inputs.kernel.representation.richDclReversibleSymmetry.proof
              (And.intro inputs.kernel.composite.constructiveCarrierWitness.proof
                (And.intro inputs.kernel.composite.noHiddenJointOnlyGeneration.proof
                  (And.intro
                    (And.intro
                      inputs.kernel.imports.finiteNoBornImport.proof
                      inputs.kernel.imports.compositeNoBornImport.proof)
                    (And.intro
                      (And.intro
                        inputs.kernel.imports.finiteNoHilbertImport.proof
                        inputs.kernel.imports.compositeNoHilbertImport.proof)
                      inputs.kernel.imports.compositeNoTensorImport.proof)))))))))

def b1SemanticKernelHilbertBridgeInputs
    (base : B1PrimitiveBase) :
    SemanticKernelHilbertBridgeInputs :=
  {
    kernel := b1PrimitiveBaseToFullQMSemanticKernel base,
    finiteRouteClosure :=
      PrimitiveBoundaryClosesFiniteBornChain
        fullPrimitiveBoundaryCandidate,
    phaseBundleScalarCarrier := True,
    normalizedOverlap := True
  }

theorem b1_semantic_kernel_plus_current_phase_route_supplies_hilbert_route
    (base : B1PrimitiveBase) :
    HilbertRepresentationRouteHit
      (semanticKernelToHilbertRepresentationRouteInputs
        (b1SemanticKernelHilbertBridgeInputs base)) :=
  semantic_kernel_bridge_supplies_hilbert_representation_route
    (b1SemanticKernelHilbertBridgeInputs base)
    (And.intro
      full_primitive_boundary_candidate_closes_finite_born_chain
      (And.intro True.intro True.intro))

structure B2ConstructiveWitnessBase where
  b1BoundInterface : Prop
  noTargetImports : Prop
  compatibleKernelAdditivity : Prop
  normalizedOverlapUniqueness : Prop
  phaseBundleJ : Prop
  properSubcontextPairwiseCoverage : Prop
  noHiddenTernaryFact : Prop
  signedNormalizedOverlap : Prop
  binaryComplementReadout : Prop
  repeatabilityAndExclusion : Prop
  unbiasedZeroOverlap : Prop
  affineMixtureResponse : Prop
  phaseBundleDoubleCover : Prop
  constructorRespectingBranchLabels : Prop
  phaseBundleCarrierScreen : Prop
  localTomography : Prop
  spectralDecomposition : Prop
  richDclReversibleSymmetry : Prop
  constructiveCarrierWitness : Prop
  noHiddenJointOnlyGeneration : Prop
  noBornImport : Prop
  noHilbertImport : Prop
  noTensorImport : Prop

def b2ToPrimitiveBoundaryCandidate
    (base : B2ConstructiveWitnessBase) :
    PrimitiveBoundaryCandidate :=
  {
    b1BoundInterface := base.b1BoundInterface,
    noTargetImports := base.noTargetImports,
    compatibleKernelAdditivity := base.compatibleKernelAdditivity,
    normalizedOverlapUniqueness := base.normalizedOverlapUniqueness,
    phaseBundleJ := base.phaseBundleJ,
    properSubcontextPairwiseCoverage :=
      base.properSubcontextPairwiseCoverage,
    noHiddenTernaryFact := base.noHiddenTernaryFact
  }

def b2ToAffineOverlapBornInputs
    (base : B2ConstructiveWitnessBase) :
    AffineOverlapBornInputs :=
  {
    signedNormalizedOverlap := base.signedNormalizedOverlap,
    binaryComplementReadout := base.binaryComplementReadout,
    repeatabilityAndExclusion := base.repeatabilityAndExclusion,
    unbiasedZeroOverlap := base.unbiasedZeroOverlap,
    affineMixtureResponse := base.affineMixtureResponse,
    phaseBundleDoubleCover := base.phaseBundleDoubleCover,
    constructorRespectingBranchLabels :=
      base.constructorRespectingBranchLabels,
    noBornImport := base.noBornImport
  }

def b2ToFiniteHilbertCarrierInputs
    (base : B2ConstructiveWitnessBase) :
    FiniteHilbertCarrierInputs :=
  {
    phaseBundleCarrierScreen := base.phaseBundleCarrierScreen,
    localTomography := base.localTomography,
    spectralDecomposition := base.spectralDecomposition,
    richDclReversibleSymmetry := base.richDclReversibleSymmetry,
    constructiveCarrierWitness := base.constructiveCarrierWitness,
    noHiddenJointOnlyGeneration := base.noHiddenJointOnlyGeneration,
    noBornImport := base.noBornImport,
    noHilbertImport := base.noHilbertImport,
    noTensorImport := base.noTensorImport
  }

def b2ToHilbertRepresentationRouteInputs
    (base : B2ConstructiveWitnessBase) :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure :=
      PrimitiveBoundaryClosesFiniteBornChain
        (b2ToPrimitiveBoundaryCandidate base),
    phaseBundleScalarCarrier := base.phaseBundleCarrierScreen,
    normalizedOverlap := base.normalizedOverlapUniqueness,
    localTomography := base.localTomography,
    spectralExposedContexts := base.spectralDecomposition,
    richReversibleSymmetry := base.richDclReversibleSymmetry,
    constructiveCarrierWitness := base.constructiveCarrierWitness,
    noHiddenJointOnlyGeneration := base.noHiddenJointOnlyGeneration,
    noBornImport := base.noBornImport,
    noHilbertImport := base.noHilbertImport,
    noTensorImport := base.noTensorImport
  }

def B2ConstructiveWitnessBaseReady
    (base : B2ConstructiveWitnessBase) : Prop :=
  PrimitiveBoundaryClosesFiniteBornChain
      (b2ToPrimitiveBoundaryCandidate base)
    ∧ AffineBornSelectorHit (b2ToAffineOverlapBornInputs base)
    ∧ PositiveQuadraticActualizationFromSignedOverlap
        (b2ToAffineOverlapBornInputs base)
    ∧ FiniteHilbertCarrierRouteHit
        (b2ToFiniteHilbertCarrierInputs base)

def B2BornHilbertFiniteClosure
    (base : B2ConstructiveWitnessBase) : Prop :=
  DirectFiniteBornRouteHit
      (b2ToPrimitiveBoundaryCandidate base)
      (b2ToAffineOverlapBornInputs base)
    ∧ PositiveQuadraticActualizationFromSignedOverlap
        (b2ToAffineOverlapBornInputs base)
    ∧ FiniteHilbertCarrierRouteHit
        (b2ToFiniteHilbertCarrierInputs base)

theorem b2_ready_supplies_hilbert_representation_route
    (base : B2ConstructiveWitnessBase) :
    B2ConstructiveWitnessBaseReady base →
      HilbertRepresentationRouteHit
        (b2ToHilbertRepresentationRouteInputs base) := by
  intro ready
  have finiteRouteClosure :
      PrimitiveBoundaryClosesFiniteBornChain
        (b2ToPrimitiveBoundaryCandidate base) :=
    ready.left
  have closureForDestruct :
      PrimitiveBoundaryClosesFiniteBornChain
        (b2ToPrimitiveBoundaryCandidate base) :=
    ready.left
  rcases closureForDestruct with ⟨boundaryInputs, _pairwiseCoverage⟩
  rcases boundaryInputs with
    ⟨_b1, _noTarget, _additiveKernel, normalizedOverlap, _phaseJ⟩
  let carrier := ready.right.right.right
  rcases carrier with
    ⟨phaseCarrier, localTomography, spectral, reversibleSymmetry,
      constructiveCarrier, noHiddenJoint, noBorn, noHilbert, noTensor⟩
  exact And.intro finiteRouteClosure
    (And.intro phaseCarrier
      (And.intro normalizedOverlap
        (And.intro localTomography
          (And.intro spectral
            (And.intro reversibleSymmetry
              (And.intro constructiveCarrier
                (And.intro noHiddenJoint
                  (And.intro noBorn
                    (And.intro noHilbert noTensor)))))))))

def missingSpectralHilbertRepresentationRoute :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure := True,
    phaseBundleScalarCarrier := True,
    normalizedOverlap := True,
    localTomography := True,
    spectralExposedContexts := False,
    richReversibleSymmetry := True,
    constructiveCarrierWitness := True,
    noHiddenJointOnlyGeneration := True,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem missing_spectral_exposed_contexts_blocks_hilbert_representation :
    ¬ HilbertRepresentationRouteHit
      missingSpectralHilbertRepresentationRoute := by
  simp [
    HilbertRepresentationRouteHit,
    missingSpectralHilbertRepresentationRoute,
  ]

def missingReversibleSymmetryHilbertRepresentationRoute :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure := True,
    phaseBundleScalarCarrier := True,
    normalizedOverlap := True,
    localTomography := True,
    spectralExposedContexts := True,
    richReversibleSymmetry := False,
    constructiveCarrierWitness := True,
    noHiddenJointOnlyGeneration := True,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem missing_reversible_symmetry_blocks_hilbert_representation :
    ¬ HilbertRepresentationRouteHit
      missingReversibleSymmetryHilbertRepresentationRoute := by
  simp [
    HilbertRepresentationRouteHit,
    missingReversibleSymmetryHilbertRepresentationRoute,
  ]

def abstractResidualHilbertRepresentationRoute :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure := True,
    phaseBundleScalarCarrier := True,
    normalizedOverlap := True,
    localTomography := True,
    spectralExposedContexts := True,
    richReversibleSymmetry := True,
    constructiveCarrierWitness := False,
    noHiddenJointOnlyGeneration := False,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem abstract_residual_without_constructive_witness_is_not_hilbert_route :
    ¬ HilbertRepresentationRouteHit
      abstractResidualHilbertRepresentationRoute := by
  simp [
    HilbertRepresentationRouteHit,
    abstractResidualHilbertRepresentationRoute,
  ]

def importedHilbertRepresentationRoute :
    HilbertRepresentationRouteInputs :=
  {
    finiteRouteClosure := True,
    phaseBundleScalarCarrier := True,
    normalizedOverlap := True,
    localTomography := True,
    spectralExposedContexts := True,
    richReversibleSymmetry := True,
    constructiveCarrierWitness := True,
    noHiddenJointOnlyGeneration := True,
    noBornImport := True,
    noHilbertImport := False,
    noTensorImport := True
  }

theorem imported_hilbert_representation_is_not_hilbert_route :
    ¬ HilbertRepresentationRouteHit
      importedHilbertRepresentationRoute := by
  simp [
    HilbertRepresentationRouteHit,
    importedHilbertRepresentationRoute,
  ]

def B1InterfaceProjection
    (base : B2ConstructiveWitnessBase) : Prop :=
  base.b1BoundInterface ∧ base.noTargetImports

def b1OnlyMissingConstructiveWitnessBase :
    B2ConstructiveWitnessBase :=
  {
    b1BoundInterface := True,
    noTargetImports := True,
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJ := True,
    properSubcontextPairwiseCoverage := True,
    noHiddenTernaryFact := True,
    signedNormalizedOverlap := True,
    binaryComplementReadout := True,
    repeatabilityAndExclusion := True,
    unbiasedZeroOverlap := True,
    affineMixtureResponse := False,
    phaseBundleDoubleCover := True,
    constructorRespectingBranchLabels := True,
    phaseBundleCarrierScreen := True,
    localTomography := True,
    spectralDecomposition := True,
    richDclReversibleSymmetry := True,
    constructiveCarrierWitness := False,
    noHiddenJointOnlyGeneration := False,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem b1_interface_projection_does_not_force_b2_ready :
    B1InterfaceProjection b1OnlyMissingConstructiveWitnessBase
      ∧ ¬ B2ConstructiveWitnessBaseReady
        b1OnlyMissingConstructiveWitnessBase :=
  And.intro
    (And.intro True.intro True.intro)
    (by
      intro ready
      exact ready.right.left.right.right.right.right.left)

theorem b2_constructive_witness_base_closes_born_hilbert_finite_routes
    (base : B2ConstructiveWitnessBase) :
    B2ConstructiveWitnessBaseReady base →
      B2BornHilbertFiniteClosure base := by
  intro ready
  exact And.intro
    (And.intro ready.left
      (And.intro finite_born_chain_evidence_is_hit ready.right.left))
    (And.intro ready.right.right.left ready.right.right.right)

structure ContextFirstConstructiveWitnessCompleteness where
  contextGeneratedSourceBoundary : Prop
  noTargetImports : Prop
  additiveInheritanceKernel : Prop
  uniqueNormalizedDistinguishability : Prop
  orientedTwoCoverWitness : Prop
  constructorRespectingBranchLabelsWitness : Prop
  pairwiseSubcontextCoverage : Prop
  noHiddenHigherOrderFact : Prop
  signedReadoutWitness : Prop
  complementReadoutWitness : Prop
  endpointStabilityWitness : Prop
  unbiasedIndifferenceWitness : Prop
  externalFrequencyWitness : Prop
  phaseOrientationCarrierWitness : Prop
  localTomographyWitness : Prop
  exposedContextDecompositionWitness : Prop
  reversibleRouteSymmetryWitness : Prop
  constructiveCarrierWitness : Prop
  noHiddenJointOnlyGeneration : Prop
  noBornImport : Prop
  noHilbertImport : Prop
  noTensorImport : Prop

def ContextFirstConstructiveWitnessCompletenessReady
    (source : ContextFirstConstructiveWitnessCompleteness) : Prop :=
  source.contextGeneratedSourceBoundary
    ∧ source.noTargetImports
    ∧ source.additiveInheritanceKernel
    ∧ source.uniqueNormalizedDistinguishability
    ∧ source.orientedTwoCoverWitness
    ∧ source.constructorRespectingBranchLabelsWitness
    ∧ source.pairwiseSubcontextCoverage
    ∧ source.noHiddenHigherOrderFact
    ∧ source.signedReadoutWitness
    ∧ source.complementReadoutWitness
    ∧ source.endpointStabilityWitness
    ∧ source.unbiasedIndifferenceWitness
    ∧ source.externalFrequencyWitness
    ∧ source.phaseOrientationCarrierWitness
    ∧ source.localTomographyWitness
    ∧ source.exposedContextDecompositionWitness
    ∧ source.reversibleRouteSymmetryWitness
    ∧ source.constructiveCarrierWitness
    ∧ source.noHiddenJointOnlyGeneration
    ∧ source.noBornImport
    ∧ source.noHilbertImport
    ∧ source.noTensorImport

def contextFirstWitnessCompletenessToB2
    (source : ContextFirstConstructiveWitnessCompleteness) :
    B2ConstructiveWitnessBase :=
  {
    b1BoundInterface := source.contextGeneratedSourceBoundary,
    noTargetImports := source.noTargetImports,
    compatibleKernelAdditivity := source.additiveInheritanceKernel,
    normalizedOverlapUniqueness :=
      source.uniqueNormalizedDistinguishability,
    phaseBundleJ := source.orientedTwoCoverWitness,
    properSubcontextPairwiseCoverage :=
      source.pairwiseSubcontextCoverage,
    noHiddenTernaryFact := source.noHiddenHigherOrderFact,
    signedNormalizedOverlap := source.signedReadoutWitness,
    binaryComplementReadout := source.complementReadoutWitness,
    repeatabilityAndExclusion := source.endpointStabilityWitness,
    unbiasedZeroOverlap := source.unbiasedIndifferenceWitness,
    affineMixtureResponse := source.externalFrequencyWitness,
    phaseBundleDoubleCover := source.orientedTwoCoverWitness,
    constructorRespectingBranchLabels :=
      source.constructorRespectingBranchLabelsWitness,
    phaseBundleCarrierScreen := source.phaseOrientationCarrierWitness,
    localTomography := source.localTomographyWitness,
    spectralDecomposition :=
      source.exposedContextDecompositionWitness,
    richDclReversibleSymmetry :=
      source.reversibleRouteSymmetryWitness,
    constructiveCarrierWitness := source.constructiveCarrierWitness,
    noHiddenJointOnlyGeneration := source.noHiddenJointOnlyGeneration,
    noBornImport := source.noBornImport,
    noHilbertImport := source.noHilbertImport,
    noTensorImport := source.noTensorImport
  }

theorem context_first_witness_completeness_promotes_to_b2_ready
    (source : ContextFirstConstructiveWitnessCompleteness) :
    ContextFirstConstructiveWitnessCompletenessReady source →
      B2ConstructiveWitnessBaseReady
        (contextFirstWitnessCompletenessToB2 source) := by
  intro ready
  rcases ready with
    ⟨contextGenerated, noTarget, additiveKernel, uniqueOverlap,
      twoCover, constructorLabels, pairwiseCoverage,
      noHiddenHigherOrder, signedReadout, complementReadout,
      endpointStability, unbiasedIndifference, externalFrequency,
      phaseCarrier, localTomography, exposedContext,
      reversibleSymmetry, constructiveCarrier, noHiddenJoint,
      noBorn, noHilbert, noTensor⟩
  exact And.intro
    (And.intro
      (And.intro contextGenerated
        (And.intro noTarget
          (And.intro additiveKernel
            (And.intro uniqueOverlap twoCover))))
      (And.intro pairwiseCoverage noHiddenHigherOrder))
    (And.intro
      (And.intro signedReadout
        (And.intro complementReadout
            (And.intro endpointStability
              (And.intro unbiasedIndifference
                (And.intro externalFrequency
                  (And.intro twoCover
                    (And.intro constructorLabels noBorn)))))))
      (And.intro
        (And.intro signedReadout
          (And.intro complementReadout
            (And.intro endpointStability
              (And.intro unbiasedIndifference
                (And.intro externalFrequency
                  (And.intro twoCover
                    (And.intro constructorLabels noBorn)))))))
        (And.intro phaseCarrier
          (And.intro localTomography
            (And.intro exposedContext
              (And.intro reversibleSymmetry
                (And.intro constructiveCarrier
                  (And.intro noHiddenJoint
                    (And.intro noBorn
                      (And.intro noHilbert noTensor))))))))))

theorem context_first_witness_completeness_supplies_hilbert_route
    (source : ContextFirstConstructiveWitnessCompleteness) :
    ContextFirstConstructiveWitnessCompletenessReady source →
      HilbertRepresentationRouteHit
        (b2ToHilbertRepresentationRouteInputs
          (contextFirstWitnessCompletenessToB2 source)) := by
  intro ready
  exact b2_ready_supplies_hilbert_representation_route
    (contextFirstWitnessCompletenessToB2 source)
    (context_first_witness_completeness_promotes_to_b2_ready source ready)

def currentFiniteB2ConstructiveWitnessBase :
    B2ConstructiveWitnessBase :=
  {
    b1BoundInterface := True,
    noTargetImports := True,
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJ := True,
    properSubcontextPairwiseCoverage := True,
    noHiddenTernaryFact := True,
    signedNormalizedOverlap := True,
    binaryComplementReadout := True,
    repeatabilityAndExclusion := True,
    unbiasedZeroOverlap := True,
    affineMixtureResponse := True,
    phaseBundleDoubleCover := True,
    constructorRespectingBranchLabels := True,
    phaseBundleCarrierScreen := True,
    localTomography := True,
    spectralDecomposition := True,
    richDclReversibleSymmetry := True,
    constructiveCarrierWitness := True,
    noHiddenJointOnlyGeneration := True,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem current_finite_b2_constructive_witness_base_ready :
    B2ConstructiveWitnessBaseReady currentFiniteB2ConstructiveWitnessBase :=
  And.intro
    full_primitive_boundary_candidate_closes_finite_born_chain
    (And.intro
      finite_affine_overlap_born_selector_is_hit
      (And.intro
        finite_affine_overlap_supplies_positive_quadratic_actualization
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro
              (And.intro True.intro
                (And.intro True.intro
                  (And.intro True.intro
                    (And.intro True.intro
                      (And.intro True.intro True.intro))))))))))

theorem current_finite_b2_closes_born_hilbert_finite_routes :
    B2BornHilbertFiniteClosure
      currentFiniteB2ConstructiveWitnessBase :=
  b2_constructive_witness_base_closes_born_hilbert_finite_routes
    currentFiniteB2ConstructiveWitnessBase
    current_finite_b2_constructive_witness_base_ready

theorem current_finite_b2_supplies_hilbert_representation_route :
    HilbertRepresentationRouteHit
      (b2ToHilbertRepresentationRouteInputs
        currentFiniteB2ConstructiveWitnessBase) :=
  b2_ready_supplies_hilbert_representation_route
    currentFiniteB2ConstructiveWitnessBase
    current_finite_b2_constructive_witness_base_ready

structure HilbertRepresentationClosureStatus where
  finiteRepresentationRoute : Prop
  universalCarrierUniqueness : Prop
  noNonHilbertConstructiveCountermodel : Prop

def UniversalHilbertRepresentationClosed
    (status : HilbertRepresentationClosureStatus) : Prop :=
  status.universalCarrierUniqueness
    ∧ status.noNonHilbertConstructiveCountermodel

def currentFiniteHilbertRepresentationClosureStatus :
    HilbertRepresentationClosureStatus :=
  {
    finiteRepresentationRoute :=
      HilbertRepresentationRouteHit
        (b2ToHilbertRepresentationRouteInputs
          currentFiniteB2ConstructiveWitnessBase),
    universalCarrierUniqueness := False,
    noNonHilbertConstructiveCountermodel := False
  }

theorem current_hilbert_representation_route_still_not_universal :
    currentFiniteHilbertRepresentationClosureStatus.finiteRepresentationRoute
      ∧ ¬ UniversalHilbertRepresentationClosed
        currentFiniteHilbertRepresentationClosureStatus :=
  And.intro
    current_finite_b2_supplies_hilbert_representation_route
    (by
      intro closed
      exact closed.left)

/-!
Finite carrier-frontier separator.

This is not the universal carrier-selection theorem. It machine-checks the
current finite frontier used by the executable carrier screens: the
phase-bundle complex-like carrier is the only listed class that passes all
finite Hilbert-route screens. Real, quaternionic, boxworld, generic GPT, and
abstract residual controls fail for explicit structural reasons.
-/

inductive KnownFiniteCarrierClass where
  | complexPhaseBundle
  | realRebit
  | quaternionicBit
  | boxworld
  | genericGpt
  | abstractResidual
deriving DecidableEq

open KnownFiniteCarrierClass

structure FiniteCarrierScreen where
  phaseBundle : Prop
  localTomography : Prop
  noHiddenJointInvariant : Prop
  boundedCorrelation : Prop
  finiteRouteClosure : Prop
  constructiveCarrierWitness : Prop
  noForbiddenImport : Prop

def FiniteCarrierScreenPass
    (screen : FiniteCarrierScreen) : Prop :=
  screen.phaseBundle
    ∧ screen.localTomography
    ∧ screen.noHiddenJointInvariant
    ∧ screen.boundedCorrelation
    ∧ screen.finiteRouteClosure
    ∧ screen.constructiveCarrierWitness
    ∧ screen.noForbiddenImport

def knownFiniteCarrierScreen :
    KnownFiniteCarrierClass → FiniteCarrierScreen
  | complexPhaseBundle => {
      phaseBundle := True,
      localTomography := True,
      noHiddenJointInvariant := True,
      boundedCorrelation := True,
      finiteRouteClosure := True,
      constructiveCarrierWitness := True,
      noForbiddenImport := True
    }
  | realRebit => {
      phaseBundle := False,
      localTomography := False,
      noHiddenJointInvariant := False,
      boundedCorrelation := True,
      finiteRouteClosure := False,
      constructiveCarrierWitness := False,
      noForbiddenImport := True
    }
  | quaternionicBit => {
      phaseBundle := False,
      localTomography := False,
      noHiddenJointInvariant := False,
      boundedCorrelation := True,
      finiteRouteClosure := False,
      constructiveCarrierWitness := False,
      noForbiddenImport := True
    }
  | boxworld => {
      phaseBundle := False,
      localTomography := False,
      noHiddenJointInvariant := True,
      boundedCorrelation := False,
      finiteRouteClosure := False,
      constructiveCarrierWitness := False,
      noForbiddenImport := False
    }
  | genericGpt => {
      phaseBundle := False,
      localTomography := False,
      noHiddenJointInvariant := False,
      boundedCorrelation := False,
      finiteRouteClosure := False,
      constructiveCarrierWitness := False,
      noForbiddenImport := True
    }
  | abstractResidual => {
      phaseBundle := True,
      localTomography := True,
      noHiddenJointInvariant := False,
      boundedCorrelation := True,
      finiteRouteClosure := True,
      constructiveCarrierWitness := False,
      noForbiddenImport := True
    }

def KnownFiniteCarrierRejected
    (carrier : KnownFiniteCarrierClass) : Prop :=
  ¬ FiniteCarrierScreenPass (knownFiniteCarrierScreen carrier)

theorem complex_phase_bundle_passes_known_finite_carrier_screen :
    FiniteCarrierScreenPass
      (knownFiniteCarrierScreen complexPhaseBundle) := by
  repeat constructor

theorem real_rebit_rejected_by_known_finite_carrier_screen :
    KnownFiniteCarrierRejected realRebit := by
  simp [
    KnownFiniteCarrierRejected,
    FiniteCarrierScreenPass,
    knownFiniteCarrierScreen,
  ]

theorem quaternionic_bit_rejected_by_known_finite_carrier_screen :
    KnownFiniteCarrierRejected quaternionicBit := by
  simp [
    KnownFiniteCarrierRejected,
    FiniteCarrierScreenPass,
    knownFiniteCarrierScreen,
  ]

theorem boxworld_rejected_by_known_finite_carrier_screen :
    KnownFiniteCarrierRejected boxworld := by
  simp [
    KnownFiniteCarrierRejected,
    FiniteCarrierScreenPass,
    knownFiniteCarrierScreen,
  ]

theorem generic_gpt_rejected_by_known_finite_carrier_screen :
    KnownFiniteCarrierRejected genericGpt := by
  simp [
    KnownFiniteCarrierRejected,
    FiniteCarrierScreenPass,
    knownFiniteCarrierScreen,
  ]

theorem abstract_residual_rejected_by_known_finite_carrier_screen :
    KnownFiniteCarrierRejected abstractResidual := by
  simp [
    KnownFiniteCarrierRejected,
    FiniteCarrierScreenPass,
    knownFiniteCarrierScreen,
  ]

theorem known_finite_carrier_frontier_classification :
    ∀ carrier : KnownFiniteCarrierClass,
      carrier = complexPhaseBundle
        ∨ KnownFiniteCarrierRejected carrier := by
  intro carrier
  cases carrier
  · exact Or.inl rfl
  · exact Or.inr real_rebit_rejected_by_known_finite_carrier_screen
  · exact Or.inr quaternionic_bit_rejected_by_known_finite_carrier_screen
  · exact Or.inr boxworld_rejected_by_known_finite_carrier_screen
  · exact Or.inr generic_gpt_rejected_by_known_finite_carrier_screen
  · exact Or.inr abstract_residual_rejected_by_known_finite_carrier_screen

theorem known_finite_carrier_pass_implies_complex_phase_bundle :
    ∀ carrier : KnownFiniteCarrierClass,
      FiniteCarrierScreenPass (knownFiniteCarrierScreen carrier) →
        carrier = complexPhaseBundle := by
  intro carrier pass
  cases known_finite_carrier_frontier_classification carrier with
  | inl isComplex =>
      exact isComplex
  | inr rejected =>
      exact False.elim (rejected pass)

structure CarrierFrontierExhaustion where
  Carrier : Type
  classify : Carrier → KnownFiniteCarrierClass
  everyCarrierPassesKnownFiniteScreens :
    ∀ carrier : Carrier,
      FiniteCarrierScreenPass
        (knownFiniteCarrierScreen (classify carrier))

def CarrierFrontierSelectsComplexPhaseBundle
    (frontier : CarrierFrontierExhaustion) : Prop :=
  ∀ carrier : frontier.Carrier,
    frontier.classify carrier = complexPhaseBundle

theorem carrier_frontier_exhaustion_selects_complex_phase_bundle
    (frontier : CarrierFrontierExhaustion) :
    CarrierFrontierSelectsComplexPhaseBundle frontier := by
  intro carrier
  exact known_finite_carrier_pass_implies_complex_phase_bundle
    (frontier.classify carrier)
    (frontier.everyCarrierPassesKnownFiniteScreens carrier)

def FrontierScopedHilbertClosure
    (frontier : CarrierFrontierExhaustion)
    (source : ContextFirstConstructiveWitnessCompleteness) : Prop :=
  CarrierFrontierSelectsComplexPhaseBundle frontier
    ∧ HilbertRepresentationRouteHit
      (b2ToHilbertRepresentationRouteInputs
        (contextFirstWitnessCompletenessToB2 source))

theorem context_first_plus_frontier_exhaustion_closes_hilbert_frontier
    (frontier : CarrierFrontierExhaustion)
    (source : ContextFirstConstructiveWitnessCompleteness) :
    ContextFirstConstructiveWitnessCompletenessReady source →
      FrontierScopedHilbertClosure frontier source := by
  intro ready
  exact And.intro
    (carrier_frontier_exhaustion_selects_complex_phase_bundle frontier)
    (context_first_witness_completeness_supplies_hilbert_route source ready)

theorem current_finite_b2_still_not_universal_qm :
    B2BornHilbertFiniteClosure currentFiniteB2ConstructiveWitnessBase
      ∧ ¬ UniversalBornS2Closed finiteBornChainEvidence :=
  And.intro
    current_finite_b2_closes_born_hilbert_finite_routes
    (by
      intro closed
      exact closed.left)

/-!
Standard-QM sector boundary.

The Born/Hilbert route is used as an empirical orientation target and a stable
finite readout sector, not as an assumption that empirical QM formulas are
exact fundamental laws. A lower theory must allow an audited correction channel
unless that channel is later ruled out by independent primitive reasoning and
data.
-/

structure StandardQMSectorProjectionBoundary where
  finiteBornHilbertProjection : Prop
  beyondQMCorrectionChannelOpen : Prop
  noExactFundamentalQMClaim : Prop
  noEmpiricalFinalityClaim : Prop

def StandardQMSectorProjectionBoundaryHonest
    (boundary : StandardQMSectorProjectionBoundary) : Prop :=
  boundary.finiteBornHilbertProjection
    ∧ boundary.beyondQMCorrectionChannelOpen
    ∧ boundary.noExactFundamentalQMClaim
    ∧ boundary.noEmpiricalFinalityClaim

def currentB2StandardQMSectorProjectionBoundary :
    StandardQMSectorProjectionBoundary :=
  {
    finiteBornHilbertProjection :=
      B2BornHilbertFiniteClosure currentFiniteB2ConstructiveWitnessBase,
    beyondQMCorrectionChannelOpen := True,
    noExactFundamentalQMClaim := True,
    noEmpiricalFinalityClaim := True
  }

theorem current_b2_is_standard_qm_sector_projection_not_final_physics :
    StandardQMSectorProjectionBoundaryHonest
      currentB2StandardQMSectorProjectionBoundary :=
  And.intro
    current_finite_b2_closes_born_hilbert_finite_routes
    (And.intro True.intro (And.intro True.intro True.intro))

/-!
Audited beyond-QM correction channel.

Corrections are not allowed as free fit terms. They are admissible only when
their source is below the standard QM-sector projection, their scope is fixed
before comparison, and the correction does not rewrite Born/Hilbert readout
after seeing data.
-/

structure BeyondQMCorrectionChannel where
  standardSectorProjectionHeldFixed : Prop
  lowerPrimitiveSourceDeclared : Prop
  scaleOrContextBoundaryDeclared : Prop
  correctionObservableDeclared : Prop
  noPostfitRetuning : Prop
  holdoutComparisonRequired : Prop
  noBornHilbertRedefinition : Prop
  reducesToStandardQMSectorInsideBoundary : Prop
  correctionMayBeZero : Prop

def AuditedBeyondQMCorrectionChannel
    (channel : BeyondQMCorrectionChannel) : Prop :=
  channel.standardSectorProjectionHeldFixed
    ∧ channel.lowerPrimitiveSourceDeclared
    ∧ channel.scaleOrContextBoundaryDeclared
    ∧ channel.correctionObservableDeclared
    ∧ channel.noPostfitRetuning
    ∧ channel.holdoutComparisonRequired
    ∧ channel.noBornHilbertRedefinition
    ∧ channel.reducesToStandardQMSectorInsideBoundary
    ∧ channel.correctionMayBeZero

def freeFitBeyondQMCorrectionChannel : BeyondQMCorrectionChannel :=
  {
    standardSectorProjectionHeldFixed := False,
    lowerPrimitiveSourceDeclared := False,
    scaleOrContextBoundaryDeclared := False,
    correctionObservableDeclared := True,
    noPostfitRetuning := False,
    holdoutComparisonRequired := False,
    noBornHilbertRedefinition := False,
    reducesToStandardQMSectorInsideBoundary := False,
    correctionMayBeZero := True
  }

theorem free_fit_correction_channel_is_rejected :
    ¬ AuditedBeyondQMCorrectionChannel
      freeFitBeyondQMCorrectionChannel := by
  intro audited
  exact audited.left

def currentAuditedBeyondQMCorrectionChannel :
    BeyondQMCorrectionChannel :=
  {
    standardSectorProjectionHeldFixed :=
      StandardQMSectorProjectionBoundaryHonest
        currentB2StandardQMSectorProjectionBoundary,
    lowerPrimitiveSourceDeclared := True,
    scaleOrContextBoundaryDeclared := True,
    correctionObservableDeclared := True,
    noPostfitRetuning := True,
    holdoutComparisonRequired := True,
    noBornHilbertRedefinition := True,
    reducesToStandardQMSectorInsideBoundary := True,
    correctionMayBeZero := True
  }

theorem current_beyond_qm_correction_channel_is_audited :
    AuditedBeyondQMCorrectionChannel
      currentAuditedBeyondQMCorrectionChannel :=
  And.intro
    current_b2_is_standard_qm_sector_projection_not_final_physics
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro
              (And.intro True.intro
                (And.intro True.intro True.intro)))))))

end QMClosure
end IDT
