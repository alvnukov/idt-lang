import Proofs.QMClosure.ConstructiveWitnessPrimitiveBase
import Proofs.QMClosure.PrimitiveBoundaryQMChain
import Proofs.QMClosure.S2BornProofSearch

namespace IDT
namespace QMClosure

/-!
Universal Born/Hilbert frontier closure.

This file does not prove exact QM from B0. It records the strongest honest
closure currently available: if a context-stable pairwise actualization source
is supplied for all admissible readout contexts, and the admissible carrier
frontier is exhausted by the known finite screens, then the exact universal
Born-readout contract and the frontier-scoped Hilbert representation route close
together.

The current finite B2 route remains insufficient by itself. The missing lower
work is to derive the context-stable pairwise actualization source and carrier
frontier exhaustion from B0 or a successor primitive base without importing the
Born rule or complex Hilbert space.
-/

structure UniversalOrientedBornContextFamily (context : Type) where
  cover : context → OrientedTwoCoverCounts
  labels : context → OrientedReadoutBranchLabels
  constructorRespecting :
    ∀ ctx : context, ConstructorRespectingBranchLabels (labels ctx)

structure UniversalEndpointStableBornContextFamily (context : Type) where
  cover : context → OrientedTwoCoverCounts
  labels : context → OrientedReadoutBranchLabels
  endpointStable :
    ∀ ctx : context, EndpointStableBinaryBranchLabels (labels ctx)

def endpointStableFamilyToConstructorRespectingFamily
    {context : Type}
    (family : UniversalEndpointStableBornContextFamily context) :
    UniversalOrientedBornContextFamily context :=
  {
    cover := family.cover,
    labels := family.labels,
    constructorRespecting := fun ctx =>
      endpoint_stable_binary_labels_are_constructor_respecting
        (family.labels ctx)
        (family.endpointStable ctx)
  }

def universalOrientedBornReadout
    {context : Type}
    (family : UniversalOrientedBornContextFamily context)
    (ctx : context) : BornYesNoCounts :=
  branchLabelsToBornReadout
    (family.cover ctx)
    (family.labels ctx)

def UniversalOrientedBornReadoutSelectsPhaseSquare
    {context : Type}
    (family : UniversalOrientedBornContextFamily context) : Prop :=
  ∀ ctx : context,
    (universalOrientedBornReadout family ctx).yes =
      (orientedTwoCoverToPhaseCounts (family.cover ctx)).amplitudeSquare

theorem universal_constructor_respecting_oriented_contexts_select_born_square
    {context : Type}
    (family : UniversalOrientedBornContextFamily context) :
    UniversalOrientedBornReadoutSelectsPhaseSquare family := by
  intro ctx
  exact constructor_respecting_oriented_readout_selects_phase_square
    (family.cover ctx)
    (family.labels ctx)
    (family.constructorRespecting ctx)

def UniversalOrientedBornReadoutIsAffineSigned
    {context : Type}
    (family : UniversalOrientedBornContextFamily context) : Prop :=
  ∀ ctx : context,
    2 * (universalOrientedBornReadout family ctx).yes =
      orientedTwoCoverTotal (family.cover ctx)
        + orientedTwoCoverSigned (family.cover ctx)

theorem universal_constructor_respecting_oriented_contexts_are_affine_signed
    {context : Type}
    (family : UniversalOrientedBornContextFamily context) :
    UniversalOrientedBornReadoutIsAffineSigned family := by
  intro ctx
  exact constructor_respecting_oriented_readout_forces_born_count
    (family.cover ctx)
    (family.labels ctx)
    (family.constructorRespecting ctx)

structure UniversalOrientedBornContextClosure where
  Context : Type
  family : UniversalOrientedBornContextFamily Context

def UniversalOrientedBornContextClosureSelectsBorn
    (closure : UniversalOrientedBornContextClosure) : Prop :=
  UniversalOrientedBornReadoutSelectsPhaseSquare closure.family
    ∧ UniversalOrientedBornReadoutIsAffineSigned closure.family

theorem universal_oriented_context_closure_selects_born
    (closure : UniversalOrientedBornContextClosure) :
    UniversalOrientedBornContextClosureSelectsBorn closure :=
  And.intro
    (universal_constructor_respecting_oriented_contexts_select_born_square
      closure.family)
    (universal_constructor_respecting_oriented_contexts_are_affine_signed
      closure.family)

structure UniversalEndpointStableBornContextClosure where
  Context : Type
  family : UniversalEndpointStableBornContextFamily Context

def endpointStableClosureToOrientedClosure
    (closure : UniversalEndpointStableBornContextClosure) :
    UniversalOrientedBornContextClosure :=
  {
    Context := closure.Context,
    family := endpointStableFamilyToConstructorRespectingFamily
      closure.family
  }

theorem universal_endpoint_stable_context_closure_selects_born
    (closure : UniversalEndpointStableBornContextClosure) :
    UniversalOrientedBornContextClosureSelectsBorn
      (endpointStableClosureToOrientedClosure closure) :=
  universal_oriented_context_closure_selects_born
    (endpointStableClosureToOrientedClosure closure)

structure UniversalPrimitivePairwiseEndpointCoverage (context : Type) where
  cover : context → OrientedTwoCoverCounts
  labels : context → OrientedReadoutBranchLabels
  discipline : context → PrimitiveBaseWitnessDiscipline
  pairwiseBasis : ∀ ctx : context, PairwiseWitnessBasis (discipline ctx)
  endpointAligned : ∀ ctx : context, (labels ctx).yesBranch = aligned
  binaryExclusive :
    ∀ ctx : context, (labels ctx).yesBranch ≠ (labels ctx).noBranch

def primitivePairwiseEndpointCoverageToEndpointStableFamily
    {context : Type}
    (coverage : UniversalPrimitivePairwiseEndpointCoverage context) :
    UniversalEndpointStableBornContextFamily context :=
  {
    cover := coverage.cover,
    labels := coverage.labels,
    endpointStable := fun ctx =>
      And.intro
        (coverage.endpointAligned ctx)
        (coverage.binaryExclusive ctx)
  }

theorem primitive_pairwise_endpoint_coverage_blocks_ternary_witness
    {context : Type}
    (coverage : UniversalPrimitivePairwiseEndpointCoverage context)
    (ctx : context) :
    ¬ (coverage.discipline ctx).ternaryWitness :=
  proper_subcontext_basis_blocks_local_ternary_witness
    (coverage.discipline ctx)
    (coverage.pairwiseBasis ctx)

theorem primitive_pairwise_endpoint_coverage_selects_born
    {context : Type}
    (coverage : UniversalPrimitivePairwiseEndpointCoverage context) :
    UniversalOrientedBornContextClosureSelectsBorn
      (endpointStableClosureToOrientedClosure
        {
          Context := context,
          family :=
            primitivePairwiseEndpointCoverageToEndpointStableFamily
              coverage
        }) :=
  universal_endpoint_stable_context_closure_selects_born
    {
      Context := context,
      family :=
        primitivePairwiseEndpointCoverageToEndpointStableFamily
          coverage
    }

def PrimitivePairwiseEndpointCoverageForDiscipline
    (discipline : PrimitiveBaseWitnessDiscipline)
    (labels : OrientedReadoutBranchLabels) : Prop :=
  PairwiseWitnessBasis discipline ∧ EndpointStableBinaryBranchLabels labels

def endpointStableToyLabels : OrientedReadoutBranchLabels :=
  {
    yesBranch := OrientedReadoutBranch.aligned,
    noBranch := OrientedReadoutBranch.opposed
  }

theorem endpoint_stable_toy_labels_are_endpoint_stable :
    EndpointStableBinaryBranchLabels endpointStableToyLabels := by
  simp [
    EndpointStableBinaryBranchLabels,
    endpointStableToyLabels,
  ]

theorem primitive_pairwise_endpoint_coverage_requires_pairwise_basis
    (discipline : PrimitiveBaseWitnessDiscipline)
    (labels : OrientedReadoutBranchLabels) :
    PrimitivePairwiseEndpointCoverageForDiscipline discipline labels →
      PairwiseWitnessBasis discipline :=
  fun coverage => coverage.left

theorem current_primitive_discipline_does_not_force_primitive_pairwise_endpoint_coverage :
    ∃ discipline : PrimitiveBaseWitnessDiscipline,
      ∃ labels : OrientedReadoutBranchLabels,
        CurrentPrimitiveBaseDiscipline discipline
          ∧ ¬ PrimitivePairwiseEndpointCoverageForDiscipline
            discipline
            labels :=
  Exists.intro localTernaryPrimitiveDiscipline
    (Exists.intro endpointStableToyLabels
      (And.intro
        local_ternary_witness_satisfies_current_primitive_discipline
        (by
          intro coverage
          exact local_ternary_witness_refutes_pairwise_basis
            (primitive_pairwise_endpoint_coverage_requires_pairwise_basis
              localTernaryPrimitiveDiscipline
              endpointStableToyLabels
              coverage))))

def primitiveBoundaryGeneratedDiscipline
    (candidate : PrimitiveBoundaryCandidate) :
    PrimitiveBaseWitnessDiscipline :=
  {
    constructorGenerated := candidate.b1BoundInterface,
    noPrimitiveGlobalFactTable := candidate.noTargetImports,
    localReadoutWitness := candidate.normalizedOverlapUniqueness,
    lossAccountingRoute := candidate.compatibleKernelAdditivity,
    properSubcontextBasis := candidate.properSubcontextPairwiseCoverage,
    ternaryWitness := False,
    stableI3Nonzero := False
  }

theorem primitive_boundary_pairwise_closure_supplies_pairwise_basis
    (candidate : PrimitiveBoundaryCandidate) :
    PrimitiveBoundaryClosesPairwiseCoverage candidate →
      PairwiseWitnessBasis
        (primitiveBoundaryGeneratedDiscipline candidate) := by
  intro pairwiseClosed
  exact And.intro pairwiseClosed.left (by intro ternary; exact ternary)

structure UniversalPrimitiveBoundaryEndpointCoverage (context : Type) where
  cover : context → OrientedTwoCoverCounts
  labels : context → OrientedReadoutBranchLabels
  boundary : context → PrimitiveBoundaryCandidate
  pairwiseClosed :
    ∀ ctx : context,
      PrimitiveBoundaryClosesPairwiseCoverage (boundary ctx)
  endpointAligned : ∀ ctx : context, (labels ctx).yesBranch = aligned
  binaryExclusive :
    ∀ ctx : context, (labels ctx).yesBranch ≠ (labels ctx).noBranch

def primitiveBoundaryEndpointCoverageToPairwiseEndpointCoverage
    {context : Type}
    (coverage : UniversalPrimitiveBoundaryEndpointCoverage context) :
    UniversalPrimitivePairwiseEndpointCoverage context :=
  {
    cover := coverage.cover,
    labels := coverage.labels,
    discipline := fun ctx =>
      primitiveBoundaryGeneratedDiscipline (coverage.boundary ctx),
    pairwiseBasis := fun ctx =>
      primitive_boundary_pairwise_closure_supplies_pairwise_basis
        (coverage.boundary ctx)
        (coverage.pairwiseClosed ctx),
    endpointAligned := coverage.endpointAligned,
    binaryExclusive := coverage.binaryExclusive
  }

theorem primitive_boundary_endpoint_coverage_selects_born
    {context : Type}
    (coverage : UniversalPrimitiveBoundaryEndpointCoverage context) :
    UniversalOrientedBornContextClosureSelectsBorn
      (endpointStableClosureToOrientedClosure
        {
          Context := context,
          family :=
            primitivePairwiseEndpointCoverageToEndpointStableFamily
              (primitiveBoundaryEndpointCoverageToPairwiseEndpointCoverage
                coverage)
        }) :=
  primitive_pairwise_endpoint_coverage_selects_born
    (primitiveBoundaryEndpointCoverageToPairwiseEndpointCoverage coverage)

structure ContextFirstUniversalEndpointData (context : Type) where
  source : ContextFirstConstructiveWitnessCompleteness
  ready : ContextFirstConstructiveWitnessCompletenessReady source
  cover : context → OrientedTwoCoverCounts
  labels : context → OrientedReadoutBranchLabels
  endpointAligned : ∀ ctx : context, (labels ctx).yesBranch = aligned
  binaryExclusive :
    ∀ ctx : context, (labels ctx).yesBranch ≠ (labels ctx).noBranch

def contextFirstEndpointDataToPrimitiveBoundaryEndpointCoverage
    {context : Type}
    (data : ContextFirstUniversalEndpointData context) :
    UniversalPrimitiveBoundaryEndpointCoverage context :=
  {
    cover := data.cover,
    labels := data.labels,
    boundary := fun _ =>
      b2ToPrimitiveBoundaryCandidate
        (contextFirstWitnessCompletenessToB2 data.source),
    pairwiseClosed := fun _ =>
      (context_first_witness_completeness_promotes_to_b2_ready
        data.source
        data.ready).left.right,
    endpointAligned := data.endpointAligned,
    binaryExclusive := data.binaryExclusive
  }

def ContextFirstEndpointBornClosure
    {context : Type}
    (data : ContextFirstUniversalEndpointData context) : Prop :=
  UniversalOrientedBornContextClosureSelectsBorn
    (endpointStableClosureToOrientedClosure
      {
        Context := context,
        family :=
          primitivePairwiseEndpointCoverageToEndpointStableFamily
            (primitiveBoundaryEndpointCoverageToPairwiseEndpointCoverage
              (contextFirstEndpointDataToPrimitiveBoundaryEndpointCoverage
                data))
      })

theorem context_first_endpoint_data_selects_born
    {context : Type}
    (data : ContextFirstUniversalEndpointData context) :
    ContextFirstEndpointBornClosure data :=
  primitive_boundary_endpoint_coverage_selects_born
    (contextFirstEndpointDataToPrimitiveBoundaryEndpointCoverage data)

def ContextFirstEndpointBornHilbertFrontierClosure
    {context : Type}
    (data : ContextFirstUniversalEndpointData context)
    (frontier : CarrierFrontierExhaustion) : Prop :=
  ContextFirstEndpointBornClosure data
    ∧ FrontierScopedHilbertClosure frontier data.source

theorem context_first_endpoint_data_plus_frontier_closes_born_hilbert
    {context : Type}
    (data : ContextFirstUniversalEndpointData context)
    (frontier : CarrierFrontierExhaustion) :
    ContextFirstEndpointBornHilbertFrontierClosure data frontier :=
  And.intro
    (context_first_endpoint_data_selects_born data)
    (context_first_plus_frontier_exhaustion_closes_hilbert_frontier
      frontier
      data.source
      data.ready)

theorem context_first_ready_requires_external_frequency
    (source : ContextFirstConstructiveWitnessCompleteness) :
    ContextFirstConstructiveWitnessCompletenessReady source →
      source.externalFrequencyWitness := by
  intro ready
  rcases ready with
    ⟨_contextGenerated, _noTarget, _additiveKernel, _uniqueOverlap,
      _twoCover, _constructorLabels, _pairwiseCoverage,
      _noHiddenHigherOrder, _signedReadout, _complementReadout,
      _endpointStability, _unbiasedIndifference, externalFrequency,
      _phaseCarrier, _localTomography, _exposedContext,
      _reversibleSymmetry, _constructiveCarrier, _noHiddenJoint,
      _noBorn, _noHilbert, _noTensor⟩
  exact externalFrequency

def b1OnlyMissingContextFirstSource :
    ContextFirstConstructiveWitnessCompleteness :=
  {
    contextGeneratedSourceBoundary := True,
    noTargetImports := True,
    additiveInheritanceKernel := True,
    uniqueNormalizedDistinguishability := True,
    orientedTwoCoverWitness := True,
    constructorRespectingBranchLabelsWitness := True,
    pairwiseSubcontextCoverage := True,
    noHiddenHigherOrderFact := True,
    signedReadoutWitness := True,
    complementReadoutWitness := True,
    endpointStabilityWitness := True,
    unbiasedIndifferenceWitness := True,
    externalFrequencyWitness := False,
    phaseOrientationCarrierWitness := True,
    localTomographyWitness := True,
    exposedContextDecompositionWitness := True,
    reversibleRouteSymmetryWitness := True,
    constructiveCarrierWitness := False,
    noHiddenJointOnlyGeneration := False,
    noBornImport := True,
    noHilbertImport := True,
    noTensorImport := True
  }

theorem b1_interface_projection_does_not_force_context_first_endpoint_data :
    B1InterfaceProjection b1OnlyMissingConstructiveWitnessBase
      ∧ ¬ ContextFirstConstructiveWitnessCompletenessReady
        b1OnlyMissingContextFirstSource :=
  And.intro
    (And.intro True.intro True.intro)
    (by
      intro ready
      exact context_first_ready_requires_external_frequency
        b1OnlyMissingContextFirstSource
        ready)

structure ContextStablePairwiseActualization where
  finiteDirectBornRoute : Prop
  allAdmissibleContextsCloseFiniteBornChain : Prop
  universalSignedReadout : Prop
  universalConstructorRespectingBranchLabels : Prop
  universalPhaseDoubleCover : Prop
  noPrimitiveHigherOrderFacticization : Prop
  probabilityAccountingIsOnlyReadout : Prop
  noBornImport : Prop
  normalizedOverlapOnly : Prop
  productCompositionMultiplicative : Prop
  binaryComplementNormalization : Prop
  stableRefinementRegularity : Prop

def ContextStablePairwiseActualizationReady
    (source : ContextStablePairwiseActualization) : Prop :=
  source.finiteDirectBornRoute
    ∧ source.allAdmissibleContextsCloseFiniteBornChain
    ∧ source.universalSignedReadout
    ∧ source.universalConstructorRespectingBranchLabels
    ∧ source.universalPhaseDoubleCover
    ∧ source.noPrimitiveHigherOrderFacticization
    ∧ source.probabilityAccountingIsOnlyReadout
    ∧ source.noBornImport
    ∧ source.normalizedOverlapOnly
    ∧ source.productCompositionMultiplicative
    ∧ source.binaryComplementNormalization
    ∧ source.stableRefinementRegularity

def contextStablePairwiseActualizationToUniversalBornContract
    (source : ContextStablePairwiseActualization) :
    UniversalBornReadoutContract :=
  {
    finiteDirectBornRoute := source.finiteDirectBornRoute,
    allAdmissibleContextsCloseFiniteBornChain :=
      source.allAdmissibleContextsCloseFiniteBornChain,
    universalSignedReadout := source.universalSignedReadout,
    universalConstructorRespectingBranchLabels :=
      source.universalConstructorRespectingBranchLabels,
    universalPhaseDoubleCover := source.universalPhaseDoubleCover,
    noPrimitiveHigherOrderFacticization :=
      source.noPrimitiveHigherOrderFacticization,
    probabilityAccountingIsOnlyReadout :=
      source.probabilityAccountingIsOnlyReadout,
    noBornImport := source.noBornImport
  }

def ContextStablePairwiseSelectorPayload
    (source : ContextStablePairwiseActualization) : Prop :=
  source.normalizedOverlapOnly
    ∧ source.productCompositionMultiplicative
    ∧ source.binaryComplementNormalization
    ∧ source.stableRefinementRegularity

theorem context_stable_pairwise_actualization_supplies_selector_payload
    (source : ContextStablePairwiseActualization) :
    ContextStablePairwiseActualizationReady source →
      ContextStablePairwiseSelectorPayload source := by
  intro ready
  rcases ready with
    ⟨_finiteRoute, _allContexts, _signedReadout, _constructorLabels,
      _phaseCover, _noHigherOrder, _probabilityBoundary, _noBornImport,
      normalizedOverlap, productComposition, binaryComplement,
      stableRefinement⟩
  exact And.intro normalizedOverlap
    (And.intro productComposition
      (And.intro binaryComplement stableRefinement))

theorem context_stable_pairwise_actualization_closes_exact_universal_born
    (source : ContextStablePairwiseActualization) :
    ContextStablePairwiseActualizationReady source →
      ExactUniversalBornReadoutClosed
        (contextStablePairwiseActualizationToUniversalBornContract source) := by
  intro ready
  rcases ready with
    ⟨finiteRoute, allContexts, signedReadout, constructorLabels,
      phaseCover, noHigherOrder, probabilityBoundary, noBornImport,
      _normalizedOverlap, _productComposition, _binaryComplement,
      _stableRefinement⟩
  exact universal_born_readout_contract_closes_exact_universal_born
    (contextStablePairwiseActualizationToUniversalBornContract source)
    finiteRoute
    allContexts
    signedReadout
    constructorLabels
    phaseCover
    noHigherOrder
    probabilityBoundary
    noBornImport

def UniversalBornHilbertFrontierClosure
    (actualization : ContextStablePairwiseActualization)
    (frontier : CarrierFrontierExhaustion)
    (witness : ContextFirstConstructiveWitnessCompleteness) : Prop :=
  ExactUniversalBornReadoutClosed
      (contextStablePairwiseActualizationToUniversalBornContract
        actualization)
    ∧ FrontierScopedHilbertClosure frontier witness

theorem context_stable_pairwise_actualization_plus_frontier_closes_universal_born_hilbert
    (actualization : ContextStablePairwiseActualization)
    (frontier : CarrierFrontierExhaustion)
    (witness : ContextFirstConstructiveWitnessCompleteness) :
    ContextStablePairwiseActualizationReady actualization →
      ContextFirstConstructiveWitnessCompletenessReady witness →
        UniversalBornHilbertFrontierClosure
          actualization
          frontier
          witness := by
  intro actualizationReady witnessReady
  exact And.intro
    (context_stable_pairwise_actualization_closes_exact_universal_born
      actualization
      actualizationReady)
    (context_first_plus_frontier_exhaustion_closes_hilbert_frontier
      frontier
      witness
      witnessReady)

structure CurrentUniversalBornHilbertClosureStatus where
  finiteBornHilbertRoute : Prop
  contextStablePairwiseActualizationDerived : Prop
  carrierFrontierExhausted : Prop

def UniversalBornHilbertClosedFromCurrentStatus
    (status : CurrentUniversalBornHilbertClosureStatus) : Prop :=
  status.contextStablePairwiseActualizationDerived
    ∧ status.carrierFrontierExhausted

def currentUniversalBornHilbertClosureStatus :
    CurrentUniversalBornHilbertClosureStatus :=
  {
    finiteBornHilbertRoute :=
      B2BornHilbertFiniteClosure currentFiniteB2ConstructiveWitnessBase,
    contextStablePairwiseActualizationDerived := False,
    carrierFrontierExhausted := False
  }

theorem current_finite_born_hilbert_route_does_not_close_universal_frontier :
    currentUniversalBornHilbertClosureStatus.finiteBornHilbertRoute
      ∧ ¬ UniversalBornHilbertClosedFromCurrentStatus
        currentUniversalBornHilbertClosureStatus :=
  And.intro
    current_finite_b2_closes_born_hilbert_finite_routes
    (by
      intro closed
      exact closed.left)

end QMClosure
end IDT
