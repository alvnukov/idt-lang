import Proofs.QMClosure.B1CGSCClauseDerivation
import Proofs.QMClosure.ConstructiveWitnessPrimitiveBase

namespace IDT
namespace QMClosure

/-!
Full finite standard-QM sector closure.

This file is the current wide closure pass. It deliberately does not prove
exact fundamental QM from the lowest primitive base. It proves the strongest
checked sector statement now available:

  B1 CGSC derivation
  + context-first constructive witness completeness
  + carrier-frontier exhaustion
  => finite standard-QM sector closure for the current obligation surface.

The remaining universal wall is explicit: derive the successor/base inputs
and carrier-frontier exhaustion from the lower primitive base, or exhibit a
constructive non-QM countermodel.
-/

structure FullFiniteStandardQMSectorStatus where
  fullQmObligationBundle : Prop
  importBoundaries : Prop
  bornHilbertFiniteRoutes : Prop
  hilbertFrontierClosure : Prop
  semanticContentScaffolds : Prop

def FullFiniteStandardQMSectorClosed
    (status : FullFiniteStandardQMSectorStatus) : Prop :=
  status.fullQmObligationBundle
    ∧ status.importBoundaries
    ∧ status.bornHilbertFiniteRoutes
    ∧ status.hilbertFrontierClosure
    ∧ status.semanticContentScaffolds

def b1ContextFirstFrontierSectorStatus
    (base : B1PrimitiveBase)
    (source : ContextFirstConstructiveWitnessCompleteness)
    (frontier : CarrierFrontierExhaustion) :
    FullFiniteStandardQMSectorStatus :=
  {
    fullQmObligationBundle :=
      FullQMObligationBundle
        (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))),
    importBoundaries :=
      (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noSpectralImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noBornImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noHilbertImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noUnitaryImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noStoneImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noGeneratorImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noTensorImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noBornImport.statement
        ∧ (semanticKernelToPackageClosure
          (contextGeneratedStableClosureFromB1SemanticKernel
            (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noHilbertImport.statement,
    bornHilbertFiniteRoutes :=
      B2BornHilbertFiniteClosure
        (contextFirstWitnessCompletenessToB2 source),
    hilbertFrontierClosure :=
      FrontierScopedHilbertClosure frontier source,
    semanticContentScaffolds :=
      qmSemanticContentScaffoldCoverage.conservativeProjectiveGluingScaffold
        ∧ qmSemanticContentScaffoldCoverage.readoutProbabilityScaffold
        ∧ qmSemanticContentScaffoldCoverage.inheritanceActionScaffold
        ∧ qmSemanticContentScaffoldCoverage.productLocalTomographyScaffold
        ∧ qmSemanticContentScaffoldCoverage.monoidalAssociativityScaffold
        ∧ qmSemanticContentScaffoldCoverage.projectiveLimitConsistencyScaffold
        ∧ qmSemanticContentScaffoldCoverage.calibratedScaleBoundaryScaffold
  }

theorem b1_context_first_frontier_closes_full_finite_standard_qm_sector
    (base : B1PrimitiveBase)
    (source : ContextFirstConstructiveWitnessCompleteness)
    (frontier : CarrierFrontierExhaustion) :
    ContextFirstConstructiveWitnessCompletenessReady source →
      FullFiniteStandardQMSectorClosed
        (b1ContextFirstFrontierSectorStatus base source frontier) := by
  intro sourceReady
  exact And.intro
    (b1_cgsc_clause_derivation_yields_full_qm_obligation_bundle base)
    (And.intro
      (b1_cgsc_clause_derivation_preserves_import_boundaries base)
      (And.intro
        (b2_constructive_witness_base_closes_born_hilbert_finite_routes
          (contextFirstWitnessCompletenessToB2 source)
          (context_first_witness_completeness_promotes_to_b2_ready
            source
            sourceReady))
        (And.intro
          (context_first_plus_frontier_exhaustion_closes_hilbert_frontier
            frontier
            source
            sourceReady)
          qm_semantic_content_scaffold_bundle_is_machine_checked)))

structure ExactFundamentalQMClosureStatus where
  finiteSectorClosed : Prop
  lowerBaseDerivesB1 : Prop
  lowerBaseDerivesContextFirstWitnessCompleteness : Prop
  lowerBaseDerivesCarrierFrontierExhaustion : Prop
  externalHilbertBornUnitaryTensorAdequacy : Prop
  exactUniversalBornReadout : Prop
  firstPrinciplesPhysicalPhaseScale : Prop

def ExactFundamentalQMClosed
    (status : ExactFundamentalQMClosureStatus) : Prop :=
  status.finiteSectorClosed
    ∧ status.lowerBaseDerivesB1
    ∧ status.lowerBaseDerivesContextFirstWitnessCompleteness
    ∧ status.lowerBaseDerivesCarrierFrontierExhaustion
    ∧ status.externalHilbertBornUnitaryTensorAdequacy
    ∧ status.exactUniversalBornReadout
    ∧ status.firstPrinciplesPhysicalPhaseScale

structure ExactFundamentalQMClosureContract where
  lowerBaseDerivesB1 : Prop
  lowerBaseDerivesContextFirstWitnessCompleteness : Prop
  lowerBaseDerivesCarrierFrontierExhaustion : Prop
  externalHilbertBornUnitaryTensorAdequacy : Prop
  exactUniversalBornReadout : Prop
  firstPrinciplesPhysicalPhaseScale : Prop

def ExactFundamentalQMClosureContractReady
    (contract : ExactFundamentalQMClosureContract) : Prop :=
  contract.lowerBaseDerivesB1
    ∧ contract.lowerBaseDerivesContextFirstWitnessCompleteness
    ∧ contract.lowerBaseDerivesCarrierFrontierExhaustion
    ∧ contract.externalHilbertBornUnitaryTensorAdequacy
    ∧ contract.exactUniversalBornReadout
    ∧ contract.firstPrinciplesPhysicalPhaseScale

structure ExternalQMAdequacyTheorems where
  hilbertRepresentationAdequacy : Prop
  bornReadoutAdequacy : Prop
  unitaryDynamicsAdequacy : Prop
  tensorCompositeAdequacy : Prop

def ExternalHilbertBornUnitaryTensorAdequacyClosed
    (adequacy : ExternalQMAdequacyTheorems) : Prop :=
  adequacy.hilbertRepresentationAdequacy
    ∧ adequacy.bornReadoutAdequacy
    ∧ adequacy.unitaryDynamicsAdequacy
    ∧ adequacy.tensorCompositeAdequacy

theorem external_qm_adequacy_theorems_close_target_adequacy
    (adequacy : ExternalQMAdequacyTheorems) :
    adequacy.hilbertRepresentationAdequacy →
      adequacy.bornReadoutAdequacy →
        adequacy.unitaryDynamicsAdequacy →
          adequacy.tensorCompositeAdequacy →
            ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy := by
  intro hilbert born unitary tensor
  exact And.intro hilbert (And.intro born (And.intro unitary tensor))

def exactContractWithExternalAdequacy
    (contract : ExactFundamentalQMClosureContract)
    (adequacy : ExternalQMAdequacyTheorems) :
    ExactFundamentalQMClosureContract :=
  {
    contract with
    externalHilbertBornUnitaryTensorAdequacy :=
      ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy
  }

theorem exact_contract_with_external_adequacy_is_ready
    (contract : ExactFundamentalQMClosureContract)
    (adequacy : ExternalQMAdequacyTheorems) :
    contract.lowerBaseDerivesB1 →
      contract.lowerBaseDerivesContextFirstWitnessCompleteness →
        contract.lowerBaseDerivesCarrierFrontierExhaustion →
          ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy →
            contract.exactUniversalBornReadout →
              contract.firstPrinciplesPhysicalPhaseScale →
                ExactFundamentalQMClosureContractReady
                  (exactContractWithExternalAdequacy contract adequacy) := by
  intro lowerB1 contextFirst carrierFrontier externalAdequacy
    exactBorn phaseScale
  exact And.intro lowerB1
    (And.intro contextFirst
      (And.intro carrierFrontier
        (And.intro externalAdequacy
          (And.intro exactBorn phaseScale))))

theorem external_qm_adequacy_requires_hilbert_representation
    (adequacy : ExternalQMAdequacyTheorems) :
    ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy →
      adequacy.hilbertRepresentationAdequacy :=
  fun closed => closed.left

theorem external_qm_adequacy_requires_born_readout
    (adequacy : ExternalQMAdequacyTheorems) :
    ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy →
      adequacy.bornReadoutAdequacy :=
  fun closed => closed.right.left

theorem external_qm_adequacy_requires_unitary_dynamics
    (adequacy : ExternalQMAdequacyTheorems) :
    ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy →
      adequacy.unitaryDynamicsAdequacy :=
  fun closed => closed.right.right.left

theorem external_qm_adequacy_requires_tensor_composite
    (adequacy : ExternalQMAdequacyTheorems) :
    ExternalHilbertBornUnitaryTensorAdequacyClosed adequacy →
      adequacy.tensorCompositeAdequacy :=
  fun closed => closed.right.right.right

def currentExternalQMAdequacyTheorems : ExternalQMAdequacyTheorems :=
  {
    hilbertRepresentationAdequacy := False,
    bornReadoutAdequacy := False,
    unitaryDynamicsAdequacy := False,
    tensorCompositeAdequacy := False
  }

theorem current_external_qm_adequacy_theorems_not_closed :
    ¬ ExternalHilbertBornUnitaryTensorAdequacyClosed
      currentExternalQMAdequacyTheorems := by
  intro closed
  exact closed.left

def exactFundamentalQMStatusFromSectorAndContract
    (sector : FullFiniteStandardQMSectorStatus)
    (contract : ExactFundamentalQMClosureContract) :
    ExactFundamentalQMClosureStatus :=
  {
    finiteSectorClosed := FullFiniteStandardQMSectorClosed sector,
    lowerBaseDerivesB1 := contract.lowerBaseDerivesB1,
    lowerBaseDerivesContextFirstWitnessCompleteness :=
      contract.lowerBaseDerivesContextFirstWitnessCompleteness,
    lowerBaseDerivesCarrierFrontierExhaustion :=
      contract.lowerBaseDerivesCarrierFrontierExhaustion,
    externalHilbertBornUnitaryTensorAdequacy :=
      contract.externalHilbertBornUnitaryTensorAdequacy,
    exactUniversalBornReadout := contract.exactUniversalBornReadout,
    firstPrinciplesPhysicalPhaseScale :=
      contract.firstPrinciplesPhysicalPhaseScale
  }

theorem full_finite_sector_plus_exact_contract_closes_exact_fundamental_qm
    (sector : FullFiniteStandardQMSectorStatus)
    (contract : ExactFundamentalQMClosureContract) :
    FullFiniteStandardQMSectorClosed sector →
      ExactFundamentalQMClosureContractReady contract →
        ExactFundamentalQMClosed
          (exactFundamentalQMStatusFromSectorAndContract sector contract) := by
  intro sectorClosed contractReady
  rcases contractReady with
    ⟨lowerB1, contextFirst, carrierFrontier, externalAdequacy,
      exactBorn, phaseScale⟩
  exact And.intro sectorClosed
    (And.intro lowerB1
      (And.intro contextFirst
        (And.intro carrierFrontier
          (And.intro externalAdequacy
            (And.intro exactBorn phaseScale)))))

theorem exact_fundamental_qm_requires_finite_sector
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status → status.finiteSectorClosed :=
  fun closed => closed.left

theorem exact_fundamental_qm_requires_lower_base_derives_b1
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status → status.lowerBaseDerivesB1 :=
  fun closed => closed.right.left

theorem exact_fundamental_qm_requires_context_first_witness_completeness
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status →
      status.lowerBaseDerivesContextFirstWitnessCompleteness :=
  fun closed => closed.right.right.left

theorem exact_fundamental_qm_requires_carrier_frontier_exhaustion
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status →
      status.lowerBaseDerivesCarrierFrontierExhaustion :=
  fun closed => closed.right.right.right.left

theorem exact_fundamental_qm_requires_external_target_adequacy
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status →
      status.externalHilbertBornUnitaryTensorAdequacy :=
  fun closed => closed.right.right.right.right.left

theorem exact_fundamental_qm_requires_exact_universal_born
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status → status.exactUniversalBornReadout :=
  fun closed => closed.right.right.right.right.right.left

theorem exact_fundamental_qm_requires_first_principles_phase_scale
    (status : ExactFundamentalQMClosureStatus) :
    ExactFundamentalQMClosed status →
      status.firstPrinciplesPhysicalPhaseScale :=
  fun closed => closed.right.right.right.right.right.right

theorem missing_lower_base_b1_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.lowerBaseDerivesB1 → ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing (exact_fundamental_qm_requires_lower_base_derives_b1 status closed)

theorem missing_context_first_witness_completeness_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.lowerBaseDerivesContextFirstWitnessCompleteness →
      ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing
      (exact_fundamental_qm_requires_context_first_witness_completeness
        status
        closed)

theorem missing_carrier_frontier_exhaustion_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.lowerBaseDerivesCarrierFrontierExhaustion →
      ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing
      (exact_fundamental_qm_requires_carrier_frontier_exhaustion
        status
        closed)

theorem missing_external_target_adequacy_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.externalHilbertBornUnitaryTensorAdequacy →
      ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing
      (exact_fundamental_qm_requires_external_target_adequacy
        status
        closed)

theorem missing_exact_universal_born_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.exactUniversalBornReadout →
      ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing
      (exact_fundamental_qm_requires_exact_universal_born status closed)

theorem missing_first_principles_phase_scale_blocks_exact_fundamental_qm
    (status : ExactFundamentalQMClosureStatus) :
    ¬ status.firstPrinciplesPhysicalPhaseScale →
      ¬ ExactFundamentalQMClosed status :=
  fun missing closed =>
    missing
      (exact_fundamental_qm_requires_first_principles_phase_scale
        status
        closed)

def currentExactFundamentalQMClosureStatus
    (base : B1PrimitiveBase)
    (source : ContextFirstConstructiveWitnessCompleteness)
    (frontier : CarrierFrontierExhaustion) :
    ExactFundamentalQMClosureStatus :=
  {
    finiteSectorClosed :=
      FullFiniteStandardQMSectorClosed
        (b1ContextFirstFrontierSectorStatus base source frontier),
    lowerBaseDerivesB1 := False,
    lowerBaseDerivesContextFirstWitnessCompleteness := False,
    lowerBaseDerivesCarrierFrontierExhaustion := False,
    externalHilbertBornUnitaryTensorAdequacy := False,
    exactUniversalBornReadout := False,
    firstPrinciplesPhysicalPhaseScale := False
  }

theorem current_full_qm_sector_closure_is_not_exact_fundamental_qm
    (base : B1PrimitiveBase)
    (source : ContextFirstConstructiveWitnessCompleteness)
    (frontier : CarrierFrontierExhaustion) :
    ¬ ExactFundamentalQMClosed
      (currentExactFundamentalQMClosureStatus base source frontier) := by
  intro closed
  exact closed.right.left

end QMClosure
end IDT
