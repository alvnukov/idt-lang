import Proofs.MetaLang.V8CurrentMigrationState

namespace IDT
namespace MetaLang
namespace V8

/-!
Current theorem-card and QM-obligation ledger.

This module migrates the current theorem-card and QM core obligation status
surface into Lean without upgrading any physical or QM claim to `formalProof`.
-/

inductive CurrentTheoremCardId where
  | contextProductExhaustionImpliesLocalTomography
  | realHilbertCompositeHiddenJointInvariant
  | purificationFilteringImpliesRecoverableSupportUpdate
  | recoverableSupportUpdateImpliesReversibleFilterClosure
  | boundedCorrelationScreenRejectsSuperquantumBoxes
  | noncomplexJordanSeparatorRejectsNoncomplexSamples
  | genericGptClosureRejectsUnconstrainedCone
  | finiteRouteCoverageReducesBroaderGenericGptCone
  | uniformRouteWitnessCompactnessClosesNonfiniteGptResidual
  | noEmergentJointOnlyInvariantsUnderContextProductExhaustion
  | finiteSignatureClosureImpliesUniformRouteWitnessBound
  | routeWitnessCompletenessImpliesTomographicStateEffectDuality
  | finiteBornQuadraticReadoutSurvivor
  | bornWallRequiresPositiveQuadraticActualizationPrinciple
  | universalCarrierSelectionTheorem
  | hilbertCarrierDerivation
  | universalBornRuleTheorem
  | wignerReversibleInheritanceTheorem
  | apparatusFacticityTheorem
  | monoidalTensorCompositionTheorem
  | firstPrinciplesHbarLock
  | fieldModeContinuumLimit
  | universalBornHilbertFrontierClosure
deriving DecidableEq, Repr

inductive CurrentProofStatus where
  | blocked
  | conditionalProof
  | finiteVerifierPass
  | open
deriving DecidableEq, Repr

def CurrentProofStatus.toClaimStatus : CurrentProofStatus → ClaimStatus
  | CurrentProofStatus.blocked => ClaimStatus.blocked
  | CurrentProofStatus.conditionalProof => ClaimStatus.conditionalProof
  | CurrentProofStatus.finiteVerifierPass => ClaimStatus.finiteVerifierPass
  | CurrentProofStatus.open => ClaimStatus.open

structure CurrentTheoremCardEntry where
  id : CurrentTheoremCardId
  role : TheoremCardRole
  status : CurrentProofStatus
deriving Repr

def currentTheoremCardLedger : List CurrentTheoremCardEntry :=
  [
    { id := .contextProductExhaustionImpliesLocalTomography, role := .theorem, status := .conditionalProof },
    { id := .realHilbertCompositeHiddenJointInvariant, role := .failure, status := .finiteVerifierPass },
    { id := .purificationFilteringImpliesRecoverableSupportUpdate, role := .theorem, status := .conditionalProof },
    { id := .recoverableSupportUpdateImpliesReversibleFilterClosure, role := .theorem, status := .conditionalProof },
    { id := .boundedCorrelationScreenRejectsSuperquantumBoxes, role := .theorem, status := .conditionalProof },
    { id := .noncomplexJordanSeparatorRejectsNoncomplexSamples, role := .theorem, status := .conditionalProof },
    { id := .genericGptClosureRejectsUnconstrainedCone, role := .theorem, status := .conditionalProof },
    { id := .finiteRouteCoverageReducesBroaderGenericGptCone, role := .theorem, status := .conditionalProof },
    { id := .uniformRouteWitnessCompactnessClosesNonfiniteGptResidual, role := .theorem, status := .conditionalProof },
    { id := .noEmergentJointOnlyInvariantsUnderContextProductExhaustion, role := .theorem, status := .conditionalProof },
    { id := .finiteSignatureClosureImpliesUniformRouteWitnessBound, role := .theorem, status := .conditionalProof },
    { id := .routeWitnessCompletenessImpliesTomographicStateEffectDuality, role := .theorem, status := .conditionalProof },
    { id := .finiteBornQuadraticReadoutSurvivor, role := .theorem, status := .conditionalProof },
    { id := .bornWallRequiresPositiveQuadraticActualizationPrinciple, role := .theorem, status := .conditionalProof },
    { id := .universalCarrierSelectionTheorem, role := .theorem, status := .open },
    { id := .hilbertCarrierDerivation, role := .theorem, status := .blocked },
    { id := .universalBornRuleTheorem, role := .theorem, status := .open },
    { id := .wignerReversibleInheritanceTheorem, role := .theorem, status := .open },
    { id := .apparatusFacticityTheorem, role := .theorem, status := .open },
    { id := .monoidalTensorCompositionTheorem, role := .theorem, status := .open },
    { id := .firstPrinciplesHbarLock, role := .theorem, status := .blocked },
    { id := .fieldModeContinuumLimit, role := .theorem, status := .open },
    { id := .universalBornHilbertFrontierClosure, role := .theorem, status := .conditionalProof }
  ]

def theoremCardStatusCount
    (status : CurrentProofStatus)
    (entries : List CurrentTheoremCardEntry) : Nat :=
  (entries.filter (fun entry => entry.status == status)).length

theorem current_theorem_card_ledger_count :
    currentTheoremCardLedger.length = 23 := by
  rfl

theorem current_theorem_card_conditional_count :
    theoremCardStatusCount .conditionalProof currentTheoremCardLedger = 14 := by
  rfl

theorem current_theorem_card_open_count :
    theoremCardStatusCount .open currentTheoremCardLedger = 6 := by
  rfl

theorem current_theorem_card_blocked_count :
    theoremCardStatusCount .blocked currentTheoremCardLedger = 2 := by
  rfl

theorem current_theorem_card_finite_pass_count :
    theoremCardStatusCount .finiteVerifierPass currentTheoremCardLedger = 1 := by
  rfl

def currentLedgerTheoremCardFormalProofCount : Nat := 0

theorem current_theorem_card_formal_proof_count_is_zero :
    currentLedgerTheoremCardFormalProofCount = 0 := by
  rfl

inductive CurrentQmObligationId where
  | finiteOperationalCore
  | probabilityMeasureLayer
  | distinguishabilityGeometry
  | productContextsSeparateStableFacts
  | hilbertCarrierDerivation
  | bornRuleDerivation
  | reversibleInheritanceSymmetry
  | measurementFacticityMechanism
  | tensorCompositionLaw
  | recompile35FromCore
  | continuumActionScaleExtension
deriving DecidableEq, Repr

inductive CurrentQmObligationStatus where
  | regressionSupported
  | target
  | derivedConditional
  | blocked
deriving DecidableEq, Repr

def CurrentQmObligationStatus.toClaimStatus :
    CurrentQmObligationStatus → ClaimStatus
  | CurrentQmObligationStatus.regressionSupported => ClaimStatus.finiteVerifierPass
  | CurrentQmObligationStatus.target => ClaimStatus.open
  | CurrentQmObligationStatus.derivedConditional => ClaimStatus.conditionalProof
  | CurrentQmObligationStatus.blocked => ClaimStatus.blocked

structure CurrentQmObligationEntry where
  id : CurrentQmObligationId
  status : CurrentQmObligationStatus
deriving Repr

def currentQmObligationLedger : List CurrentQmObligationEntry :=
  [
    { id := .finiteOperationalCore, status := .regressionSupported },
    { id := .probabilityMeasureLayer, status := .regressionSupported },
    { id := .distinguishabilityGeometry, status := .target },
    { id := .productContextsSeparateStableFacts, status := .derivedConditional },
    { id := .hilbertCarrierDerivation, status := .blocked },
    { id := .bornRuleDerivation, status := .blocked },
    { id := .reversibleInheritanceSymmetry, status := .regressionSupported },
    { id := .measurementFacticityMechanism, status := .regressionSupported },
    { id := .tensorCompositionLaw, status := .target },
    { id := .recompile35FromCore, status := .target },
    { id := .continuumActionScaleExtension, status := .blocked }
  ]

def qmObligationStatusCount
    (status : CurrentQmObligationStatus)
    (entries : List CurrentQmObligationEntry) : Nat :=
  (entries.filter (fun entry => entry.status == status)).length

theorem current_qm_obligation_ledger_count :
    currentQmObligationLedger.length = 11 := by
  rfl

theorem current_qm_obligation_regression_supported_count :
    qmObligationStatusCount .regressionSupported currentQmObligationLedger = 4 := by
  rfl

theorem current_qm_obligation_target_count :
    qmObligationStatusCount .target currentQmObligationLedger = 3 := by
  rfl

theorem current_qm_obligation_blocked_count :
    qmObligationStatusCount .blocked currentQmObligationLedger = 3 := by
  rfl

theorem current_qm_obligation_derived_conditional_count :
    qmObligationStatusCount .derivedConditional currentQmObligationLedger = 1 := by
  rfl

def currentLedgerQmObligationFormalProofCount : Nat := 0

theorem current_qm_obligation_formal_proof_count_is_zero :
    currentLedgerQmObligationFormalProofCount = 0 := by
  rfl

def hasBlockedOrOpenTheoremCards : Prop :=
  theoremCardStatusCount .blocked currentTheoremCardLedger
    + theoremCardStatusCount .open currentTheoremCardLedger > 0

def hasBlockedOrTargetQmObligations : Prop :=
  qmObligationStatusCount .blocked currentQmObligationLedger
    + qmObligationStatusCount .target currentQmObligationLedger > 0

theorem current_theorem_cards_have_blockers :
    hasBlockedOrOpenTheoremCards := by
  unfold hasBlockedOrOpenTheoremCards
  decide

theorem current_qm_obligations_have_blockers :
    hasBlockedOrTargetQmObligations := by
  unfold hasBlockedOrTargetQmObligations
  decide

end V8
end MetaLang
end IDT
