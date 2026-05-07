import Proofs.MetaLang.V8CurrentTheoremAndObligationLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
Theorem-card and QM-obligation dependency boundary ledger.

This module migrates dependency counts, forbidden-claim counts, open-gap
presence, and claim-boundary presence for the current public theorem cards and
QM core obligations. It keeps the migration at status/boundary level; it does
not upgrade any claim to physical or QM `formalProof`.
-/

structure TheoremCardBoundaryEntry where
  id : CurrentTheoremCardId
  dependencyCount : Nat
  forbiddenClaimCount : Nat
deriving Repr

def currentTheoremCardBoundaryLedger : List TheoremCardBoundaryEntry :=
  [
    { id := .contextProductExhaustionImpliesLocalTomography, dependencyCount := 5, forbiddenClaimCount := 4 },
    { id := .realHilbertCompositeHiddenJointInvariant, dependencyCount := 3, forbiddenClaimCount := 2 },
    { id := .purificationFilteringImpliesRecoverableSupportUpdate, dependencyCount := 2, forbiddenClaimCount := 4 },
    { id := .recoverableSupportUpdateImpliesReversibleFilterClosure, dependencyCount := 4, forbiddenClaimCount := 4 },
    { id := .boundedCorrelationScreenRejectsSuperquantumBoxes, dependencyCount := 3, forbiddenClaimCount := 4 },
    { id := .noncomplexJordanSeparatorRejectsNoncomplexSamples, dependencyCount := 2, forbiddenClaimCount := 4 },
    { id := .genericGptClosureRejectsUnconstrainedCone, dependencyCount := 3, forbiddenClaimCount := 4 },
    { id := .finiteRouteCoverageReducesBroaderGenericGptCone, dependencyCount := 4, forbiddenClaimCount := 4 },
    { id := .uniformRouteWitnessCompactnessClosesNonfiniteGptResidual, dependencyCount := 7, forbiddenClaimCount := 4 },
    { id := .noEmergentJointOnlyInvariantsUnderContextProductExhaustion, dependencyCount := 3, forbiddenClaimCount := 4 },
    { id := .finiteSignatureClosureImpliesUniformRouteWitnessBound, dependencyCount := 4, forbiddenClaimCount := 4 },
    { id := .routeWitnessCompletenessImpliesTomographicStateEffectDuality, dependencyCount := 4, forbiddenClaimCount := 4 },
    { id := .finiteBornQuadraticReadoutSurvivor, dependencyCount := 3, forbiddenClaimCount := 4 },
    { id := .bornWallRequiresPositiveQuadraticActualizationPrinciple, dependencyCount := 3, forbiddenClaimCount := 5 },
    { id := .universalCarrierSelectionTheorem, dependencyCount := 6, forbiddenClaimCount := 1 },
    { id := .hilbertCarrierDerivation, dependencyCount := 1, forbiddenClaimCount := 1 },
    { id := .universalBornRuleTheorem, dependencyCount := 4, forbiddenClaimCount := 1 },
    { id := .wignerReversibleInheritanceTheorem, dependencyCount := 3, forbiddenClaimCount := 1 },
    { id := .apparatusFacticityTheorem, dependencyCount := 4, forbiddenClaimCount := 1 },
    { id := .monoidalTensorCompositionTheorem, dependencyCount := 3, forbiddenClaimCount := 1 },
    { id := .firstPrinciplesHbarLock, dependencyCount := 3, forbiddenClaimCount := 1 },
    { id := .fieldModeContinuumLimit, dependencyCount := 3, forbiddenClaimCount := 1 },
    { id := .universalBornHilbertFrontierClosure, dependencyCount := 6, forbiddenClaimCount := 4 }
  ]

def TheoremCardBoundaryEntry.hasDependencyBoundary
    (entry : TheoremCardBoundaryEntry) : Prop :=
  entry.dependencyCount > 0

def TheoremCardBoundaryEntry.hasForbiddenClaimBoundary
    (entry : TheoremCardBoundaryEntry) : Prop :=
  entry.forbiddenClaimCount > 0

def theoremCardBoundaryLedgerAccepted
    (entries : List TheoremCardBoundaryEntry) : Prop :=
  ∀ entry, entry ∈ entries →
    entry.hasDependencyBoundary ∧ entry.hasForbiddenClaimBoundary

theorem current_theorem_card_boundary_ledger_count :
    currentTheoremCardBoundaryLedger.length = 23 := by
  rfl

theorem current_theorem_card_boundary_ledger_is_accepted :
    theoremCardBoundaryLedgerAccepted currentTheoremCardBoundaryLedger := by
  intro entry entryPresent
  simp [currentTheoremCardBoundaryLedger] at entryPresent
  rcases entryPresent with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · unfold TheoremCardBoundaryEntry.hasDependencyBoundary
      decide
    · unfold TheoremCardBoundaryEntry.hasForbiddenClaimBoundary
      decide

structure QmObligationBoundaryEntry where
  id : CurrentQmObligationId
  dependencyCount : Nat
  hasOpenGap : Bool
  hasClaimBoundary : Bool
deriving Repr

def currentQmObligationBoundaryLedger : List QmObligationBoundaryEntry :=
  [
    { id := .finiteOperationalCore, dependencyCount := 0, hasOpenGap := true, hasClaimBoundary := true },
    { id := .probabilityMeasureLayer, dependencyCount := 1, hasOpenGap := true, hasClaimBoundary := true },
    { id := .distinguishabilityGeometry, dependencyCount := 2, hasOpenGap := true, hasClaimBoundary := true },
    { id := .productContextsSeparateStableFacts, dependencyCount := 1, hasOpenGap := false, hasClaimBoundary := true },
    { id := .hilbertCarrierDerivation, dependencyCount := 1, hasOpenGap := true, hasClaimBoundary := true },
    { id := .bornRuleDerivation, dependencyCount := 2, hasOpenGap := true, hasClaimBoundary := true },
    { id := .reversibleInheritanceSymmetry, dependencyCount := 1, hasOpenGap := true, hasClaimBoundary := true },
    { id := .measurementFacticityMechanism, dependencyCount := 2, hasOpenGap := true, hasClaimBoundary := true },
    { id := .tensorCompositionLaw, dependencyCount := 3, hasOpenGap := true, hasClaimBoundary := true },
    { id := .recompile35FromCore, dependencyCount := 3, hasOpenGap := true, hasClaimBoundary := true },
    { id := .continuumActionScaleExtension, dependencyCount := 1, hasOpenGap := true, hasClaimBoundary := true }
  ]

def QmObligationBoundaryEntry.hasDependencyOrIsFiniteCore
    (entry : QmObligationBoundaryEntry) : Prop :=
  entry.dependencyCount > 0 ∨ entry.id = CurrentQmObligationId.finiteOperationalCore

def QmObligationBoundaryEntry.hasRequiredBoundary
    (entry : QmObligationBoundaryEntry) : Prop :=
  entry.hasClaimBoundary = true

def qmObligationBoundaryLedgerAccepted
    (entries : List QmObligationBoundaryEntry) : Prop :=
  ∀ entry, entry ∈ entries →
    entry.hasDependencyOrIsFiniteCore ∧ entry.hasRequiredBoundary

theorem current_qm_obligation_boundary_ledger_count :
    currentQmObligationBoundaryLedger.length = 11 := by
  rfl

theorem current_qm_obligation_boundary_ledger_is_accepted :
    qmObligationBoundaryLedgerAccepted currentQmObligationBoundaryLedger := by
  intro entry entryPresent
  simp [currentQmObligationBoundaryLedger] at entryPresent
  rcases entryPresent with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · unfold QmObligationBoundaryEntry.hasDependencyOrIsFiniteCore
      first | left; decide | right; rfl
    · unfold QmObligationBoundaryEntry.hasRequiredBoundary
      rfl

def qmObligationsWithOpenGaps : Nat :=
  (currentQmObligationBoundaryLedger.filter
    (fun entry => entry.hasOpenGap)).length

theorem current_qm_obligations_with_open_gaps_count :
    qmObligationsWithOpenGaps = 10 := by
  rfl

theorem product_context_separator_is_the_only_obligation_without_open_gap :
    (currentQmObligationBoundaryLedger.filter
      (fun entry => !entry.hasOpenGap)).length = 1 := by
  rfl

end V8
end MetaLang
end IDT
