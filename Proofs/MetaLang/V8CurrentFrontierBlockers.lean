import Proofs.MetaLang.V8TheoremDependencyBoundaryLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
Current frontier blockers.

This module records the concrete theorem-card and QM-obligation blockers that
prevent exact/full QM closure in the current migration state. It does not add a
new physical claim and does not turn any blocker into a proof.
-/

inductive FrontierBlockerKind where
  | carrierSelection
  | hilbertCarrier
  | bornRule
  | reversibleInheritance
  | apparatusFacticity
  | tensorComposition
  | physicalActionScale
  | fieldModeContinuum
  | finiteCoreRecompile
deriving DecidableEq, Repr

structure TheoremCardFrontierBlocker where
  id : CurrentTheoremCardId
  kind : FrontierBlockerKind
  status : CurrentProofStatus
deriving Repr

def currentTheoremCardFrontierBlockers : List TheoremCardFrontierBlocker :=
  [
    { id := .universalCarrierSelectionTheorem, kind := .carrierSelection, status := .open },
    { id := .hilbertCarrierDerivation, kind := .hilbertCarrier, status := .blocked },
    { id := .universalBornRuleTheorem, kind := .bornRule, status := .open },
    { id := .wignerReversibleInheritanceTheorem, kind := .reversibleInheritance, status := .open },
    { id := .apparatusFacticityTheorem, kind := .apparatusFacticity, status := .open },
    { id := .monoidalTensorCompositionTheorem, kind := .tensorComposition, status := .open },
    { id := .firstPrinciplesHbarLock, kind := .physicalActionScale, status := .blocked },
    { id := .fieldModeContinuumLimit, kind := .fieldModeContinuum, status := .open }
  ]

def TheoremCardFrontierBlocker.isActive
    (blocker : TheoremCardFrontierBlocker) : Prop :=
  blocker.status = CurrentProofStatus.open
    ∨ blocker.status = CurrentProofStatus.blocked

def theoremCardFrontierBlockersActive
    (blockers : List TheoremCardFrontierBlocker) : Prop :=
  ∀ blocker, blocker ∈ blockers → blocker.isActive

theorem current_theorem_card_frontier_blocker_count :
    currentTheoremCardFrontierBlockers.length = 8 := by
  rfl

theorem current_theorem_card_frontier_blockers_are_active :
    theoremCardFrontierBlockersActive currentTheoremCardFrontierBlockers := by
  intro blocker present
  simp [currentTheoremCardFrontierBlockers] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold TheoremCardFrontierBlocker.isActive
    first | left; rfl | right; rfl

structure QmObligationFrontierBlocker where
  id : CurrentQmObligationId
  kind : FrontierBlockerKind
  status : CurrentQmObligationStatus
deriving Repr

def currentQmObligationFrontierBlockers : List QmObligationFrontierBlocker :=
  [
    { id := .distinguishabilityGeometry, kind := .carrierSelection, status := .target },
    { id := .hilbertCarrierDerivation, kind := .hilbertCarrier, status := .blocked },
    { id := .bornRuleDerivation, kind := .bornRule, status := .blocked },
    { id := .tensorCompositionLaw, kind := .tensorComposition, status := .target },
    { id := .recompile35FromCore, kind := .finiteCoreRecompile, status := .target },
    { id := .continuumActionScaleExtension, kind := .physicalActionScale, status := .blocked }
  ]

def QmObligationFrontierBlocker.isActive
    (blocker : QmObligationFrontierBlocker) : Prop :=
  blocker.status = CurrentQmObligationStatus.target
    ∨ blocker.status = CurrentQmObligationStatus.blocked

def qmObligationFrontierBlockersActive
    (blockers : List QmObligationFrontierBlocker) : Prop :=
  ∀ blocker, blocker ∈ blockers → blocker.isActive

theorem current_qm_obligation_frontier_blocker_count :
    currentQmObligationFrontierBlockers.length = 6 := by
  rfl

theorem current_qm_obligation_frontier_blockers_are_active :
    qmObligationFrontierBlockersActive currentQmObligationFrontierBlockers := by
  intro blocker present
  simp [currentQmObligationFrontierBlockers] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold QmObligationFrontierBlocker.isActive
    first | left; rfl | right; rfl

def exactQmClosureBlockedByCurrentFrontier : Prop :=
  currentTheoremCardFrontierBlockers.length > 0
    ∧ currentQmObligationFrontierBlockers.length > 0
    ∧ theoremCardFrontierBlockersActive currentTheoremCardFrontierBlockers
    ∧ qmObligationFrontierBlockersActive currentQmObligationFrontierBlockers

theorem current_frontier_blocks_exact_qm_closure :
    exactQmClosureBlockedByCurrentFrontier := by
  exact And.intro
    (by decide)
    (And.intro
      (by decide)
      (And.intro
        current_theorem_card_frontier_blockers_are_active
        current_qm_obligation_frontier_blockers_are_active))

theorem hilbert_and_born_are_explicit_current_blockers :
    ∃ hilbert born,
      hilbert ∈ currentQmObligationFrontierBlockers
        ∧ born ∈ currentQmObligationFrontierBlockers
        ∧ hilbert.kind = FrontierBlockerKind.hilbertCarrier
        ∧ born.kind = FrontierBlockerKind.bornRule := by
  exact ⟨
    { id := .hilbertCarrierDerivation, kind := .hilbertCarrier, status := .blocked },
    { id := .bornRuleDerivation, kind := .bornRule, status := .blocked },
    by simp [currentQmObligationFrontierBlockers],
    by simp [currentQmObligationFrontierBlockers],
    rfl,
    rfl
  ⟩

end V8
end MetaLang
end IDT
