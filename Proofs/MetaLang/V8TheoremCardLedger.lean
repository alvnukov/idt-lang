import Proofs.MetaLang.V8VerificationLanguage

namespace IDT
namespace MetaLang
namespace V8

inductive TheoremCardRole where
  | theorem
  | failure
deriving DecidableEq, Repr

inductive ProofObligationScope where
  | finiteCore
  | fullQMFrontier
  | physicalScale
  | primitiveBase
  | carrierFrontier
deriving DecidableEq, Repr

structure TheoremCard where
  identifier : String
  role : TheoremCardRole
  claim : Claim
  assumptions : List String
  dependencies : List DependencyStatus
  verifier : String
  knownFailures : List String
  forbiddenClaims : List String
deriving Repr

def TheoremCard.hasAssumptions (card : TheoremCard) : Prop :=
  card.assumptions.length > 0

def TheoremCard.hasDependencies (card : TheoremCard) : Prop :=
  card.dependencies.length > 0

def TheoremCard.hasVerifier (card : TheoremCard) : Prop :=
  card.verifier.length > 0

def TheoremCard.hasForbiddenClaims (card : TheoremCard) : Prop :=
  card.forbiddenClaims.length > 0

def TheoremCard.isFormal (card : TheoremCard) : Prop :=
  card.claim.status = ClaimStatus.formalProof

def TheoremCard.isConditional (card : TheoremCard) : Prop :=
  card.claim.status = ClaimStatus.conditionalProof

def TheoremCard.isOpenOrBlocked (card : TheoremCard) : Prop :=
  card.claim.status = ClaimStatus.open ∨ card.claim.status = ClaimStatus.blocked

def TheoremCard.hasMachineBoundary (card : TheoremCard) : Prop :=
  card.hasVerifier ∧ card.hasForbiddenClaims

def TheoremCard.formalStatusIsLeanGrounded (card : TheoremCard) : Prop :=
  card.isFormal → card.claim.hasLean4ProofArtifact

def TheoremCard.conditionalStatusHasAssumptions (card : TheoremCard) : Prop :=
  card.isConditional → card.hasAssumptions

def TheoremCard.openOrBlockedStatusCannotMoveAsDerived (card : TheoremCard) : Prop :=
  card.isOpenOrBlocked → card.claim.status ≠ ClaimStatus.derived

def TheoremCard.isAcceptedForV8 (card : TheoremCard) : Prop :=
  card.hasMachineBoundary
    ∧ card.formalStatusIsLeanGrounded
    ∧ card.conditionalStatusHasAssumptions
    ∧ card.openOrBlockedStatusCannotMoveAsDerived

theorem accepted_theorem_card_formal_status_has_lean_artifact
    (card : TheoremCard)
    (accepted : card.isAcceptedForV8)
    (formal : card.isFormal) :
    card.claim.hasLean4ProofArtifact :=
  accepted.right.left formal

theorem accepted_theorem_card_conditional_status_has_assumptions
    (card : TheoremCard)
    (accepted : card.isAcceptedForV8)
    (conditional : card.isConditional) :
    card.hasAssumptions :=
  accepted.right.right.left conditional

theorem accepted_theorem_card_has_machine_boundary
    (card : TheoremCard)
    (accepted : card.isAcceptedForV8) :
    card.hasMachineBoundary :=
  accepted.left

structure ProofObligation where
  identifier : String
  status : ClaimStatus
  scope : ProofObligationScope
  dependencies : List DependencyStatus
  evidenceRefs : List String
  openGap : String
  claimBoundary : String
deriving Repr

def ProofObligation.hasEvidence (obligation : ProofObligation) : Prop :=
  obligation.evidenceRefs.length > 0

def ProofObligation.hasBoundary (obligation : ProofObligation) : Prop :=
  obligation.claimBoundary.length > 0

def ProofObligation.isOpenOrBlocked (obligation : ProofObligation) : Prop :=
  obligation.status = ClaimStatus.open ∨ obligation.status = ClaimStatus.blocked

def ProofObligation.isDerived (obligation : ProofObligation) : Prop :=
  obligation.status = ClaimStatus.derived

def ProofObligation.openOrBlockedHasGap (obligation : ProofObligation) : Prop :=
  obligation.isOpenOrBlocked → obligation.openGap.length > 0

def ProofObligation.derivedHasNoOpenOrBlockedDependencies
    (obligation : ProofObligation) : Prop :=
  obligation.isDerived →
    ∀ dependency, dependency ∈ obligation.dependencies →
      ¬ dependency.isOpenOrBlocked

def ProofObligation.isAcceptedForV8 (obligation : ProofObligation) : Prop :=
  obligation.hasEvidence
    ∧ obligation.hasBoundary
    ∧ obligation.openOrBlockedHasGap
    ∧ obligation.derivedHasNoOpenOrBlockedDependencies

theorem accepted_open_or_blocked_obligation_has_gap
    (obligation : ProofObligation)
    (accepted : obligation.isAcceptedForV8)
    (openOrBlocked : obligation.isOpenOrBlocked) :
    obligation.openGap.length > 0 :=
  accepted.right.right.left openOrBlocked

theorem accepted_derived_obligation_has_no_open_or_blocked_dependencies
    (obligation : ProofObligation)
    (accepted : obligation.isAcceptedForV8)
    (derived : obligation.isDerived) :
    ∀ dependency, dependency ∈ obligation.dependencies →
      ¬ dependency.isOpenOrBlocked :=
  accepted.right.right.right derived

structure TheoremCardLedger where
  theoremCards : List TheoremCard
  proofObligations : List ProofObligation
deriving Repr

def TheoremCardLedger.isAcceptedForV8 (ledger : TheoremCardLedger) : Prop :=
  (∀ card, card ∈ ledger.theoremCards → card.isAcceptedForV8)
    ∧ (∀ obligation, obligation ∈ ledger.proofObligations →
      obligation.isAcceptedForV8)

theorem accepted_ledger_accepts_all_theorem_cards
    (ledger : TheoremCardLedger)
    (accepted : ledger.isAcceptedForV8)
    (card : TheoremCard) :
    card ∈ ledger.theoremCards → card.isAcceptedForV8 :=
  accepted.left card

theorem accepted_ledger_accepts_all_proof_obligations
    (ledger : TheoremCardLedger)
    (accepted : ledger.isAcceptedForV8)
    (obligation : ProofObligation) :
    obligation ∈ ledger.proofObligations → obligation.isAcceptedForV8 :=
  accepted.right obligation

end V8
end MetaLang
end IDT
