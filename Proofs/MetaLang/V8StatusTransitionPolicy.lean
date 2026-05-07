import Proofs.MetaLang.V8TheoremCardLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 status-transition policy.

This module moves the anti-hallucination upgrade discipline into Lean. It does
not prove any physical theorem. It only specifies when a claim-status transition
is allowed during the Lean-first migration.
-/

inductive StatusTransitionEvidence where
  | leanArtifact
  | explicitAssumptions
  | finiteVerifierPass
  | calibrationRecord
  | failureWitness
  | noEvidence
deriving DecidableEq, Repr

structure StatusTransition where
  claimId : String
  fromStatus : ClaimStatus
  toStatus : ClaimStatus
  evidence : List StatusTransitionEvidence
  dependencies : List DependencyStatus
deriving Repr

def StatusTransition.hasEvidence
    (transition : StatusTransition)
    (evidence : StatusTransitionEvidence) : Prop :=
  evidence ∈ transition.evidence

def StatusTransition.hasOpenOrBlockedDependency
    (transition : StatusTransition) : Prop :=
  ∃ dependency, dependency ∈ transition.dependencies
    ∧ dependency.isOpenOrBlocked

def StatusTransition.toFormalProofIsLeanGrounded
    (transition : StatusTransition) : Prop :=
  transition.toStatus = ClaimStatus.formalProof →
    transition.hasEvidence StatusTransitionEvidence.leanArtifact

def StatusTransition.toConditionalProofHasAssumptions
    (transition : StatusTransition) : Prop :=
  transition.toStatus = ClaimStatus.conditionalProof →
    transition.hasEvidence StatusTransitionEvidence.explicitAssumptions

def StatusTransition.toFiniteVerifierPassHasFiniteGate
    (transition : StatusTransition) : Prop :=
  transition.toStatus = ClaimStatus.finiteVerifierPass →
    transition.hasEvidence StatusTransitionEvidence.finiteVerifierPass

def StatusTransition.toDerivedHasNoOpenOrBlockedDependency
    (transition : StatusTransition) : Prop :=
  transition.toStatus = ClaimStatus.derived →
    ¬ transition.hasOpenOrBlockedDependency

def StatusTransition.noEvidenceCannotUpgrade
    (transition : StatusTransition) : Prop :=
  transition.hasEvidence StatusTransitionEvidence.noEvidence →
    transition.toStatus = transition.fromStatus

def StatusTransition.isAllowedForV8
    (transition : StatusTransition) : Prop :=
  transition.toFormalProofIsLeanGrounded
    ∧ transition.toConditionalProofHasAssumptions
    ∧ transition.toFiniteVerifierPassHasFiniteGate
    ∧ transition.toDerivedHasNoOpenOrBlockedDependency
    ∧ transition.noEvidenceCannotUpgrade

theorem allowed_transition_to_formal_proof_has_lean_artifact
    (transition : StatusTransition)
    (allowed : transition.isAllowedForV8)
    (toFormal : transition.toStatus = ClaimStatus.formalProof) :
    transition.hasEvidence StatusTransitionEvidence.leanArtifact :=
  allowed.left toFormal

theorem allowed_transition_to_conditional_proof_has_assumptions
    (transition : StatusTransition)
    (allowed : transition.isAllowedForV8)
    (toConditional : transition.toStatus = ClaimStatus.conditionalProof) :
    transition.hasEvidence StatusTransitionEvidence.explicitAssumptions :=
  allowed.right.left toConditional

theorem allowed_transition_to_finite_verifier_pass_has_finite_gate
    (transition : StatusTransition)
    (allowed : transition.isAllowedForV8)
    (toFinitePass : transition.toStatus = ClaimStatus.finiteVerifierPass) :
    transition.hasEvidence StatusTransitionEvidence.finiteVerifierPass :=
  allowed.right.right.left toFinitePass

theorem allowed_transition_to_derived_has_no_open_or_blocked_dependency
    (transition : StatusTransition)
    (allowed : transition.isAllowedForV8)
    (toDerived : transition.toStatus = ClaimStatus.derived) :
    ¬ transition.hasOpenOrBlockedDependency :=
  allowed.right.right.right.left toDerived

theorem no_evidence_transition_preserves_status
    (transition : StatusTransition)
    (allowed : transition.isAllowedForV8)
    (noEvidence : transition.hasEvidence StatusTransitionEvidence.noEvidence) :
    transition.toStatus = transition.fromStatus :=
  allowed.right.right.right.right noEvidence

structure StatusTransitionLedger where
  transitions : List StatusTransition
deriving Repr

def StatusTransitionLedger.isAcceptedForV8
    (ledger : StatusTransitionLedger) : Prop :=
  ∀ transition, transition ∈ ledger.transitions →
    transition.isAllowedForV8

theorem accepted_status_transition_ledger_allows_only_guarded_transitions
    (ledger : StatusTransitionLedger)
    (accepted : ledger.isAcceptedForV8)
    (transition : StatusTransition) :
    transition ∈ ledger.transitions → transition.isAllowedForV8 :=
  accepted transition

end V8
end MetaLang
end IDT
