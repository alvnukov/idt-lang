import Proofs.MetaLang.V8DeclarativeReportContract

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 claim-strength invariant.

This module formalizes the project rule that conclusions must not be stronger
than their evidence. The goal is not to prove the whole theory at any cost; the
goal is to prevent overclaiming.
-/

inductive EvidenceStrength where
  | none
  | researchRoute
  | finiteVerifierPass
  | conditionalProof
  | runnableLeanProof
deriving DecidableEq, Repr

inductive ConclusionStrength where
  | open
  | researchRoute
  | finiteClaim
  | conditionalClaim
  | formalProof
deriving DecidableEq, Repr

def EvidenceStrength.rank : EvidenceStrength → Nat
  | EvidenceStrength.none => 0
  | EvidenceStrength.researchRoute => 1
  | EvidenceStrength.finiteVerifierPass => 2
  | EvidenceStrength.conditionalProof => 3
  | EvidenceStrength.runnableLeanProof => 4

def ConclusionStrength.rank : ConclusionStrength → Nat
  | ConclusionStrength.open => 0
  | ConclusionStrength.researchRoute => 1
  | ConclusionStrength.finiteClaim => 2
  | ConclusionStrength.conditionalClaim => 3
  | ConclusionStrength.formalProof => 4

structure ClaimStrengthAssessment where
  evidence : EvidenceStrength
  conclusion : ConclusionStrength
deriving Repr

def ClaimStrengthAssessment.notOverclaimed
    (assessment : ClaimStrengthAssessment) : Prop :=
  assessment.conclusion.rank ≤ assessment.evidence.rank

theorem runnable_lean_proof_can_support_formal_proof :
    ({ evidence := EvidenceStrength.runnableLeanProof,
       conclusion := ConclusionStrength.formalProof } :
      ClaimStrengthAssessment).notOverclaimed := by
  unfold ClaimStrengthAssessment.notOverclaimed
  decide

theorem finite_verifier_pass_cannot_support_formal_proof :
    ¬ ({ evidence := EvidenceStrength.finiteVerifierPass,
         conclusion := ConclusionStrength.formalProof } :
        ClaimStrengthAssessment).notOverclaimed := by
  unfold ClaimStrengthAssessment.notOverclaimed
  decide

theorem research_route_cannot_support_finite_claim :
    ¬ ({ evidence := EvidenceStrength.researchRoute,
         conclusion := ConclusionStrength.finiteClaim } :
        ClaimStrengthAssessment).notOverclaimed := by
  unfold ClaimStrengthAssessment.notOverclaimed
  decide

theorem conditional_proof_cannot_support_formal_proof :
    ¬ ({ evidence := EvidenceStrength.conditionalProof,
         conclusion := ConclusionStrength.formalProof } :
        ClaimStrengthAssessment).notOverclaimed := by
  unfold ClaimStrengthAssessment.notOverclaimed
  decide

def evidenceStrengthForStatus : ClaimStatus → EvidenceStrength
  | ClaimStatus.formalProof => EvidenceStrength.runnableLeanProof
  | ClaimStatus.conditionalProof => EvidenceStrength.conditionalProof
  | ClaimStatus.finiteVerifierPass => EvidenceStrength.finiteVerifierPass
  | ClaimStatus.numericalEvidence => EvidenceStrength.finiteVerifierPass
  | ClaimStatus.calibratedMatch => EvidenceStrength.finiteVerifierPass
  | ClaimStatus.derived => EvidenceStrength.conditionalProof
  | ClaimStatus.open => EvidenceStrength.none
  | ClaimStatus.blocked => EvidenceStrength.none
  | _ => EvidenceStrength.researchRoute

def conclusionStrengthForStatus : ClaimStatus → ConclusionStrength
  | ClaimStatus.formalProof => ConclusionStrength.formalProof
  | ClaimStatus.conditionalProof => ConclusionStrength.conditionalClaim
  | ClaimStatus.finiteVerifierPass => ConclusionStrength.finiteClaim
  | ClaimStatus.numericalEvidence => ConclusionStrength.finiteClaim
  | ClaimStatus.calibratedMatch => ConclusionStrength.finiteClaim
  | ClaimStatus.open => ConclusionStrength.open
  | ClaimStatus.blocked => ConclusionStrength.open
  | _ => ConclusionStrength.researchRoute

def ClaimStatus.notStrongerThanItsEvidence (status : ClaimStatus) : Prop :=
  ({ evidence := evidenceStrengthForStatus status,
     conclusion := conclusionStrengthForStatus status } :
    ClaimStrengthAssessment).notOverclaimed

theorem formal_proof_status_requires_runnable_lean_strength :
    evidenceStrengthForStatus ClaimStatus.formalProof =
      EvidenceStrength.runnableLeanProof := by
  rfl

theorem finite_verifier_status_is_not_formal_strength :
    conclusionStrengthForStatus ClaimStatus.finiteVerifierPass ≠
      ConclusionStrength.formalProof := by
  decide

theorem blocked_status_has_open_conclusion_strength :
    conclusionStrengthForStatus ClaimStatus.blocked =
      ConclusionStrength.open := by
  rfl

end V8
end MetaLang
end IDT
