import Proofs.MetaLang.V8MigrationStopBoundary

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 formal-proof scope boundary.

The repository currently has Lean-checked formal claims for verification
discipline, but no formal physical/QM theorem-card closure. This file prevents
those two scopes from being collapsed.
-/

inductive FormalProofScope where
  | verificationDiscipline
  | declarativeLanguage
  | physicalTheory
  | qmClosure
deriving DecidableEq, Repr

structure FormalProofScopeCounts where
  verificationDiscipline : Nat
  declarativeLanguage : Nat
  physicalTheory : Nat
  qmClosure : Nat
deriving Repr

def currentFormalProofScopeCounts : FormalProofScopeCounts :=
  {
    verificationDiscipline := 234,
    declarativeLanguage := 0,
    physicalTheory := 0,
    qmClosure := 0
  }

def FormalProofScopeCounts.total
    (counts : FormalProofScopeCounts) : Nat :=
  counts.verificationDiscipline
    + counts.declarativeLanguage
    + counts.physicalTheory
    + counts.qmClosure

def FormalProofScopeCounts.hasNoPhysicalClosure
    (counts : FormalProofScopeCounts) : Prop :=
  counts.physicalTheory = 0 ∧ counts.qmClosure = 0

def FormalProofScopeCounts.hasVerificationDisciplineProofs
    (counts : FormalProofScopeCounts) : Prop :=
  counts.verificationDiscipline > 0

theorem current_formal_proof_scope_total_is_234 :
    currentFormalProofScopeCounts.total = 234 := by
  rfl

theorem current_formal_proofs_are_verification_scope_only :
    currentFormalProofScopeCounts.hasNoPhysicalClosure := by
  exact And.intro rfl rfl

theorem current_formal_proof_scope_has_verification_proofs :
    currentFormalProofScopeCounts.hasVerificationDisciplineProofs := by
  unfold FormalProofScopeCounts.hasVerificationDisciplineProofs
  decide

structure ScopedFormalProofClaim where
  identifier : String
  scope : FormalProofScope
  status : ClaimStatus
deriving Repr

def ScopedFormalProofClaim.isPhysicalOrQM
    (claim : ScopedFormalProofClaim) : Prop :=
  claim.scope = FormalProofScope.physicalTheory
    ∨ claim.scope = FormalProofScope.qmClosure

def ScopedFormalProofClaim.isFormalProof
    (claim : ScopedFormalProofClaim) : Prop :=
  claim.status = ClaimStatus.formalProof

def ScopedFormalProofClaim.allowedInCurrentBoundary
    (claim : ScopedFormalProofClaim) : Prop :=
  claim.isFormalProof → ¬ claim.isPhysicalOrQM

theorem current_boundary_rejects_physical_or_qm_formal_claim
    (claim : ScopedFormalProofClaim)
    (allowed : claim.allowedInCurrentBoundary)
    (formal : claim.isFormalProof) :
    ¬ claim.isPhysicalOrQM :=
  allowed formal

def theoremCardFormalProofCount : Nat := 0
def qmCoreObligationFormalProofCount : Nat := 0

theorem theorem_cards_have_no_formal_physical_claims :
    theoremCardFormalProofCount = 0 := by
  rfl

theorem qm_core_obligations_have_no_formal_qm_claims :
    qmCoreObligationFormalProofCount = 0 := by
  rfl

end V8
end MetaLang
end IDT
