namespace IDT
namespace MetaLang
namespace V8

inductive VocabularyStatus where
  | standard
  | projectLocal
  | proposedTerm
deriving DecidableEq, Repr

structure VocabularyEntry where
  term : String
  status : VocabularyStatus
  domain : String
  definition : String
  approvalRequired : Bool
deriving Repr

def VocabularyEntry.isAccepted (entry : VocabularyEntry) : Prop :=
  entry.status ≠ VocabularyStatus.proposedTerm ∨ entry.approvalRequired = true

theorem proposed_vocabulary_terms_require_approval
    (entry : VocabularyEntry)
    (proposed : entry.status = VocabularyStatus.proposedTerm)
    (accepted : entry.isAccepted) :
    entry.approvalRequired = true := by
  unfold VocabularyEntry.isAccepted at accepted
  cases accepted with
  | inl notProposed =>
      contradiction
  | inr approved =>
      exact approved

inductive ClaimStatus where
  | primitive
  | definition
  | axiom
  | bridge
  | calibration
  | readout
  | gate
  | prediction
  | failure
  | derived
  | blocked
  | open
  | formalProof
  | conditionalProof
  | finiteVerifierPass
  | numericalEvidence
  | calibratedMatch
deriving DecidableEq, Repr

inductive ProofSystem where
  | lean4
  | idtVerifier
  | external
deriving DecidableEq, Repr

structure ProofArtifact where
  system : ProofSystem
  path : String
  theoremName : String
  checkCommand : String
deriving Repr

def ProofArtifact.isLean4 (artifact : ProofArtifact) : Prop :=
  artifact.system = ProofSystem.lean4

structure DependencyStatus where
  reference : String
  status : ClaimStatus
deriving Repr

def DependencyStatus.isOpenOrBlocked (dependency : DependencyStatus) : Prop :=
  dependency.status = ClaimStatus.open ∨ dependency.status = ClaimStatus.blocked

structure Claim where
  identifier : String
  statement : String
  status : ClaimStatus
  dependencies : List DependencyStatus
  proofArtifacts : List ProofArtifact
deriving Repr

def Claim.hasLean4ProofArtifact (claim : Claim) : Prop :=
  ∃ artifact, artifact ∈ claim.proofArtifacts ∧ artifact.isLean4

def Claim.hasNoOpenOrBlockedDependencies (claim : Claim) : Prop :=
  ∀ dependency, dependency ∈ claim.dependencies → ¬ dependency.isOpenOrBlocked

structure VerifiedClaim where
  claim : Claim
  formalProofHasLeanArtifact :
    claim.status = ClaimStatus.formalProof → claim.hasLean4ProofArtifact
  derivedHasNoOpenOrBlockedDependencies :
    claim.status = ClaimStatus.derived → claim.hasNoOpenOrBlockedDependencies

theorem verified_formal_proof_has_lean_artifact
    (verified : VerifiedClaim)
    (formal : verified.claim.status = ClaimStatus.formalProof) :
    verified.claim.hasLean4ProofArtifact :=
  verified.formalProofHasLeanArtifact formal

theorem verified_derived_claim_has_no_open_or_blocked_dependencies
    (verified : VerifiedClaim)
    (derived : verified.claim.status = ClaimStatus.derived) :
    verified.claim.hasNoOpenOrBlockedDependencies :=
  verified.derivedHasNoOpenOrBlockedDependencies derived

def Claim.isAllowedToMoveForward (claim : Claim) : Prop :=
  (claim.status = ClaimStatus.formalProof → claim.hasLean4ProofArtifact)
    ∧ (claim.status = ClaimStatus.derived → claim.hasNoOpenOrBlockedDependencies)

theorem allowed_formal_claims_are_machine_grounded
    (claim : Claim)
    (allowed : claim.isAllowedToMoveForward)
    (formal : claim.status = ClaimStatus.formalProof) :
    claim.hasLean4ProofArtifact :=
  allowed.left formal

theorem allowed_derived_claims_do_not_depend_on_open_or_blocked_claims
    (claim : Claim)
    (allowed : claim.isAllowedToMoveForward)
    (derived : claim.status = ClaimStatus.derived) :
    claim.hasNoOpenOrBlockedDependencies :=
  allowed.right derived

end V8
end MetaLang
end IDT
