import Proofs.MetaLang.V8DependencyGraphPolicy

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 proof-artifact contract.

This module tightens the Lean-first trust boundary: a formal proof claim must
not merely name Lean as a backend; it must point to a runnable Lean artifact
with a theorem name and a check command.
-/

def ProofArtifact.hasPath (artifact : ProofArtifact) : Prop :=
  artifact.path.length > 0

def ProofArtifact.hasTheoremName (artifact : ProofArtifact) : Prop :=
  artifact.theoremName.length > 0

def ProofArtifact.hasCheckCommand (artifact : ProofArtifact) : Prop :=
  artifact.checkCommand.length > 0

def ProofArtifact.isRunnableLean4 (artifact : ProofArtifact) : Prop :=
  artifact.isLean4
    ∧ artifact.hasPath
    ∧ artifact.hasTheoremName
    ∧ artifact.hasCheckCommand

def Claim.hasRunnableLean4ProofArtifact (claim : Claim) : Prop :=
  ∃ artifact, artifact ∈ claim.proofArtifacts ∧ artifact.isRunnableLean4

theorem runnable_lean4_artifact_is_lean4
    (artifact : ProofArtifact)
    (runnable : artifact.isRunnableLean4) :
    artifact.isLean4 :=
  runnable.left

theorem claim_with_runnable_lean4_artifact_has_lean4_artifact
    (claim : Claim)
    (runnable : claim.hasRunnableLean4ProofArtifact) :
    claim.hasLean4ProofArtifact := by
  rcases runnable with ⟨artifact, artifactPresent, artifactRunnable⟩
  exact ⟨artifact, artifactPresent,
    runnable_lean4_artifact_is_lean4 artifact artifactRunnable⟩

structure RunnableFormalClaim where
  claim : Claim
  isFormal : claim.status = ClaimStatus.formalProof
  hasRunnableArtifact : claim.hasRunnableLean4ProofArtifact

theorem runnable_formal_claim_is_machine_grounded
    (formalClaim : RunnableFormalClaim) :
    formalClaim.claim.hasLean4ProofArtifact :=
  claim_with_runnable_lean4_artifact_has_lean4_artifact
    formalClaim.claim
    formalClaim.hasRunnableArtifact

structure ProofArtifactUpgradeRequest where
  transition : StatusTransition
  claim : Claim
deriving Repr

def ProofArtifactUpgradeRequest.targetsSameClaim
    (request : ProofArtifactUpgradeRequest) : Prop :=
  request.transition.claimId = request.claim.identifier

def ProofArtifactUpgradeRequest.formalUpgradeIsRunnable
    (request : ProofArtifactUpgradeRequest) : Prop :=
  request.transition.toStatus = ClaimStatus.formalProof →
    request.targetsSameClaim
      ∧ request.transition.hasEvidence StatusTransitionEvidence.leanArtifact
      ∧ request.claim.hasRunnableLean4ProofArtifact

def ProofArtifactUpgradeRequest.isAcceptedForV8
    (request : ProofArtifactUpgradeRequest) : Prop :=
  request.formalUpgradeIsRunnable

theorem accepted_formal_upgrade_has_runnable_lean_artifact
    (request : ProofArtifactUpgradeRequest)
    (accepted : request.isAcceptedForV8)
    (toFormal : request.transition.toStatus = ClaimStatus.formalProof) :
    request.claim.hasRunnableLean4ProofArtifact :=
  (accepted toFormal).right.right

theorem accepted_formal_upgrade_targets_same_claim
    (request : ProofArtifactUpgradeRequest)
    (accepted : request.isAcceptedForV8)
    (toFormal : request.transition.toStatus = ClaimStatus.formalProof) :
    request.targetsSameClaim :=
  (accepted toFormal).left

theorem accepted_formal_upgrade_has_lean_transition_evidence
    (request : ProofArtifactUpgradeRequest)
    (accepted : request.isAcceptedForV8)
    (toFormal : request.transition.toStatus = ClaimStatus.formalProof) :
    request.transition.hasEvidence StatusTransitionEvidence.leanArtifact :=
  (accepted toFormal).right.left

end V8
end MetaLang
end IDT
