import Proofs.MetaLang.V8ExternalCheckerBoundary
import Proofs.MetaLang.V8ProofArtifactContract
import Proofs.MetaLang.V8TheoremCardLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 Lean-first trust kernel.

This file composes the already migrated verification-discipline layers. It is
the current Lean-side trust boundary: accepted theorem cards, status
transitions, dependencies, proof-artifact upgrades, and the legacy Python
boundary must all be accepted together.
-/

structure LeanFirstTrustKernel where
  theoremLedger : TheoremCardLedger
  transitionLedger : StatusTransitionLedger
  dependencyLedger : DependencyClaimLedger
  proofArtifactRequests : List ProofArtifactUpgradeRequest
  legacyBoundary : LegacyPythonVerifierBoundary
  theoremLedgerAccepted : theoremLedger.isAcceptedForV8
  transitionLedgerAccepted : transitionLedger.isAcceptedForV8
  dependencyLedgerAccepted : dependencyLedger.isAcceptedForV8
  proofArtifactRequestsAccepted :
    ∀ request, request ∈ proofArtifactRequests → request.isAcceptedForV8
  legacyBoundaryAccepted : legacyBoundary.valid

theorem lean_first_kernel_accepts_theorem_cards
    (kernel : LeanFirstTrustKernel)
    (card : TheoremCard)
    (cardPresent : card ∈ kernel.theoremLedger.theoremCards) :
    card.isAcceptedForV8 :=
  accepted_ledger_accepts_all_theorem_cards
    kernel.theoremLedger
    kernel.theoremLedgerAccepted
    card
    cardPresent

theorem lean_first_kernel_accepts_status_transitions
    (kernel : LeanFirstTrustKernel)
    (transition : StatusTransition)
    (transitionPresent : transition ∈ kernel.transitionLedger.transitions) :
    transition.isAllowedForV8 :=
  accepted_status_transition_ledger_allows_only_guarded_transitions
    kernel.transitionLedger
    kernel.transitionLedgerAccepted
    transition
    transitionPresent

theorem lean_first_kernel_accepts_dependency_records
    (kernel : LeanFirstTrustKernel)
    (record : DependencyClaimRecord)
    (recordPresent : record ∈ kernel.dependencyLedger.records) :
    record.dependenciesAreGrounded kernel.dependencyLedger.graph.graph
      ∧ record.forwardStatusIsDependencyClean :=
  kernel.dependencyLedgerAccepted record recordPresent

theorem lean_first_kernel_formal_upgrade_has_runnable_lean_artifact
    (kernel : LeanFirstTrustKernel)
    (request : ProofArtifactUpgradeRequest)
    (requestPresent : request ∈ kernel.proofArtifactRequests)
    (toFormal : request.transition.toStatus = ClaimStatus.formalProof) :
    request.claim.hasRunnableLean4ProofArtifact :=
  accepted_formal_upgrade_has_runnable_lean_artifact
    request
    (kernel.proofArtifactRequestsAccepted request requestPresent)
    toFormal

theorem lean_first_kernel_legacy_python_boundary_is_finite_only
    (kernel : LeanFirstTrustKernel) :
    kernel.legacyBoundary.allowedStatus = ClaimStatus.finiteVerifierPass
      ∧ kernel.legacyBoundary.forbiddenStatus = ClaimStatus.formalProof :=
  And.intro
    kernel.legacyBoundaryAccepted.right.left
    kernel.legacyBoundaryAccepted.right.right

end V8
end MetaLang
end IDT
