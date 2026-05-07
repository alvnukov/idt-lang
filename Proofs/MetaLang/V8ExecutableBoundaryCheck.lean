import Proofs.MetaLang.V8AcceptedDocumentInventory
import Proofs.MetaLang.V8CurrentStopReadiness

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 executable boundary check.

This module contains the Lean-side invariants mirrored by
`lake exe idt_v8_protocol_status -- --check-boundary`.
-/

structure ExecutableBoundarySnapshot where
  acceptedDocumentCount : Nat
  verificationDisciplineTheorems : Nat
  residualQmExperiments : Nat
  theoremCardFormalProofs : Nat
  qmObligationFormalProofs : Nat
  qmExperimentFormalProofs : Nat
  physicalFormalProofs : Nat
  qmFormalProofs : Nat

def currentExecutableBoundarySnapshot : ExecutableBoundarySnapshot :=
  {
    acceptedDocumentCount := currentAcceptedV8DocumentInventory.documentCount,
    verificationDisciplineTheorems :=
      currentFormalProofScopeCounts.verificationDiscipline,
    residualQmExperiments :=
      currentExperimentProgramArchitecture.residualLedger.length,
    theoremCardFormalProofs := theoremCardFormalProofCount,
    qmObligationFormalProofs := qmCoreObligationFormalProofCount,
    qmExperimentFormalProofs := qmExperimentResidualFormalProofCount,
    physicalFormalProofs := currentFormalProofScopeCounts.physicalTheory,
    qmFormalProofs := currentFormalProofScopeCounts.qmClosure
  }

def ExecutableBoundarySnapshot.matchesCurrentBoundary
    (snapshot : ExecutableBoundarySnapshot) : Prop :=
  snapshot.acceptedDocumentCount = 5
    ∧ snapshot.verificationDisciplineTheorems = 259
    ∧ snapshot.residualQmExperiments = 35
    ∧ snapshot.theoremCardFormalProofs = 0
    ∧ snapshot.qmObligationFormalProofs = 0
    ∧ snapshot.qmExperimentFormalProofs = 0
    ∧ snapshot.physicalFormalProofs = 0
    ∧ snapshot.qmFormalProofs = 0

theorem current_executable_boundary_snapshot_matches :
    currentExecutableBoundarySnapshot.matchesCurrentBoundary := by
  exact And.intro
    current_accepted_v8_document_inventory_has_five_documents
    (And.intro
      rfl
      (And.intro
        current_qm_experiment_residual_ledger_count
        (And.intro
          theorem_cards_have_no_formal_physical_claims
          (And.intro
            qm_core_obligations_have_no_formal_qm_claims
            (And.intro
              current_qm_experiment_residuals_have_no_formal_proof_closure
              current_formal_proofs_are_verification_scope_only)))))

end V8
end MetaLang
end IDT
