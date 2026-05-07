import Proofs.MetaLang.V8MigrationStopBoundary

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 accepted document inventory.

This module collects the IDT v8 declarative documents that currently participate
in the Lean migration boundary. It is an inventory of accepted verification
documents, not a physics proof.
-/

inductive AcceptedV8DocumentId where
  | coreClaimDiscipline
  | finiteGateResiduals
  | qmExperimentResiduals
  | qmCoreObligations
  | theoremCardResiduals
deriving DecidableEq, Repr

def AcceptedV8DocumentId.toDocumentId : AcceptedV8DocumentId → String
  | .coreClaimDiscipline => "idt_v8_core_claim_discipline"
  | .finiteGateResiduals => "idt_v8_finite_gate_residuals"
  | .qmExperimentResiduals => "idt_v8_qm_experiment_residuals"
  | .qmCoreObligations => "idt_v8_qm_core_obligations"
  | .theoremCardResiduals => "idt_v8_theorem_card_residuals"

def acceptedV8DocumentIds : List AcceptedV8DocumentId :=
  [
    AcceptedV8DocumentId.coreClaimDiscipline,
    AcceptedV8DocumentId.finiteGateResiduals,
    AcceptedV8DocumentId.qmExperimentResiduals,
    AcceptedV8DocumentId.qmCoreObligations,
    AcceptedV8DocumentId.theoremCardResiduals
  ]

def acceptedV8DocumentCount : Nat :=
  acceptedV8DocumentIds.length

theorem accepted_v8_document_count_is_five :
    acceptedV8DocumentCount = 5 := by
  rfl

structure AcceptedV8DocumentInventory where
  documentCount : Nat
  coreDocumentAccepted :
    v8CoreClaimDisciplineDocument.isAcceptedForV8
  finiteGateResidualDocumentAccepted :
    v8FiniteGateResidualDocument.isAcceptedForV8
  qmExperimentResidualDocumentAccepted :
    v8QmExperimentResidualDocument.isAcceptedForV8
  qmCoreObligationDocumentAccepted :
    v8QmCoreObligationDocument.isAcceptedForV8
  theoremCardResidualDocumentAccepted :
    v8TheoremCardResidualDocument.isAcceptedForV8

def currentAcceptedV8DocumentInventory : AcceptedV8DocumentInventory :=
  {
    documentCount := acceptedV8DocumentCount,
    coreDocumentAccepted :=
      v8_core_claim_discipline_document_is_accepted,
    finiteGateResidualDocumentAccepted :=
      v8_finite_gate_residual_document_is_accepted,
    qmExperimentResidualDocumentAccepted :=
      v8_qm_experiment_residual_document_is_accepted,
    qmCoreObligationDocumentAccepted :=
      v8_qm_core_obligation_document_is_accepted,
    theoremCardResidualDocumentAccepted :=
      v8_theorem_card_residual_document_is_accepted
  }

theorem current_accepted_v8_document_inventory_has_five_documents :
    currentAcceptedV8DocumentInventory.documentCount = 5 :=
  accepted_v8_document_count_is_five

theorem current_accepted_v8_document_inventory_matches_stop_boundary :
    v8CoreClaimDisciplineDocument.isAcceptedForV8
      ∧ v8FiniteGateResidualDocument.isAcceptedForV8
      ∧ v8QmExperimentResidualDocument.isAcceptedForV8
      ∧ v8QmCoreObligationDocument.isAcceptedForV8
      ∧ v8TheoremCardResidualDocument.isAcceptedForV8 := by
  exact And.intro
    currentAcceptedV8DocumentInventory.coreDocumentAccepted
    (And.intro
      currentAcceptedV8DocumentInventory.finiteGateResidualDocumentAccepted
      (And.intro
        currentAcceptedV8DocumentInventory.qmExperimentResidualDocumentAccepted
        (And.intro
          currentAcceptedV8DocumentInventory.qmCoreObligationDocumentAccepted
          currentAcceptedV8DocumentInventory.theoremCardResidualDocumentAccepted)))

end V8
end MetaLang
end IDT
