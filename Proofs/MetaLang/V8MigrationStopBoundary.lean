import Proofs.MetaLang.V8ResidualMigrationLedger
import Proofs.MetaLang.V8SymbolResidualDocument
import Proofs.MetaLang.V8EquationResidualDocument
import Proofs.MetaLang.V8DerivationResidualDocument
import Proofs.MetaLang.V8QmExperimentResidualDocument
import Proofs.MetaLang.V8QmUniversalPatternResidualDocument
import Proofs.MetaLang.V8QmCoreObligationDocument
import Proofs.MetaLang.V8TheoremCardResidualDocument
import Proofs.MetaLang.V8FiniteGateResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 migration stop boundary.

This module records the point where migration work must stop before any new CI,
legacy archive, or research handoff. The stop boundary requires:

* accepted Lean mirror of the core IDT v8 discipline document;
* accepted Lean mirror of the symbol residual discipline document;
* accepted Lean mirror of the equation residual discipline document;
* accepted Lean mirror of the derivation residual discipline document;
* accepted Lean mirror of the finite-gate residual discipline document;
* accepted Lean mirror of the QM experiment residual discipline document;
* accepted Lean mirror of the QM universal-pattern residual discipline document;
* accepted Lean mirror of the QM core obligation discipline document;
* accepted Lean mirror of the theorem-card residual discipline document;
* accepted manifest input boundary;
* accepted residual migration ledger;
* old Python verifier marked deprecated compatibility only.
-/

structure MigrationStopBoundary where
  coreDocumentAccepted :
    v8CoreClaimDisciplineDocument.isAcceptedForV8
  symbolResidualDocumentAccepted :
    v8SymbolResidualDocument.isAcceptedForV8
  equationResidualDocumentAccepted :
    v8EquationResidualDocument.isAcceptedForV8
  derivationResidualDocumentAccepted :
    v8DerivationResidualDocument.isAcceptedForV8
  finiteGateResidualDocumentAccepted :
    v8FiniteGateResidualDocument.isAcceptedForV8
  qmExperimentResidualDocumentAccepted :
    v8QmExperimentResidualDocument.isAcceptedForV8
  qmUniversalPatternResidualDocumentAccepted :
    v8QmUniversalPatternResidualDocument.isAcceptedForV8
  qmCoreObligationDocumentAccepted :
    v8QmCoreObligationDocument.isAcceptedForV8
  theoremCardResidualDocumentAccepted :
    v8TheoremCardResidualDocument.isAcceptedForV8
  manifestBoundaryAccepted :
    currentManifestInputBoundary.isAcceptedForV8
  residualBoundaryAccepted :
    currentResidualMigrationBoundary.isAcceptedForV8
  pythonDeprecated :
    oldPythonVerifierRole.isDeprecatedCompatibility

def currentMigrationStopBoundary : MigrationStopBoundary :=
  {
    coreDocumentAccepted := v8_core_claim_discipline_document_is_accepted,
    symbolResidualDocumentAccepted :=
      v8_symbol_residual_document_is_accepted,
    equationResidualDocumentAccepted :=
      v8_equation_residual_document_is_accepted,
    derivationResidualDocumentAccepted :=
      v8_derivation_residual_document_is_accepted,
    finiteGateResidualDocumentAccepted :=
      v8_finite_gate_residual_document_is_accepted,
    qmExperimentResidualDocumentAccepted :=
      v8_qm_experiment_residual_document_is_accepted,
    qmUniversalPatternResidualDocumentAccepted :=
      v8_qm_universal_pattern_residual_document_is_accepted,
    qmCoreObligationDocumentAccepted :=
      v8_qm_core_obligation_document_is_accepted,
    theoremCardResidualDocumentAccepted :=
      v8_theorem_card_residual_document_is_accepted,
    manifestBoundaryAccepted := current_manifest_input_boundary_is_accepted_for_v8,
    residualBoundaryAccepted := current_residual_migration_boundary_is_accepted,
    pythonDeprecated := old_python_verifier_is_deprecated_compatibility
  }

def MigrationStopBoundary.allowsNewCi
    (_boundary : MigrationStopBoundary) : Prop :=
  phasePrecedes MigrationPhase.migrationStop MigrationPhase.newCi

def MigrationStopBoundary.allowsLegacyArchive
    (_boundary : MigrationStopBoundary) : Prop :=
  phasePrecedes MigrationPhase.newCi MigrationPhase.archiveLegacy

def MigrationStopBoundary.allowsResearchHandoff
    (_boundary : MigrationStopBoundary) : Prop :=
  phasePrecedes MigrationPhase.researchContextPacker
    MigrationPhase.researchReady

def MigrationStopBoundary.requiresResearchContextPacker
    (_boundary : MigrationStopBoundary) : Prop :=
  researchContextPackerRequirement.required = true
    ∧ researchContextPackerRequirement.assignedToResearchModel = true

theorem current_stop_boundary_allows_new_ci_only_after_stop :
    currentMigrationStopBoundary.allowsNewCi :=
  migration_stop_precedes_new_ci

theorem current_stop_boundary_allows_archive_only_after_new_ci :
    currentMigrationStopBoundary.allowsLegacyArchive :=
  new_ci_precedes_legacy_archive

theorem current_stop_boundary_allows_research_only_after_archive :
    currentMigrationStopBoundary.allowsResearchHandoff :=
  research_context_packer_precedes_research_ready

theorem current_stop_boundary_requires_research_context_packer :
    currentMigrationStopBoundary.requiresResearchContextPacker :=
  And.intro research_context_packer_is_required
    research_context_packer_is_research_model_work

theorem current_stop_boundary_keeps_python_deprecated :
    oldPythonVerifierRole.isDeprecatedCompatibility :=
  currentMigrationStopBoundary.pythonDeprecated

theorem current_stop_boundary_keeps_manifest_non_proof_authority :
    currentManifestInputBoundary.proofAuthority ≠
      VerificationAuthority.proofTruth :=
  current_manifest_boundary_is_not_proof_truth

theorem current_stop_boundary_accepts_qm_experiment_residual_document :
    v8QmExperimentResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.qmExperimentResidualDocumentAccepted

theorem current_stop_boundary_accepts_finite_gate_residual_document :
    v8FiniteGateResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.finiteGateResidualDocumentAccepted

theorem current_stop_boundary_accepts_symbol_residual_document :
    v8SymbolResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.symbolResidualDocumentAccepted

theorem current_stop_boundary_accepts_equation_residual_document :
    v8EquationResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.equationResidualDocumentAccepted

theorem current_stop_boundary_accepts_derivation_residual_document :
    v8DerivationResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.derivationResidualDocumentAccepted

theorem current_stop_boundary_accepts_qm_universal_pattern_residual_document :
    v8QmUniversalPatternResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.qmUniversalPatternResidualDocumentAccepted

theorem current_stop_boundary_accepts_qm_core_obligation_document :
    v8QmCoreObligationDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.qmCoreObligationDocumentAccepted

theorem current_stop_boundary_accepts_theorem_card_residual_document :
    v8TheoremCardResidualDocument.isAcceptedForV8 :=
  currentMigrationStopBoundary.theoremCardResidualDocumentAccepted

end V8
end MetaLang
end IDT
