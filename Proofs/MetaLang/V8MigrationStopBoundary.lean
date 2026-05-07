import Proofs.MetaLang.V8ResidualMigrationLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 migration stop boundary.

This module records the point where migration work must stop before any new CI,
legacy archive, or research handoff. The stop boundary requires:

* accepted Lean mirror of the core IDT v8 discipline document;
* accepted manifest input boundary;
* accepted residual migration ledger;
* old Python verifier marked deprecated compatibility only.
-/

structure MigrationStopBoundary where
  coreDocumentAccepted :
    v8CoreClaimDisciplineDocument.isAcceptedForV8
  manifestBoundaryAccepted :
    currentManifestInputBoundary.isAcceptedForV8
  residualBoundaryAccepted :
    currentResidualMigrationBoundary.isAcceptedForV8
  pythonDeprecated :
    oldPythonVerifierRole.isDeprecatedCompatibility

def currentMigrationStopBoundary : MigrationStopBoundary :=
  {
    coreDocumentAccepted := v8_core_claim_discipline_document_is_accepted,
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
  phasePrecedes MigrationPhase.archiveLegacy MigrationPhase.researchReady

theorem current_stop_boundary_allows_new_ci_only_after_stop :
    currentMigrationStopBoundary.allowsNewCi :=
  migration_stop_precedes_new_ci

theorem current_stop_boundary_allows_archive_only_after_new_ci :
    currentMigrationStopBoundary.allowsLegacyArchive :=
  new_ci_precedes_legacy_archive

theorem current_stop_boundary_allows_research_only_after_archive :
    currentMigrationStopBoundary.allowsResearchHandoff :=
  legacy_archive_precedes_research_ready

theorem current_stop_boundary_keeps_python_deprecated :
    oldPythonVerifierRole.isDeprecatedCompatibility :=
  currentMigrationStopBoundary.pythonDeprecated

theorem current_stop_boundary_keeps_manifest_non_proof_authority :
    currentManifestInputBoundary.proofAuthority ≠
      VerificationAuthority.proofTruth :=
  current_manifest_boundary_is_not_proof_truth

end V8
end MetaLang
end IDT
