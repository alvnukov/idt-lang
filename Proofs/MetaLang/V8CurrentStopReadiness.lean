import Proofs.MetaLang.V8ExperimentProgramReadiness

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 current stop readiness.

This module composes the active blockers that prevent the repository from
leaving migration mode. It is a stop/readiness ledger, not a research result.
-/

structure CurrentStopReadiness where
  leanEligibleMigrationComplete : Prop
  residualEncodingReady : Prop
  experimentProgramReady : Prop
  noPhysicalFormalProofUpgrade : Prop

def currentStopReadiness : CurrentStopReadiness :=
  {
    leanEligibleMigrationComplete :=
      currentLeanEligibleMigrationCriterion.isComplete,
    residualEncodingReady :=
      currentResidualEncodingRequirements.readyForMigrationStop,
    experimentProgramReady :=
      currentExperimentProgramReadiness.readyForResearchHandoff,
    noPhysicalFormalProofUpgrade :=
      currentLedgerTheoremCardFormalProofCount = 0
        ∧ currentLedgerQmObligationFormalProofCount = 0
        ∧ qmExperimentResidualFormalProofCount = 0
  }

def CurrentStopReadiness.readyForMigrationStop
    (readiness : CurrentStopReadiness) : Prop :=
  readiness.leanEligibleMigrationComplete
    ∧ readiness.residualEncodingReady
    ∧ readiness.experimentProgramReady
    ∧ readiness.noPhysicalFormalProofUpgrade

theorem current_stop_readiness_preserves_no_physical_formal_upgrade :
    currentStopReadiness.noPhysicalFormalProofUpgrade := by
  exact And.intro
    current_theorem_card_formal_proof_count_is_zero
    (And.intro
      current_qm_obligation_formal_proof_count_is_zero
      current_qm_experiment_residuals_have_no_formal_proof_closure)

theorem current_stop_readiness_blocked_by_lean_migration :
    ¬ currentStopReadiness.leanEligibleMigrationComplete :=
  current_lean_eligible_migration_is_not_complete

theorem current_stop_readiness_residual_encoding_ready :
    currentStopReadiness.residualEncodingReady :=
  current_residual_encoding_ready_for_migration_stop

theorem current_stop_readiness_experiment_program_ready :
    currentStopReadiness.experimentProgramReady :=
  current_experiment_program_readiness_is_locally_ready

theorem current_stop_readiness_is_not_ready_for_migration_stop :
    ¬ currentStopReadiness.readyForMigrationStop := by
  intro ready
  exact current_stop_readiness_blocked_by_lean_migration ready.1

end V8
end MetaLang
end IDT
