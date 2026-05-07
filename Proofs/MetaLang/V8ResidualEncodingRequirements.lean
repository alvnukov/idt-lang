import Proofs.MetaLang.V8CurrentMigrationState
import Proofs.MetaLang.V8ResidualGateExperimentProfile

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 residual encoding requirements.

This module records when the repository may move from Lean migration into IDT
v8 residual encoding. It deliberately does not classify the residual physics
material and does not turn finite gates or experiments into proof truth.
-/

structure ResidualEncodingRequirements where
  gateExperimentBoundaryAccepted : Prop
  qmExperimentsClassified : Prop
  residualInputAuthorityOnly : Prop

def currentResidualEncodingRequirements : ResidualEncodingRequirements :=
  {
    gateExperimentBoundaryAccepted :=
      currentResidualGateExperimentBoundary.isAcceptedForV8,
    qmExperimentsClassified :=
      currentResidualQmExperimentProfile.isIdtV8Classified,
    residualInputAuthorityOnly :=
      currentResidualGateExperimentBoundary.authority =
        VerificationAuthority.declarativeInputCheck
  }

def ResidualEncodingRequirements.readyForMigrationStop
    (requirements : ResidualEncodingRequirements) : Prop :=
  requirements.gateExperimentBoundaryAccepted
    ∧ requirements.qmExperimentsClassified
    ∧ requirements.residualInputAuthorityOnly

theorem current_residual_encoding_requirements_grounded :
    currentResidualEncodingRequirements.gateExperimentBoundaryAccepted
      ∧ currentResidualEncodingRequirements.qmExperimentsClassified
      ∧ currentResidualEncodingRequirements.residualInputAuthorityOnly := by
  exact And.intro
    current_residual_gate_experiment_boundary_is_accepted
    (And.intro current_qm_experiments_are_idt_v8_classified rfl)

theorem current_residual_encoding_ready_for_migration_stop :
    currentResidualEncodingRequirements.readyForMigrationStop := by
  exact current_residual_encoding_requirements_grounded

theorem current_state_has_not_completed_residual_encoding_task :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.encodeResidualMaterialInIdtV8 := by
  simp [
    currentMigrationState,
    CompletedMigrationTasks.hasCompleted,
  ]

theorem current_state_blocks_migration_stop :
    currentMigrationState.phaseBlocked MigrationPhase.migrationStop := by
  intro unblocked
  have completed :=
    phase_unblock_requires_blocking_task_completion
      currentMigrationState.completedTasks
      MigrationPhase.migrationStop
      unblocked
      {
        task := MigrationTask.encodeResidualMaterialInIdtV8,
        blocksPhase := MigrationPhase.migrationStop,
        requiredBeforePhase := MigrationPhase.migrationStop
      }
      (by simp [currentTaskBlockers])
      rfl
  exact current_state_has_not_completed_residual_encoding_task completed

end V8
end MetaLang
end IDT
