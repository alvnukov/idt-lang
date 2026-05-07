import Proofs.MetaLang.V8TaskBlockerLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 current migration state.

This module records the active process state during migration. Later phases are
blocked unless their typed task blockers have been completed.
-/

structure MigrationState where
  currentPhase : MigrationPhase
  completedTasks : CompletedMigrationTasks
deriving Repr

def currentMigrationState : MigrationState :=
  {
    currentPhase := MigrationPhase.leanMigration,
    completedTasks := {
      completed := []
    }
  }

def MigrationState.phaseIsCurrent
    (state : MigrationState)
    (phase : MigrationPhase) : Prop :=
  state.currentPhase = phase

def MigrationState.phaseIsFuture
    (state : MigrationState)
    (phase : MigrationPhase) : Prop :=
  phasePrecedes state.currentPhase phase

def MigrationState.canEnterPhase
    (state : MigrationState)
    (phase : MigrationPhase) : Prop :=
  state.completedTasks.unblocks phase

def MigrationState.phaseBlocked
    (state : MigrationState)
    (phase : MigrationPhase) : Prop :=
  ¬ state.canEnterPhase phase

theorem current_state_is_lean_migration :
    currentMigrationState.phaseIsCurrent MigrationPhase.leanMigration := by
  rfl

theorem current_state_has_not_completed_lean_migration_task :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.migrateLeanEligibleMaterial := by
  simp [
    currentMigrationState,
    CompletedMigrationTasks.hasCompleted,
  ]

theorem current_state_has_not_completed_new_ci_task :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.buildNewCi := by
  simp [
    currentMigrationState,
    CompletedMigrationTasks.hasCompleted,
  ]

theorem current_state_has_not_completed_archive_task :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.archiveLegacyVerifier := by
  simp [
    currentMigrationState,
    CompletedMigrationTasks.hasCompleted,
  ]

theorem current_state_has_not_completed_research_context_packer_task :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.buildResearchContextPacker := by
  simp [
    currentMigrationState,
    CompletedMigrationTasks.hasCompleted,
  ]

theorem current_state_blocks_idt_v8_residual_encoding :
    currentMigrationState.phaseBlocked MigrationPhase.idtV8ResidualEncoding := by
  intro unblocked
  have completed :=
    phase_unblock_requires_blocking_task_completion
      currentMigrationState.completedTasks
      MigrationPhase.idtV8ResidualEncoding
      unblocked
      {
        task := MigrationTask.migrateLeanEligibleMaterial,
        blocksPhase := MigrationPhase.idtV8ResidualEncoding,
        requiredBeforePhase := MigrationPhase.idtV8ResidualEncoding
      }
      (by simp [currentTaskBlockers])
      rfl
  exact current_state_has_not_completed_lean_migration_task completed

theorem current_state_blocks_legacy_archive :
    currentMigrationState.phaseBlocked MigrationPhase.archiveLegacy := by
  intro unblocked
  have completed :=
    phase_unblock_requires_blocking_task_completion
      currentMigrationState.completedTasks
      MigrationPhase.archiveLegacy
      unblocked
      {
        task := MigrationTask.buildNewCi,
        blocksPhase := MigrationPhase.archiveLegacy,
        requiredBeforePhase := MigrationPhase.archiveLegacy
      }
      (by simp [currentTaskBlockers])
      rfl
  exact current_state_has_not_completed_new_ci_task completed

theorem current_state_blocks_research_ready :
    currentMigrationState.phaseBlocked MigrationPhase.researchReady := by
  intro unblocked
  have completed :=
    phase_unblock_requires_blocking_task_completion
      currentMigrationState.completedTasks
      MigrationPhase.researchReady
      unblocked
      {
        task := MigrationTask.buildResearchContextPacker,
        blocksPhase := MigrationPhase.researchReady,
        requiredBeforePhase := MigrationPhase.researchReady
      }
      (by simp [currentTaskBlockers])
      rfl
  exact current_state_has_not_completed_research_context_packer_task completed

end V8
end MetaLang
end IDT
