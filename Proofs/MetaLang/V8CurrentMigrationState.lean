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
    currentPhase := MigrationPhase.migrationStop,
    completedTasks := {
      completed := [
        MigrationTask.migrateLeanEligibleMaterial,
        MigrationTask.encodeResidualMaterialInIdtV8,
        MigrationTask.reachMigrationStopBoundary
      ]
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

theorem current_state_is_migration_stop :
    currentMigrationState.phaseIsCurrent MigrationPhase.migrationStop := by
  rfl

theorem current_state_has_completed_lean_migration_task :
    currentMigrationState.completedTasks.hasCompleted
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

theorem current_state_has_completed_migration_stop_task :
    currentMigrationState.completedTasks.hasCompleted
      MigrationTask.reachMigrationStopBoundary := by
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

theorem current_state_allows_idt_v8_residual_encoding :
    currentMigrationState.canEnterPhase MigrationPhase.idtV8ResidualEncoding := by
  intro blocker blockerPresent blocks
  simp [currentTaskBlockers] at blockerPresent
  rcases blockerPresent with rfl | rfl | rfl | rfl | rfl | rfl
  · exact current_state_has_completed_lean_migration_task
  all_goals contradiction

theorem current_state_allows_new_ci :
    currentMigrationState.canEnterPhase MigrationPhase.newCi := by
  intro blocker blockerPresent blocks
  simp [currentTaskBlockers] at blockerPresent
  rcases blockerPresent with rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · contradiction
  · exact current_state_has_completed_migration_stop_task
  all_goals contradiction

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

theorem current_state_blocks_research_context_packer :
    currentMigrationState.phaseBlocked MigrationPhase.researchContextPacker := by
  intro unblocked
  have completed :=
    phase_unblock_requires_blocking_task_completion
      currentMigrationState.completedTasks
      MigrationPhase.researchContextPacker
      unblocked
      {
        task := MigrationTask.archiveLegacyVerifier,
        blocksPhase := MigrationPhase.researchContextPacker,
        requiredBeforePhase := MigrationPhase.researchContextPacker
      }
      (by simp [currentTaskBlockers])
      rfl
  exact current_state_has_not_completed_archive_task completed

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
