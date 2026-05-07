import Proofs.MetaLang.V8ResidualRouteClassification

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 task blocker ledger.

Lean is used here as a governance layer: project tasks become typed blockers
for phase transitions. This file does not add physical claims or CI work.
-/

inductive MigrationTask where
  | migrateLeanEligibleMaterial
  | encodeResidualMaterialInIdtV8
  | reachMigrationStopBoundary
  | buildNewCi
  | archiveLegacyVerifier
  | buildResearchContextPacker
  | handoffToResearchModel
deriving DecidableEq, Repr

structure TaskBlocker where
  task : MigrationTask
  blocksPhase : MigrationPhase
  requiredBeforePhase : MigrationPhase
deriving Repr

def currentTaskBlockers : List TaskBlocker :=
  [
    {
      task := MigrationTask.migrateLeanEligibleMaterial,
      blocksPhase := MigrationPhase.idtV8ResidualEncoding,
      requiredBeforePhase := MigrationPhase.idtV8ResidualEncoding
    },
    {
      task := MigrationTask.encodeResidualMaterialInIdtV8,
      blocksPhase := MigrationPhase.migrationStop,
      requiredBeforePhase := MigrationPhase.migrationStop
    },
    {
      task := MigrationTask.reachMigrationStopBoundary,
      blocksPhase := MigrationPhase.newCi,
      requiredBeforePhase := MigrationPhase.newCi
    },
    {
      task := MigrationTask.buildNewCi,
      blocksPhase := MigrationPhase.archiveLegacy,
      requiredBeforePhase := MigrationPhase.archiveLegacy
    },
    {
      task := MigrationTask.archiveLegacyVerifier,
      blocksPhase := MigrationPhase.researchContextPacker,
      requiredBeforePhase := MigrationPhase.researchContextPacker
    },
    {
      task := MigrationTask.buildResearchContextPacker,
      blocksPhase := MigrationPhase.researchReady,
      requiredBeforePhase := MigrationPhase.researchReady
    }
  ]

def TaskBlocker.isOrdered (blocker : TaskBlocker) : Prop :=
  phasePrecedes blocker.requiredBeforePhase blocker.blocksPhase
    ∨ blocker.requiredBeforePhase = blocker.blocksPhase

def allTaskBlockersOrdered (blockers : List TaskBlocker) : Prop :=
  ∀ blocker, blocker ∈ blockers → blocker.isOrdered

theorem current_task_blockers_are_ordered :
    allTaskBlockersOrdered currentTaskBlockers := by
  intro blocker blockerPresent
  simp [currentTaskBlockers] at blockerPresent
  rcases blockerPresent with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold TaskBlocker.isOrdered
    right
    rfl

def taskBlocksPhase
    (task : MigrationTask)
    (phase : MigrationPhase)
    (blockers : List TaskBlocker) : Prop :=
  ∃ blocker, blocker ∈ blockers
    ∧ blocker.task = task
    ∧ blocker.blocksPhase = phase

theorem migration_stop_task_blocks_new_ci :
    taskBlocksPhase
      MigrationTask.reachMigrationStopBoundary
      MigrationPhase.newCi
      currentTaskBlockers := by
  exact ⟨{
      task := MigrationTask.reachMigrationStopBoundary,
      blocksPhase := MigrationPhase.newCi,
      requiredBeforePhase := MigrationPhase.newCi
    },
    by simp [currentTaskBlockers],
    And.intro rfl rfl⟩

theorem new_ci_task_blocks_legacy_archive :
    taskBlocksPhase
      MigrationTask.buildNewCi
      MigrationPhase.archiveLegacy
      currentTaskBlockers := by
  exact ⟨{
      task := MigrationTask.buildNewCi,
      blocksPhase := MigrationPhase.archiveLegacy,
      requiredBeforePhase := MigrationPhase.archiveLegacy
    },
    by simp [currentTaskBlockers],
    And.intro rfl rfl⟩

theorem research_context_packer_task_blocks_research_ready :
    taskBlocksPhase
      MigrationTask.buildResearchContextPacker
      MigrationPhase.researchReady
      currentTaskBlockers := by
  exact ⟨{
      task := MigrationTask.buildResearchContextPacker,
      blocksPhase := MigrationPhase.researchReady,
      requiredBeforePhase := MigrationPhase.researchReady
    },
    by simp [currentTaskBlockers],
    And.intro rfl rfl⟩

structure CompletedMigrationTasks where
  completed : List MigrationTask
deriving Repr

def CompletedMigrationTasks.hasCompleted
    (tasks : CompletedMigrationTasks)
    (task : MigrationTask) : Prop :=
  task ∈ tasks.completed

def CompletedMigrationTasks.unblocks
    (tasks : CompletedMigrationTasks)
    (phase : MigrationPhase) : Prop :=
  ∀ blocker, blocker ∈ currentTaskBlockers →
    blocker.blocksPhase = phase →
      tasks.hasCompleted blocker.task

theorem phase_unblock_requires_blocking_task_completion
    (tasks : CompletedMigrationTasks)
    (phase : MigrationPhase)
    (unblocked : tasks.unblocks phase)
    (blocker : TaskBlocker)
    (blockerPresent : blocker ∈ currentTaskBlockers)
    (blocks : blocker.blocksPhase = phase) :
    tasks.hasCompleted blocker.task :=
  unblocked blocker blockerPresent blocks

end V8
end MetaLang
end IDT
