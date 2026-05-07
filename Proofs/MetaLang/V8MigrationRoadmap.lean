import Proofs.MetaLang.V8CoreClaimDisciplineDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 migration roadmap.

This file records the current project plan as a proof-side process boundary.
No new research is allowed during this migration phase:

1. migrate everything that can be migrated into Lean;
2. encode the remaining non-Lean material in IDT v8;
3. stop at that boundary;
4. only then build new CI;
5. archive legacy verifier infrastructure;
6. hand the repository back to a research model.
-/

inductive MigrationPhase where
  | leanMigration
  | idtV8ResidualEncoding
  | migrationStop
  | newCi
  | archiveLegacy
  | researchReady
deriving DecidableEq, Repr

def MigrationPhase.rank : MigrationPhase → Nat
  | MigrationPhase.leanMigration => 0
  | MigrationPhase.idtV8ResidualEncoding => 1
  | MigrationPhase.migrationStop => 2
  | MigrationPhase.newCi => 3
  | MigrationPhase.archiveLegacy => 4
  | MigrationPhase.researchReady => 5

def phasePrecedes (left right : MigrationPhase) : Prop :=
  left.rank < right.rank

structure MigrationRoadmap where
  phases : List MigrationPhase
deriving Repr

def v8LeanIdtMigrationRoadmap : MigrationRoadmap :=
  {
    phases := [
      MigrationPhase.leanMigration,
      MigrationPhase.idtV8ResidualEncoding,
      MigrationPhase.migrationStop,
      MigrationPhase.newCi,
      MigrationPhase.archiveLegacy,
      MigrationPhase.researchReady
    ]
  }

theorem lean_migration_precedes_idt_v8_residual_encoding :
    phasePrecedes
      MigrationPhase.leanMigration
      MigrationPhase.idtV8ResidualEncoding := by
  unfold phasePrecedes
  decide

theorem idt_v8_residual_encoding_precedes_migration_stop :
    phasePrecedes
      MigrationPhase.idtV8ResidualEncoding
      MigrationPhase.migrationStop := by
  unfold phasePrecedes
  decide

theorem migration_stop_precedes_new_ci :
    phasePrecedes
      MigrationPhase.migrationStop
      MigrationPhase.newCi := by
  unfold phasePrecedes
  decide

theorem new_ci_precedes_legacy_archive :
    phasePrecedes
      MigrationPhase.newCi
      MigrationPhase.archiveLegacy := by
  unfold phasePrecedes
  decide

theorem legacy_archive_precedes_research_ready :
    phasePrecedes
      MigrationPhase.archiveLegacy
      MigrationPhase.researchReady := by
  unfold phasePrecedes
  decide

theorem research_is_after_migration_stop :
    phasePrecedes
      MigrationPhase.migrationStop
      MigrationPhase.researchReady := by
  unfold phasePrecedes
  decide

theorem ci_is_after_migration_stop :
    phasePrecedes
      MigrationPhase.migrationStop
      MigrationPhase.newCi := by
  unfold phasePrecedes
  decide

theorem legacy_archive_is_after_new_ci :
    phasePrecedes
      MigrationPhase.newCi
      MigrationPhase.archiveLegacy := by
  unfold phasePrecedes
  decide

end V8
end MetaLang
end IDT
