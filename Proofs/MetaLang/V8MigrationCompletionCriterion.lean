import Proofs.MetaLang.V8CurrentTheoremAndObligationLedger
import Proofs.MetaLang.V8ResidualEncodingRequirements

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 migration completion criterion.

This module states the local completion gate for the Lean-eligible migration
phase. It is a process criterion only: it does not prove physics and does not
upgrade any theorem card or QM obligation.
-/

structure LeanEligibleMigrationCriterion where
  theoremCardLedgerEncoded : Prop
  qmObligationLedgerEncoded : Prop
  noFalseFormalProofClosure : Prop
  noOpenOrBlockedTheoremCandidates : Prop
  noBlockedOrTargetQmObligations : Prop

def currentLeanEligibleMigrationCriterion : LeanEligibleMigrationCriterion :=
  {
    theoremCardLedgerEncoded := currentTheoremCardLedger.length = 23,
    qmObligationLedgerEncoded := currentQmObligationLedger.length = 11,
    noFalseFormalProofClosure :=
      currentLedgerTheoremCardFormalProofCount = 0
        ∧ currentLedgerQmObligationFormalProofCount = 0,
    noOpenOrBlockedTheoremCandidates := ¬ hasBlockedOrOpenTheoremCards,
    noBlockedOrTargetQmObligations := ¬ hasBlockedOrTargetQmObligations
  }

def LeanEligibleMigrationCriterion.isComplete
    (criterion : LeanEligibleMigrationCriterion) : Prop :=
  criterion.theoremCardLedgerEncoded
    ∧ criterion.qmObligationLedgerEncoded
    ∧ criterion.noFalseFormalProofClosure
    ∧ criterion.noOpenOrBlockedTheoremCandidates
    ∧ criterion.noBlockedOrTargetQmObligations

theorem current_lean_candidate_ledgers_are_encoded :
    currentLeanEligibleMigrationCriterion.theoremCardLedgerEncoded
      ∧ currentLeanEligibleMigrationCriterion.qmObligationLedgerEncoded := by
  exact And.intro current_theorem_card_ledger_count current_qm_obligation_ledger_count

theorem current_lean_candidate_ledgers_have_no_false_formal_closure :
    currentLeanEligibleMigrationCriterion.noFalseFormalProofClosure := by
  exact And.intro
    current_theorem_card_formal_proof_count_is_zero
    current_qm_obligation_formal_proof_count_is_zero

theorem current_lean_eligible_migration_is_not_complete :
    ¬ currentLeanEligibleMigrationCriterion.isComplete := by
  intro complete
  exact complete.2.2.2.1 current_theorem_cards_have_blockers

theorem current_lean_migration_task_must_remain_uncompleted :
    ¬ currentMigrationState.completedTasks.hasCompleted
      MigrationTask.migrateLeanEligibleMaterial :=
  current_state_has_not_completed_lean_migration_task

theorem current_residual_encoding_phase_is_blocked_by_incomplete_lean_migration :
    currentMigrationState.phaseBlocked MigrationPhase.idtV8ResidualEncoding :=
  current_state_blocks_idt_v8_residual_encoding

end V8
end MetaLang
end IDT
