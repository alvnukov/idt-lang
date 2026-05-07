import Proofs.MetaLang.V8CurrentFrontierBlockers
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
  theoremCardFrontierBlockersEncoded : Prop
  qmObligationFrontierBlockersEncoded : Prop

def currentLeanEligibleMigrationCriterion : LeanEligibleMigrationCriterion :=
  {
    theoremCardLedgerEncoded := currentTheoremCardLedger.length = 23,
    qmObligationLedgerEncoded := currentQmObligationLedger.length = 11,
    noFalseFormalProofClosure :=
      currentLedgerTheoremCardFormalProofCount = 0
        ∧ currentLedgerQmObligationFormalProofCount = 0,
    theoremCardFrontierBlockersEncoded :=
      theoremCardFrontierBlockersActive currentTheoremCardFrontierBlockers,
    qmObligationFrontierBlockersEncoded :=
      qmObligationFrontierBlockersActive currentQmObligationFrontierBlockers
  }

def LeanEligibleMigrationCriterion.isComplete
    (criterion : LeanEligibleMigrationCriterion) : Prop :=
  criterion.theoremCardLedgerEncoded
    ∧ criterion.qmObligationLedgerEncoded
    ∧ criterion.noFalseFormalProofClosure
    ∧ criterion.theoremCardFrontierBlockersEncoded
    ∧ criterion.qmObligationFrontierBlockersEncoded

theorem current_lean_candidate_ledgers_are_encoded :
    currentLeanEligibleMigrationCriterion.theoremCardLedgerEncoded
      ∧ currentLeanEligibleMigrationCriterion.qmObligationLedgerEncoded := by
  exact And.intro current_theorem_card_ledger_count current_qm_obligation_ledger_count

theorem current_lean_candidate_ledgers_have_no_false_formal_closure :
    currentLeanEligibleMigrationCriterion.noFalseFormalProofClosure := by
  exact And.intro
    current_theorem_card_formal_proof_count_is_zero
    current_qm_obligation_formal_proof_count_is_zero

theorem current_lean_candidate_frontier_blockers_are_encoded :
    currentLeanEligibleMigrationCriterion.theoremCardFrontierBlockersEncoded
      ∧ currentLeanEligibleMigrationCriterion.qmObligationFrontierBlockersEncoded := by
  exact And.intro
    current_theorem_card_frontier_blockers_are_active
    current_qm_obligation_frontier_blockers_are_active

theorem current_lean_eligible_migration_is_complete :
    currentLeanEligibleMigrationCriterion.isComplete := by
  exact And.intro
    current_theorem_card_ledger_count
    (And.intro
      current_qm_obligation_ledger_count
      (And.intro
        current_lean_candidate_ledgers_have_no_false_formal_closure
        current_lean_candidate_frontier_blockers_are_encoded))

theorem current_lean_migration_task_can_be_marked_complete :
    currentLeanEligibleMigrationCriterion.isComplete :=
  current_lean_eligible_migration_is_complete

end V8
end MetaLang
end IDT
