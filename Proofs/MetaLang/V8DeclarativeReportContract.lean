import Proofs.MetaLang.V8CoreRuleSemanticClosure

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 declarative report contract.

This module mirrors the pass/fail discipline of the declarative checker. It is
not a Python implementation proof. It records the Lean-side contract that a
report with issues is not accepted, and an accepted report has no issues.
-/

inductive DeclarativeIssueCode where
  | specificationKindMismatch
  | languageVersionMismatch
  | vocabularyStatusUnknown
  | vocabularyFieldMissing
  | proposedTermWithoutApprovalGate
  | fieldMissing
  | fieldEmpty
  | fieldValueNotAllowed
  | forbiddenFieldValue
  | fieldMismatch
  | unknownReference
  | requiredValuesMissing
  | nestedFieldMismatch
  | missingFile
  | forbiddenIntersection
  | unknownAssertionPredicate
deriving DecidableEq, Repr

structure DeclarativeIssueRecord where
  code : DeclarativeIssueCode
  ruleId : String
  objectId : String
  message : String
deriving Repr

structure DeclarativeVerificationReport where
  specificationDocuments : List String
  rulesChecked : Nat
  issues : List DeclarativeIssueRecord
deriving Repr

def DeclarativeVerificationReport.ok
    (report : DeclarativeVerificationReport) : Prop :=
  report.issues = []

def DeclarativeVerificationReport.hasIssues
    (report : DeclarativeVerificationReport) : Prop :=
  report.issues ≠ []

structure AcceptedDeclarativeReport where
  report : DeclarativeVerificationReport
  ok : report.ok

theorem accepted_declarative_report_has_no_issues
    (accepted : AcceptedDeclarativeReport) :
    accepted.report.issues = [] :=
  accepted.ok

theorem report_with_issues_is_not_accepted
    (report : DeclarativeVerificationReport)
    (hasIssues : report.hasIssues) :
    ¬ report.ok := by
  intro ok
  exact hasIssues ok

theorem accepted_report_is_not_issue_bearing
    (accepted : AcceptedDeclarativeReport) :
    ¬ accepted.report.hasIssues := by
  intro hasIssues
  exact hasIssues accepted.ok

def DeclarativeVerificationReport.checkedAtLeastOneRule
    (report : DeclarativeVerificationReport) : Prop :=
  report.rulesChecked > 0

structure AcceptedCoreDeclarativeReport where
  accepted : AcceptedDeclarativeReport
  checkedRules : accepted.report.rulesChecked =
    v8CoreClaimDisciplineRules.length

theorem accepted_core_declarative_report_checked_six_rules
    (report : AcceptedCoreDeclarativeReport) :
    report.accepted.report.rulesChecked = 6 := by
  rw [report.checkedRules]
  exact v8_core_claim_discipline_has_six_rules

theorem accepted_core_declarative_report_has_no_issues
    (report : AcceptedCoreDeclarativeReport) :
    report.accepted.report.issues = [] :=
  accepted_declarative_report_has_no_issues report.accepted

end V8
end MetaLang
end IDT
