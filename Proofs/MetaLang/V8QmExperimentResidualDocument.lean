import Proofs.MetaLang.V8CoreClaimDisciplineDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 QM experiment residual document.

This module mirrors `rules/v8/qm_experiment_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. It constrains residual experiment rows as
executable-gate inputs with grounded finite-gate references; it does not
classify the experiments or promote them to formal proofs.
-/

def qmExperimentResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "qm_experiment_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.qmExperiments,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldIn
    ]
  }

def qmExperimentResidualRefsGroundedRule : VerificationRuleSpec :=
  {
    id := "qm_experiment_residual_refs_are_grounded",
    collection := ManifestReferenceCollection.qmExperiments,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def v8QmExperimentResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_qm_experiment_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      qmExperimentResidualCoreFieldsRule,
      qmExperimentResidualRefsGroundedRule
    ]
  }

theorem qm_experiment_residual_core_fields_rule_is_accepted_for_v8 :
    qmExperimentResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmExperimentResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem qm_experiment_residual_refs_rule_is_accepted_for_v8 :
    qmExperimentResidualRefsGroundedRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmExperimentResidualRefsGroundedRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_qm_experiment_residual_document_is_accepted :
    v8QmExperimentResidualDocument.isAcceptedForV8 := by
  unfold DeclarativeSpecificationDocument.isAcceptedForV8
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact Nat.zero_lt_succ 9
  constructor
  · exact Nat.zero_lt_succ 1
  constructor
  · intro entry entryPresent proposed
    exact proposed_terms_in_v8_vocabulary_require_approval
      entry
      entryPresent
      proposed
  · intro rule rulePresent
    simp [v8QmExperimentResidualDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact qm_experiment_residual_core_fields_rule_is_accepted_for_v8
    · exact qm_experiment_residual_refs_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
