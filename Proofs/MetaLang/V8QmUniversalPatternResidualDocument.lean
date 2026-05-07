import Proofs.MetaLang.V8DerivationResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 QM universal-pattern residual document.

This module mirrors `rules/v8/qm_universal_pattern_residuals.idtl.json` as a
Lean-side accepted IDT v8 specification. These pattern rows remain residual
organizing inputs; they do not prove universal QM closure.
-/

def qmUniversalPatternResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "qm_universal_pattern_core_fields_are_declared",
    collection := ManifestReferenceCollection.qmUniversalPatterns,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def qmUniversalPatternResidualRefsGroundedRule : VerificationRuleSpec :=
  {
    id := "qm_universal_pattern_refs_are_grounded",
    collection := ManifestReferenceCollection.qmUniversalPatterns,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.refsExist
    ]
  }

def v8QmUniversalPatternResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_qm_universal_pattern_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      qmUniversalPatternResidualCoreFieldsRule,
      qmUniversalPatternResidualRefsGroundedRule
    ]
  }

theorem qm_universal_pattern_core_fields_rule_is_accepted_for_v8 :
    qmUniversalPatternResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmUniversalPatternResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem qm_universal_pattern_refs_rule_is_accepted_for_v8 :
    qmUniversalPatternResidualRefsGroundedRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmUniversalPatternResidualRefsGroundedRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_qm_universal_pattern_residual_document_is_accepted :
    v8QmUniversalPatternResidualDocument.isAcceptedForV8 := by
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
    simp [v8QmUniversalPatternResidualDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact qm_universal_pattern_core_fields_rule_is_accepted_for_v8
    · exact qm_universal_pattern_refs_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
