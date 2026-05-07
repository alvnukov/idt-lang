import Proofs.MetaLang.V8CoreClaimDisciplineDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 symbol residual document.

This module mirrors `rules/v8/symbol_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. It classifies symbols as residual manifest
inputs, not as proof truth.
-/

def symbolResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "symbol_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.symbols,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldRequired,
      assertion AssertionPredicate.fieldIn
    ]
  }

def v8SymbolResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_symbol_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      symbolResidualCoreFieldsRule
    ]
  }

theorem symbol_residual_core_fields_rule_is_accepted_for_v8 :
    symbolResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    symbolResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_symbol_residual_document_is_accepted :
    v8SymbolResidualDocument.isAcceptedForV8 := by
  unfold DeclarativeSpecificationDocument.isAcceptedForV8
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact Nat.zero_lt_succ 9
  constructor
  · exact Nat.zero_lt_succ 0
  constructor
  · intro entry entryPresent proposed
    exact proposed_terms_in_v8_vocabulary_require_approval
      entry
      entryPresent
      proposed
  · intro rule rulePresent
    simp [v8SymbolResidualDocument] at rulePresent
    rcases rulePresent with rfl
    exact symbol_residual_core_fields_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
