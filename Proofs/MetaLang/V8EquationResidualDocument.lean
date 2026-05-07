import Proofs.MetaLang.V8SymbolResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 equation residual document.

This module mirrors `rules/v8/equation_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. It keeps equations as grounded residual inputs
until migrated into Lean theorem artifacts or IDT v8 residual semantics.
-/

def equationResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "equation_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.equations,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.refsExist
    ]
  }

def v8EquationResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_equation_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      equationResidualCoreFieldsRule
    ]
  }

theorem equation_residual_core_fields_rule_is_accepted_for_v8 :
    equationResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    equationResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_equation_residual_document_is_accepted :
    v8EquationResidualDocument.isAcceptedForV8 := by
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
    simp [v8EquationResidualDocument] at rulePresent
    rcases rulePresent with rfl
    exact equation_residual_core_fields_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
