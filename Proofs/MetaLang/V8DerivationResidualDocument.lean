import Proofs.MetaLang.V8EquationResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 derivation residual document.

This module mirrors `rules/v8/derivation_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. A manifest derivation remains a residual route
until a Lean artifact or IDT v8 residual semantics discharges it.
-/

def derivationResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "derivation_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.derivations,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldIn,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def derivationResidualRefsGroundedRule : VerificationRuleSpec :=
  {
    id := "derivation_residual_refs_are_grounded",
    collection := ManifestReferenceCollection.derivations,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.refsExist
    ]
  }

def v8DerivationResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_derivation_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      derivationResidualCoreFieldsRule,
      derivationResidualRefsGroundedRule
    ]
  }

theorem derivation_residual_core_fields_rule_is_accepted_for_v8 :
    derivationResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    derivationResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem derivation_residual_refs_rule_is_accepted_for_v8 :
    derivationResidualRefsGroundedRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    derivationResidualRefsGroundedRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_derivation_residual_document_is_accepted :
    v8DerivationResidualDocument.isAcceptedForV8 := by
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
    simp [v8DerivationResidualDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact derivation_residual_core_fields_rule_is_accepted_for_v8
    · exact derivation_residual_refs_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
