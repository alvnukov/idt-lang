import Proofs.MetaLang.V8QmCoreObligationDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 theorem-card residual document.

This module mirrors `rules/v8/theorem_card_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. It keeps current theorem cards in residual
statuses and requires grounded dependencies, grounded verifier gates, physical
scope, and forbidden-claim boundaries.
-/

def theoremCardResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "theorem_card_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.theoremCards,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldIn,
      assertion AssertionPredicate.fieldIn
    ]
  }

def theoremCardResidualRefsAndBoundariesRule : VerificationRuleSpec :=
  {
    id := "theorem_card_residual_refs_and_boundaries_are_grounded",
    collection := ManifestReferenceCollection.theoremCards,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def v8TheoremCardResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_theorem_card_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      theoremCardResidualCoreFieldsRule,
      theoremCardResidualRefsAndBoundariesRule
    ]
  }

theorem theorem_card_residual_core_fields_rule_is_accepted_for_v8 :
    theoremCardResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    theoremCardResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem theorem_card_residual_refs_rule_is_accepted_for_v8 :
    theoremCardResidualRefsAndBoundariesRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    theoremCardResidualRefsAndBoundariesRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_theorem_card_residual_document_is_accepted :
    v8TheoremCardResidualDocument.isAcceptedForV8 := by
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
    simp [v8TheoremCardResidualDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact theorem_card_residual_core_fields_rule_is_accepted_for_v8
    · exact theorem_card_residual_refs_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
