import Proofs.MetaLang.V8QmExperimentResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 QM core obligation document.

This module mirrors `rules/v8/qm_core_obligations.idtl.json` as a Lean-side
accepted IDT v8 specification. It keeps QM proof obligations in target,
conditional, regression-supported, or blocked states; it does not allow
`formal_proof` to appear as a residual-obligation status.
-/

def qmCoreObligationCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "qm_core_obligation_core_fields_are_declared",
    collection := ManifestReferenceCollection.qmCoreProofObligations,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldIn
    ]
  }

def qmCoreObligationRefsGroundedRule : VerificationRuleSpec :=
  {
    id := "qm_core_obligation_refs_are_grounded",
    collection := ManifestReferenceCollection.qmCoreProofObligations,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.refsExist
    ]
  }

def v8QmCoreObligationDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_qm_core_obligations",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      qmCoreObligationCoreFieldsRule,
      qmCoreObligationRefsGroundedRule
    ]
  }

theorem qm_core_obligation_core_fields_rule_is_accepted_for_v8 :
    qmCoreObligationCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmCoreObligationCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem qm_core_obligation_refs_rule_is_accepted_for_v8 :
    qmCoreObligationRefsGroundedRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmCoreObligationRefsGroundedRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_qm_core_obligation_document_is_accepted :
    v8QmCoreObligationDocument.isAcceptedForV8 := by
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
    simp [v8QmCoreObligationDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact qm_core_obligation_core_fields_rule_is_accepted_for_v8
    · exact qm_core_obligation_refs_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
