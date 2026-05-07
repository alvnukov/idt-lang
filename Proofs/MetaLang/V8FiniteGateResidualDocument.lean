import Proofs.MetaLang.V8TheoremCardResidualDocument

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 finite-gate residual document.

This module mirrors `rules/v8/finite_gate_residuals.idtl.json` as a Lean-side
accepted IDT v8 specification. The current finite-gate surface is still mostly
legacy-shaped, so this document intentionally records a minimal residual
boundary: every finite gate needs an id and type, and no finite-gate residual
may claim `formal_proof` status.
-/

def finiteGateResidualCoreFieldsRule : VerificationRuleSpec :=
  {
    id := "finite_gate_residual_core_fields_are_declared",
    collection := ManifestReferenceCollection.finiteGates,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def finiteGateResidualNoFormalProofStatusRule : VerificationRuleSpec :=
  {
    id := "finite_gate_residual_status_cannot_claim_formal_proof",
    collection := ManifestReferenceCollection.finiteGates,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNotIn
    ]
  }

def v8FiniteGateResidualDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_finite_gate_residuals",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      finiteGateResidualCoreFieldsRule,
      finiteGateResidualNoFormalProofStatusRule
    ]
  }

theorem finite_gate_residual_core_fields_rule_is_accepted_for_v8 :
    finiteGateResidualCoreFieldsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    finiteGateResidualCoreFieldsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem finite_gate_residual_no_formal_proof_rule_is_accepted_for_v8 :
    finiteGateResidualNoFormalProofStatusRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    finiteGateResidualNoFormalProofStatusRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_finite_gate_residual_document_is_accepted :
    v8FiniteGateResidualDocument.isAcceptedForV8 := by
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
    simp [v8FiniteGateResidualDocument] at rulePresent
    rcases rulePresent with rfl | rfl
    · exact finite_gate_residual_core_fields_rule_is_accepted_for_v8
    · exact finite_gate_residual_no_formal_proof_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
