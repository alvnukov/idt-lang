import Proofs.MetaLang.V8DeclarativeDocumentSchema

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 core claim-discipline document.

This file mirrors `rules/v8/core_claim_discipline.idtl.json` as a Lean object.
The JSON file can remain as a human-editable IDT v8 input, but this module is
the proof-side acceptance artifact for the current core discipline document.
-/

def assertion (predicate : AssertionPredicate) : AssertionSpec :=
  {
    predicate := predicate,
    fieldPath := "",
    parameters := []
  }

def theoremCardsUseControlledStatusesRule : VerificationRuleSpec :=
  {
    id := "theorem_cards_use_controlled_statuses",
    collection := ManifestReferenceCollection.theoremCards,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldIn,
      assertion AssertionPredicate.fieldIn,
      assertion AssertionPredicate.refsExist
    ]
  }

def finiteGateCoreFieldsAreDeclaredRule : VerificationRuleSpec :=
  {
    id := "finite_gate_core_fields_are_declared",
    collection := ManifestReferenceCollection.finiteGates,
    wherePredicate := none,
    idNonEmpty := by native_decide,
    assertions := [
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def qmRecompileRouteCountsAndRefsAreGroundedRule : VerificationRuleSpec :=
  {
    id := "qm_recompile_route_counts_and_refs_are_grounded",
    collection := ManifestReferenceCollection.finiteGates,
    idNonEmpty := by native_decide,
    wherePredicate := some
      (RuleWherePredicate.equals { fieldPath := "id" }
        "qm_core_recompile_route_demo"),
    assertions := [
      assertion AssertionPredicate.equalsField,
      assertion AssertionPredicate.equalsField,
      assertion AssertionPredicate.refsExist
    ]
  }

def contextFirstBaseUsesCandidateNotProofStatusRule : VerificationRuleSpec :=
  {
    id := "context_first_base_uses_candidate_not_proof_status",
    collection := ManifestReferenceCollection.finiteGates,
    idNonEmpty := by native_decide,
    wherePredicate := some
      (RuleWherePredicate.equals { fieldPath := "id" }
        "context_first_primitive_base_revision_demo"),
    assertions := [
      assertion AssertionPredicate.everyFieldEquals,
      assertion AssertionPredicate.listContainsAll
    ]
  }

def proofCardsHaveArtifactsAndCommandsRule : VerificationRuleSpec :=
  {
    id := "proof_cards_have_artifacts_and_commands",
    collection := ManifestReferenceCollection.finiteGates,
    idNonEmpty := by native_decide,
    wherePredicate := some
      (RuleWherePredicate.equals { fieldPath := "id" }
        "formal_proof_ledger_audit_demo"),
    assertions := [
      assertion AssertionPredicate.fileExists,
      assertion AssertionPredicate.fieldNonEmpty,
      assertion AssertionPredicate.fieldNotIn
    ]
  }

def formalProofStatusRequiresTheoremCardBoundaryRule : VerificationRuleSpec :=
  {
    id := "formal_proof_status_requires_theorem_card_boundary",
    collection := ManifestReferenceCollection.theoremCards,
    idNonEmpty := by native_decide,
    wherePredicate := some
      (RuleWherePredicate.equals { fieldPath := "proof_status" }
        "formal_proof"),
    assertions := [
      assertion AssertionPredicate.refsExist,
      assertion AssertionPredicate.fieldNonEmpty
    ]
  }

def v8CoreClaimDisciplineDocument : DeclarativeSpecificationDocument :=
  {
    id := "idt_v8_core_claim_discipline",
    kind := DeclarativeDocumentKind.verificationSpecification,
    languageMajor := 8,
    languageMinor := 0,
    controlledVocabulary := v8ControlledVocabulary,
    verificationRules := [
      theoremCardsUseControlledStatusesRule,
      finiteGateCoreFieldsAreDeclaredRule,
      qmRecompileRouteCountsAndRefsAreGroundedRule,
      contextFirstBaseUsesCandidateNotProofStatusRule,
      proofCardsHaveArtifactsAndCommandsRule,
      formalProofStatusRequiresTheoremCardBoundaryRule
    ]
  }

theorem assertion_has_lean_semantics
    (spec : AssertionSpec) :
    spec.hasLeanSemantics :=
  every_supported_python_predicate_has_v8_semantics spec.predicate

theorem theorem_cards_rule_is_accepted_for_v8 :
    theoremCardsUseControlledStatusesRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    theoremCardsUseControlledStatusesRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem finite_gate_core_rule_is_accepted_for_v8 :
    finiteGateCoreFieldsAreDeclaredRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    finiteGateCoreFieldsAreDeclaredRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem qm_recompile_rule_is_accepted_for_v8 :
    qmRecompileRouteCountsAndRefsAreGroundedRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    qmRecompileRouteCountsAndRefsAreGroundedRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem context_first_candidate_rule_is_accepted_for_v8 :
    contextFirstBaseUsesCandidateNotProofStatusRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    contextFirstBaseUsesCandidateNotProofStatusRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem proof_cards_rule_is_accepted_for_v8 :
    proofCardsHaveArtifactsAndCommandsRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    proofCardsHaveArtifactsAndCommandsRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem formal_proof_boundary_rule_is_accepted_for_v8 :
    formalProofStatusRequiresTheoremCardBoundaryRule.isAcceptedForV8 := by
  unfold VerificationRuleSpec.isAcceptedForV8
  simp [
    formalProofStatusRequiresTheoremCardBoundaryRule,
    VerificationRuleSpec.targetCollectionIsAllowed,
    v8ManifestReferenceCollections,
    VerificationRuleSpec.assertionsHaveLeanSemantics,
    assertion,
    AssertionSpec.hasLeanSemantics,
    every_supported_python_predicate_has_v8_semantics,
  ]

theorem v8_core_claim_discipline_document_is_accepted :
    v8CoreClaimDisciplineDocument.isAcceptedForV8 := by
  unfold DeclarativeSpecificationDocument.isAcceptedForV8
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact Nat.zero_lt_succ 9
  constructor
  · exact Nat.zero_lt_succ 5
  constructor
  · intro entry entryPresent proposed
    exact proposed_terms_in_v8_vocabulary_require_approval
      entry
      entryPresent
      proposed
  · intro rule rulePresent
    simp [v8CoreClaimDisciplineDocument] at rulePresent
    rcases rulePresent with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact theorem_cards_rule_is_accepted_for_v8
    · exact finite_gate_core_rule_is_accepted_for_v8
    · exact qm_recompile_rule_is_accepted_for_v8
    · exact context_first_candidate_rule_is_accepted_for_v8
    · exact proof_cards_rule_is_accepted_for_v8
    · exact formal_proof_boundary_rule_is_accepted_for_v8

end V8
end MetaLang
end IDT
