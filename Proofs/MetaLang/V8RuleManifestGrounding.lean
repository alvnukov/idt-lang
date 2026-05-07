import Proofs.MetaLang.V8ManifestCollectionContract

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 rule-manifest grounding.

This module connects the core declarative rule inventory to the manifest
collection contract. A core rule may only target a collection that is allowed
by the v8 manifest reference-index boundary.
-/

def RuleCollection.toManifestReferenceCollection
    (collection : RuleCollection) : ManifestReferenceCollection :=
  match collection with
  | RuleCollection.theoremCards =>
      ManifestReferenceCollection.theoremCards
  | RuleCollection.finiteGates =>
      ManifestReferenceCollection.finiteGates

def CoreRuleSpec.targetsAllowedManifestCollection
    (rule : CoreRuleSpec) : Prop :=
  rule.collection.toManifestReferenceCollection ∈
    v8ManifestReferenceCollections

theorem theorem_card_rule_collection_is_manifest_grounded :
    theoremCardsUseControlledStatusesSpec
      |>.targetsAllowedManifestCollection := by
  simp [
    CoreRuleSpec.targetsAllowedManifestCollection,
    RuleCollection.toManifestReferenceCollection,
    theoremCardsUseControlledStatusesSpec,
    v8ManifestReferenceCollections,
  ]

theorem finite_gate_rule_collection_is_manifest_grounded :
    finiteGateCoreFieldsAreDeclaredSpec
      |>.targetsAllowedManifestCollection := by
  simp [
    CoreRuleSpec.targetsAllowedManifestCollection,
    RuleCollection.toManifestReferenceCollection,
    finiteGateCoreFieldsAreDeclaredSpec,
    v8ManifestReferenceCollections,
  ]

theorem v8_core_rule_collections_are_manifest_grounded
    (rule : CoreRuleSpec)
    (rulePresent : rule ∈ v8CoreClaimDisciplineRules) :
    rule.targetsAllowedManifestCollection := by
  simp [
    v8CoreClaimDisciplineRules,
    CoreRuleSpec.targetsAllowedManifestCollection,
    RuleCollection.toManifestReferenceCollection,
    theoremCardsUseControlledStatusesSpec,
    finiteGateCoreFieldsAreDeclaredSpec,
    qmRecompileRouteCountsAndRefsAreGroundedSpec,
    contextFirstBaseUsesCandidateNotProofStatusSpec,
    proofCardsHaveArtifactsAndCommandsSpec,
    formalProofStatusRequiresTheoremCardBoundarySpec,
    v8ManifestReferenceCollections,
  ] at rulePresent ⊢
  rcases rulePresent with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

theorem v8_core_rules_can_use_manifest_reference_queries
    (rule : CoreRuleSpec)
    (rulePresent : rule ∈ v8CoreClaimDisciplineRules) :
    ManifestReferenceSelector.named
      rule.collection.toManifestReferenceCollection
      |>.isAllowedForV8 :=
  v8_core_rule_collections_are_manifest_grounded rule rulePresent

end V8
end MetaLang
end IDT
