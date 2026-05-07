import Proofs.MetaLang.V8LeanFirstTrustKernel

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 core claim-discipline rule inventory.

The JSON `.idtl.json` file remains a research/declarative input. This Lean file
records the already accepted v8 rule inventory as a proof-side contract: the
core specification has exactly the known rule identifiers, target collections,
and assertion predicate shapes.
-/

inductive RuleCollection where
  | theoremCards
  | finiteGates
deriving DecidableEq, Repr

inductive AssertionPredicate where
  | fieldRequired
  | fieldNonEmpty
  | fieldIn
  | fieldNotIn
  | equalsField
  | refsExist
  | listContainsAll
  | everyFieldEquals
  | fileExists
  | noIntersection
deriving DecidableEq, Repr

inductive CoreClaimDisciplineRuleId where
  | theoremCardsUseControlledStatuses
  | finiteGateCoreFieldsAreDeclared
  | qmRecompileRouteCountsAndRefsAreGrounded
  | contextFirstBaseUsesCandidateNotProofStatus
  | proofCardsHaveArtifactsAndCommands
  | formalProofStatusRequiresTheoremCardBoundary
deriving DecidableEq, Repr

structure CoreRuleSpec where
  id : CoreClaimDisciplineRuleId
  collection : RuleCollection
  predicates : List AssertionPredicate
deriving DecidableEq, Repr

def theoremCardsUseControlledStatusesSpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.theoremCardsUseControlledStatuses,
    collection := RuleCollection.theoremCards,
    predicates := [
      AssertionPredicate.fieldNonEmpty,
      AssertionPredicate.fieldIn,
      AssertionPredicate.fieldIn,
      AssertionPredicate.refsExist
    ]
  }

def finiteGateCoreFieldsAreDeclaredSpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.finiteGateCoreFieldsAreDeclared,
    collection := RuleCollection.finiteGates,
    predicates := [
      AssertionPredicate.fieldNonEmpty,
      AssertionPredicate.fieldNonEmpty
    ]
  }

def qmRecompileRouteCountsAndRefsAreGroundedSpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.qmRecompileRouteCountsAndRefsAreGrounded,
    collection := RuleCollection.finiteGates,
    predicates := [
      AssertionPredicate.equalsField,
      AssertionPredicate.equalsField,
      AssertionPredicate.refsExist
    ]
  }

def contextFirstBaseUsesCandidateNotProofStatusSpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.contextFirstBaseUsesCandidateNotProofStatus,
    collection := RuleCollection.finiteGates,
    predicates := [
      AssertionPredicate.everyFieldEquals,
      AssertionPredicate.listContainsAll
    ]
  }

def proofCardsHaveArtifactsAndCommandsSpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.proofCardsHaveArtifactsAndCommands,
    collection := RuleCollection.finiteGates,
    predicates := [
      AssertionPredicate.fileExists,
      AssertionPredicate.fieldNonEmpty,
      AssertionPredicate.fieldNotIn
    ]
  }

def formalProofStatusRequiresTheoremCardBoundarySpec : CoreRuleSpec :=
  {
    id := CoreClaimDisciplineRuleId.formalProofStatusRequiresTheoremCardBoundary,
    collection := RuleCollection.theoremCards,
    predicates := [
      AssertionPredicate.refsExist,
      AssertionPredicate.fieldNonEmpty
    ]
  }

def v8CoreClaimDisciplineRules : List CoreRuleSpec :=
  [
    theoremCardsUseControlledStatusesSpec,
    finiteGateCoreFieldsAreDeclaredSpec,
    qmRecompileRouteCountsAndRefsAreGroundedSpec,
    contextFirstBaseUsesCandidateNotProofStatusSpec,
    proofCardsHaveArtifactsAndCommandsSpec,
    formalProofStatusRequiresTheoremCardBoundarySpec
  ]

def CoreRuleSpec.hasPredicate
    (rule : CoreRuleSpec)
    (predicate : AssertionPredicate) : Prop :=
  predicate ∈ rule.predicates

theorem v8_core_claim_discipline_has_six_rules :
    v8CoreClaimDisciplineRules.length = 6 := by
  rfl

theorem v8_core_claim_discipline_contains_theorem_card_status_rule :
    theoremCardsUseControlledStatusesSpec ∈ v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem v8_core_claim_discipline_contains_finite_gate_core_rule :
    finiteGateCoreFieldsAreDeclaredSpec ∈ v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem v8_core_claim_discipline_contains_qm_recompile_grounding_rule :
    qmRecompileRouteCountsAndRefsAreGroundedSpec ∈ v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem v8_core_claim_discipline_contains_context_first_candidate_rule :
    contextFirstBaseUsesCandidateNotProofStatusSpec ∈
      v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem v8_core_claim_discipline_contains_proof_card_artifact_rule :
    proofCardsHaveArtifactsAndCommandsSpec ∈ v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem v8_core_claim_discipline_contains_formal_proof_boundary_rule :
    formalProofStatusRequiresTheoremCardBoundarySpec ∈
      v8CoreClaimDisciplineRules := by
  simp [v8CoreClaimDisciplineRules]

theorem proof_card_artifact_rule_requires_existing_file :
    proofCardsHaveArtifactsAndCommandsSpec.hasPredicate
      AssertionPredicate.fileExists := by
  simp [
    CoreRuleSpec.hasPredicate,
    proofCardsHaveArtifactsAndCommandsSpec,
  ]

theorem formal_proof_boundary_rule_requires_grounded_refs :
    formalProofStatusRequiresTheoremCardBoundarySpec.hasPredicate
      AssertionPredicate.refsExist := by
  simp [
    CoreRuleSpec.hasPredicate,
    formalProofStatusRequiresTheoremCardBoundarySpec,
  ]

theorem qm_recompile_rule_requires_grounded_refs :
    qmRecompileRouteCountsAndRefsAreGroundedSpec.hasPredicate
      AssertionPredicate.refsExist := by
  simp [
    CoreRuleSpec.hasPredicate,
    qmRecompileRouteCountsAndRefsAreGroundedSpec,
  ]

end V8
end MetaLang
end IDT
