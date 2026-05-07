import Proofs.MetaLang.V8AssertionPredicateSemantics

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 core-rule semantic closure.

The core rule inventory lists predicate names. The assertion semantics module
defines what each supported predicate means. This file connects both layers:
every predicate used by every accepted core rule has Lean-side semantics.
-/

def CoreRuleSpec.predicatesHaveLeanSemantics
    (rule : CoreRuleSpec) : Prop :=
  ∀ predicate, predicate ∈ rule.predicates →
    ∃ evaluation, AssertionEvaluation.predicate evaluation = predicate

theorem every_v8_core_rule_predicate_has_lean_semantics
    (rule : CoreRuleSpec)
    (_rulePresent : rule ∈ v8CoreClaimDisciplineRules) :
    rule.predicatesHaveLeanSemantics := by
  intro predicate _predicatePresent
  exact every_supported_python_predicate_has_v8_semantics predicate

theorem proof_card_artifact_rule_file_exists_has_lean_semantics :
    ∃ evaluation,
      AssertionEvaluation.predicate evaluation =
        AssertionPredicate.fileExists :=
  every_supported_python_predicate_has_v8_semantics
    AssertionPredicate.fileExists

theorem formal_proof_boundary_refs_exist_has_lean_semantics :
    ∃ evaluation,
      AssertionEvaluation.predicate evaluation =
        AssertionPredicate.refsExist :=
  every_supported_python_predicate_has_v8_semantics
    AssertionPredicate.refsExist

theorem context_first_candidate_rule_list_contains_all_has_lean_semantics :
    ∃ evaluation,
      AssertionEvaluation.predicate evaluation =
        AssertionPredicate.listContainsAll :=
  every_supported_python_predicate_has_v8_semantics
    AssertionPredicate.listContainsAll

end V8
end MetaLang
end IDT
