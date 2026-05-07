import Proofs.MetaLang.V8VerifierDecommissionPolicy

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 declarative document schema.

This is the Lean-side schema for IDT v8 declarative verification documents.
It is a migration step away from the old Python verifier: the IDT v8 document
shape becomes part of the Lean proof boundary.
-/

inductive DeclarativeDocumentKind where
  | verificationSpecification
deriving DecidableEq, Repr

structure FieldSelector where
  fieldPath : String
deriving Repr

inductive RuleWherePredicate where
  | equals : FieldSelector → String → RuleWherePredicate
  | inSet : FieldSelector → List String → RuleWherePredicate
deriving Repr

structure AssertionSpec where
  predicate : AssertionPredicate
  fieldPath : String
  parameters : List String
deriving Repr

structure VerificationRuleSpec where
  id : String
  collection : ManifestReferenceCollection
  wherePredicate : Option RuleWherePredicate
  assertions : List AssertionSpec
  idNonEmpty : id.length > 0
deriving Repr

structure DeclarativeSpecificationDocument where
  id : String
  kind : DeclarativeDocumentKind
  languageMajor : Nat
  languageMinor : Nat
  controlledVocabulary : List VocabularyEntry
  verificationRules : List VerificationRuleSpec
deriving Repr

def DeclarativeSpecificationDocument.isV8
    (document : DeclarativeSpecificationDocument) : Prop :=
  document.languageMajor = 8

def DeclarativeSpecificationDocument.hasVocabulary
    (document : DeclarativeSpecificationDocument) : Prop :=
  document.controlledVocabulary.length > 0

def DeclarativeSpecificationDocument.hasRules
    (document : DeclarativeSpecificationDocument) : Prop :=
  document.verificationRules.length > 0

def VocabularyEntry.approvalDisciplineHolds
    (entry : VocabularyEntry) : Prop :=
  entry.status = VocabularyStatus.proposedTerm →
    entry.approvalRequired = true

def AssertionSpec.hasLeanSemantics
    (assertion : AssertionSpec) : Prop :=
  ∃ evaluation,
    AssertionEvaluation.predicate evaluation = assertion.predicate

def VerificationRuleSpec.targetCollectionIsAllowed
    (rule : VerificationRuleSpec) : Prop :=
  rule.collection ∈ v8ManifestReferenceCollections

def VerificationRuleSpec.assertionsHaveLeanSemantics
    (rule : VerificationRuleSpec) : Prop :=
  ∀ assertion, assertion ∈ rule.assertions →
    assertion.hasLeanSemantics

def VerificationRuleSpec.isAcceptedForV8
    (rule : VerificationRuleSpec) : Prop :=
  rule.targetCollectionIsAllowed
    ∧ rule.assertions.length > 0
    ∧ rule.assertionsHaveLeanSemantics

def DeclarativeSpecificationDocument.isAcceptedForV8
    (document : DeclarativeSpecificationDocument) : Prop :=
  document.kind = DeclarativeDocumentKind.verificationSpecification
    ∧ document.isV8
    ∧ document.hasVocabulary
    ∧ document.hasRules
    ∧ (∀ entry, entry ∈ document.controlledVocabulary →
        entry.approvalDisciplineHolds)
    ∧ (∀ rule, rule ∈ document.verificationRules →
        rule.isAcceptedForV8)

theorem accepted_declarative_document_is_v8
    (document : DeclarativeSpecificationDocument)
    (accepted : document.isAcceptedForV8) :
    document.isV8 :=
  accepted.right.left

theorem accepted_declarative_document_rules_have_lean_semantics
    (document : DeclarativeSpecificationDocument)
    (accepted : document.isAcceptedForV8)
    (rule : VerificationRuleSpec)
    (rulePresent : rule ∈ document.verificationRules) :
    rule.assertionsHaveLeanSemantics :=
  (accepted.right.right.right.right.right rule rulePresent).right.right

theorem accepted_declarative_document_rule_targets_are_allowed
    (document : DeclarativeSpecificationDocument)
    (accepted : document.isAcceptedForV8)
    (rule : VerificationRuleSpec)
    (rulePresent : rule ∈ document.verificationRules) :
    rule.targetCollectionIsAllowed :=
  (accepted.right.right.right.right.right rule rulePresent).left

theorem accepted_declarative_document_proposed_terms_need_approval
    (document : DeclarativeSpecificationDocument)
    (accepted : document.isAcceptedForV8)
    (entry : VocabularyEntry)
    (entryPresent : entry ∈ document.controlledVocabulary)
    (proposed : entry.status = VocabularyStatus.proposedTerm) :
    entry.approvalRequired = true :=
  accepted.right.right.right.right.left entry entryPresent proposed

end V8
end MetaLang
end IDT
