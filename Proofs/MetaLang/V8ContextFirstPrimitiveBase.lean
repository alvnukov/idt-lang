import Proofs.MetaLang.V8VerificationLanguage

namespace IDT
namespace MetaLang
namespace V8

inductive ContextFirstPrimitive where
  | admissibleContextCover
  | localOutcomeEventPresheaf
  | inheritanceTransitionFamily
  | facticizationWitnessRelation
  | stableDistinguishabilityRelation
deriving DecidableEq, Repr

inductive LegacyReadoutScaffold where
  | globalHistory
  | eventAlgebra
  | readoutContextFamily
  | inheritanceActFamily
deriving DecidableEq, Repr

inductive ForbiddenPrimitiveImport where
  | bornRule
  | hilbertCarrier
  | metricSpacetime
  | globalFactTable
  | physicalHbar
  | physicalG
deriving DecidableEq, Repr

def canonicalContextFirstPrimitives : List ContextFirstPrimitive :=
  [
    ContextFirstPrimitive.admissibleContextCover,
    ContextFirstPrimitive.localOutcomeEventPresheaf,
    ContextFirstPrimitive.inheritanceTransitionFamily,
    ContextFirstPrimitive.facticizationWitnessRelation,
    ContextFirstPrimitive.stableDistinguishabilityRelation
  ]

def legacyReadoutScaffold : List LegacyReadoutScaffold :=
  [
    LegacyReadoutScaffold.globalHistory,
    LegacyReadoutScaffold.eventAlgebra,
    LegacyReadoutScaffold.readoutContextFamily,
    LegacyReadoutScaffold.inheritanceActFamily
  ]

structure ContextFirstPrimitiveBaseCandidate where
  primitives : List ContextFirstPrimitive
  compatibilityScaffold : List LegacyReadoutScaffold
  forbiddenPrimitiveImports : List ForbiddenPrimitiveImport
  legacyScaffoldIsPrimitive : Bool
deriving Repr

def ContextFirstPrimitiveBaseCandidate.isLeanMigrationBoundary
    (base : ContextFirstPrimitiveBaseCandidate) : Prop :=
  base.primitives = canonicalContextFirstPrimitives
    ∧ base.compatibilityScaffold = legacyReadoutScaffold
    ∧ base.forbiddenPrimitiveImports = []
    ∧ base.legacyScaffoldIsPrimitive = false

def canonicalContextFirstBaseCandidate : ContextFirstPrimitiveBaseCandidate :=
  {
    primitives := canonicalContextFirstPrimitives,
    compatibilityScaffold := legacyReadoutScaffold,
    forbiddenPrimitiveImports := [],
    legacyScaffoldIsPrimitive := false
  }

theorem canonical_context_first_base_has_five_primitives :
    canonicalContextFirstBaseCandidate.primitives.length = 5 := by
  rfl

theorem canonical_context_first_base_has_four_legacy_scaffold_items :
    canonicalContextFirstBaseCandidate.compatibilityScaffold.length = 4 := by
  rfl

theorem canonical_context_first_base_has_no_forbidden_primitive_imports :
    canonicalContextFirstBaseCandidate.forbiddenPrimitiveImports = [] := by
  rfl

theorem canonical_context_first_base_demotes_legacy_scaffold :
    canonicalContextFirstBaseCandidate.legacyScaffoldIsPrimitive = false := by
  rfl

theorem canonical_context_first_base_is_migration_boundary :
    canonicalContextFirstBaseCandidate.isLeanMigrationBoundary := by
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

structure ContextFirstVocabularyClaim where
  primitive : ContextFirstPrimitive
  claim : Claim

def ContextFirstVocabularyClaim.isPrimitiveDeclaration
    (entry : ContextFirstVocabularyClaim) : Prop :=
  entry.claim.status = ClaimStatus.primitive

structure ContextFirstVocabularyPackage where
  entries : List ContextFirstVocabularyClaim
  base : ContextFirstPrimitiveBaseCandidate

def ContextFirstVocabularyPackage.declaresExactlyBase
    (package : ContextFirstVocabularyPackage) : Prop :=
  package.entries.map (fun entry => entry.primitive) = package.base.primitives
    ∧ ∀ entry, entry ∈ package.entries →
      entry.isPrimitiveDeclaration

theorem declared_context_first_vocabulary_uses_only_base_primitives
    (package : ContextFirstVocabularyPackage)
    (declared : package.declaresExactlyBase) :
    package.entries.map (fun entry => entry.primitive) = package.base.primitives :=
  declared.left

theorem declared_context_first_vocabulary_marks_entries_as_primitives
    (package : ContextFirstVocabularyPackage)
    (declared : package.declaresExactlyBase)
    (entry : ContextFirstVocabularyClaim) :
    entry ∈ package.entries → entry.isPrimitiveDeclaration :=
  declared.right entry

end V8
end MetaLang
end IDT
