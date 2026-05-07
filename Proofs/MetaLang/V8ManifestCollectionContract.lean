import Proofs.MetaLang.V8ControlledVocabularyInventory

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 manifest collection contract.

The manifest remains an input, not the proof source of truth. This Lean module
records which manifest collections the v8 declarative checker may treat as
reference-index collections. It deliberately does not freeze current collection
sizes, because the manifest can grow.
-/

inductive ManifestReferenceCollection where
  | symbols
  | equations
  | derivations
  | finiteGates
  | qmExperiments
  | qmUniversalPatterns
  | qmCoreProofObligations
  | theoremCards
deriving DecidableEq, Repr

def v8ManifestReferenceCollections : List ManifestReferenceCollection :=
  [
    ManifestReferenceCollection.symbols,
    ManifestReferenceCollection.equations,
    ManifestReferenceCollection.derivations,
    ManifestReferenceCollection.finiteGates,
    ManifestReferenceCollection.qmExperiments,
    ManifestReferenceCollection.qmUniversalPatterns,
    ManifestReferenceCollection.qmCoreProofObligations,
    ManifestReferenceCollection.theoremCards
  ]

inductive ManifestReferenceSelector where
  | named : ManifestReferenceCollection → ManifestReferenceSelector
  | wildcard
deriving DecidableEq, Repr

structure ManifestReferenceQuery where
  selectors : List ManifestReferenceSelector
deriving Repr

def ManifestReferenceSelector.isAllowedForV8
    (selector : ManifestReferenceSelector) : Prop :=
  match selector with
  | ManifestReferenceSelector.named collection =>
      collection ∈ v8ManifestReferenceCollections
  | ManifestReferenceSelector.wildcard =>
      True

def ManifestReferenceQuery.isAllowedForV8
    (query : ManifestReferenceQuery) : Prop :=
  ∀ selector, selector ∈ query.selectors →
    selector.isAllowedForV8

theorem v8_manifest_reference_collections_count :
    v8ManifestReferenceCollections.length = 8 := by
  rfl

theorem finite_gates_are_v8_manifest_reference_collection :
    ManifestReferenceCollection.finiteGates ∈
      v8ManifestReferenceCollections := by
  simp [v8ManifestReferenceCollections]

theorem theorem_cards_are_v8_manifest_reference_collection :
    ManifestReferenceCollection.theoremCards ∈
      v8ManifestReferenceCollections := by
  simp [v8ManifestReferenceCollections]

theorem qm_core_obligations_are_v8_manifest_reference_collection :
    ManifestReferenceCollection.qmCoreProofObligations ∈
      v8ManifestReferenceCollections := by
  simp [v8ManifestReferenceCollections]

theorem wildcard_reference_selector_is_allowed_for_v8 :
    ManifestReferenceSelector.wildcard.isAllowedForV8 := by
  trivial

theorem accepted_manifest_reference_query_allows_each_selector
    (query : ManifestReferenceQuery)
    (accepted : query.isAllowedForV8)
    (selector : ManifestReferenceSelector)
    (selectorPresent : selector ∈ query.selectors) :
    selector.isAllowedForV8 :=
  accepted selector selectorPresent

end V8
end MetaLang
end IDT
