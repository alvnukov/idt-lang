import Proofs.MetaLang.V8RuleManifestGrounding

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 assertion-predicate semantics.

The Python declarative verifier remains a legacy safety net. This Lean module
records the abstract semantics of the ten predicate operations that the v8
declarative checker supports. It does not parse JSON; it specifies what each
operation means after path extraction has produced values.
-/

inductive FieldValue where
  | string : String → FieldValue
  | present : FieldValue
  | empty : FieldValue
deriving DecidableEq, Repr

def FieldValue.isNonEmpty : FieldValue → Prop
  | FieldValue.string value => value.length > 0
  | FieldValue.present => True
  | FieldValue.empty => False

def FieldValue.asString? : FieldValue → Option String
  | FieldValue.string value => some value
  | _ => none

structure ExtractedPath where
  values : List FieldValue
deriving Repr

def ExtractedPath.exists : ExtractedPath → Prop
  | path => path.values.length > 0

def ExtractedPath.allNonEmpty (path : ExtractedPath) : Prop :=
  path.exists ∧ ∀ value, value ∈ path.values → value.isNonEmpty

def ExtractedPath.stringValues (path : ExtractedPath) : List String :=
  path.values.filterMap FieldValue.asString?

def ExtractedPath.allStringsIn
    (path : ExtractedPath)
    (allowed : List String) : Prop :=
  ∀ value, value ∈ path.values →
    ∃ stringValue, value = FieldValue.string stringValue
      ∧ stringValue ∈ allowed

def ExtractedPath.noStringIn
    (path : ExtractedPath)
    (forbidden : List String) : Prop :=
  ∀ value, value ∈ path.values →
    ∀ stringValue, value = FieldValue.string stringValue →
      stringValue ∉ forbidden

def ExtractedPath.equalsSingleValue
    (left right : ExtractedPath) : Prop :=
  ∃ value, left.values = [value] ∧ right.values = [value]

def ExtractedPath.containsAllStrings
    (path : ExtractedPath)
    (required : List String) : Prop :=
  ∀ value, value ∈ required → value ∈ path.stringValues

def ExtractedPath.hasNoStringIntersection
    (path : ExtractedPath)
    (forbidden : List String) : Prop :=
  ∀ value, value ∈ path.stringValues → value ∉ forbidden

structure NestedFieldCheck where
  checkedObjects : List String
  mismatchedObjects : List String
deriving Repr

def NestedFieldCheck.allEqualExpected (check : NestedFieldCheck) : Prop :=
  check.mismatchedObjects = []

structure FileExistenceCheck where
  paths : List String
  missingPaths : List String
deriving Repr

def FileExistenceCheck.allExist (check : FileExistenceCheck) : Prop :=
  check.missingPaths = []

structure ReferenceExistenceCheck where
  refs : List String
  allowedRefs : List String
deriving Repr

def ReferenceExistenceCheck.allExist
    (check : ReferenceExistenceCheck) : Prop :=
  ∀ ref, ref ∈ check.refs → ref ∈ check.allowedRefs

inductive AssertionEvaluation where
  | fieldRequired : ExtractedPath → AssertionEvaluation
  | fieldNonEmpty : ExtractedPath → AssertionEvaluation
  | fieldIn : ExtractedPath → List String → AssertionEvaluation
  | fieldNotIn : ExtractedPath → List String → AssertionEvaluation
  | equalsField : ExtractedPath → ExtractedPath → AssertionEvaluation
  | refsExist : ReferenceExistenceCheck → AssertionEvaluation
  | listContainsAll : ExtractedPath → List String → AssertionEvaluation
  | everyFieldEquals : NestedFieldCheck → AssertionEvaluation
  | fileExists : FileExistenceCheck → AssertionEvaluation
  | noIntersection : ExtractedPath → List String → AssertionEvaluation
deriving Repr

def AssertionEvaluation.predicate : AssertionEvaluation → AssertionPredicate
  | AssertionEvaluation.fieldRequired _ => AssertionPredicate.fieldRequired
  | AssertionEvaluation.fieldNonEmpty _ => AssertionPredicate.fieldNonEmpty
  | AssertionEvaluation.fieldIn _ _ => AssertionPredicate.fieldIn
  | AssertionEvaluation.fieldNotIn _ _ => AssertionPredicate.fieldNotIn
  | AssertionEvaluation.equalsField _ _ => AssertionPredicate.equalsField
  | AssertionEvaluation.refsExist _ => AssertionPredicate.refsExist
  | AssertionEvaluation.listContainsAll _ _ =>
      AssertionPredicate.listContainsAll
  | AssertionEvaluation.everyFieldEquals _ =>
      AssertionPredicate.everyFieldEquals
  | AssertionEvaluation.fileExists _ => AssertionPredicate.fileExists
  | AssertionEvaluation.noIntersection _ _ =>
      AssertionPredicate.noIntersection

def AssertionEvaluation.passes : AssertionEvaluation → Prop
  | AssertionEvaluation.fieldRequired path =>
      path.exists
  | AssertionEvaluation.fieldNonEmpty path =>
      path.allNonEmpty
  | AssertionEvaluation.fieldIn path allowed =>
      path.allStringsIn allowed
  | AssertionEvaluation.fieldNotIn path forbidden =>
      path.noStringIn forbidden
  | AssertionEvaluation.equalsField left right =>
      left.equalsSingleValue right
  | AssertionEvaluation.refsExist check =>
      check.allExist
  | AssertionEvaluation.listContainsAll path required =>
      path.containsAllStrings required
  | AssertionEvaluation.everyFieldEquals check =>
      check.allEqualExpected
  | AssertionEvaluation.fileExists check =>
      check.allExist
  | AssertionEvaluation.noIntersection path forbidden =>
      path.hasNoStringIntersection forbidden

theorem field_non_empty_implies_field_required
    (path : ExtractedPath)
    (passes : (AssertionEvaluation.fieldNonEmpty path).passes) :
    (AssertionEvaluation.fieldRequired path).passes :=
  passes.left

theorem field_in_rejects_non_string_values
    (path : ExtractedPath)
    (allowed : List String)
    (passes : (AssertionEvaluation.fieldIn path allowed).passes)
    (value : FieldValue)
    (valuePresent : value ∈ path.values) :
    ∃ stringValue, value = FieldValue.string stringValue
      ∧ stringValue ∈ allowed :=
  passes value valuePresent

theorem refs_exist_means_every_ref_is_allowed
    (check : ReferenceExistenceCheck)
    (passes : (AssertionEvaluation.refsExist check).passes)
    (ref : String)
    (refPresent : ref ∈ check.refs) :
    ref ∈ check.allowedRefs :=
  passes ref refPresent

theorem file_exists_means_no_missing_paths
    (check : FileExistenceCheck)
    (passes : (AssertionEvaluation.fileExists check).passes) :
    check.missingPaths = [] :=
  passes

theorem no_intersection_means_no_forbidden_string_value
    (path : ExtractedPath)
    (forbidden : List String)
    (passes : (AssertionEvaluation.noIntersection path forbidden).passes)
    (value : String)
    (valuePresent : value ∈ path.stringValues) :
    value ∉ forbidden :=
  passes value valuePresent

theorem every_supported_python_predicate_has_v8_semantics
    (predicate : AssertionPredicate) :
    ∃ evaluation, AssertionEvaluation.predicate evaluation = predicate := by
  cases predicate with
  | fieldRequired =>
      exact ⟨AssertionEvaluation.fieldRequired { values := [] }, rfl⟩
  | fieldNonEmpty =>
      exact ⟨AssertionEvaluation.fieldNonEmpty { values := [] }, rfl⟩
  | fieldIn =>
      exact ⟨AssertionEvaluation.fieldIn { values := [] } [], rfl⟩
  | fieldNotIn =>
      exact ⟨AssertionEvaluation.fieldNotIn { values := [] } [], rfl⟩
  | equalsField =>
      exact ⟨AssertionEvaluation.equalsField { values := [] } { values := [] }, rfl⟩
  | refsExist =>
      exact ⟨AssertionEvaluation.refsExist { refs := [], allowedRefs := [] }, rfl⟩
  | listContainsAll =>
      exact ⟨AssertionEvaluation.listContainsAll { values := [] } [], rfl⟩
  | everyFieldEquals =>
      exact ⟨AssertionEvaluation.everyFieldEquals
        { checkedObjects := [], mismatchedObjects := [] }, rfl⟩
  | fileExists =>
      exact ⟨AssertionEvaluation.fileExists { paths := [], missingPaths := [] }, rfl⟩
  | noIntersection =>
      exact ⟨AssertionEvaluation.noIntersection { values := [] } [], rfl⟩

end V8
end MetaLang
end IDT
