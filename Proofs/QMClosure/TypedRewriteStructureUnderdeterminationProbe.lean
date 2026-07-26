import Mathlib

namespace IDT.QMClosure

/-!
# Typed rewrite structure underdetermination probe

This file tests whether typed local rewrites with identity and sequential
composition automatically provide the extra structures used by process- and
effect-theoretic quantum reconstructions.

They do not. A finite directed rewrite category has no possible total dagger,
and its same rewrite relation supports two distinct symmetric associative
parallel products. Thus dagger duality and parallel composition are not
consequences of bare typed sequential rewriting; the dagger-adjoint
filter/compression and purification packages require additional assumptions.
-/

def DirectedRewrite (source target : Bool) : Prop :=
  source = false ∨ target = true

def directedRewriteIdentity (object : Bool) :
    DirectedRewrite object object := by
  cases object <;> simp [DirectedRewrite]

def directedRewriteCompose
    {source middle target : Bool}
    (first : DirectedRewrite source middle)
    (second : DirectedRewrite middle target) :
    DirectedRewrite source target := by
  rcases first with sourceFalse | middleTrue
  · exact Or.inl sourceFalse
  · rcases second with middleFalse | targetTrue
    · simp_all
    · exact Or.inr targetTrue

theorem directed_rewrite_composition_is_associative
    {a b c d : Bool}
    (first : DirectedRewrite a b)
    (second : DirectedRewrite b c)
    (third : DirectedRewrite c d) :
    directedRewriteCompose
        (directedRewriteCompose first second) third =
      directedRewriteCompose first
        (directedRewriteCompose second third) := by
  apply Subsingleton.elim

theorem directed_rewrite_left_identity
    {source target : Bool}
    (rewrite : DirectedRewrite source target) :
    directedRewriteCompose (directedRewriteIdentity source) rewrite =
      rewrite := by
  apply Subsingleton.elim

theorem directed_rewrite_right_identity
    {source target : Bool}
    (rewrite : DirectedRewrite source target) :
    directedRewriteCompose rewrite (directedRewriteIdentity target) =
      rewrite := by
  apply Subsingleton.elim

structure DirectedRewriteDagger where
  reverse : ∀ {source target : Bool},
    DirectedRewrite source target → DirectedRewrite target source

theorem directed_rewrite_admits_no_total_dagger :
    ¬ Nonempty DirectedRewriteDagger := by
  rintro ⟨dagger⟩
  have forward : DirectedRewrite false true := Or.inl rfl
  have reverse := dagger.reverse forward
  norm_num [DirectedRewrite] at reverse

structure DirectedRewriteParallelLaw where
  tensor : Bool → Bool → Bool
  unit : Bool
  associative : ∀ a b c,
    tensor (tensor a b) c = tensor a (tensor b c)
  commutative : ∀ a b, tensor a b = tensor b a
  leftUnit : ∀ a, tensor unit a = a
  rightUnit : ∀ a, tensor a unit = a
  preservesRewrite : ∀ a a' b b',
    DirectedRewrite a a' →
      DirectedRewrite b b' →
        DirectedRewrite (tensor a b) (tensor a' b')

def andParallelLaw : DirectedRewriteParallelLaw where
  tensor := (· && ·)
  unit := true
  associative := by native_decide
  commutative := by native_decide
  leftUnit := by native_decide
  rightUnit := by native_decide
  preservesRewrite := by
    intro a a' b b' first second
    cases a <;> cases a' <;> cases b <;> cases b' <;>
      simp_all [DirectedRewrite]

def orParallelLaw : DirectedRewriteParallelLaw where
  tensor := (· || ·)
  unit := false
  associative := by native_decide
  commutative := by native_decide
  leftUnit := by native_decide
  rightUnit := by native_decide
  preservesRewrite := by
    intro a a' b b' first second
    cases a <;> cases a' <;> cases b <;> cases b' <;>
      simp_all [DirectedRewrite]

theorem and_or_parallel_laws_are_distinct :
    andParallelLaw.tensor false true ≠
      orParallelLaw.tensor false true := by
  decide

theorem sequential_rewrite_laws_do_not_select_parallel_composition :
    ∃ first second : DirectedRewriteParallelLaw,
      first.tensor false true ≠ second.tensor false true := by
  exact ⟨andParallelLaw, orParallelLaw,
    and_or_parallel_laws_are_distinct⟩

inductive TypedRewriteStructureFinding where
  | finiteTypedSequentialRewriteModelExists
  | identitiesAndAssociativeCompositionHold
  | totalDaggerNeedNotExist
  | parallelProductIsNotUnique
  | filterCompressionAdjunctionIsNotDerived
  | bareTypedRewritesAreInsufficient
  deriving DecidableEq, Repr

def typedRewriteStructureFindings :
    List TypedRewriteStructureFinding :=
  [ .finiteTypedSequentialRewriteModelExists,
    .identitiesAndAssociativeCompositionHold,
    .totalDaggerNeedNotExist,
    .parallelProductIsNotUnique,
    .filterCompressionAdjunctionIsNotDerived,
    .bareTypedRewritesAreInsufficient ]

theorem typed_rewrite_structure_probe_records_six_findings :
    typedRewriteStructureFindings.length = 6 := by
  rfl

inductive TypedRewriteStructureOpenObligation where
  | deriveBoundaryDualityOrDeclareItAsPrimitive
  | deriveUniquePhysicalParallelComposition
  | deriveDiscardAndOperationalEffects
  | deriveFilterCompressionUniversalProperties
  | deriveReversiblePurification
  | deriveOrderedNormalizedScalars
  | excludeClassicalAndSuperquantumModels
  deriving DecidableEq, Repr

def typedRewriteStructureOpenObligations :
    List TypedRewriteStructureOpenObligation :=
  [ .deriveBoundaryDualityOrDeclareItAsPrimitive,
    .deriveUniquePhysicalParallelComposition,
    .deriveDiscardAndOperationalEffects,
    .deriveFilterCompressionUniversalProperties,
    .deriveReversiblePurification,
    .deriveOrderedNormalizedScalars,
    .excludeClassicalAndSuperquantumModels ]

theorem typed_rewrite_structure_probe_keeps_seven_open_obligations :
    typedRewriteStructureOpenObligations.length = 7 := by
  rfl

def typedRewriteStructureProbeStatus : String :=
  "bare_typed_sequential_rewrites_rejected_as_sufficient_lower_base"

def typedRewriteStructureProbeClaimBoundary : String :=
  "A finite typed rewrite model has associative sequential composition but no total dagger, while two distinct symmetric parallel products preserve the same rewrites. Therefore dagger, a unique tensor, dagger-adjoint filter/compression, purification, quantum mechanics, the Standard Model, and gravity are not derived from bare typed rewrites."

end IDT.QMClosure
