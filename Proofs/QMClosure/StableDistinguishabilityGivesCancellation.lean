import Proofs.QMClosure.ParallelCompositionFixesScale

namespace IDT
namespace QMClosure

/-!
# Cancellation is the stability clause of distinguishability

`ParallelCompositionFixesScale` reduced the selection of addition to three
demands -- merging, independent composition, cancellation -- and left open
whether a contextual theory can justify the third without assuming
probability. This file settles what can be settled and marks precisely what
cannot.

Cancellation says merging does not forget its parts. Read contrapositively it
says that two alternatives told apart before merging are still told apart
after merging with a common third one. That is a stability clause on
distinguishability, and `stableDistinguishabilityRelation` is already one of
the five context-first primitives.

What is proved below:

* cancellation and preservation of distinguishability are the same condition,
  in both directions;
* strict monotonicity implies both, so the reading does not depend on one
  artificial choice of wording;
* addition satisfies all three, `max` fails all three;
* the clause does real work: `max` satisfies commutativity, associativity,
  neutrality, non-negativity and distributivity over independent composition,
  and is excluded by this clause alone;
* the strength matters: `max` does satisfy the weak reading, monotonicity
  without strictness. So a stability clause stated non-strictly would not
  deliver cancellation, and the gap between the two readings is exactly where
  the content sits.

What is **not** proved, and must not be read into this file. The repository has
no definition of `stableDistinguishabilityRelation`: in `MetaLang` it is an
enum constructor, and in the V7 files `D` is `fun _ _ _ => True`. So this is
not a derivation of cancellation from an existing primitive. It is a proposed
reading of a primitive that currently has no semantics, together with the proof
that the reading is non-vacuous and does the required job. Whether that reading
is the intended one is a theory decision and remains open.

The identification is also not a derivation in the logical sense: for
distinguishability taken as numerical distinctness, the clause and cancellation
are definitionally equivalent, and the theorem below says exactly that. The
content is the identification, not an inference -- which is why it is recorded
as a reading and not as a closure of the obligation.
-/

/-- Alternatives told apart before merging are told apart after merging. -/
def PreservesDistinguishability (merge : ℚ → ℚ → ℚ) : Prop :=
  ∀ fixed left right : ℚ,
    0 ≤ fixed → 0 ≤ left → 0 ≤ right →
      left ≠ right → merge fixed left ≠ merge fixed right

/-- The strict reading: a strictly heavier part gives a strictly heavier whole. -/
def StrictlyMonotoneMerge (merge : ℚ → ℚ → ℚ) : Prop :=
  ∀ fixed left right : ℚ,
    0 ≤ fixed → 0 ≤ left → 0 ≤ right →
      left < right → merge fixed left < merge fixed right

/-- The weak reading, which turns out not to be enough. -/
def WeaklyMonotoneMerge (merge : ℚ → ℚ → ℚ) : Prop :=
  ∀ fixed left right : ℚ,
    0 ≤ fixed → 0 ≤ left → 0 ≤ right →
      left ≤ right → merge fixed left ≤ merge fixed right

/-- Cancellation and preservation of distinguishability are the same condition. -/
theorem preserves_distinguishability_iff_cancellative (merge : ℚ → ℚ → ℚ) :
    PreservesDistinguishability merge ↔ Cancellative merge := by
  constructor
  · intro preserves fixed left right fixedNonneg leftNonneg rightNonneg equalMerges
    by_contra different
    exact preserves fixed left right fixedNonneg leftNonneg rightNonneg different
      equalMerges
  · intro cancellative fixed left right fixedNonneg leftNonneg rightNonneg different
      equalMerges
    exact different
      (cancellative fixed left right fixedNonneg leftNonneg rightNonneg equalMerges)

/-- The strict reading implies the distinguishability reading. -/
theorem strictly_monotone_preserves_distinguishability (merge : ℚ → ℚ → ℚ)
    (strict : StrictlyMonotoneMerge merge) :
    PreservesDistinguishability merge := by
  intro fixed left right fixedNonneg leftNonneg rightNonneg different
  rcases lt_trichotomy left right with hlt | heq | hgt
  · exact ne_of_lt (strict fixed left right fixedNonneg leftNonneg rightNonneg hlt)
  · exact absurd heq different
  · exact ne_of_gt
      (strict fixed right left fixedNonneg rightNonneg leftNonneg hgt)

/-- Addition satisfies the strict reading. -/
theorem addition_is_strictly_monotone :
    StrictlyMonotoneMerge (relabelledMerge 0) := by
  intro fixed left right _ _ _ hlt
  unfold relabelledMerge
  linarith

/-- Addition therefore preserves distinguishability. -/
theorem addition_preserves_distinguishability :
    PreservesDistinguishability (relabelledMerge 0) :=
  strictly_monotone_preserves_distinguishability _ addition_is_strictly_monotone

/--
`max` fails the clause, witnessed at `fixed = 2`, `left = 1`, `right = 0`: two
alternatives that differ become indistinguishable once merged with a dominant
third one.
-/
theorem max_does_not_preserve_distinguishability :
    ¬ PreservesDistinguishability max := by
  intro preserves
  have distinct : (1 : ℚ) ≠ 0 := by norm_num
  have collapsed : max (2 : ℚ) 1 ≠ max (2 : ℚ) 0 :=
    preserves 2 1 0 (by norm_num) (by norm_num) (by norm_num) distinct
  apply collapsed
  norm_num

theorem max_is_not_strictly_monotone : ¬ StrictlyMonotoneMerge max := by
  intro strict
  have collapsed : max (2 : ℚ) 0 < max (2 : ℚ) 1 :=
    strict 2 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at collapsed

/--
The guard against reading the clause too weakly. `max` does satisfy
monotonicity without strictness, so a stability clause stated non-strictly
would not exclude possibilistic readout. The gap between the weak and strict
readings is where the whole content sits.
-/
theorem max_is_weakly_monotone : WeaklyMonotoneMerge max := by
  intro fixed left right _ _ _ hle
  exact max_le_max le_rfl hle

/-- Addition satisfies the weak reading too, so the weak reading separates nothing. -/
theorem addition_is_weakly_monotone : WeaklyMonotoneMerge (relabelledMerge 0) := by
  intro fixed left right _ _ _ hle
  unfold relabelledMerge
  linarith

/--
The clause does real work rather than restating earlier demands: `max` passes
independent-composition distributivity and is excluded by this clause alone.
-/
theorem clause_is_not_implied_by_distributivity :
    DistributesOverNonneg independentScale max
      ∧ ¬ PreservesDistinguishability max :=
  ⟨independent_scale_distributes_over_max,
    max_does_not_preserve_distinguishability⟩

/--
And it is not implied by the relabelling family either: every `relabelledMerge`
with `lambda ≥ 0` preserves distinguishability while failing distributivity for
`lambda ≠ 0`. The two demands cut in genuinely different directions.
-/
theorem relabelled_merge_preserves_distinguishability
    (lambda : ℚ) (nonneg : 0 ≤ lambda) :
    PreservesDistinguishability (relabelledMerge lambda) :=
  (preserves_distinguishability_iff_cancellative _).mpr
    (relabelled_merge_is_cancellative lambda nonneg)

inductive StableDistinguishabilityFinding where
  | cancellationIsPreservationOfDistinguishability
  | strictMonotonicityGivesTheSameReading
  | maxFailsTheClauseAndIsTherebyExcluded
  | weakMonotonicityWouldNotExcludeMax
  | clauseIsIndependentOfDistributivity
  deriving DecidableEq, Repr

def stableDistinguishabilityFindings : List StableDistinguishabilityFinding :=
  [ .cancellationIsPreservationOfDistinguishability,
    .strictMonotonicityGivesTheSameReading,
    .maxFailsTheClauseAndIsTherebyExcluded,
    .weakMonotonicityWouldNotExcludeMax,
    .clauseIsIndependentOfDistributivity ]

theorem stable_distinguishability_records_five_findings :
    stableDistinguishabilityFindings.length = 5 := by
  rfl

inductive StableDistinguishabilityOpenObligation where
  | giveStableDistinguishabilityAnActualDefinitionInTheBase
  | decideWhetherTheStrictReadingIsTheIntendedOne
  | deriveTheClauseRatherThanPostulateIt
  | proveTheThreeDemandsPinAdditionUniquely
  | separateAdditivityFromQuadraticReadout
  deriving DecidableEq, Repr

def stableDistinguishabilityOpenObligations :
    List StableDistinguishabilityOpenObligation :=
  [ .giveStableDistinguishabilityAnActualDefinitionInTheBase,
    .decideWhetherTheStrictReadingIsTheIntendedOne,
    .deriveTheClauseRatherThanPostulateIt,
    .proveTheThreeDemandsPinAdditionUniquely,
    .separateAdditivityFromQuadraticReadout ]

theorem stable_distinguishability_keeps_five_open_obligations :
    stableDistinguishabilityOpenObligations.length = 5 := by
  rfl

def stableDistinguishabilityClaimBoundary : String :=
  "Cancellation is definitionally the same condition as preservation of distinguishability under merging, and max is excluded by it while satisfying every earlier demand. This is a proposed reading of stableDistinguishabilityRelation, which has no definition in the repository, not a derivation of cancellation from an existing primitive. It does not close the obligation, does not derive the Born rule, and does not derive the quadratic form of the readout."

end QMClosure
end IDT
