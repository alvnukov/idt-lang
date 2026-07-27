import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# Parallel composition removes the scale freedom, but not by itself

`CoarseGrainingDoesNotFixScale` left the merge law determined only up to a
relabelling of the value axis: `combine x y = x + y + lambda * x * y` satisfies
every coarse-graining demand for any `lambda`, and equals addition read through
`weight |-> 1 + lambda * weight`. This file discharges the obligation recorded
there as `decideWhetherIdtCanSelectARelabellingWithoutImportingBorn`.

The context-first resource that has not been used yet is parallel composition of
independent contexts: product contexts are already among the primitives, and
`deriveTypedParallelComposition` is an open obligation of the base. Weighing
independent contexts multiplies their weights, and the natural coherence demand
is that scaling by an independent context commutes with merging alternatives:

    scale z (merge x y) = merge (scale z x) (scale z y)

The answer comes in three layers, and each layer is a separate primitive doing
exactly one job.

1. Distributivity kills the whole relabelling family at once. Multiplication
   distributes over `combine_lambda` only when `lambda = 0`. So parallel
   composition does fix the scale, and it does so without mentioning
   probability, amplitude, or the Born rule.

2. Distributivity alone does not force addition. `max` satisfies every
   coarse-graining demand on non-negative weights and multiplication
   distributes over it too. What survives is possibilistic readout, not
   probabilistic.

3. `max` is separated from addition by cancellation, not by distributivity:
   `max 2 1 = max 2 0` while `2 + 1 ≠ 2 + 0`.

So selecting addition needs merging, independent composition, and cancellation,
and no two of the three suffice. None of them is the Born rule.

Scope. Finite, over ℚ. Layer 1 is proved for the whole `lambda` family, not for
arbitrary merge laws. That the three demands together pin addition uniquely is
the classical Aczel result; it is not proved here and stays open.
-/

/-- Scaling by an independent context commutes with merging alternatives. -/
def DistributesOverNonneg (scale merge : ℚ → ℚ → ℚ) : Prop :=
  ∀ outer left right : ℚ,
    0 ≤ outer → 0 ≤ left → 0 ≤ right →
      scale outer (merge left right)
        = merge (scale outer left) (scale outer right)

/-- Weighing independent contexts multiplies their weights. -/
def independentScale : ℚ → ℚ → ℚ :=
  fun outer inner => outer * inner

/-- The relabelling family left open by coarse-graining. -/
def relabelledMerge (lambda : ℚ) : ℚ → ℚ → ℚ :=
  fun left right => left + right + lambda * (left * right)

theorem relabelledMerge_zero_is_addition (left right : ℚ) :
    relabelledMerge 0 left right = left + right := by
  unfold relabelledMerge
  ring

/-- Layer 1, positive half: independent composition distributes over addition. -/
theorem independent_scale_distributes_over_addition :
    DistributesOverNonneg independentScale (relabelledMerge 0) := by
  intro outer left right _ _ _
  unfold independentScale relabelledMerge
  ring

/--
Layer 1, the point. For every non-zero `lambda` the relabelled merge law fails
distributivity, witnessed at `outer = 1/2`, `left = right = 1`. So parallel
composition selects `lambda = 0` out of the entire family that coarse-graining
could not separate.
-/
theorem independent_scale_distributes_only_over_addition
    (lambda : ℚ) (nonzero : lambda ≠ 0) :
    ¬ DistributesOverNonneg independentScale (relabelledMerge lambda) := by
  intro distributes
  have witness := distributes (1 / 2) 1 1 (by norm_num) (by norm_num) (by norm_num)
  unfold independentScale relabelledMerge at witness
  apply nonzero
  linarith

/--
Layer 2. `max` is a legitimate merge law on non-negative weights: commutative,
associative, neutral at `0`, monotone, and non-negativity preserving.
-/
theorem max_is_commutative (left right : ℚ) : max left right = max right left :=
  max_comm left right

theorem max_is_associative (left middle right : ℚ) :
    max (max left middle) right = max left (max middle right) :=
  max_assoc left middle right

theorem max_is_neutral_at_zero (weight : ℚ) (nonneg : 0 ≤ weight) :
    max weight 0 = weight :=
  max_eq_left nonneg

/--
Layer 2, the point. Independent composition distributes over `max` as well, so
distributivity does not single addition out. Possibilistic readout survives
every demand made so far.
-/
theorem independent_scale_distributes_over_max :
    DistributesOverNonneg independentScale max := by
  intro outer left right outerNonneg _ _
  unfold independentScale
  rcases le_total left right with hle | hle
  · rw [max_eq_right hle, max_eq_right (by nlinarith)]
  · rw [max_eq_left hle, max_eq_left (by nlinarith)]

/-- Merging is cancellative: the whole determines the part. -/
def Cancellative (merge : ℚ → ℚ → ℚ) : Prop :=
  ∀ fixed left right : ℚ,
    0 ≤ fixed → 0 ≤ left → 0 ≤ right →
      merge fixed left = merge fixed right → left = right

/-- Layer 3, positive half: addition is cancellative. -/
theorem addition_is_cancellative : Cancellative (relabelledMerge 0) := by
  intro fixed left right _ _ _ equalMerges
  unfold relabelledMerge at equalMerges
  linarith

/--
Layer 3, the point. `max` is not cancellative: a dominant whole forgets its
part, since `max 2 1 = max 2 0` while `1 ≠ 0`. So cancellation, and not
distributivity, is what separates probabilistic from possibilistic merging.
-/
theorem max_is_not_cancellative : ¬ Cancellative max := by
  intro cancellative
  have collapse : (1 : ℚ) = 0 :=
    cancellative 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at collapse

/--
The three demands are independent in the sense that matters here: the
relabelling family passes coarse-graining and cancellation but fails
distributivity, and `max` passes coarse-graining and distributivity but fails
cancellation.
-/
theorem relabelled_merge_is_cancellative
    (lambda : ℚ) (nonneg : 0 ≤ lambda) :
    Cancellative (relabelledMerge lambda) := by
  intro fixed left right fixedNonneg _ _ equalMerges
  unfold relabelledMerge at equalMerges
  have factored : (1 + lambda * fixed) * (left - right) = 0 := by ring_nf; ring_nf at equalMerges; linarith
  have positive : 0 < 1 + lambda * fixed := by nlinarith
  have : left - right = 0 := by
    rcases mul_eq_zero.mp factored with h | h
    · exact absurd h (ne_of_gt positive)
    · exact h
  linarith

inductive ScaleSelectionFinding where
  | parallelCompositionKillsTheRelabellingFamily
  | distributivityAloneDoesNotForceAddition
  | possibilisticMaxSurvivesDistributivity
  | cancellationSeparatesAdditionFromMax
  deriving DecidableEq, Repr

def scaleSelectionFindings : List ScaleSelectionFinding :=
  [ .parallelCompositionKillsTheRelabellingFamily,
    .distributivityAloneDoesNotForceAddition,
    .possibilisticMaxSurvivesDistributivity,
    .cancellationSeparatesAdditionFromMax ]

theorem scale_selection_records_four_findings :
    scaleSelectionFindings.length = 4 := by
  rfl

inductive ScaleSelectionOpenObligation where
  | proveTheThreeDemandsPinAdditionUniquely
  | deriveParallelCompositionFromContextFirstPrimitives
  | justifyCancellationWithoutAssumingProbability
  | separateAdditivityFromQuadraticReadout
  deriving DecidableEq, Repr

def scaleSelectionOpenObligations : List ScaleSelectionOpenObligation :=
  [ .proveTheThreeDemandsPinAdditionUniquely,
    .deriveParallelCompositionFromContextFirstPrimitives,
    .justifyCancellationWithoutAssumingProbability,
    .separateAdditivityFromQuadraticReadout ]

theorem scale_selection_keeps_four_open_obligations :
    scaleSelectionOpenObligations.length = 4 := by
  rfl

def scaleSelectionClaimBoundary : String :=
  "Finite result over ℚ. Independent composition distributing over merging selects lambda = 0 from the whole relabelling family, so the value scale can be fixed without importing the Born rule. It does not force addition on its own, because max survives; cancellation is the separate demand that excludes max. That the three demands pin addition uniquely is the classical Aczel theorem and is not proved here. Nothing here derives the Born rule or the quadratic form of the readout."

end QMClosure
end IDT
