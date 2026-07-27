import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# Coarse-graining closure does not fix the value scale

`OrderDeterminedReadoutNoGo` showed that no order-determined constraint entails
additivity, so reaching the Born readout needs a primitive carrying arithmetic
on the value scale. This file tests the cheapest candidate for that primitive,
recorded there as `testWhetherCoarseGrainingClosureSufficesForAdditivity`.

Coarse-graining closure says that merging two disjoint alternatives yields a
weight determined by the weights of the parts: there is a combination law
`combine` with `weight (A ∪ B) = combine (weight A) (weight B)`. The natural
demands on such a law are that merging is order-independent and
bracket-independent, that merging with an impossible alternative changes
nothing, that heavier parts do not produce lighter wholes, and that weights
stay non-negative.

Addition satisfies all of them. So does `combine x y = x + y + x * y`, and the
two disagree. The witness below is a strictly positive, coarse-graining-closed
readout on three alternatives whose whole has weight `1` while its parts sum to
`19/24`.

So coarse-graining closure does not entail additivity. What it does not fix is
specifically the scale: `1 + combine x y = (1 + x) * (1 + y)`, so the second law
is addition read through a relabelling of the value axis. Combined with the
previous no-go -- no order-determined constraint can pin the scale -- the
freedom that survives coarse-graining is exactly the freedom no relational
primitive can remove.

Scope. Finite, three alternatives, over ℚ. It does not derive the Born rule and
does not show that no arithmetic primitive suffices; it rules out this one. The
general statement, that continuity plus cancellation would force addition up to
a monotone relabelling, is classical but is not proved here and is recorded as
an open obligation.
-/

/-- A law for merging the weights of two disjoint alternatives. -/
structure CoarseGrainingLaw where
  combine : ℚ → ℚ → ℚ
  /-- Merging does not depend on the order of the parts. -/
  commutative : ∀ left right, combine left right = combine right left
  /-- Merging three parts does not depend on the bracketing. -/
  associative : ∀ left middle right,
    combine (combine left middle) right = combine left (combine middle right)
  /-- Merging with an impossible alternative changes nothing. -/
  neutral : ∀ weight, combine weight 0 = weight
  /-- A heavier part never yields a lighter whole. -/
  monotone : ∀ fixed lighter heavier,
    0 ≤ fixed → lighter ≤ heavier →
      combine fixed lighter ≤ combine fixed heavier
  /-- Merging non-negative weights stays non-negative. -/
  nonnegClosed : ∀ left right,
    0 ≤ left → 0 ≤ right → 0 ≤ combine left right

/-- Ordinary addition is a coarse-graining law. -/
def additionLaw : CoarseGrainingLaw where
  combine := fun left right => left + right
  commutative := by intro left right; ring
  associative := by intro left middle right; ring
  neutral := by intro weight; ring
  monotone := by intro fixed lighter heavier _ hle; linarith
  nonnegClosed := by intro left right hleft hright; linarith

/--
The inclusion-exclusion law `x + y + x * y`. It satisfies every demand above and
is not addition.
-/
def inclusionExclusionLaw : CoarseGrainingLaw where
  combine := fun left right => left + right + left * right
  commutative := by intro left right; ring
  associative := by intro left middle right; ring
  neutral := by intro weight; ring
  monotone := by
    intro fixed lighter heavier hfixed hle
    nlinarith
  nonnegClosed := by
    intro left right hleft hright
    nlinarith

/-- A weight assignment to three mutually exclusive alternatives. -/
structure ThreeAlternativeReadout where
  first : ℚ
  second : ℚ
  third : ℚ
  firstNonneg : 0 ≤ first
  secondNonneg : 0 ≤ second
  thirdNonneg : 0 ≤ third

/-- Merging all three alternatives under `law` yields the certain alternative. -/
def ClosesToUnit (law : CoarseGrainingLaw) (readout : ThreeAlternativeReadout) :
    Prop :=
  law.combine (law.combine readout.first readout.second) readout.third = 1

/-- The parts sum to the whole. -/
def PartsSumToUnit (readout : ThreeAlternativeReadout) : Prop :=
  readout.first + readout.second + readout.third = 1

/-- Weights `1/6, 2/6, 3/6`: closed under addition, and additive. -/
def additiveReadout : ThreeAlternativeReadout where
  first := 1 / 6
  second := 2 / 6
  third := 3 / 6
  firstNonneg := by norm_num
  secondNonneg := by norm_num
  thirdNonneg := by norm_num

/--
Weights `1/3, 1/8, 1/3`: strictly positive, closed to unit under the
inclusion-exclusion law, and summing to `19/24`.
-/
def inclusionExclusionReadout : ThreeAlternativeReadout where
  first := 1 / 3
  second := 1 / 8
  third := 1 / 3
  firstNonneg := by norm_num
  secondNonneg := by norm_num
  thirdNonneg := by norm_num

theorem additive_readout_closes_under_addition :
    ClosesToUnit additionLaw additiveReadout := by
  unfold ClosesToUnit additionLaw additiveReadout
  norm_num

theorem additive_readout_parts_sum_to_unit :
    PartsSumToUnit additiveReadout := by
  unfold PartsSumToUnit additiveReadout
  norm_num

theorem inclusion_exclusion_readout_closes_to_unit :
    ClosesToUnit inclusionExclusionLaw inclusionExclusionReadout := by
  unfold ClosesToUnit inclusionExclusionLaw inclusionExclusionReadout
  norm_num

theorem inclusion_exclusion_readout_parts_do_not_sum_to_unit :
    ¬ PartsSumToUnit inclusionExclusionReadout := by
  unfold PartsSumToUnit inclusionExclusionReadout
  norm_num

/--
The result. There is a coarse-graining law and a non-negative readout closed to
unit under it whose parts do not sum to unit. Coarse-graining closure therefore
does not entail additivity.
-/
theorem coarse_graining_closure_does_not_entail_additivity :
    ∃ law : CoarseGrainingLaw, ∃ readout : ThreeAlternativeReadout,
      ClosesToUnit law readout ∧ ¬ PartsSumToUnit readout :=
  ⟨inclusionExclusionLaw, inclusionExclusionReadout,
    inclusion_exclusion_readout_closes_to_unit,
    inclusion_exclusion_readout_parts_do_not_sum_to_unit⟩

/-- Addition is not the only coarse-graining law: the two disagree somewhere. -/
theorem coarse_graining_law_is_not_unique :
    ∃ left right : ℚ,
      additionLaw.combine left right ≠ inclusionExclusionLaw.combine left right :=
  ⟨1, 1, by unfold additionLaw inclusionExclusionLaw; norm_num⟩

/--
What coarse-graining closure fails to fix is the scale, not the structure: the
inclusion-exclusion law is addition read through the relabelling
`weight ↦ 1 + weight`, which turns merging into multiplication.
-/
theorem inclusion_exclusion_is_addition_after_relabelling (left right : ℚ) :
    1 + inclusionExclusionLaw.combine left right = (1 + left) * (1 + right) := by
  unfold inclusionExclusionLaw
  ring

inductive CoarseGrainingScaleFinding where
  | coarseGrainingClosureAdmitsNonAdditiveLaw
  | strictlyPositiveClosedReadoutNeedNotSumToUnit
  | inclusionExclusionLawIsAdditionAfterRelabelling
  | remainingFreedomIsTheValueScale
  deriving DecidableEq, Repr

def coarseGrainingScaleFindings : List CoarseGrainingScaleFinding :=
  [ .coarseGrainingClosureAdmitsNonAdditiveLaw,
    .strictlyPositiveClosedReadoutNeedNotSumToUnit,
    .inclusionExclusionLawIsAdditionAfterRelabelling,
    .remainingFreedomIsTheValueScale ]

theorem coarse_graining_scale_records_four_findings :
    coarseGrainingScaleFindings.length = 4 := by
  rfl

inductive CoarseGrainingScaleOpenObligation where
  | proveContinuityAndCancellationForceAdditionUpToRelabelling
  | decideWhetherIdtCanSelectARelabellingWithoutImportingBorn
  | extendBeyondThreeAlternatives
  | separateScaleFixingFromQuadraticReadout
  deriving DecidableEq, Repr

def coarseGrainingScaleOpenObligations :
    List CoarseGrainingScaleOpenObligation :=
  [ .proveContinuityAndCancellationForceAdditionUpToRelabelling,
    .decideWhetherIdtCanSelectARelabellingWithoutImportingBorn,
    .extendBeyondThreeAlternatives,
    .separateScaleFixingFromQuadraticReadout ]

theorem coarse_graining_scale_keeps_four_open_obligations :
    coarseGrainingScaleOpenObligations.length = 4 := by
  rfl

def coarseGrainingScaleClaimBoundary : String :=
  "Finite counterexample over three alternatives: commutative, associative, neutral, monotone, non-negativity-preserving coarse-graining closure does not entail additivity, because x + y + x*y satisfies all of it. It does not derive the Born rule, does not show that no arithmetic primitive suffices, and does not prove the classical continuity-plus-cancellation theorem it points at."

end QMClosure
end IDT
