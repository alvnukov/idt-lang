import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# The Born readout survives all three demands

This file corrects a claim made when `ParallelCompositionFixesScale` was
recorded, and the correction is the result.

That file proved: independent composition distributing over merging fails for
`relabelledMerge lambda = x + y + lambda * x * y` unless `lambda = 0`. Its scope
note said the proof covers the `lambda` family and not arbitrary merge laws.
The surrounding claim -- that parallel composition therefore selects addition
out of the whole relabelling freedom -- does not follow, and is false.

The witness is the Born readout itself. Take weights to be squares of
amplitudes and merging of alternatives to be addition of amplitudes, so that
the merged weight is `(a + b)^2`. As a law on weights this is
`merge x y = (sqrt x + sqrt y)^2`, addition read through the relabelling
`weight |-> sqrt weight`. It satisfies every demand assembled so far:

* commutativity, associativity and neutrality at zero;
* distributivity under independent composition, because
  `z^2 * (a + b)^2 = (z*a + z*b)^2`;
* cancellation, because squaring is injective on non-negative reals.

And it is not additive: `(a + b)^2 - a^2 - b^2 = 2*a*b`, non-zero whenever both
amplitudes are.

So the three demands do not pin addition. They leave at least the pair
`classical` and `Born`, and in fact the whole power family
`merge_k x y = (x^k + y^k)^(1/k)`, since
`z * merge_k x y = merge_k (z*x) (z*y)` for every `k`. Classical is `k = 1`,
Born is `k = 1/2`. Only that family is stated here informally; what is proved
is the `k = 1/2` case, which suffices to refute the claim.

This is good news for the programme and bad news for the shortcut. The three
structural demands are compatible with the Born readout rather than opposed to
it, but they do not select it, and no amount of further merging, composition or
cancellation discipline will. What selects `k` is a separate question, and the
interference structure below is where it is visible: the Born readout has
non-zero two-path interference and vanishing three-path interference, which is
Sorkin's second-order signature, while every additive readout has both terms
zero.

Scope. Finite, over ℚ, amplitudes rather than a Hilbert space. It does not
derive the Born rule, does not derive the complex carrier, and does not show
that the power family is exhaustive.
-/

/-- The weight of an alternative carrying amplitude `amplitude`. -/
def bornWeight (amplitude : ℚ) : ℚ := amplitude * amplitude

/-- Merging alternatives adds amplitudes, so the merged weight is a square. -/
def bornMerge (left right : ℚ) : ℚ := bornWeight (left + right)

theorem born_merge_commutative (left right : ℚ) :
    bornMerge left right = bornMerge right left := by
  unfold bornMerge bornWeight
  ring

theorem born_merge_associative (left middle right : ℚ) :
    bornWeight (left + middle + right) = bornWeight (left + (middle + right)) := by
  unfold bornWeight
  ring

theorem born_merge_neutral (amplitude : ℚ) :
    bornMerge amplitude 0 = bornWeight amplitude := by
  unfold bornMerge bornWeight
  ring

/--
Independent composition distributes over Born merging. Weighing by an
independent context of amplitude `outer` scales weights by `outer^2`, and that
commutes with adding amplitudes.
-/
theorem born_scale_distributes (outer left right : ℚ) :
    bornWeight outer * bornMerge left right
      = bornMerge (outer * left) (outer * right) := by
  unfold bornMerge bornWeight
  ring

/-- Born merging is cancellative on non-negative amplitudes. -/
theorem born_merge_cancellative (fixed left right : ℚ)
    (fixedNonneg : 0 ≤ fixed) (leftNonneg : 0 ≤ left) (rightNonneg : 0 ≤ right)
    (equalMerges : bornMerge fixed left = bornMerge fixed right) :
    left = right := by
  unfold bornMerge bornWeight at equalMerges
  nlinarith [equalMerges, fixedNonneg, leftNonneg, rightNonneg]

/-- Born merging is strictly monotone on non-negative amplitudes. -/
theorem born_merge_strictly_monotone (fixed left right : ℚ)
    (fixedNonneg : 0 ≤ fixed) (leftNonneg : 0 ≤ left)
    (increase : left < right) :
    bornMerge fixed left < bornMerge fixed right := by
  unfold bornMerge bornWeight
  nlinarith

/--
The point. The Born readout is not additive, so it is a genuine alternative to
addition that passes every demand above.
-/
theorem born_readout_is_not_additive :
    ¬ (∀ left right : ℚ, 0 ≤ left → 0 ≤ right →
        bornMerge left right = bornWeight left + bornWeight right) := by
  intro additive
  have collapse := additive 1 1 (by norm_num) (by norm_num)
  unfold bornMerge bornWeight at collapse
  norm_num at collapse

/-- Two-path interference of the Born readout. -/
def twoPathInterference (left right : ℚ) : ℚ :=
  bornWeight (left + right) - bornWeight left - bornWeight right

theorem two_path_interference_is_twice_the_product (left right : ℚ) :
    twoPathInterference left right = 2 * (left * right) := by
  unfold twoPathInterference bornWeight
  ring

theorem two_path_interference_nonzero (left right : ℚ)
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    twoPathInterference left right ≠ 0 := by
  rw [two_path_interference_is_twice_the_product]
  positivity

/-- Three-path interference, the Sorkin third-order term. -/
def threePathInterference (left middle right : ℚ) : ℚ :=
  bornWeight (left + middle + right)
    - bornWeight (left + middle)
    - bornWeight (left + right)
    - bornWeight (middle + right)
    + bornWeight left + bornWeight middle + bornWeight right

/--
The Sorkin signature: the Born readout is exactly second order. Third-order
interference vanishes identically, for every triple of amplitudes.
-/
theorem three_path_interference_vanishes (left middle right : ℚ) :
    threePathInterference left middle right = 0 := by
  unfold threePathInterference bornWeight
  ring

/-- An additive readout on weights. -/
def AdditiveWeightReadout (readout : ℚ → ℚ) : Prop :=
  ∀ left right : ℚ, readout (left + right) = readout left + readout right

/-- Every additive readout has no two-path interference at all. -/
theorem additive_readout_has_no_interference (readout : ℚ → ℚ)
    (additive : AdditiveWeightReadout readout) (left right : ℚ) :
    readout (left + right) - readout left - readout right = 0 := by
  rw [additive left right]
  ring

/--
The correction, stated as one theorem: Born merging satisfies distributivity
under independent composition and cancellation, and is not additive. So those
two demands do not select addition.
-/
theorem three_demands_do_not_select_addition :
    (∀ outer left right : ℚ,
        bornWeight outer * bornMerge left right
          = bornMerge (outer * left) (outer * right))
      ∧ (∀ fixed left right : ℚ,
        0 ≤ fixed → 0 ≤ left → 0 ≤ right →
          bornMerge fixed left = bornMerge fixed right → left = right)
      ∧ ¬ (∀ left right : ℚ, 0 ≤ left → 0 ≤ right →
        bornMerge left right = bornWeight left + bornWeight right) :=
  ⟨born_scale_distributes, born_merge_cancellative, born_readout_is_not_additive⟩

inductive BornSurvivalFinding where
  | bornMergeIsAdditionThroughSquareRootRelabelling
  | bornMergePassesDistributivityAndCancellation
  | earlierSelectionClaimHeldOnlyForTheLambdaFamily
  | interferenceIsWhereTheRemainingFreedomIsVisible
  | sorkinThirdOrderTermVanishes
  deriving DecidableEq, Repr

def bornSurvivalFindings : List BornSurvivalFinding :=
  [ .bornMergeIsAdditionThroughSquareRootRelabelling,
    .bornMergePassesDistributivityAndCancellation,
    .earlierSelectionClaimHeldOnlyForTheLambdaFamily,
    .interferenceIsWhereTheRemainingFreedomIsVisible,
    .sorkinThirdOrderTermVanishes ]

theorem born_survival_records_five_findings :
    bornSurvivalFindings.length = 5 := by
  rfl

inductive BornSurvivalOpenObligation where
  | proveThePowerFamilyIsExhaustiveUnderTheThreeDemands
  | findWhatSelectsTheExponentWithoutImportingBorn
  | deriveComplexAmplitudesRatherThanRationalOnes
  | connectExponentSelectionToContextualExclusivity
  deriving DecidableEq, Repr

def bornSurvivalOpenObligations : List BornSurvivalOpenObligation :=
  [ .proveThePowerFamilyIsExhaustiveUnderTheThreeDemands,
    .findWhatSelectsTheExponentWithoutImportingBorn,
    .deriveComplexAmplitudesRatherThanRationalOnes,
    .connectExponentSelectionToContextualExclusivity ]

theorem born_survival_keeps_four_open_obligations :
    bornSurvivalOpenObligations.length = 4 := by
  rfl

def bornSurvivalClaimBoundary : String :=
  "Corrects the claim that parallel composition selects addition: that holds for the lambda family only. The Born readout, addition through a square-root relabelling, passes coarse-graining, distributivity under independent composition and cancellation while failing additivity, so the three demands leave at least classical and Born standing. It does not derive the Born rule, does not derive a complex carrier, and does not show the power family is exhaustive."

end QMClosure
end IDT
