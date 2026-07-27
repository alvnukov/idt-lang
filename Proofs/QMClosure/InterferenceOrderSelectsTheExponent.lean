import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# Interference order selects the exponent

`BornSurvivesTheThreeDemands` showed that merging, independent composition and
cancellation leave a whole family of readouts standing, classical and Born
among them, and recorded `findWhatSelectsTheExponentWithoutImportingBorn`. This
file answers that for monomial readouts.

Weigh a set of alternatives by raising the sum of their amplitudes to a fixed
exponent, `weight S = (sum of amplitudes in S) ^ n`. Sorkin's interference terms
measure how far merging departs from additivity:

    I2 a b   = w(a+b) - w(a) - w(b)
    I3 a b c = w(a+b+c) - w(a+b) - w(a+c) - w(b+c) + w(a) + w(b) + w(c)

Two conditions, neither of which mentions amplitudes, Hilbert space or the Born
rule, pin the exponent to `2`:

* alternatives do interfere, `I2 ≠ 0`;
* interference stops at pairs, `I3 = 0`.

`I2` vanishes identically at exponent `1`, so the first condition excludes the
classical readout. `I3` vanishes identically at exponents `1` and `2`, and at
unit amplitudes equals `3^n - 3*2^n + 3`, which is proved positive for every
`n ≥ 3`. Exponent `0` fails both. So `n = 2` exactly, and that is Born.

This converts the open question from "what picks the Born readout" into "why
does interference terminate at second order". The second question is sharper,
is empirically testable on its own, and is already listed among the finite QM
gates of this repository. It is not thereby answered: the terminating-order
condition is an additional postulate here, not something derived from the
context-first primitives.

Scope. Natural-number exponents and monomial readouts over ℚ, not the full
power family with real exponents, and not arbitrary weight functions. The
general fact that `I3` vanishes identically exactly for polynomials of degree at
most two is not proved here. Amplitudes are rational, not complex, so this does
not derive the complex carrier, and it does not derive the Born rule from the
primitive base.
-/

/-- Weight of a set of alternatives whose amplitudes sum to `total`. -/
def pathWeight (exponent : ℕ) (total : ℚ) : ℚ := total ^ exponent

/-- Sorkin's second-order interference term. -/
def twoPathInterference (exponent : ℕ) (left right : ℚ) : ℚ :=
  pathWeight exponent (left + right)
    - pathWeight exponent left
    - pathWeight exponent right

/-- Sorkin's third-order interference term. -/
def threePathInterference (exponent : ℕ) (left middle right : ℚ) : ℚ :=
  pathWeight exponent (left + middle + right)
    - pathWeight exponent (left + middle)
    - pathWeight exponent (left + right)
    - pathWeight exponent (middle + right)
    + pathWeight exponent left
    + pathWeight exponent middle
    + pathWeight exponent right

/-- The classical readout does not interfere at all. -/
theorem two_path_vanishes_at_exponent_one (left right : ℚ) :
    twoPathInterference 1 left right = 0 := by
  unfold twoPathInterference pathWeight
  ring

/-- The Born readout interferes, by twice the product of amplitudes. -/
theorem two_path_at_exponent_two (left right : ℚ) :
    twoPathInterference 2 left right = 2 * (left * right) := by
  unfold twoPathInterference pathWeight
  ring

theorem three_path_vanishes_at_exponent_one (left middle right : ℚ) :
    threePathInterference 1 left middle right = 0 := by
  unfold threePathInterference pathWeight
  ring

/-- The Born readout is exactly second order: no genuine three-path term. -/
theorem three_path_vanishes_at_exponent_two (left middle right : ℚ) :
    threePathInterference 2 left middle right = 0 := by
  unfold threePathInterference pathWeight
  ring

/-- At unit amplitudes the third-order term is `3^n - 3*2^n + 3`. -/
theorem three_path_at_unit_amplitudes (exponent : ℕ) :
    threePathInterference exponent 1 1 1
      = (3 : ℚ) ^ exponent - 3 * 2 ^ exponent + 3 := by
  unfold threePathInterference pathWeight
  norm_num
  ring

theorem two_le_two_pow (exponent : ℕ) (atLeastOne : 1 ≤ exponent) :
    (2 : ℚ) ≤ 2 ^ exponent := by
  calc (2 : ℚ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ exponent := by
        apply pow_le_pow_right₀ (by norm_num) atLeastOne

/--
Above the second order the third-order term is strictly positive, for every
exponent. This is what forbids third-order and higher readouts.
-/
theorem three_path_positive_above_second_order (exponent : ℕ)
    (aboveSecond : 3 ≤ exponent) :
    0 < threePathInterference exponent 1 1 1 := by
  rw [three_path_at_unit_amplitudes]
  induction exponent, aboveSecond using Nat.le_induction with
  | base => norm_num
  | succ current atLeastThree inductionHypothesis =>
      have twoBound : (2 : ℚ) ≤ 2 ^ current :=
        two_le_two_pow current (by omega)
      have expand : (3 : ℚ) ^ (current + 1) = 3 * 3 ^ current := by ring
      have expandTwo : (2 : ℚ) ^ (current + 1) = 2 * 2 ^ current := by ring
      rw [expand, expandTwo]
      linarith

/--
The selection. Requiring that alternatives interfere and that interference
stops at pairs forces the exponent to be `2`.
-/
theorem interference_order_selects_exponent_two (exponent : ℕ)
    (interferes : twoPathInterference exponent 1 1 ≠ 0)
    (stopsAtPairs : threePathInterference exponent 1 1 1 = 0) :
    exponent = 2 := by
  match exponent with
  | 0 =>
      exfalso
      rw [three_path_at_unit_amplitudes] at stopsAtPairs
      norm_num at stopsAtPairs
  | 1 =>
      exfalso
      exact interferes (two_path_vanishes_at_exponent_one 1 1)
  | 2 => rfl
  | (remainder + 3) =>
      exfalso
      have positive := three_path_positive_above_second_order (remainder + 3) (by omega)
      rw [stopsAtPairs] at positive
      exact lt_irrefl 0 positive

/-- Both conditions do hold at exponent `2`, so the selection is not vacuous. -/
theorem exponent_two_satisfies_both_conditions :
    twoPathInterference 2 1 1 ≠ 0 ∧ threePathInterference 2 1 1 1 = 0 := by
  constructor
  · rw [two_path_at_exponent_two]
    norm_num
  · exact three_path_vanishes_at_exponent_two 1 1 1

inductive InterferenceOrderFinding where
  | classicalReadoutDoesNotInterfere
  | bornReadoutInterferesAtSecondOrder
  | thirdOrderTermVanishesOnlyBelowExponentThree
  | interferenceOrderPinsTheExponentToTwo
  | terminatingOrderIsAPostulateNotADerivation
  deriving DecidableEq, Repr

def interferenceOrderFindings : List InterferenceOrderFinding :=
  [ .classicalReadoutDoesNotInterfere,
    .bornReadoutInterferesAtSecondOrder,
    .thirdOrderTermVanishesOnlyBelowExponentThree,
    .interferenceOrderPinsTheExponentToTwo,
    .terminatingOrderIsAPostulateNotADerivation ]

theorem interference_order_records_five_findings :
    interferenceOrderFindings.length = 5 := by
  rfl

inductive InterferenceOrderOpenObligation where
  | deriveTerminatingInterferenceOrderFromContextFirstPrimitives
  | extendSelectionToRealExponentsAndArbitraryWeightFunctions
  | deriveComplexAmplitudesRatherThanRationalOnes
  | connectTerminatingOrderToContextualExclusivity
  deriving DecidableEq, Repr

def interferenceOrderOpenObligations : List InterferenceOrderOpenObligation :=
  [ .deriveTerminatingInterferenceOrderFromContextFirstPrimitives,
    .extendSelectionToRealExponentsAndArbitraryWeightFunctions,
    .deriveComplexAmplitudesRatherThanRationalOnes,
    .connectTerminatingOrderToContextualExclusivity ]

theorem interference_order_keeps_four_open_obligations :
    interferenceOrderOpenObligations.length = 4 := by
  rfl

def interferenceOrderClaimBoundary : String :=
  "For monomial readouts with natural exponents over ℚ, requiring non-zero two-path interference and vanishing three-path interference forces the exponent to be 2. This selects the Born readout from the surviving family without mentioning Hilbert space or the Born rule, but it postulates the terminating interference order rather than deriving it from the context-first primitives. It does not derive the Born rule, does not derive complex amplitudes, and does not cover real exponents or arbitrary weight functions."

end QMClosure
end IDT
