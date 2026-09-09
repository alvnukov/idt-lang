import Proofs.QMClosure.NativeAmplitudeObservability

namespace IDT.QMClosure.NativeOperationBridge

open NativeAmplitudeObservability

/-!
# Operation-sensitive observability in the supplied integer amplitude algebra

An individual weight and reversibility do not determine which transformations
preserve coherent-reference observations. The parity map below is a universal
counterexample to that implication. Pair-sum weight preservation is a sufficient
conditional bridge; additive, individually weight-preserving maps supply it.

All coordinates, references, and operations here are mathematical inputs. No
physical preparability, complete measurement set, normalized overlap, or quantum
dynamics is derived. In particular, these theorems do not discharge the existing
QM overlap-preservation obligation. Multiplicativity is deliberately not imposed
on state transformations: the quarter-turn control would violate that filter.
-/

def paritySign (x : CoordinatePlane) : CoordinatePlane :=
  ⟨if x.im % 2 = 0 then x.re else -x.re, x.im⟩

theorem paritySign_involutive : Function.Involutive paritySign := by
  intro x
  rcases x with ⟨a, b⟩
  by_cases hb : b % 2 = 0 <;> simp [paritySign, hb]

theorem paritySign_bijective : Function.Bijective paritySign := by
  constructor
  · intro x y h
    calc
      x = paritySign (paritySign x) := (paritySign_involutive x).symm
      _ = paritySign (paritySign y) := congrArg paritySign h
      _ = y := paritySign_involutive y
  · intro x
    exact ⟨paritySign x, paritySign_involutive x⟩

theorem paritySign_preserves_weight (eta : ℤ) (x : CoordinatePlane) :
    planeWeight eta (paritySign x) = planeWeight eta x := by
  by_cases hb : x.im % 2 = 0 <;> simp [planeWeight, paritySign, hb]

/-- Equivalence is relative to the explicitly supplied set of all references. -/
def ReferenceEquivalent (eta : ℤ) (x y : CoordinatePlane) : Prop :=
  ∀ reference,
    planeWeight eta (planeAdd x reference) =
      planeWeight eta (planeAdd y reference)

theorem dual_reference_equivalent_iff (x y : CoordinatePlane) :
    ReferenceEquivalent 0 x y ↔ x.re = y.re := by
  constructor
  · intro h
    have atZero := h ⟨0, 0⟩
    have atUnit := h ⟨1, 0⟩
    norm_num [planeWeight, planeAdd] at atZero atUnit
    nlinarith
  · intro sameReal reference
    simp [planeWeight, planeAdd, sameReal]

def parityWitnessLeft : CoordinatePlane := ⟨1, 0⟩

def parityWitnessRight : CoordinatePlane := ⟨1, 1⟩

def unitReference : CoordinatePlane := ⟨1, 0⟩

theorem parity_witness_initially_reference_equivalent :
    ReferenceEquivalent 0 parityWitnessLeft parityWitnessRight := by
  rw [dual_reference_equivalent_iff]
  rfl

theorem parity_witness_after_reference_weights :
    planeWeight 0 (planeAdd (paritySign parityWitnessLeft) unitReference) = 4 ∧
      planeWeight 0 (planeAdd (paritySign parityWitnessRight) unitReference) = 0 := by
  norm_num [planeWeight, planeAdd, paritySign, parityWitnessLeft,
    parityWitnessRight, unitReference]

theorem paritySign_breaks_reference_equivalence :
    ¬ ReferenceEquivalent 0
      (paritySign parityWitnessLeft) (paritySign parityWitnessRight) := by
  intro h
  have witness := h unitReference
  have weights := parity_witness_after_reference_weights
  rw [weights.1, weights.2] at witness
  norm_num at witness

theorem paritySign_not_additive :
    ¬ (∀ x y, paritySign (planeAdd x y) =
      planeAdd (paritySign x) (paritySign y)) := by
  intro h
  have witness := congrArg GaussianHistoryAmplitude.re
    (h parityWitnessLeft parityWitnessRight)
  norm_num [paritySign, planeAdd, parityWitnessLeft, parityWitnessRight] at witness

theorem paritySign_changes_coherent_pair_weight :
    planeWeight 0 (planeAdd
      (paritySign parityWitnessLeft) (paritySign parityWitnessRight)) = 0 ∧
      planeWeight 0 (planeAdd parityWitnessLeft parityWitnessRight) = 4 := by
  norm_num [planeWeight, planeAdd, paritySign, parityWitnessLeft, parityWitnessRight]

def PairSumWeightPreserving (eta : ℤ) (f : CoordinatePlane → CoordinatePlane) : Prop :=
  ∀ x y, planeWeight eta (planeAdd (f x) (f y)) =
    planeWeight eta (planeAdd x y)

/-- A surjective map lets each output reference be pulled back to an input reference. -/
theorem reference_equivalence_transport
    (eta : ℤ) (f : CoordinatePlane → CoordinatePlane)
    (surjective : Function.Surjective f)
    (preservesPair : PairSumWeightPreserving eta f)
    (x y : CoordinatePlane) (equivalent : ReferenceEquivalent eta x y) :
    ReferenceEquivalent eta (f x) (f y) := by
  intro reference
  obtain ⟨sourceReference, rfl⟩ := surjective reference
  rw [preservesPair x sourceReference, preservesPair y sourceReference]
  exact equivalent sourceReference

/-- This is a supplied sufficient bridge, not an inferred physical admissibility law. -/
theorem additive_weight_preserving_implies_pair_sum
    (eta : ℤ) (f : CoordinatePlane → CoordinatePlane)
    (additive : ∀ x y, f (planeAdd x y) = planeAdd (f x) (f y))
    (preservesWeight : ∀ x, planeWeight eta (f x) = planeWeight eta x) :
    PairSumWeightPreserving eta f := by
  intro x y
  rw [← additive x y, preservesWeight]

def integerMatrixMap (p q r s : ℤ) (x : CoordinatePlane) : CoordinatePlane :=
  ⟨p * x.re + q * x.im, r * x.re + s * x.im⟩

/-- The full polynomial defect; three coefficients replace an unbounded search. -/
theorem integer_matrix_weight_defect (eta p q r s : ℤ) (x : CoordinatePlane) :
    planeWeight eta (integerMatrixMap p q r s x) - planeWeight eta x =
      (p ^ 2 + eta * r ^ 2 - 1) * x.re ^ 2 +
        (2 * (p * q + eta * r * s)) * x.re * x.im +
        (q ^ 2 + eta * s ^ 2 - eta) * x.im ^ 2 := by
  simp only [planeWeight, integerMatrixMap]
  ring

theorem integer_matrix_preserves_weight_iff (eta p q r s : ℤ) :
    (∀ x, planeWeight eta (integerMatrixMap p q r s x) = planeWeight eta x) ↔
      p ^ 2 + eta * r ^ 2 - 1 = 0 ∧
        2 * (p * q + eta * r * s) = 0 ∧
        q ^ 2 + eta * s ^ 2 - eta = 0 := by
  constructor
  · intro preservesWeight
    have atFirst := integer_matrix_weight_defect eta p q r s ⟨1, 0⟩
    have atSecond := integer_matrix_weight_defect eta p q r s ⟨0, 1⟩
    have atMixed := integer_matrix_weight_defect eta p q r s ⟨1, 1⟩
    rw [preservesWeight] at atFirst atSecond atMixed
    norm_num at atFirst atSecond atMixed
    constructor
    · linarith [atFirst]
    · constructor
      · nlinarith [atFirst, atSecond, atMixed]
      · linarith [atSecond]
  · rintro ⟨firstZero, mixedZero, secondZero⟩ x
    have defect := integer_matrix_weight_defect eta p q r s x
    rw [firstZero, mixedZero, secondZero] at defect
    simp only [zero_mul, zero_add] at defect
    exact sub_eq_zero.mp defect

/-- Even without invertibility, a dual-weight-preserving integer matrix has no
hidden-to-visible entry. This assertion does not classify nonlinear maps. -/
theorem dual_weight_preserving_matrix_first_row (p q r s : ℤ)
    (preservesWeight : ∀ x,
      planeWeight 0 (integerMatrixMap p q r s x) = planeWeight 0 x) :
    q = 0 ∧ p ^ 2 = 1 := by
  have atSecond := preservesWeight ⟨0, 1⟩
  have atFirst := preservesWeight ⟨1, 0⟩
  norm_num [planeWeight, integerMatrixMap] at atSecond atFirst
  constructor
  · nlinarith [sq_nonneg q]
  · rcases atFirst with positive | negative
    · rw [positive]
      norm_num
    · rw [negative]
      norm_num

theorem dual_weight_preserving_matrix_respects_equivalence (p q r s : ℤ)
    (preservesWeight : ∀ x,
      planeWeight 0 (integerMatrixMap p q r s x) = planeWeight 0 x)
    (x y : CoordinatePlane) (equivalent : ReferenceEquivalent 0 x y) :
    ReferenceEquivalent 0
      (integerMatrixMap p q r s x) (integerMatrixMap p q r s y) := by
  have firstRow := dual_weight_preserving_matrix_first_row p q r s preservesWeight
  have sameReal := (dual_reference_equivalent_iff x y).mp equivalent
  rw [dual_reference_equivalent_iff]
  simp [integerMatrixMap, firstRow.1, sameReal]

def quarterTurn (x : CoordinatePlane) : CoordinatePlane := ⟨-x.im, x.re⟩

def inverseQuarterTurn (x : CoordinatePlane) : CoordinatePlane := ⟨x.im, -x.re⟩

theorem quarterTurn_left_inverse (x : CoordinatePlane) :
    inverseQuarterTurn (quarterTurn x) = x := by
  cases x
  simp [quarterTurn, inverseQuarterTurn]

theorem quarterTurn_right_inverse (x : CoordinatePlane) :
    quarterTurn (inverseQuarterTurn x) = x := by
  cases x
  simp [quarterTurn, inverseQuarterTurn]

theorem quarterTurn_bijective : Function.Bijective quarterTurn := by
  constructor
  · intro x y h
    calc
      x = inverseQuarterTurn (quarterTurn x) := (quarterTurn_left_inverse x).symm
      _ = inverseQuarterTurn (quarterTurn y) := congrArg inverseQuarterTurn h
      _ = y := quarterTurn_left_inverse y
  · intro x
    exact ⟨inverseQuarterTurn x, quarterTurn_right_inverse x⟩

theorem quarterTurn_additive (x y : CoordinatePlane) :
    quarterTurn (planeAdd x y) = planeAdd (quarterTurn x) (quarterTurn y) := by
  simp [quarterTurn, planeAdd, neg_add_rev, add_comm]

theorem quarterTurn_preserves_gaussian_weight (x : CoordinatePlane) :
    planeWeight 1 (quarterTurn x) = planeWeight 1 x := by
  simp [quarterTurn, planeWeight, add_comm]

theorem quarterTurn_preserves_gaussian_pair_sum :
    PairSumWeightPreserving 1 quarterTurn :=
  additive_weight_preserving_implies_pair_sum 1 quarterTurn
    quarterTurn_additive quarterTurn_preserves_gaussian_weight

/-- Rejecting every nonmultiplicative state map would also reject this additive,
reversible, Gaussian-weight-preserving control. This is a filter-scope result. -/
theorem quarterTurn_not_multiplicative :
    ¬ (∀ x y, quarterTurn (planeMul (-1) x y) =
      planeMul (-1) (quarterTurn x) (quarterTurn y)) := by
  intro h
  have witness := congrArg GaussianHistoryAmplitude.re (h ⟨1, 0⟩ ⟨1, 0⟩)
  norm_num [quarterTurn, planeMul] at witness

end IDT.QMClosure.NativeOperationBridge
