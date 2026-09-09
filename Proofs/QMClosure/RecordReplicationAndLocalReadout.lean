import Mathlib.Tactic

namespace IDT.QMClosure.RecordReplication

/-!
# Record copying and the local-readout selector

Continuation of InternalDetectorReadoutSeparation.

1. Arbitrarily many ideal copies of a distinguished pointer value preserve its
   marginal weight for EVERY weight function with w(0)=0. Copying records alone
   therefore supplies no exponent selector. This is copying distinguishable
   basis labels, not cloning arbitrary quantum states. It does not establish
   thermodynamic stability or select one branch of a superposition.
2. Grant a two-party rational amplitude table and a specific reversible local
   rotation on Bob's two columns. For weights |a|^n, n a positive natural number,
   Alice's marginal on one explicit preparation is unchanged by Bob's operation
   if and only if n=2. This is a necessary no-signalling test, not a proof that
   all states and operations obey no-signalling at n=2.

The preparation has rows (5,0) and (3,4); Bob's rotation sends these to (3,-4)
and (5,0). Square row masses remain 25 and 25. Fourth-power row masses change
from 625:337 to 337:625, permitting a signalling channel if such states and
operations are physically available and the proposed joint readout is used.
Common amplitude normalization cancels from this homogeneous readout.

Imports: signed rational amplitudes, the joint two-party carrier, marginalizing
by summing exclusive outcome weights, global normalization, the monomial family,
and availability of Bob's rotation. The rotation preserves a sum of squares;
this geometry is granted, not derived. We prove its algebra and isolate its
role instead of presenting no-signalling alone as a derivation of Born.

Related external literature, not formalized by this file:
Masanes-Galley-Mueller, https://arxiv.org/abs/1811.11060 (2019): their abstract
explicitly starts with unitary quantum mechanics and finite state estimation.
Pati, https://arxiv.org/abs/2601.13012 (2026 preprint): its abstract assumes local
unitary dynamics and entangled states in a modified-inner-product analysis.
Our finite proof below is independent of those external proofs.
-/

def copiedAmplitude (a : Bool → ℚ) (copies : ℕ)
    (pointer : Bool) (memory : Fin copies → Bool) : ℚ :=
  if memory = (fun _ => pointer) then a pointer else 0

/-- The finite sum includes every memory configuration, including mismatches. -/
theorem copying_preserves_any_zero_supported_weight
    (w : ℚ → ℚ) (zero : w 0 = 0) (a : Bool → ℚ)
    (copies : ℕ) (pointer : Bool) :
    (∑ memory : Fin copies → Bool, w (copiedAmplitude a copies pointer memory)) =
      w (a pointer) := by
  simp [copiedAmplitude, apply_ite, zero]

def powerWeight (n : ℕ) (a : ℚ) : ℚ := |a| ^ n

theorem positive_powers_survive_arbitrary_record_copying
    (n : ℕ) (positive : 0 < n) (a : Bool → ℚ)
    (copies : ℕ) (pointer : Bool) :
    (∑ memory : Fin copies → Bool,
      powerWeight n (copiedAmplitude a copies pointer memory)) =
        powerWeight n (a pointer) := by
  apply copying_preserves_any_zero_supported_weight
  simp [powerWeight, Nat.ne_of_gt positive]

def rotate (v : ℚ × ℚ) : ℚ × ℚ :=
  ((3 * v.1 + 4 * v.2) / 5, (-4 * v.1 + 3 * v.2) / 5)

def inverseRotate (v : ℚ × ℚ) : ℚ × ℚ :=
  ((3 * v.1 - 4 * v.2) / 5, (4 * v.1 + 3 * v.2) / 5)

theorem rotation_reversible (v : ℚ × ℚ) :
    inverseRotate (rotate v) = v ∧ rotate (inverseRotate v) = v := by
  constructor <;> apply Prod.ext <;> simp [rotate, inverseRotate] <;> ring

theorem rotation_preserves_quadratic_mass (v : ℚ × ℚ) :
    (rotate v).1 ^ 2 + (rotate v).2 ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
  simp only [rotate]
  ring

/-- Alice indexes rows, Bob indexes the two entries in each row. -/
abbrev JointAmplitude := Bool → ℚ × ℚ

def bobOperation (state : JointAmplitude) : JointAmplitude :=
  fun alice => rotate (state alice)

def preparation : JointAmplitude :=
  fun alice => if alice then (3, 4) else (5, 0)

theorem bob_changes_only_the_column_coordinates (state : JointAmplitude)
    (alice : Bool) : bobOperation state alice = rotate (state alice) := rfl

theorem preparation_transforms_as_stated :
    bobOperation preparation false = (3, -4) ∧
      bobOperation preparation true = (5, 0) := by
  norm_num [bobOperation, preparation, rotate]

def rowMass (n : ℕ) (row : ℚ × ℚ) : ℚ :=
  powerWeight n row.1 + powerWeight n row.2

def aliceProbability (n : ℕ) (state : JointAmplitude) : ℚ :=
  rowMass n (state false) / (rowMass n (state false) + rowMass n (state true))

theorem probability_before (n : ℕ) (positive : 0 < n) :
    aliceProbability n preparation =
      5 ^ n / ((5 : ℚ) ^ n + (3 ^ n + 4 ^ n)) := by
  simp [aliceProbability, rowMass, powerWeight, preparation, Nat.ne_of_gt positive]

theorem probability_after (n : ℕ) (positive : 0 < n) :
    aliceProbability n (bobOperation preparation) =
      (3 ^ n + 4 ^ n) / ((5 : ℚ) ^ n + (3 ^ n + 4 ^ n)) := by
  rw [aliceProbability, preparation_transforms_as_stated.1,
    preparation_transforms_as_stated.2]
  norm_num [rowMass, powerWeight, Nat.ne_of_gt positive]
  ring

theorem higher_powers_break_345_balance (n : ℕ) (high : 3 ≤ n) :
    (3 : ℚ) ^ n + 4 ^ n < 5 ^ n := by
  induction n, high using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
      have threeNonnegative : 0 ≤ (3 : ℚ) ^ k := by positivity
      have fivePositive : 0 < (5 : ℚ) ^ k := by positivity
      simp only [pow_succ]
      linarith

theorem balance_selects_two (n : ℕ) :
    (3 : ℚ) ^ n + 4 ^ n = 5 ^ n ↔ n = 2 := by
  constructor
  · intro balance
    by_cases high : 3 ≤ n
    · exact False.elim ((ne_of_lt (higher_powers_break_345_balance n high)) balance)
    · interval_cases n <;> norm_num at *
  · rintro rfl
    norm_num

/-- Exact classification for this witness and the positive-natural power family. -/
theorem local_readout_invariance_iff_square (n : ℕ) (positive : 0 < n) :
    aliceProbability n preparation = aliceProbability n (bobOperation preparation) ↔
      n = 2 := by
  rw [probability_before n positive, probability_after n positive]
  have denominator : (5 : ℚ) ^ n + (3 ^ n + 4 ^ n) ≠ 0 := by positivity
  constructor
  · intro invariant
    have balance : (5 : ℚ) ^ n = 3 ^ n + 4 ^ n := by
      field_simp [denominator] at invariant
      exact invariant
    exact (balance_selects_two n).mp balance.symm
  · rintro rfl
    norm_num

theorem quartic_local_signal :
    aliceProbability 4 preparation = 625 / 962 ∧
    aliceProbability 4 (bobOperation preparation) = 337 / 962 ∧
    aliceProbability 4 preparation ≠ aliceProbability 4 (bobOperation preparation) := by
  rw [probability_before 4 (by omega), probability_after 4 (by omega)]
  norm_num

theorem square_passes_this_local_test :
    aliceProbability 2 preparation = 1 / 2 ∧
    aliceProbability 2 (bobOperation preparation) = 1 / 2 := by
  rw [probability_before 2 (by omega), probability_after 2 (by omega)]
  norm_num

/-! Open research obligations; this list asserts no completed physical derivation. -/
inductive OpenObligation where
  | deriveAllowedLocalTransformationsWithoutQuadraticImport
  | deriveJointCarrierAndMarginalReadoutFromLowerPrimitives
  | extendBeyondNaturalMonomialWeightsAndRationalAmplitudes
  | deriveStableRecordsRatherThanIdealLabelCopies
  | explainIndividualOutcomesAndTheirFrequencies
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [ .deriveAllowedLocalTransformationsWithoutQuadraticImport,
    .deriveJointCarrierAndMarginalReadoutFromLowerPrimitives,
    .extendBeyondNaturalMonomialWeightsAndRationalAmplitudes,
    .deriveStableRecordsRatherThanIdealLabelCopies,
    .explainIndividualOutcomesAndTheirFrequencies ]

end IDT.QMClosure.RecordReplication
