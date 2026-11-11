import Proofs.QMClosure.NativeTwoProbeContinuationReadout
import Proofs.QMClosure.NativeRegularReadoutCountercontrol

/-!
# Restricted adjacent-square continuation for the native readout

Only the prescribed adjacent-square quartets are compared. Rotation and one
native seed propagate their vanishing mixed difference to the whole integer
lattice. Rectangle separation and the native diagonal scaling then select the
squared norm independently of the full pair-congruence selector.

After this selection, the global two-probe and four-corner laws and native
readout consequences follow from the established norm identity. A concrete
norm witness inhabits the contract. The regular native countercontrol fails
the restricted premise at one exact square. Off-native polynomial controls
show incomparability with universal four-corner pair congruence.

The grammar, scalar normalization, universal native transfers and restricted
continuation premise remain supplied. Physical origins and full QM remain open.
-/

noncomputable section

namespace IDT.QMClosure.NativeLocalSquareReadout

open FiniteMixtureContinuationRank
open FiniteTranslationSmallRankSupport
open IDT.FixedCornerHalfMixtureReadout
open IDT.MultiplicativeMixtureReadout
open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout
open NativeTwoProbeContinuationReadout

attribute [local instance] presentationCommRing presentationCharZero

/-- The mixed difference of one adjacent lattice square. -/
def squareDifference (f : IntegerLattice -> Real) (z : IntegerLattice) : Real :=
  f z + f (z + (1, 1)) - f (z + (1, 0)) - f (z + (0, 1))

/-- Only equal horizontal-probe sums for one adjacent square are continued. -/
def RestrictedSquareContinuation (f : IntegerLattice -> Real) : Prop :=
  forall z,
    horizontalProbes f z + horizontalProbes f (z + (1, 1)) =
        horizontalProbes f (z + (1, 0)) + horizontalProbes f (z + (0, 1)) ->
      horizontalProbes f (z + (1, 0)) +
          horizontalProbes f ((z + (1, 0)) + (1, 1)) =
        horizontalProbes f ((z + (1, 0)) + (1, 0)) +
          horizontalProbes f ((z + (1, 0)) + (0, 1))

/-- A square probe-pair equality comprises two adjacent zero mixed differences. -/
theorem square_pair_eq_iff (f : IntegerLattice -> Real) (z : IntegerLattice) :
    Iff (horizontalProbes f z + horizontalProbes f (z + (1, 1)) =
        horizontalProbes f (z + (1, 0)) + horizontalProbes f (z + (0, 1)))
      (And (squareDifference f z = 0) (squareDifference f (z + (1, 0)) = 0)) := by
  constructor
  next =>
    intro h
    have hzero : f z + f (z + (1, 1)) = f (z + (1, 0)) + f (z + (0, 1)) := by
      simpa [horizontalProbes] using congrFun h 0
    have hone : f (z + (1, 0)) + f ((z + (1, 0)) + (1, 1)) =
        f ((z + (1, 0)) + (1, 0)) + f ((z + (1, 0)) + (0, 1)) := by
      simpa [horizontalProbes, add_assoc, add_left_comm, add_comm] using congrFun h 1
    constructor <;> dsimp [squareDifference] <;> linarith
  next =>
    intro h
    have hzero := h.1
    have hone := h.2
    dsimp [squareDifference] at hzero hone
    funext j
    fin_cases j
    next =>
      change f z + f (z + (1, 1)) = f (z + (1, 0)) + f (z + (0, 1))
      linarith
    next =>
      have hnext : f (z + (1, 0)) + f ((z + (1, 0)) + (1, 1)) =
          f ((z + (1, 0)) + (1, 0)) + f ((z + (1, 0)) + (0, 1)) := by
        linarith
      simpa [horizontalProbes, add_assoc, add_left_comm, add_comm] using hnext

theorem restrictedSquareContinuation_iff (f : IntegerLattice -> Real) :
    Iff (RestrictedSquareContinuation f)
      (forall z, squareDifference f z = 0 -> squareDifference f (z + (1, 0)) = 0 ->
        squareDifference f (z + (2, 0)) = 0) := by
  constructor
  next =>
    intro h z hzero hone
    have hseed := (square_pair_eq_iff f z).mpr (And.intro hzero hone)
    have hnext := (square_pair_eq_iff f (z + (1, 0))).mp (h z hseed)
    simpa only [add_assoc] using hnext.2
  next =>
    intro h z hseed
    have hpair := (square_pair_eq_iff f z).mp hseed
    apply (square_pair_eq_iff f (z + (1, 0))).mpr
    refine And.intro hpair.2 ?_
    simpa only [add_assoc] using h z hpair.1 hpair.2

theorem restrictedSquareContinuation_of_horizontalPairLaw
    (f : IntegerLattice -> Real)
    (h : PairCongruentUnder (horizontalProbes f) (fun z => z + (1, 0))) :
    RestrictedSquareContinuation f := by
  intro z hseed
  simpa only [add_assoc, add_left_comm, add_comm] using
    h z (z + (1, 1)) (z + (1, 0)) (z + (0, 1)) hseed

section AbstractPropagation

/-- The square opposite under two affine quarter turns. -/
def squareOpposite (z : IntegerLattice) : IntegerLattice := -z - (1, 1)

theorem cornerTurn_twice (z : IntegerLattice) :
    cornerTurn (cornerTurn z) = squareOpposite z := by
  apply Prod.ext <;> dsimp [cornerTurn, turn, squareOpposite] <;> ring

/-- Rotation sign reversal and forward two-zero propagation force every value
to vanish once the origin vanishes. -/
theorem zero_everywhere_of_cornerTurn_forward
    (D : IntegerLattice -> Real)
    (hturn : forall z, D (cornerTurn z) = -D z)
    (hforward : forall z, D z = 0 -> D (z + (1, 0)) = 0 -> D (z + (2, 0)) = 0)
    (hseed : D (0, 0) = 0) (z : IntegerLattice) : D z = 0 := by
  have hopposite (w : IntegerLattice) : D (squareOpposite w) = D w := by
    rw [<- cornerTurn_twice, hturn, hturn, neg_neg]
  have hbackward (w : IntegerLattice) (hzero : D w = 0)
      (hone : D (w + (1, 0)) = 0) : D (w - (1, 0)) = 0 := by
    have hleft : D (squareOpposite (w + (1, 0))) = 0 := by
      rw [hopposite, hone]
    have hcenter : D (squareOpposite (w + (1, 0)) + (1, 0)) = 0 := by
      have heq : squareOpposite (w + (1, 0)) + (1, 0) = squareOpposite w := by
        apply Prod.ext <;> dsimp [squareOpposite] <;> ring
      rw [heq, hopposite, hzero]
    have hnext := hforward (squareOpposite (w + (1, 0))) hleft hcenter
    have heq : squareOpposite (w + (1, 0)) + (2, 0) =
        squareOpposite (w - (1, 0)) := by
      apply Prod.ext <;> dsimp [squareOpposite] <;> ring
    rw [heq, hopposite] at hnext
    exact hnext
  have hrow (x y : Int) (hzero : D (x, y) = 0) (hone : D (x + 1, y) = 0)
      (n : Int) : D (n, y) = 0 := by
    have hoffset (m : Int) : And (D (x + m, y) = 0) (D (x + m + 1, y) = 0) := by
      induction m using Int.induction_on with
      | zero => simpa using And.intro hzero hone
      | succ m ih =>
          constructor
          next =>
            simpa only [add_assoc] using ih.2
          next =>
            have hnext := hforward (x + (m : Int), y) ih.1 (by simpa using ih.2)
            have heq : ((x + (m : Int), y) : IntegerLattice) + (2, 0) =
                (x + ((m : Int) + 1) + 1, y) := by
              apply Prod.ext <;> dsimp <;> ring
            rw [heq] at hnext
            exact hnext
      | pred m ih =>
          constructor
          next =>
            have hprev := hbackward (x + (-(m : Int)), y) ih.1 (by simpa using ih.2)
            have heq : ((x + (-(m : Int)), y) : IntegerLattice) - (1, 0) =
                (x + (-(m : Int) - 1), y) := by
              apply Prod.ext <;> dsimp <;> ring
            rw [heq] at hprev
            exact hprev
          next =>
            have heq : x + (-(m : Int) - 1) + 1 = x + (-(m : Int)) := by ring
            rw [heq]
            exact ih.1
    have h := (hoffset (n - x)).1
    have heq : x + (n - x) = n := by ring
    rw [heq] at h
    exact h
  have hminus : D (-1, 0) = 0 := by
    simpa [cornerTurn, turn, hseed] using hturn (0, 0)
  have hrowZero (x : Int) : D (x, 0) = 0 := by
    exact hrow (-1) 0 hminus (by simpa using hseed) x
  have hrowMinus (x : Int) : D (x, -1) = 0 := by
    have h := hopposite (-x - 1, 0)
    have heq : squareOpposite (-x - 1, 0) = (x, -1) := by
      apply Prod.ext <;> dsimp [squareOpposite] <;> ring
    rw [heq, hrowZero] at h
    exact h
  have hcolumnMinus (y : Int) : D (-1, y) = 0 := by
    simpa [cornerTurn, turn, hrowZero] using hturn (y, 0)
  have hcolumnZero (y : Int) : D (0, y) = 0 := by
    simpa [cornerTurn, turn, hrowMinus] using hturn (y, -1)
  exact hrow (-1) z.2 (hcolumnMinus z.2) (by simpa using hcolumnZero z.2) z.1

end AbstractPropagation

section IntegerSelection

theorem squareDifference_cornerTurn (f : IntegerLattice -> Real)
    (hrot : forall z, f (turn z) = f z) (z : IntegerLattice) :
    squareDifference f (cornerTurn z) = -squareDifference f z := by
  have hzero := fixedCornerProbes_cornerTurn f hrot z 0
  have hone := fixedCornerProbes_cornerTurn f hrot z 1
  have htwo := fixedCornerProbes_cornerTurn f hrot z 2
  have hthree := fixedCornerProbes_cornerTurn f hrot z 3
  norm_num [fixedCornerProbes, cornerPermutation, normCorner, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, show ((0, 0) : IntegerLattice) = 0 from rfl] at hzero hone htwo hthree
  dsimp [squareDifference]
  linarith

theorem squareDifference_seed (f : IntegerLattice -> Real)
    (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
    (hrot : forall z, f (turn z) = f z)
    (hdiagonal : forall z, f (gaussianMul (1, 1) z) = 2 * f z) :
    squareDifference f (0, 0) = 0 := by
  have hi : f (0, 1) = 1 := by
    simpa [turn, hunit] using hrot (1, 0)
  have hdiag : f (1, 1) = 2 := by
    simpa [gaussianMul, hunit] using hdiagonal (1, 0)
  norm_num [squareDifference, hzero, hunit, hi, hdiag]

theorem squareDifference_eq_zero (f : IntegerLattice -> Real)
    (hrestricted : RestrictedSquareContinuation f)
    (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
    (hrot : forall z, f (turn z) = f z)
    (hdiagonal : forall z, f (gaussianMul (1, 1) z) = 2 * f z)
    (z : IntegerLattice) : squareDifference f z = 0 :=
  zero_everywhere_of_cornerTurn_forward (squareDifference f)
    (squareDifference_cornerTurn f hrot)
    ((restrictedSquareContinuation_iff f).mp hrestricted)
    (squareDifference_seed f hzero hunit hrot hdiagonal) z

/-- Norm selection uses mixed differences, separation and an axis recurrence. -/
theorem integer_readout_eq_norm_of_restricted_square
    (f : IntegerLattice -> Real) (hrestricted : RestrictedSquareContinuation f)
    (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
    (hrot : forall z, f (turn z) = f z)
    (hdiagonal : forall z, f (gaussianMul (1, 1) z) = 2 * f z)
    (z : IntegerLattice) : f z = (z.1 : Real) ^ 2 + (z.2 : Real) ^ 2 := by
  have hrectangle (x y : Int) :
      f (x + 1, y + 1) + f (x, y) = f (x + 1, y) + f (x, y + 1) := by
    have h := squareDifference_eq_zero f hrestricted hzero hunit hrot hdiagonal (x, y)
    simp [squareDifference] at h
    linarith
  have hseparates (x y : Int) : f (x, y) = f (x, 0) + f (y, 0) := by
    have h := integer_rectangle_separates (fun x y => f (x, y)) hrectangle x y
    have haxis : f (0, y) = f (y, 0) := by simpa [turn] using hrot (y, 0)
    simpa [hzero, haxis] using h
  have hparallelogram (x y : Int) :
      f (x + y, 0) + f (x - y, 0) = 2 * f (x, 0) + 2 * f (y, 0) := by
    have hproduct : f (x - y, x + y) = 2 * f (x, y) := by
      simpa [gaussianMul, add_comm] using hdiagonal (x, y)
    have hsepleft := hseparates (x - y) (x + y)
    have hsepright := hseparates x y
    rw [hsepleft, hsepright] at hproduct
    linarith
  have heven (n : Int) : f (-n, 0) = f (n, 0) := by
    simpa using negation_invariant_of_rotation f hrot (n, 0)
  have hrec (n : Int) : f (n + 1, 0) + f (n - 1, 0) = 2 * f (n, 0) + 2 := by
    simpa [hunit] using hparallelogram n 1
  have haxis (n : Int) : f (n, 0) = (n : Real) ^ 2 :=
    integer_quadratic_recurrence (fun n => f (n, 0)) hzero hunit heven hrec n
  rw [hseparates z.1 z.2, haxis, haxis]

end IntegerSelection

section NativeSelection

theorem integerReadout_eq_norm_of_native_restricted_square
    (W : Presentation -> Real) (L : NativeTransfer W)
    (hrestricted : RestrictedSquareContinuation (integerReadout W))
    (z : IntegerLattice) : integerReadout W z = (z.1 : Real) ^ 2 + (z.2 : Real) ^ 2 := by
  apply integer_readout_eq_norm_of_restricted_square (integerReadout W) hrestricted
  next =>
    simpa [integerReadout, Arithmetic.gaussian] using readout_zero L
  next =>
    simpa [integerReadout, Arithmetic.gaussian] using L.unit
  next =>
    intro t
    unfold integerReadout
    rw [gaussian_turn, readout_phase_mul L]
  next =>
    intro t
    unfold integerReadout
    rw [gaussian_diagonal, readout_diagonal_mul L]

theorem readout_normal_form_of_native_restricted_square
    (W : Presentation -> Real) (L : NativeTransfer W)
    (hrestricted : RestrictedSquareContinuation (integerReadout W))
    (k : Nat) (z : IntegerLattice) :
    W (NormalForm.value k z) =
      ((z.1 : Real) ^ 2 + (z.2 : Real) ^ 2) / (4 : Real) ^ k := by
  change W (half ^ k * Arithmetic.gaussian phase z) = _
  rw [readout_half_pow_mul L]
  exact congrArg (fun t : Real => t / (4 : Real) ^ k)
    (integerReadout_eq_norm_of_native_restricted_square W L hrestricted z)

theorem readout_eq_complex_norm_of_native_restricted_square
    (W : Presentation -> Real) (L : NativeTransfer W)
    (hrestricted : RestrictedSquareContinuation (integerReadout W))
    (p : Presentation) : W p = Complex.normSq (complexEval p) := by
  cases NormalForm.exists_value p with
  | intro k hk =>
      cases hk with
      | intro z hp =>
          rw [hp]
          exact (readout_normal_form_of_native_restricted_square W L hrestricted k z).trans
            (complex_norm_normal_form k z).symm

/-- The universal pair laws are consequences of the independently selected norm. -/
theorem twoProbeContinuation_of_native_restricted_square
    (W : Presentation -> Real) (L : NativeTransfer W)
    (hrestricted : RestrictedSquareContinuation (integerReadout W)) :
    TwoProbeContinuationLaw W := by
  have heq : integerReadout W = normReadout := by
    funext z
    exact integerReadout_eq_norm_of_native_restricted_square W L hrestricted z
  unfold TwoProbeContinuationLaw
  rw [heq]
  exact normReadout_horizontal_pairCongruent

theorem fixedCornerPairLaws_of_native_restricted_square
    (W : Presentation -> Real) (L : NativeTransfer W)
    (hrestricted : RestrictedSquareContinuation (integerReadout W)) :
    FixedCornerPairLaws W := by
  have heq : integerReadout W = normReadout := by
    funext z
    exact integerReadout_eq_norm_of_native_restricted_square W L hrestricted z
  unfold FixedCornerPairLaws
  rw [heq]
  exact fun j => normReadout_pairCongruent_translation (localStep j)

theorem readout_eq_complex_norm_of_restricted_square
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (hrestricted : RestrictedSquareContinuation (integerReadout W)) (p : Presentation) :
    W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_native_restricted_square W
    (nativeTransfer_of_normalized_generator_transfer W hnorm ha hb) hrestricted p

theorem readout_normal_form_of_restricted_square
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (hrestricted : RestrictedSquareContinuation (integerReadout W))
    (k : Nat) (z : IntegerLattice) :
    W (NormalForm.value k z) =
      ((z.1 : Real) ^ 2 + (z.2 : Real) ^ 2) / (4 : Real) ^ k :=
  readout_normal_form_of_native_restricted_square W
    (nativeTransfer_of_normalized_generator_transfer W hnorm ha hb) hrestricted k z

theorem global_readout_laws_of_restricted_square
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (hrestricted : RestrictedSquareContinuation (integerReadout W)) :
    And (forall p q, W (p * q) = W p * W q)
      (And (forall p, W (reflection p) = W p)
        (And (forall p, 0 <= W p)
          (And (forall p, Iff (W p = 0) (p = 0))
            (forall p : Prod Presentation Presentation,
              W (mixer p).1 + W (mixer p).2 = W p.1 + W p.2)))) := by
  let L := nativeTransfer_of_normalized_generator_transfer W hnorm ha hb
  let M := fixedCornerPairLaws_of_native_restricted_square W L hrestricted
  exact And.intro (readout_multiplicative L M)
    (And.intro (readout_reflection L M)
      (And.intro (readout_nonnegative L M)
        (And.intro (readout_zero_iff L M) (mixer_conservation L M))))

end NativeSelection

section Witness

theorem normReadout_squareDifference (z : IntegerLattice) :
    squareDifference normReadout z = 0 := by
  simp [squareDifference, normReadout]
  ring

theorem normReadout_restricted_square : RestrictedSquareContinuation normReadout := by
  apply (restrictedSquareContinuation_iff normReadout).mpr
  intro z _ _
  exact normReadout_squareDifference (z + (2, 0))

/-- Every square antecedent is inhabited for the norm witness. -/
theorem normReadout_square_pair (z : IntegerLattice) :
    horizontalProbes normReadout z + horizontalProbes normReadout (z + (1, 1)) =
      horizontalProbes normReadout (z + (1, 0)) +
        horizontalProbes normReadout (z + (0, 1)) :=
  (square_pair_eq_iff normReadout z).mpr
    (And.intro (normReadout_squareDifference z)
      (normReadout_squareDifference (z + (1, 0))))

theorem modelReadout_restricted_square :
    RestrictedSquareContinuation (integerReadout modelReadout) := by
  rw [modelReadout_integer]
  exact normReadout_restricted_square

theorem modelReadout_restricted_square_contract :
    And (modelReadout a + modelReadout b = 1)
      (And (forall p, modelReadout (a * p) = modelReadout a * modelReadout p)
        (And (forall p, modelReadout (b * p) = modelReadout b * modelReadout p)
          (RestrictedSquareContinuation (integerReadout modelReadout)))) := by
  have hmodel := modelReadout_reduced_contract
  exact And.intro hmodel.1
    (And.intro hmodel.2.1 (And.intro hmodel.2.2.1 modelReadout_restricted_square))

theorem native_restricted_square_iff_twoProbe
    (W : Presentation -> Real) (L : NativeTransfer W) :
    Iff (RestrictedSquareContinuation (integerReadout W)) (TwoProbeContinuationLaw W) :=
  Iff.intro (twoProbeContinuation_of_native_restricted_square W L)
    (restrictedSquareContinuation_of_horizontalPairLaw (integerReadout W))

theorem native_restricted_square_iff_norm
    (W : Presentation -> Real) (L : NativeTransfer W) :
    Iff (RestrictedSquareContinuation (integerReadout W))
      (forall p, W p = Complex.normSq (complexEval p)) := by
  constructor
  next =>
    exact readout_eq_complex_norm_of_native_restricted_square W L
  next =>
    intro hnorm
    have heq : W = modelReadout := by
      funext p
      exact hnorm p
    rw [heq]
    exact modelReadout_restricted_square

end Witness

section RegularCountercontrol

open NativeRegularReadoutCountercontrol

theorem regular_square_seed_packets (c : Real) :
    And (horizontalProbes (latticeWeight c) (-1, -1) +
        horizontalProbes (latticeWeight c) (0, 0) = ![(2 : Real), 2])
      (horizontalProbes (latticeWeight c) (0, -1) +
        horizontalProbes (latticeWeight c) (-1, 0) = ![(2 : Real), 2]) := by
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [horizontalProbes, latticeWeight_formula]

theorem regular_square_shift_packets (c : Real) :
    And (horizontalProbes (latticeWeight c) (0, -1) +
        horizontalProbes (latticeWeight c) (1, 0) = ![(2 : Real), 6])
      (horizontalProbes (latticeWeight c) (1, -1) +
        horizontalProbes (latticeWeight c) (0, 0) = ![(2 : Real), 6 + defect c]) := by
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [horizontalProbes, latticeWeight_formula, defect] <;> ring

theorem regular_square_difference_values (c : Real) :
    And (squareDifference (latticeWeight c) (-1, -1) = 0)
      (And (squareDifference (latticeWeight c) (0, -1) = 0)
        (squareDifference (latticeWeight c) (1, -1) = -defect c)) := by
  constructor
  next =>
    norm_num [squareDifference, latticeWeight_formula]
  next =>
    constructor
    next =>
      norm_num [squareDifference, latticeWeight_formula]
    next =>
      norm_num [squareDifference, latticeWeight_formula, defect] <;> ring

theorem counterWeight_not_restricted_square (c : Real) (hc : 0 < c) :
    Not (RestrictedSquareContinuation (integerReadout (counterWeight c))) := by
  intro h
  have hforward := (restrictedSquareContinuation_iff (latticeWeight c)).mp h
  have hvalues := regular_square_difference_values c
  have hnext := hforward (-1, -1) hvalues.1 (by simpa using hvalues.2.1)
  have hnext' : squareDifference (latticeWeight c) (1, -1) = 0 := by simpa using hnext
  rw [hvalues.2.2] at hnext'
  have hd := defect_pos c hc
  linarith

end RegularCountercontrol

section OffNativeComparison

/-- A separable polynomial has vanishing mixed differences. -/
def separableQuartic (z : IntegerLattice) : Real :=
  (z.1 : Real) ^ 4 + (z.2 : Real) ^ 4

theorem separableQuartic_squareDifference (z : IntegerLattice) :
    squareDifference separableQuartic z = 0 := by
  simp [squareDifference, separableQuartic]
  ring

theorem separableQuartic_restricted_square :
    RestrictedSquareContinuation separableQuartic := by
  apply (restrictedSquareContinuation_iff separableQuartic).mpr
  intro z _ _
  exact separableQuartic_squareDifference (z + (2, 0))

theorem separableQuartic_not_fourCorner :
    Not (PairCongruentUnder (fixedCornerProbes separableQuartic)
      (fun z => z + (1, 0))) := by
  intro h
  have hseed : fixedCornerProbes separableQuartic (0, 1) +
      fixedCornerProbes separableQuartic (-1, -2) =
      fixedCornerProbes separableQuartic (1, 0) +
        fixedCornerProbes separableQuartic (-2, -1) := by
    funext j
    fin_cases j <;> norm_num [fixedCornerProbes, normCorner, separableQuartic]
  have hnext := congrFun (h (0, 1) (-1, -2) (1, 0) (-2, -1) hseed) 1
  norm_num [fixedCornerProbes, normCorner, separableQuartic] at hnext

theorem separableQuartic_not_horizontal :
    Not (PairCongruentUnder (horizontalProbes separableQuartic)
      (fun z => z + (1, 0))) := by
  intro h
  exact separableQuartic_not_fourCorner
    (fixedCornerPairLaw_of_horizontalPairLaw separableQuartic h)

/-- A fourth-degree one-coordinate polynomial supplies the converse control. -/
def projectedQuartic (z : IntegerLattice) : Real :=
  ((z.1 : Real) + 2 * (z.2 : Real)) ^ 4 -
    4 * ((z.1 : Real) + 2 * (z.2 : Real)) ^ 2

theorem projectedQuartic_two_steps (z : IntegerLattice) :
    projectedQuartic (z + (2, 0)) = projectedQuartic (z + (0, 1)) := by
  simp [projectedQuartic]
  ring

theorem projectedQuartic_four_steps (z : IntegerLattice) :
    projectedQuartic (z + (2, 1)) =
      4 * projectedQuartic (z + (1, 1)) - 6 * projectedQuartic (z + (0, 1)) +
        4 * projectedQuartic (z + (1, 0)) - projectedQuartic z + 24 := by
  simp [projectedQuartic]
  ring

theorem projectedQuartic_fourCorner_continuation :
    PairCongruentUnder (fixedCornerProbes projectedQuartic) (fun z => z + (1, 0)) := by
  intro a b c d hpair
  have hzero := congrFun hpair 0
  have hone := congrFun hpair 1
  have htwo := congrFun hpair 2
  have hthree := congrFun hpair 3
  simp only [Pi.add_apply, fixedCornerProbes, normCorner,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    show ((0, 0) : IntegerLattice) = 0 from rfl, add_zero] at hzero hone htwo hthree
  funext j
  fin_cases j
  next =>
    simpa [fixedCornerProbes, normCorner, show ((0, 0) : IntegerLattice) = 0 from rfl] using hone
  next =>
    change projectedQuartic ((a + (1, 0)) + (1, 0)) +
        projectedQuartic ((b + (1, 0)) + (1, 0)) =
        projectedQuartic ((c + (1, 0)) + (1, 0)) +
        projectedQuartic ((d + (1, 0)) + (1, 0))
    simp only [add_assoc]
    change projectedQuartic (a + (2, 0)) + projectedQuartic (b + (2, 0)) =
      projectedQuartic (c + (2, 0)) + projectedQuartic (d + (2, 0))
    simpa only [projectedQuartic_two_steps] using htwo
  next =>
    simpa [fixedCornerProbes, normCorner, add_assoc] using hthree
  next =>
    change projectedQuartic ((a + (1, 0)) + (1, 1)) +
        projectedQuartic ((b + (1, 0)) + (1, 1)) =
        projectedQuartic ((c + (1, 0)) + (1, 1)) +
        projectedQuartic ((d + (1, 0)) + (1, 1))
    simp only [add_assoc]
    change projectedQuartic (a + (2, 1)) + projectedQuartic (b + (2, 1)) =
      projectedQuartic (c + (2, 1)) + projectedQuartic (d + (2, 1))
    simp only [projectedQuartic_four_steps]
    linarith

theorem projectedQuartic_squareDifference (z : IntegerLattice) :
    squareDifference projectedQuartic z =
      24 * ((z.1 : Real) + 2 * (z.2 : Real) + 1) *
        ((z.1 : Real) + 2 * (z.2 : Real) + 2) := by
  simp [squareDifference, projectedQuartic]
  ring

theorem projectedQuartic_not_restricted_square :
    Not (RestrictedSquareContinuation projectedQuartic) := by
  intro h
  have hforward := (restrictedSquareContinuation_iff projectedQuartic).mp h
  have hzero : squareDifference projectedQuartic (-2, 0) = 0 := by
    norm_num [projectedQuartic_squareDifference]
  have hone : squareDifference projectedQuartic ((-2, 0) + (1, 0)) = 0 := by
    norm_num [projectedQuartic_squareDifference]
  have hnext := hforward (-2, 0) hzero hone
  norm_num [projectedQuartic_squareDifference] at hnext

/-- The restricted and universal four-corner laws are incomparable off native. -/
theorem restricted_fourCorner_incomparable :
    And
      (Exists fun f : IntegerLattice -> Real =>
        And (RestrictedSquareContinuation f)
          (Not (PairCongruentUnder (fixedCornerProbes f) (fun z => z + (1, 0)))))
      (Exists fun f : IntegerLattice -> Real =>
        And (PairCongruentUnder (fixedCornerProbes f) (fun z => z + (1, 0)))
          (Not (RestrictedSquareContinuation f))) :=
  And.intro
    (Exists.intro separableQuartic
      (And.intro separableQuartic_restricted_square separableQuartic_not_fourCorner))
    (Exists.intro projectedQuartic
      (And.intro projectedQuartic_fourCorner_continuation projectedQuartic_not_restricted_square))

theorem restricted_does_not_imply_horizontal :
    Exists fun f : IntegerLattice -> Real =>
      And (RestrictedSquareContinuation f)
        (Not (PairCongruentUnder (horizontalProbes f) (fun z => z + (1, 0)))) :=
  Exists.intro separableQuartic
    (And.intro separableQuartic_restricted_square separableQuartic_not_horizontal)

end OffNativeComparison

end IDT.QMClosure.NativeLocalSquareReadout
