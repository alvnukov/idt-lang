import Proofs.QMClosure.NativeSingleContinuationReadout

/-!
# Two horizontal probes for the native readout contract

The two prescribed translates of the same readout obey one universal pair-sum
continuation law. This law implies the published four-corner continuation law.
Normalization and the two native generator transfers then select the squared
norm. The concrete norm inhabits the supplied contract.

One scalar fixed-translate probe cannot satisfy this continuation law under
the same native assumptions. This minimality statement concerns only scalar
fixed translates. Off the native contract, the two-probe law is strictly
stronger than the four-corner law, as an explicit cubic control demonstrates.

All grammar, real-valued readout and universal transfer/continuation contracts
remain supplied. This artifact makes no physical-origin or full-QM claim.
-/

noncomputable section

namespace IDT.QMClosure.NativeTwoProbeContinuationReadout

open FiniteMixtureContinuationRank
open FiniteTranslationSmallRankSupport
open IDT.FixedCornerHalfMixtureReadout
open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout

attribute [local instance] presentationCommRing presentationCharZero

/-- Exactly two horizontal translates of one supplied scalar readout. -/
def horizontalProbes (f : IntegerLattice -> Real) (z : IntegerLattice) : Fin 2 -> Real :=
  ![f z, f (z + (1, 0))]

/-- One universal pair-sum law for the two prescribed readout probes. -/
def TwoProbeContinuationLaw (W : Presentation -> Real) : Prop :=
  PairCongruentUnder (horizontalProbes (integerReadout W)) (fun z => z + (1, 0))

/-- Two horizontal laws, at heights zero and one, propagate the four corners. -/
theorem fixedCornerPairLaw_of_horizontalPairLaw (f : IntegerLattice -> Real)
    (h : PairCongruentUnder (horizontalProbes f) (fun z => z + (1, 0))) :
    PairCongruentUnder (fixedCornerProbes f) (fun z => z + (1, 0)) := by
  intro a b c d hpair
  have hbase : horizontalProbes f a + horizontalProbes f b =
      horizontalProbes f c + horizontalProbes f d := by
    funext j
    fin_cases j
    next =>
      simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl] using congrFun hpair 0
    next =>
      simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl] using congrFun hpair 1
  have hupper : horizontalProbes f (a + (0, 1)) +
      horizontalProbes f (b + (0, 1)) =
      horizontalProbes f (c + (0, 1)) + horizontalProbes f (d + (0, 1)) := by
    funext j
    fin_cases j
    next =>
      simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl] using congrFun hpair 2
    next =>
      simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl, add_assoc] using
        congrFun hpair 3
  have hbaseNext := h a b c d hbase
  have hupperNext := h _ _ _ _ hupper
  funext j
  fin_cases j
  next =>
    simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl] using congrFun hbaseNext 0
  next =>
    simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl] using congrFun hbaseNext 1
  next =>
    simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl,
      add_assoc, add_left_comm, add_comm] using congrFun hupperNext 0
  next =>
    simpa [horizontalProbes, fixedCornerProbes, normCorner, Matrix.cons_val_two, Matrix.cons_val_three, show ((0, 0) : IntegerLattice) = 0 from rfl,
      add_assoc, add_left_comm, add_comm] using congrFun hupperNext 1

theorem singleContinuationLaw_of_twoProbe (W : Presentation -> Real)
    (htwo : TwoProbeContinuationLaw W) : SingleContinuationLaw W :=
  fixedCornerPairLaw_of_horizontalPairLaw (integerReadout W) htwo

/-- The two-probe premise derives the existing full native/local contract. -/
theorem native_contract_of_twoProbe
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (htwo : TwoProbeContinuationLaw W) : And (NativeTransfer W) (FixedCornerPairLaws W) :=
  native_contract_of_single_continuation W hnorm ha hb
    (singleContinuationLaw_of_twoProbe W htwo)

theorem readout_eq_complex_norm_of_twoProbe
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (htwo : TwoProbeContinuationLaw W) (p : Presentation) :
    W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_single_continuation W hnorm ha hb
    (singleContinuationLaw_of_twoProbe W htwo) p

theorem readout_normal_form_of_twoProbe
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (htwo : TwoProbeContinuationLaw W) (k : Nat) (z : IntegerLattice) :
    W (NormalForm.value k z) =
      ((z.1 : Real) ^ 2 + (z.2 : Real) ^ 2) / (4 : Real) ^ k :=
  readout_normal_form_of_single_continuation W hnorm ha hb
    (singleContinuationLaw_of_twoProbe W htwo) k z

theorem global_readout_laws_of_twoProbe
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p)
    (htwo : TwoProbeContinuationLaw W) :
    And (forall p q, W (p * q) = W p * W q)
      (And (forall p, W (reflection p) = W p)
        (And (forall p, 0 <= W p)
          (And (forall p, Iff (W p = 0) (p = 0))
            (forall p : Prod Presentation Presentation,
              W (mixer p).1 + W (mixer p).2 = W p.1 + W p.2)))) :=
  global_readout_laws_of_single_continuation W hnorm ha hb
    (singleContinuationLaw_of_twoProbe W htwo)

section Witness

theorem normReadout_horizontal_recurrence (z : IntegerLattice) :
    normReadout ((z + (1, 0)) + (1, 0)) =
      2 * normReadout (z + (1, 0)) - normReadout z + 2 := by
  simp [normReadout]
  ring

theorem normReadout_horizontal_pairCongruent :
    PairCongruentUnder (horizontalProbes normReadout) (fun z => z + (1, 0)) := by
  intro a b c d hpair
  have hzero := congrFun hpair 0
  have hone := congrFun hpair 1
  simp only [Pi.add_apply, horizontalProbes, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hzero hone
  funext j
  fin_cases j
  next =>
    simpa [horizontalProbes] using hone
  next =>
    change normReadout ((a + (1, 0)) + (1, 0)) +
        normReadout ((b + (1, 0)) + (1, 0)) =
        normReadout ((c + (1, 0)) + (1, 0)) +
        normReadout ((d + (1, 0)) + (1, 0))
    simp only [normReadout_horizontal_recurrence]
    linarith

theorem modelReadout_twoProbe_continuation : TwoProbeContinuationLaw modelReadout := by
  unfold TwoProbeContinuationLaw
  rw [modelReadout_integer]
  exact normReadout_horizontal_pairCongruent

theorem modelReadout_twoProbe_contract :
    And (modelReadout a + modelReadout b = 1)
      (And (forall p, modelReadout (a * p) = modelReadout a * modelReadout p)
        (And (forall p, modelReadout (b * p) = modelReadout b * modelReadout p)
          (TwoProbeContinuationLaw modelReadout))) := by
  have hmodel := modelReadout_reduced_contract
  exact And.intro hmodel.1
    (And.intro hmodel.2.1 (And.intro hmodel.2.2.1 modelReadout_twoProbe_continuation))

end Witness

section ScalarTranslateMinimality

/-- Scalar probes in this statement are fixed lattice translates of the readout. -/
def ScalarTranslateContinuationLaw (f : IntegerLattice -> Real)
    (offset : IntegerLattice) : Prop :=
  PairCongruentUnder (fun z => f (z + offset)) (fun z => z + (1, 0))

/-- The native assumptions fix the four values used by the scalar obstruction. -/
theorem integerReadout_axis_values (W : Presentation -> Real) (L : NativeTransfer W) :
    And (integerReadout W (0, 0) = 0)
      (And (integerReadout W (1, 0) = 1)
        (And (integerReadout W (-1, 0) = 1) (integerReadout W (2, 0) = 4))) := by
  have hzero : integerReadout W (0, 0) = 0 := by
    simpa [integerReadout, Arithmetic.gaussian] using readout_zero L
  have hone : integerReadout W (1, 0) = 1 := by
    simpa [integerReadout, Arithmetic.gaussian] using L.unit
  have hrot (z : IntegerLattice) : integerReadout W (turn z) = integerReadout W z := by
    change W (Arithmetic.gaussian phase (turn z)) = W (Arithmetic.gaussian phase z)
    rw [gaussian_turn, readout_phase_mul L]
  have hneg : integerReadout W (-1, 0) = 1 := by
    calc
      integerReadout W (-1, 0) = integerReadout W (turn (turn (1, 0))) := by rfl
      _ = integerReadout W (1, 0) := by rw [hrot, hrot]
      _ = 1 := hone
  have htwo : integerReadout W (2, 0) = 4 := by
    simpa [integerReadout, Arithmetic.gaussian, L.unit] using readout_double_mul L 1
  exact And.intro hzero (And.intro hone (And.intro hneg htwo))

/-- No single scalar fixed translate can carry the stated native pair law. -/
theorem no_scalar_translate_continuation_of_native
    (W : Presentation -> Real) (L : NativeTransfer W) (offset : IntegerLattice) :
    Not (ScalarTranslateContinuationLaw (integerReadout W) offset) := by
  intro h
  have haxis := integerReadout_axis_values W L
  have hzero := haxis.1
  have hone := haxis.2.1
  have hneg := haxis.2.2.1
  have htwo := haxis.2.2.2
  have hseed : integerReadout W (((1, 0) - offset) + offset) +
      integerReadout W (((1, 0) - offset) + offset) =
      integerReadout W (((-1, 0) - offset) + offset) +
      integerReadout W (((-1, 0) - offset) + offset) := by
    simp only [sub_add_cancel, hone, hneg]
  have hnext := h ((1, 0) - offset) ((1, 0) - offset)
    ((-1, 0) - offset) ((-1, 0) - offset) hseed
  have hcancel (z : IntegerLattice) :
      ((z - offset) + (1, 0)) + offset = z + (1, 0) := by abel
  change integerReadout W ((((1, 0) - offset) + (1, 0)) + offset) +
      integerReadout W ((((1, 0) - offset) + (1, 0)) + offset) =
      integerReadout W ((((-1, 0) - offset) + (1, 0)) + offset) +
      integerReadout W ((((-1, 0) - offset) + (1, 0)) + offset) at hnext
  simp only [hcancel] at hnext
  change integerReadout W (2, 0) + integerReadout W (2, 0) =
    integerReadout W (0, 0) + integerReadout W (0, 0) at hnext
  rw [htwo, hzero] at hnext
  norm_num at hnext

theorem no_scalar_translate_continuation
    (W : Presentation -> Real) (hnorm : W a + W b = 1)
    (ha : forall p, W (a * p) = W a * W p)
    (hb : forall p, W (b * p) = W b * W p) (offset : IntegerLattice) :
    Not (ScalarTranslateContinuationLaw (integerReadout W) offset) :=
  no_scalar_translate_continuation_of_native W
    (nativeTransfer_of_normalized_generator_transfer W hnorm ha hb) offset

end ScalarTranslateMinimality

section OffNativeControl

/-- A polynomial control used solely to compare the two continuation predicates. -/
def cubicReadout (z : IntegerLattice) : Real :=
  (z.1 : Real) ^ 3 + (z.1 : Real) * (z.2 : Real)

theorem cubicReadout_second_step (z : IntegerLattice) :
    cubicReadout (z + (2, 0)) =
      2 * cubicReadout (z + (1, 0)) + 6 * cubicReadout (z + (0, 1)) -
        7 * cubicReadout z + 6 := by
  simp [cubicReadout]
  ring

theorem cubicReadout_second_step_up (z : IntegerLattice) :
    cubicReadout (z + (2, 1)) =
      2 * cubicReadout (z + (1, 0)) + 7 * cubicReadout (z + (0, 1)) -
        8 * cubicReadout z + 8 := by
  simp [cubicReadout]
  ring

theorem cubicReadout_fourCorner_continuation :
    PairCongruentUnder (fixedCornerProbes cubicReadout) (fun z => z + (1, 0)) := by
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
    change cubicReadout ((a + (1, 0)) + (1, 0)) +
        cubicReadout ((b + (1, 0)) + (1, 0)) =
        cubicReadout ((c + (1, 0)) + (1, 0)) +
        cubicReadout ((d + (1, 0)) + (1, 0))
    simp only [add_assoc]
    change cubicReadout (a + (2, 0)) + cubicReadout (b + (2, 0)) =
      cubicReadout (c + (2, 0)) + cubicReadout (d + (2, 0))
    simp only [cubicReadout_second_step]
    linarith
  next =>
    simpa [fixedCornerProbes, normCorner, add_assoc] using hthree
  next =>
    change cubicReadout ((a + (1, 0)) + (1, 1)) +
        cubicReadout ((b + (1, 0)) + (1, 1)) =
        cubicReadout ((c + (1, 0)) + (1, 1)) +
        cubicReadout ((d + (1, 0)) + (1, 1))
    simp only [add_assoc]
    change cubicReadout (a + (2, 1)) + cubicReadout (b + (2, 1)) =
      cubicReadout (c + (2, 1)) + cubicReadout (d + (2, 1))
    simp only [cubicReadout_second_step_up]
    linarith

theorem cubicReadout_not_horizontal_continuation :
    Not (PairCongruentUnder (horizontalProbes cubicReadout) (fun z => z + (1, 0))) := by
  intro h
  have hseed : horizontalProbes cubicReadout (0, 5) +
      horizontalProbes cubicReadout (0, 5) =
      horizontalProbes cubicReadout (1, -1) + horizontalProbes cubicReadout (1, -1) := by
    funext j
    fin_cases j <;> norm_num [horizontalProbes, cubicReadout]
  have hnext := congrFun (h (0, 5) (0, 5) (1, -1) (1, -1) hseed) 1
  norm_num [horizontalProbes, cubicReadout] at hnext

theorem fourCorner_does_not_imply_horizontal :
    Exists fun f : IntegerLattice -> Real =>
      And (PairCongruentUnder (fixedCornerProbes f) (fun z => z + (1, 0)))
        (Not (PairCongruentUnder (horizontalProbes f) (fun z => z + (1, 0)))) :=
  Exists.intro cubicReadout
    (And.intro cubicReadout_fourCorner_continuation cubicReadout_not_horizontal_continuation)

end OffNativeControl

end IDT.QMClosure.NativeTwoProbeContinuationReadout
