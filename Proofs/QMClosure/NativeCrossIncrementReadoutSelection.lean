import Proofs.QMClosure.CountCrossIncrementRigidity
import Proofs.QMClosure.OriginalOccurrenceNormSelection

/-!
Native transfer plus an eventually uniform mixed-increment sign selects the
norm readout. The finite original-kernel carrier is constructed after count
rigidity. Physical origins of the mixed-increment sign remain open.
-/

noncomputable section

namespace IDT.QMClosure.NativeCrossIncrementReadoutSelection

open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalOccurrenceNormSelection
open CountCrossIncrementRigidity

attribute [local instance] presentationCommRing presentationCharZero

def countGrid (W : Presentation → ℝ) : Grid := fun n m => W (bagEval n m)

def axisGrid (W : Presentation → ℝ) (n : ℕ) : ℝ := W (n : Presentation) / 2

theorem countGrid_zero {W : Presentation → ℝ} (L : NativeTransfer W) :
    countGrid W 0 0 = 0 := by simpa [countGrid, bagEval] using readout_zero L

theorem countGrid_axes {W : Presentation → ℝ} (L : NativeTransfer W) (n : ℕ) :
    countGrid W n 0 = axisGrid W n ∧ countGrid W 0 n = axisGrid W n := by
  constructor
  · simpa [countGrid, axisGrid, bagEval, mul_comm] using L.left_a (n : Presentation)
  · simpa [countGrid, axisGrid, bagEval, mul_comm] using L.left_b (n : Presentation)

theorem countGrid_diagonal {W : Presentation → ℝ} (n : ℕ) :
    countGrid W n n = W (n : Presentation) := by
  have hh : bagEval n n = (n : Presentation) := by
    unfold bagEval
    rw [← mul_add, transparent, mul_one]
  exact congrArg W hh

theorem countGrid_saturated {W : Presentation → ℝ} (L : NativeTransfer W) :
    SaturatedSquares (countGrid W) := by
  intro n
  rw [countGrid_diagonal, (countGrid_axes L n).1, (countGrid_axes L n).2,
    countGrid_zero L]
  dsimp [axisGrid]
  ring

theorem countGrid_dyadic {W : Presentation → ℝ} (L : NativeTransfer W) :
    Dyadic (countGrid W) := by
  intro n m
  exact (congrArg W (bagEval_double n m)).trans (readout_double_mul L (bagEval n m))

theorem countGrid_mixed_origin {W : Presentation → ℝ} (L : NativeTransfer W) :
    mixed (countGrid W) 0 0 = 0 := by
  norm_num [mixed, countGrid, bagEval, transparent, L.unit, readout_a L,
    readout_b L, readout_zero L]

/-- A subtraction-free identity of presented histories. -/
theorem bag_row_transfer (k : ℕ) :
    bagEval (k + 2) k = ((2 : Presentation) * a) * bagEval 1 (k + 1) := by
  unfold bagEval
  push_cast
  have hc : a * b + b * a = 1 := laws.cross
  linear_combination (((k : Presentation) + 1) - a + b) * transparent -
    ((k : Presentation) + 1) * hc - destructive

theorem countGrid_row_transfer {W : Presentation → ℝ} (L : NativeTransfer W) (k : ℕ) :
    countGrid W (k + 2) k = 2 * countGrid W 1 (k + 1) := by
  unfold countGrid
  rw [bag_row_transfer]
  have hh : ((2 : Presentation) * a) * bagEval 1 (k + 1) =
      (2 : Presentation) * (a * bagEval 1 (k + 1)) := by ring
  rw [hh, readout_double_mul L, L.left_a]
  ring

/-- Count rigidity uses native transfer only after mixed increments vanish. -/
theorem count_formula_of_mixed_zero {W : Presentation → ℝ} (L : NativeTransfer W)
    (hz : ∀ n m, mixed (countGrid W) n m = 0) (n m : ℕ) :
    countGrid W n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  have hsep (i j : ℕ) : countGrid W i j = axisGrid W i + axisGrid W j := by
    rw [separable_of_mixed_zero hz, (countGrid_axes L i).1,
      (countGrid_axes L j).2, countGrid_zero L, sub_zero]
  have h0 : axisGrid W 0 = 0 := by simp [axisGrid, readout_zero L]
  have h1 : axisGrid W 1 = 1 / 2 := by simp [axisGrid, L.unit]
  have hrec (k : ℕ) : axisGrid W (k + 2) + axisGrid W k =
      2 * axisGrid W (k + 1) + 1 := by
    have hh := countGrid_row_transfer L k
    rw [hsep, hsep, h1] at hh
    linarith
  have hquad (k : ℕ) : axisGrid W k = (k : ℝ) ^ 2 / 2 := by
    have hp : ∀ k : ℕ, axisGrid W k = (k : ℝ) ^ 2 / 2 ∧
        axisGrid W (k + 1) = ((k + 1 : ℕ) : ℝ) ^ 2 / 2 := by
      intro k
      induction k with
      | zero => norm_num [h0, h1]
      | succ k ih =>
          refine ⟨ih.2, ?_⟩
          have hh := hrec k
          rw [ih.1, ih.2] at hh
          push_cast at hh ⊢
          nlinarith
    exact (hp k).1
  rw [hsep, hquad, hquad]
  ring

/-- The order-two carrier is obtained as a conclusion. -/
theorem compatible_pair_of_mixed_zero {W : Presentation → ℝ} (L : NativeTransfer W)
    (hz : ∀ n m, mixed (countGrid W) n m = 0) : CompatibleOriginalKernel W 2 pairKernel := by
  intro n m
  rw [originalSubsetCount_eq_binomialSum, binomialSum_pairKernel]
  exact count_formula_of_mixed_zero L hz n m

theorem readout_eq_norm_of_mixed_zero {W : Presentation → ℝ} (L : NativeTransfer W)
    (hz : ∀ n m, mixed (countGrid W) n m = 0) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  obtain ⟨k, z, rfl⟩ := NormalForm.exists_value p
  have hread : W (NormalForm.value k z) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k := by
    change W (half ^ k * SingleCalibrationScalarFaithfulness.Arithmetic.gaussian phase z) = _
    rw [readout_half_pow_mul L]
    exact congrArg (fun t : ℝ => t / (4 : ℝ) ^ k)
      (readout_gaussian_eq_norm_of_bag_formula L
        (fun n m => count_formula_of_mixed_zero L hz n m) z.1 z.2)
  exact hread.trans (complex_norm_normal_form k z).symm

theorem readout_eq_norm_of_uniform_mixed_sign {W : Presentation → ℝ} (L : NativeTransfer W)
    (hs : (∀ n m, 0 ≤ mixed (countGrid W) n m) ∨
      (∀ n m, mixed (countGrid W) n m ≤ 0)) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  apply readout_eq_norm_of_mixed_zero L
  rcases hs with hs | hs
  · exact mixed_zero_of_nonnegative (countGrid_saturated L) hs
  · exact mixed_zero_of_nonpositive (countGrid_saturated L) hs

theorem readout_eq_norm_of_eventual_mixed_sign {W : Presentation → ℝ} (L : NativeTransfer W)
    (hs : EventuallyNonnegative (mixed (countGrid W)) ∨
      EventuallyNonpositive (mixed (countGrid W))) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  apply readout_eq_norm_of_mixed_zero L
  rcases hs with hs | hs
  · exact mixed_zero_of_eventual_nonnegative (countGrid_saturated L)
      (countGrid_dyadic L) (countGrid_mixed_origin L) hs
  · exact mixed_zero_of_eventual_nonpositive (countGrid_saturated L)
      (countGrid_dyadic L) (countGrid_mixed_origin L) hs

/-- Every nonnorm native readout has both mixed-increment signs arbitrarily far,
with one positive magnitude independent of the requested threshold. -/
theorem nonnorm_both_signs_arbitrarily_far {W : Presentation → ℝ} (L : NativeTransfer W)
    (hn : ¬ ∀ p, W p = Complex.normSq (complexEval p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ D : ℕ, ∃ n m r s,
      D < n + m ∧ D < r + s ∧ ε ≤ mixed (countGrid W) n m ∧
        mixed (countGrid W) r s ≤ -ε := by
  apply both_signs_arbitrarily_far (countGrid_saturated L) (countGrid_dyadic L)
    (countGrid_mixed_origin L)
  intro hz
  exact hn (readout_eq_norm_of_mixed_zero L hz)

end IDT.QMClosure.NativeCrossIncrementReadoutSelection
