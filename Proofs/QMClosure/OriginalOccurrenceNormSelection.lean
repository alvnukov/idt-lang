import Proofs.QMClosure.OriginalOccurrenceKernel
import Proofs.QMClosure.QuadraticPolynomialDyadicSelection

/-!
# Native readout selection from finite original-occurrence kernels

The natural-grid polynomial argument uses the public adapter in
QuadraticPolynomialDyadicSelection.lean.

One finite original-occurrence kernel, compatible with the same readout on
EVERY natural a/b bag, selects norm square from NativeTransfer. K is arbitrary.
The positivity of the pairKernel witness is consistent with this theorem.
No uniqueness claim about the individual κ coefficients is made.
-/

noncomputable section

namespace IDT.QMClosure.OriginalOccurrenceNormSelection

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open SingleCalibrationScalarFaithfulness
open MvPolynomial

attribute [local instance] presentationCommRing presentationCharZero

theorem bagEval_double (n m : ℕ) :
    bagEval (2 * n) (2 * m) = (2 : Presentation) * bagEval n m := by
  unfold bagEval
  push_cast
  ring

/-- Native doubling and native a, b, a+b calibrations select the polynomial. -/
theorem kernelPolynomial_eq_half_sum_squares
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) :
    kernelPolynomial K κ = C (1 / 2) * (X 0 ^ 2 + X 1 ^ 2) := by
  apply IDT.TranslationRankGap.polynomial_eq_half_sum_squares_of_nat_dyadic_calibrations
  · intro n m
    rw [compatible_polynomial_eval H, compatible_polynomial_eval H,
      bagEval_double, readout_double_mul L]
    push_cast
    ring
  · have h := compatible_polynomial_eval H 1 0
    simpa [bagEval, readout_a L] using h
  · have h := compatible_polynomial_eval H 0 1
    simpa [bagEval, readout_b L] using h
  · have h := compatible_polynomial_eval H 1 1
    simpa [bagEval, transparent, L.unit] using h

/-- The original a/b bag family has the selected quadratic response. -/
theorem readout_bag_eq_half_sum_squares
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) (n m : ℕ) :
    W (bagEval n m) = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  apply Complex.ofReal_injective
  have h := compatible_polynomial_eval H n m
  rw [kernelPolynomial_eq_half_sum_squares L H] at h
  simpa [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- The lower bound K ≥ 2 is a conclusion. A global finite cutoff K is supplied,
but K = 2 is not assumed. Orders zero and one are incompatible with the native
zero, singleton, and doubled singleton values. -/
theorem compatible_order_at_least_two
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) : 2 ≤ K := by
  have hrep (n m : ℕ) : W (bagEval n m) = binomialSum K κ n m :=
    (H n m).trans (originalSubsetCount_eq_binomialSum K κ n m)
  have h00 : binomialSum K κ 0 0 = 0 := by
    rw [← hrep]
    simpa [bagEval] using readout_zero L
  have h10 : binomialSum K κ 1 0 = 1 / 2 := by
    rw [← hrep]
    simpa [bagEval] using readout_a L
  have h20 : binomialSum K κ 2 0 = 2 := by
    rw [← hrep]
    simp only [bagEval, Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero]
    rw [readout_double_mul L, readout_a L]
    norm_num
  by_contra h
  have hK : K ≤ 1 := by omega
  interval_cases K <;>
    norm_num [binomialSum, Finset.sum_range_succ] at h00 h10 h20 <;> linarith

/-- Derived from the native coefficients and half-doubling identity. -/
theorem a_sub_b_eq_phase : a - b = phase := by
  rw [coefficient_a, coefficient_b]
  calc
    _ = ((2 : Presentation) * half) * phase := by ring
    _ = phase := by rw [half_doubles, one_mul]

/-- A real-dominant Gaussian integer belongs to the original positive bag cone. -/
theorem gaussian_eq_bag_of_cone (m n : ℤ)
    (hp : 0 ≤ m + n) (hm : 0 ≤ m - n) :
    Arithmetic.gaussian phase (m, n) = bagEval (m + n).toNat (m - n).toNat := by
  have hpcast : ((m + n).toNat : Presentation) = (m : Presentation) + (n : Presentation) := by
    exact_mod_cast Int.toNat_of_nonneg hp
  have hmcast : ((m - n).toNat : Presentation) = (m : Presentation) - (n : Presentation) := by
    exact_mod_cast Int.toNat_of_nonneg hm
  dsimp [Arithmetic.gaussian, bagEval]
  rw [hpcast, hmcast]
  linear_combination -(m : Presentation) * transparent - (n : Presentation) * a_sub_b_eq_phase

private theorem readout_gaussian_cone
    {W : Presentation → ℝ} (B : ∀ n m : ℕ,
      W (bagEval n m) = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2)
    (m n : ℤ) (hp : 0 ≤ m + n) (hm : 0 ≤ m - n) :
    W (Arithmetic.gaussian phase (m, n)) = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
  rw [gaussian_eq_bag_of_cone m n hp hm, B]
  have hpcast : ((m + n).toNat : ℝ) = (m : ℝ) + (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hp
  have hmcast : ((m - n).toNat : ℝ) = (m : ℝ) - (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm
  rw [hpcast, hmcast]
  ring

/-- Quarter turns move every Gaussian integer into the positive a/b cone.
Only the already derived native phase invariance transports the readout. -/
theorem readout_gaussian_eq_norm_of_bag_formula
    {W : Presentation → ℝ} (L : NativeTransfer W)
    (B : ∀ n m : ℕ,
      W (bagEval n m) = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2)
    (m n : ℤ) :
    W (Arithmetic.gaussian phase (m, n)) = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
  have hturn (r s : ℤ) :
      W (Arithmetic.gaussian phase (-s, r)) =
        W (Arithmetic.gaussian phase (r, s)) := by
    change W (Arithmetic.gaussian phase
      (FiniteTranslationSmallRankSupport.turn (r, s))) = _
    rw [gaussian_turn, readout_phase_mul L]
  by_cases hp : 0 ≤ m + n
  · by_cases hm : 0 ≤ m - n
    · exact readout_gaussian_cone B m n hp hm
    · calc
        W (Arithmetic.gaussian phase (m, n)) =
            W (Arithmetic.gaussian phase (n, -m)) := by
          simpa using hturn n (-m)
        _ = (n : ℝ) ^ 2 + ((-m : ℤ) : ℝ) ^ 2 :=
          readout_gaussian_cone B n (-m) (by omega) (by omega)
        _ = _ := by push_cast; ring
  · by_cases hm : 0 ≤ m - n
    · calc
        W (Arithmetic.gaussian phase (m, n)) =
            W (Arithmetic.gaussian phase (-n, m)) := (hturn m n).symm
        _ = ((-n : ℤ) : ℝ) ^ 2 + (m : ℝ) ^ 2 :=
          readout_gaussian_cone B (-n) m (by omega) (by omega)
        _ = _ := by push_cast; ring
    · have htwice :
          W (Arithmetic.gaussian phase (-m, -n)) =
            W (Arithmetic.gaussian phase (m, n)) :=
          (hturn (-n) m).trans (hturn m n)
      calc
        W (Arithmetic.gaussian phase (m, n)) =
            W (Arithmetic.gaussian phase (-m, -n)) := htwice.symm
        _ = ((-m : ℤ) : ℝ) ^ 2 + ((-n : ℤ) : ℝ) ^ 2 :=
          readout_gaussian_cone B (-m) (-n) (by omega) (by omega)
        _ = _ := by push_cast; ring

/-- Selection reaches every dyadic Gaussian normal form. -/
theorem readout_normal_form_of_original_kernel
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ)
    (k : ℕ) (z : NormalForm.Coefficients) :
    W (NormalForm.value k z) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k := by
  change W (half ^ k * Arithmetic.gaussian phase z) = _
  rw [readout_half_pow_mul L]
  have hz := readout_gaussian_eq_norm_of_bag_formula L
    (readout_bag_eq_half_sum_squares L H) z.1 z.2
  exact congrArg (fun t : ℝ => t / (4 : ℝ) ^ k) hz

/-- Universal selection from the supplied original-occurrence kernel contract. -/
theorem readout_eq_complex_norm_of_original_kernel
    {W : Presentation → ℝ} (L : NativeTransfer W) {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  obtain ⟨k, z, rfl⟩ := NormalForm.exists_value p
  exact (readout_normal_form_of_original_kernel L H k z).trans
    (complex_norm_normal_form k z).symm

/-- The normalized generator-transfer premises imply the same selection. -/
theorem readout_eq_complex_norm_of_normalized_generator_transfer
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    {K : ℕ} {κ : Kernel} (H : CompatibleOriginalKernel W K κ)
    (p : Presentation) :
    W p = Complex.normSq (complexEval p) :=
  readout_eq_complex_norm_of_original_kernel
    (nativeTransfer_of_normalized_generator_transfer W hnorm ha hb) H p

/-- A concrete consistency witness for the native transfer assumptions. -/
def normReadout (p : Presentation) : ℝ := Complex.normSq (complexEval p)

theorem normReadout_nativeTransfer : NativeTransfer normReadout := by
  refine ⟨by simp [normReadout], ?_, ?_⟩
  · intro p
    simp only [normReadout, map_mul, Complex.normSq_mul, complexEval_a]
    have ha : Complex.normSq ComplexModel.a = (1 / 2 : ℝ) := by
      norm_num [ComplexModel.a, Complex.normSq_apply]
    rw [ha]
    ring
  · intro p
    simp only [normReadout, map_mul, Complex.normSq_mul, complexEval_b]
    have hb : Complex.normSq ComplexModel.b = (1 / 2 : ℝ) := by
      norm_num [ComplexModel.b, Complex.normSq_apply]
    rw [hb]
    ring

theorem normReadout_bag (n m : ℕ) :
    normReadout (bagEval n m) = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  simp [normReadout, bagEval, ComplexModel.a, ComplexModel.b, Complex.normSq_apply]
  ring

/-- K=2 is inhabited by the explicitly nonnegative kernel. -/
theorem pairKernel_compatible_normReadout : CompatibleOriginalKernel normReadout 2 pairKernel := by
  intro n m
  rw [originalSubsetCount_eq_binomialSum, binomialSum_pairKernel, normReadout_bag]

end IDT.QMClosure.OriginalOccurrenceNormSelection
