import Proofs.QMClosure.NativeInitialHistoryPresentation
import Proofs.QMClosure.FixedCornerHalfMixtureReadout

/-!
# Native two-generator transfer and fixed-corner half mixtures

The input is an arbitrary real readout on the initial destructive two-letter
semiring presentation. Its native transfer laws concern multiplication by the
two fixed generators at every input. Unit calibration and these two laws alone
give the normalized raw echo. Alternatively, the normalized generator baseline
and the two universal native transfer laws derive both unit calibration and
equal generator readings, using the grammar's equal fourth histories.
Fixed-corner pair congruence is introduced only after the native echo, on the
integer Gaussian restriction of the same readout.

The pair law then selects the squared Gaussian norm on the whole presented
ring. Positivity, faithfulness, multiplication, reflection invariance and
all-input mixer conservation follow as conclusions. The complex evaluation
used in the conclusion is the previously proved faithful algebraic model.

Equal-half ensemble means are external real arithmetic on two readout values.
Coherent composition remains the presented expression `a * x + b * y`.
Physical origins of the grammar, destructive relator, baseline/transfer laws
and fixed-corner pair sufficiency remain open. These are raw readout results.
-/

noncomputable section

namespace IDT.QMClosure.NativeGeneratorMixtureReadout

open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open FiniteMixtureContinuationRank
open IDT.MultiplicativeMixtureReadout
open IDT.FixedCornerHalfMixtureReadout

attribute [local instance] presentationCommRing presentationCharZero

/-- Two fixed native contexts, each quantified over every input. -/
structure NativeTransfer (W : Presentation → ℝ) : Prop where
  unit : W 1 = 1
  left_a : ∀ p, W (a * p) = W p / 2
  left_b : ∀ p, W (b * p) = W p / 2

/-- Symmetric normalized baseline readings and their two universal transfer
laws derive the unit calibration as well as the fixed-half transfers. -/
theorem nativeTransfer_of_symmetric_normalized_baseline
    (W : Presentation → ℝ) (hsym : W a = W b)
    (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p) : NativeTransfer W := by
  have hva : W a = 1 / 2 := by linarith
  have hvb : W b = 1 / 2 := by linarith
  have hu := ha 1
  simp only [mul_one] at hu
  rw [hva] at hu
  refine ⟨by linarith, ?_, ?_⟩
  · intro p
    rw [ha, hva]
    ring
  · intro p
    rw [hb, hvb]
    ring

/-- Equality of fourth histories follows from the destructive grammar alone. -/
theorem generator_fourth_history : a ^ 4 = b ^ 4 := by
  linear_combination (a * a - b * b) * destructive

/-- A normalized generator baseline and the two universal native transfer laws
already force unit calibration and generator symmetry. Symmetry follows from
the grammar's equal fourth histories and the real-valued transfer equations. -/
theorem nativeTransfer_of_normalized_generator_transfer
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p) : NativeTransfer W := by
  have hunit : W 1 = 1 := by
    have hA := ha 1
    have hB := hb 1
    simp only [mul_one] at hA hB
    have hsum : W a + W b = (W a + W b) * W 1 := by
      calc
        _ = W a * W 1 + W b * W 1 :=
          congrArg₂ (fun x y : ℝ => x + y) hA hB
        _ = (W a + W b) * W 1 := by ring
    rw [hnorm, one_mul] at hsum
    exact hsum.symm
  have hpa : W (a ^ 4) = W a ^ 4 := by
    have heq : a ^ 4 = a * (a * (a * (a * 1))) := by ring
    rw [heq, ha, ha, ha, ha, hunit]
    ring
  have hpb : W (b ^ 4) = W b ^ 4 := by
    have heq : b ^ 4 = b * (b * (b * (b * 1))) := by ring
    rw [heq, hb, hb, hb, hb, hunit]
    ring
  have hfour : W a ^ 4 = W b ^ 4 := by
    rw [← hpa, ← hpb, generator_fourth_history]
  have hfactor : (W a - W b) * (W a + W b) * (W a ^ 2 + W b ^ 2) = 0 := by
    linear_combination hfour
  have hsumSquare : (W a + W b) ^ 2 = 1 := by rw [hnorm]; norm_num
  have hpositive : 0 < W a ^ 2 + W b ^ 2 := by
    nlinarith [sq_nonneg (W a - W b)]
  have hfactor' : (W a - W b) * (W a ^ 2 + W b ^ 2) = 0 := by
    simpa only [hnorm, mul_one] using hfactor
  have hsym : W a = W b :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor').resolve_right (ne_of_gt hpositive))
  exact nativeTransfer_of_symmetric_normalized_baseline W hsym hnorm ha hb

section Native

variable {W : Presentation → ℝ} (L : NativeTransfer W)

include L in
theorem readout_zero : W 0 = 0 := by
  have h := L.left_a 0
  simp only [mul_zero] at h
  linarith

include L in
theorem readout_a : W a = 1 / 2 := by
  simpa only [mul_one, L.unit] using L.left_a 1

include L in
theorem readout_b : W b = 1 / 2 := by
  simpa only [mul_one, L.unit] using L.left_b 1

include L in
theorem readout_half_mul (p : Presentation) : W (half * p) = W p / 4 := by
  change W ((a * b) * p) = _
  rw [mul_assoc, L.left_a, L.left_b]
  ring

include L in
theorem readout_double_mul (p : Presentation) : W ((2 : Presentation) * p) = 4 * W p := by
  have hc : half * ((2 : Presentation) * p) = p := by
    calc
      _ = ((2 : Presentation) * half) * p := by ring
      _ = p := by rw [half_doubles, one_mul]
  have h := readout_half_mul L ((2 : Presentation) * p)
  rw [hc] at h
  linarith

theorem double_a : (2 : Presentation) * a = 1 + phase := by
  rw [coefficient_a]
  calc
    _ = ((2 : Presentation) * half) * (1 + phase) := by ring
    _ = 1 + phase := by rw [half_doubles, one_mul]

include L in
theorem readout_phase_mul (p : Presentation) : W (phase * p) = W p := by
  have hp : phase * p = (2 : Presentation) * (a * (a * p)) := by
    change (a * a + a * a) * p = _
    ring
  rw [hp, readout_double_mul L, L.left_a, L.left_a]
  ring

include L in
theorem readout_diagonal_mul (p : Presentation) :
    W ((1 + phase) * p) = 2 * W p := by
  have hp : (1 + phase) * p = a * ((2 : Presentation) * p) := by
    rw [← double_a]
    ring
  rw [hp, L.left_a, readout_double_mul L]
  ring

include L in
theorem readout_half_pow_mul (k : ℕ) (p : Presentation) :
    W (half ^ k * p) = W p / (4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hp : half ^ k * half * p = half * (half ^ k * p) := by ring
      rw [hp, readout_half_mul L, ih, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The two-channel expression belongs to the original presented grammar. -/
def mixer (p : Presentation × Presentation) : Presentation × Presentation :=
  (a * p.1 + b * p.2, b * p.1 + a * p.2)

theorem mixer_twice (p : Presentation × Presentation) : mixer (mixer p) = (p.2, p.1) := by
  have hcross : a * b + b * a = 1 := laws.cross
  apply Prod.ext
  · change a * (a * p.1 + b * p.2) + b * (b * p.1 + a * p.2) = p.2
    calc
      _ = (a * a + b * b) * p.1 + (a * b + b * a) * p.2 := by ring
      _ = p.2 := by rw [destructive, hcross]; simp
  · change b * (a * p.1 + b * p.2) + a * (b * p.1 + a * p.2) = p.1
    calc
      _ = (a * b + b * a) * p.1 + (a * a + b * b) * p.2 := by ring
      _ = p.1 := by rw [destructive, hcross]; simp

theorem mixer_unit : mixer (1, 0) = (a, b) := by simp [mixer]

theorem mixer_generators : mixer (a, b) = (0, 1) := by
  simpa only [mixer_unit] using mixer_twice (1, 0)

include L in
/-- Native transfer alone gives a nondegenerate normalized raw echo. Its
statement has no fixed-corner pair premise or event/frequency interpretation. -/
theorem normalized_raw_echo :
    mixer (1, 0) = (a, b) ∧ mixer (a, b) = (0, 1) ∧
      W a = 1 / 2 ∧ W b = 1 / 2 ∧ W a + W b = 1 ∧
      0 < W a ∧ 0 < W b ∧ W 0 = 0 ∧ W 1 = 1 := by
  refine ⟨mixer_unit, mixer_generators, readout_a L, readout_b L, ?_, ?_, ?_,
    readout_zero L, L.unit⟩ <;> norm_num [readout_a L, readout_b L]

end Native

/-- The integer restriction is prescribed by the same supplied readout. -/
def integerReadout (W : Presentation → ℝ) (z : IntegerLattice) : ℝ :=
  W (Arithmetic.gaussian phase z)

/-- Only equal sums of two prescribed corner probe vectors are compared. -/
def FixedCornerPairLaws (W : Presentation → ℝ) : Prop :=
  ∀ j, PairCongruentUnder (fixedCornerProbes (integerReadout W))
    (fun z => z + localStep j)

theorem gaussian_turn (z : IntegerLattice) :
    Arithmetic.gaussian phase (FiniteTranslationSmallRankSupport.turn z) =
      phase * Arithmetic.gaussian phase z := by
  dsimp [Arithmetic.gaussian, FiniteTranslationSmallRankSupport.turn]
  push_cast
  linear_combination -(z.2 : Presentation) * phase_square

theorem gaussian_diagonal (z : IntegerLattice) :
    Arithmetic.gaussian phase (gaussianMul (1, 1) z) =
      (1 + phase) * Arithmetic.gaussian phase z := by
  dsimp [Arithmetic.gaussian, gaussianMul]
  push_cast
  linear_combination -(z.2 : Presentation) * phase_square

section Selection

variable {W : Presentation → ℝ} (L : NativeTransfer W) (M : FixedCornerPairLaws W)

include L M in
theorem integer_readout_eq_norm (z : IntegerLattice) :
    integerReadout W z = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  apply fixed_corner_readout_eq_norm_of_generator_laws (integerReadout W) M
  · simpa [integerReadout, Arithmetic.gaussian] using readout_zero L
  · simpa [integerReadout, Arithmetic.gaussian] using L.unit
  · intro t
    unfold integerReadout
    rw [gaussian_turn, readout_phase_mul L]
  · intro t
    unfold integerReadout
    rw [gaussian_diagonal, readout_diagonal_mul L]

include L M in
theorem readout_normal_form (k : ℕ) (z : IntegerLattice) :
    W (NormalForm.value k z) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k := by
  change W (half ^ k * Arithmetic.gaussian phase z) = _
  rw [readout_half_pow_mul L]
  exact congrArg (fun t : ℝ => t / (4 : ℝ) ^ k) (integer_readout_eq_norm L M z)

theorem complex_norm_normal_form (k : ℕ) (z : IntegerLattice) :
    Complex.normSq (complexEval (NormalForm.value k z)) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k := by
  rw [NormalForm.complexEval_value]
  dsimp [Arithmetic.value]
  rw [map_mul, map_pow]
  have hh : Complex.normSq (1 / 2 : ℂ) = (1 / 4 : ℝ) := by norm_num
  have hg : Complex.normSq (Arithmetic.gaussian Complex.I z) =
      (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    simp [Arithmetic.gaussian, Complex.normSq_apply]
    ring
  rw [hh, hg, div_pow]
  simp only [one_pow]
  ring

include L M in
/-- The supplied readout is proved to equal the squared norm of the faithful
algebraic evaluation. The norm is the conclusion of the selection argument. -/
theorem readout_eq_complex_norm (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  obtain ⟨k, z, rfl⟩ := NormalForm.exists_value p
  exact (readout_normal_form L M k z).trans (complex_norm_normal_form k z).symm

include L M in
theorem readout_multiplicative (p q : Presentation) : W (p * q) = W p * W q := by
  rw [readout_eq_complex_norm L M, map_mul, Complex.normSq_mul,
    readout_eq_complex_norm L M, readout_eq_complex_norm L M]

include L M in
theorem readout_reflection (p : Presentation) : W (reflection p) = W p := by
  obtain ⟨k, z, rfl⟩ := NormalForm.exists_value p
  rw [NormalForm.reflection_value, readout_normal_form L M, readout_normal_form L M]
  simp [Arithmetic.conjugatePair]

include L M in
theorem readout_nonnegative (p : Presentation) : 0 ≤ W p := by
  rw [readout_eq_complex_norm L M]
  exact Complex.normSq_nonneg _

include L M in
theorem readout_zero_iff (p : Presentation) : W p = 0 ↔ p = 0 := by
  rw [readout_eq_complex_norm L M, Complex.normSq_eq_zero]
  constructor
  · intro h
    apply NormalForm.complexEval_injective
    simpa using h
  · rintro rfl
    exact map_zero complexEval

include L M in
theorem readout_nat (n : ℕ) : W (n : Presentation) = (n : ℝ) ^ 2 := by
  rw [readout_eq_complex_norm L M, map_natCast, Complex.normSq_natCast]
  ring

include L M in
theorem readout_nat_order_iff (m n : ℕ) :
    W (m : Presentation) ≤ W (n : Presentation) ↔ m ≤ n := by
  rw [readout_nat L M, readout_nat L M]
  constructor
  · intro h
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmn : (m : ℝ) ≤ (n : ℝ) := by
      by_contra hbad
      have hlt : (n : ℝ) < (m : ℝ) := lt_of_not_ge hbad
      have hp : 0 < ((m : ℝ) - (n : ℝ)) * ((m : ℝ) + (n : ℝ)) :=
        mul_pos (sub_pos.mpr hlt) (by linarith)
      nlinarith
    exact_mod_cast hmn
  · intro h
    have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hp : 0 ≤ ((n : ℝ) - (m : ℝ)) * ((n : ℝ) + (m : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hmn) (by positivity)
    nlinarith

include L M in
theorem readout_dyadic_count (k n : ℕ) :
    W (half ^ k * (n : Presentation)) = (n : ℝ) ^ 2 / (4 : ℝ) ^ k := by
  rw [readout_half_pow_mul L, readout_nat L M]

include L M in
theorem mixer_conservation (p : Presentation × Presentation) :
    W (mixer p).1 + W (mixer p).2 = W p.1 + W p.2 := by
  simp only [mixer, readout_eq_complex_norm L M, map_add, map_mul,
    complexEval_a, complexEval_b]
  norm_num [Complex.normSq_apply, ComplexModel.a, ComplexModel.b,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

include L M in
theorem readout_parallelogram (p q : Presentation) :
    W (p + q) + W (p - q) = 2 * W p + 2 * W q := by
  simp only [readout_eq_complex_norm L M, map_add, map_sub]
  simp [Complex.normSq_apply]
  ring

include L M in
/-- The raw third-order inclusion-exclusion expression vanishes universally. -/
theorem raw_I3_zero (p q r : Presentation) :
    W (p + q + r) - W (p + q) - W (p + r) - W (q + r) +
      W p + W q + W r - W 0 = 0 := by
  simp only [readout_eq_complex_norm L M, map_add, map_zero]
  simp [Complex.normSq_apply]
  ring

end Selection

/-- The full readout selector needs only normalized generator readings, two
universal native transfer laws and the prescribed fixed-corner pair law. -/
theorem readout_eq_complex_norm_of_normalized_generator_transfer
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    (M : FixedCornerPairLaws W) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  exact readout_eq_complex_norm
    (nativeTransfer_of_normalized_generator_transfer W hnorm ha hb) M p

section Witness

/-- A concrete inhabitant is introduced after the arbitrary-readout theorem. -/
def modelReadout (p : Presentation) : ℝ := Complex.normSq (complexEval p)

theorem modelReadout_native : NativeTransfer modelReadout := by
  have ha : Complex.normSq ComplexModel.a = (1 / 2 : ℝ) := by
    norm_num [ComplexModel.a, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hb : Complex.normSq ComplexModel.b = (1 / 2 : ℝ) := by
    norm_num [ComplexModel.b, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  refine ⟨by simp [modelReadout], ?_, ?_⟩
  · intro p
    simp only [modelReadout, map_mul, complexEval_a, Complex.normSq_mul, ha]
    ring
  · intro p
    simp only [modelReadout, map_mul, complexEval_b, Complex.normSq_mul, hb]
    ring

theorem modelReadout_integer : integerReadout modelReadout = normReadout := by
  funext z
  have h := complex_norm_normal_form 0 z
  simpa [integerReadout, modelReadout, NormalForm.value, Arithmetic.value,
    normReadout] using h

theorem modelReadout_pairs : FixedCornerPairLaws modelReadout := by
  unfold FixedCornerPairLaws
  rw [modelReadout_integer]
  intro j
  exact normReadout_pairCongruent_translation (localStep j)

/-- The complete native-transfer and fixed-corner pair contract is inhabited. -/
theorem exists_native_pair_contract :
    ∃ W : Presentation → ℝ, NativeTransfer W ∧ FixedCornerPairLaws W :=
  ⟨modelReadout, modelReadout_native, modelReadout_pairs⟩

end Witness

end IDT.QMClosure.NativeGeneratorMixtureReadout
