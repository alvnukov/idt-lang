import Proofs.QMClosure.NativeSingleContinuationReadout
import Mathlib.Analysis.Complex.Basic

/-!
# A continuous faithful native-transfer countercontrol

The supplied family on the same initial history presentation is the restriction
of `F c z = normSq z + c * ((z^4).im)^2 / (normSq z)^3`. For nonnegative `c`
it is nonnegative and faithful, is invariant under reflection, has the ordinary
squared readings on real scalars and preserves count order. Its ambient complex
extension is globally continuous. The two fixed native contexts halve its
reading at every input, so the calibrated canonical raw echo follows.

For positive `c`, explicit finite packets violate the single continuation law.
The coherent mixer fails conservation on `(1,2)`, raw third-order inclusion-
exclusion is nonzero, and global multiplication fails. Global multiplication
is a conclusion of the selector theorem whose continuation premise fails.

Complex evaluation defines this concrete countercontrol on the grammar's
initial carrier. Ambient continuity supplies an extension property. This file
does not install a topology on the abstract initial carrier. Differentiability,
physical readout origins, event interpretation and full QM closure remain open
within the scope of this artifact.
-/

noncomputable section

namespace IDT.QMClosure.NativeRegularReadoutCountercontrol

open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open FiniteMixtureContinuationRank
open IDT.FixedCornerHalfMixtureReadout
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout
open scoped ComplexConjugate

attribute [local instance] presentationCommRing presentationCharZero

/-- Fourth-harmonic polynomial in the real coordinate algebra. -/
def quarticImag (z : ℂ) : ℝ := (z ^ 4).im

/-- Total division gives value zero at the origin. -/
def angularCorrection (z : ℂ) : ℝ :=
  quarticImag z ^ 2 / Complex.normSq z ^ 3

/-- A concrete ambient family. Nonnegativity of the parameter is used by bounds. -/
def ambientWeight (c : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq z + c * angularCorrection z

/-- A supplied countercontrol on the original initial grammar. -/
def counterWeight (c : ℝ) (p : Presentation) : ℝ :=
  ambientWeight c (complexEval p)

theorem quarticImag_formula (z : ℂ) :
    quarticImag z = 4 * z.re * z.im * (z.re ^ 2 - z.im ^ 2) := by
  simp [quarticImag, pow_succ, Complex.mul_re, Complex.mul_im]
  <;> ring

@[simp] theorem quarticImag_zero : quarticImag 0 = 0 := by simp [quarticImag]
@[simp] theorem angularCorrection_zero : angularCorrection 0 = 0 := by
  simp [angularCorrection]
@[simp] theorem ambientWeight_zero (c : ℝ) : ambientWeight c 0 = 0 := by
  simp [ambientWeight]
@[simp] theorem counterWeight_zero (c : ℝ) : counterWeight c 0 = 0 := by
  simp [counterWeight]

/-- The norm-square power identity gives the bounded fourth-harmonic defect. -/
theorem norm_fourth_decomposition (z : ℂ) :
    Complex.normSq z ^ 4 = (z ^ 4).re ^ 2 + quarticImag z ^ 2 := by
  rw [← map_pow]
  simp only [Complex.normSq_apply, quarticImag, pow_two]

theorem angularCorrection_nonnegative (z : ℂ) : 0 ≤ angularCorrection z := by
  exact div_nonneg (sq_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _)

theorem angularCorrection_le_norm (z : ℂ) :
    angularCorrection z ≤ Complex.normSq z := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  apply (div_le_iff₀ (pow_pos hn 3)).mpr
  have h := norm_fourth_decomposition z
  nlinarith [sq_nonneg ((z ^ 4).re)]

theorem ambientWeight_bounds (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    Complex.normSq z ≤ ambientWeight c z ∧
      ambientWeight c z ≤ (1 + c) * Complex.normSq z := by
  have h0 := mul_nonneg hc (angularCorrection_nonnegative z)
  have h1 := mul_le_mul_of_nonneg_left (angularCorrection_le_norm z) hc
  dsimp [ambientWeight]
  constructor <;> nlinarith

theorem ambientWeight_nonnegative (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    0 ≤ ambientWeight c z :=
  (Complex.normSq_nonneg z).trans (ambientWeight_bounds c hc z).1

theorem ambientWeight_zero_iff (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ambientWeight c z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply Complex.normSq_eq_zero.mp
    have h := (ambientWeight_bounds c hc z).1
    rw [hz] at h
    exact le_antisymm h (Complex.normSq_nonneg z)
  · rintro rfl
    exact ambientWeight_zero c

/-- The squeeze at zero is the only singular-denominator continuity step. -/
theorem angularCorrection_continuous : Continuous angularCorrection := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    change Filter.Tendsto angularCorrection (nhds (0 : ℂ))
      (nhds (angularCorrection 0))
    rw [angularCorrection_zero]
    have hn0 : Filter.Tendsto Complex.normSq (nhds (0 : ℂ))
        (nhds (Complex.normSq (0 : ℂ))) :=
      Complex.continuous_normSq.continuousAt
    exact squeeze_zero angularCorrection_nonnegative angularCorrection_le_norm
      (by simpa using hn0)
  · have hnum : Continuous (fun z : ℂ => quarticImag z ^ 2) := by
      exact (Complex.continuous_im.comp (continuous_id.pow 4)).pow 2
    exact hnum.continuousAt.div (Complex.continuous_normSq.pow 3).continuousAt
      (pow_ne_zero 3 (ne_of_gt (Complex.normSq_pos.mpr hz)))

theorem ambientWeight_continuous (c : ℝ) : Continuous (ambientWeight c) := by
  exact Complex.continuous_normSq.add (continuous_const.mul angularCorrection_continuous)

theorem quarticImag_conj (z : ℂ) : quarticImag (conj z) = -quarticImag z := by
  simp [quarticImag, ← map_pow]

@[simp] theorem angularCorrection_conj (z : ℂ) :
    angularCorrection (conj z) = angularCorrection z := by
  simp [angularCorrection, quarticImag_conj]

@[simp] theorem ambientWeight_conj (c : ℝ) (z : ℂ) :
    ambientWeight c (conj z) = ambientWeight c z := by
  simp [ambientWeight]

@[simp] theorem ambientWeight_real (c r : ℝ) : ambientWeight c (r : ℂ) = r ^ 2 := by
  simp [ambientWeight, angularCorrection, quarticImag, ← Complex.ofReal_pow, pow_two]

@[simp] theorem ambientWeight_one (c : ℝ) : ambientWeight c 1 = 1 := by
  simpa using ambientWeight_real c 1

@[simp] theorem counterWeight_one (c : ℝ) : counterWeight c 1 = 1 := by
  simp [counterWeight]

private theorem complex_a_fourth : ComplexModel.a ^ 4 = (-1 / 4 : ℂ) := by
  apply Complex.ext <;> norm_num [ComplexModel.a, pow_succ, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

private theorem complex_b_fourth : ComplexModel.b ^ 4 = (-1 / 4 : ℂ) := by
  apply Complex.ext <;> norm_num [ComplexModel.b, pow_succ, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

private theorem complex_a_norm : Complex.normSq ComplexModel.a = 1 / 2 := by
  norm_num [ComplexModel.a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem complex_b_norm : Complex.normSq ComplexModel.b = 1 / 2 := by
  norm_num [ComplexModel.b, Complex.normSq_apply, Complex.div_re, Complex.div_im]

/-- Both native generators have the same fourth-harmonic factor, including sign. -/
theorem quarticImag_a (z : ℂ) :
    quarticImag (ComplexModel.a * z) = -quarticImag z / 4 := by
  rw [quarticImag, mul_pow, complex_a_fourth]
  simp [Complex.mul_im, quarticImag]
  <;> ring

theorem quarticImag_b (z : ℂ) :
    quarticImag (ComplexModel.b * z) = -quarticImag z / 4 := by
  rw [quarticImag, mul_pow, complex_b_fourth]
  simp [Complex.mul_im, quarticImag]
  <;> ring

private theorem correction_half_of_native (t z : ℂ)
    (ht : Complex.normSq t = 1 / 2)
    (hh : quarticImag (t * z) = -quarticImag z / 4) :
    angularCorrection (t * z) = angularCorrection z / 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
  unfold angularCorrection
  rw [hh, Complex.normSq_mul, ht]
  field_simp [hn]
  <;> ring

@[simp] theorem ambientWeight_a (c : ℝ) (z : ℂ) :
    ambientWeight c (ComplexModel.a * z) = ambientWeight c z / 2 := by
  have hq := correction_half_of_native ComplexModel.a z complex_a_norm (quarticImag_a z)
  simp only [ambientWeight, Complex.normSq_mul, complex_a_norm, hq]
  ring

@[simp] theorem ambientWeight_b (c : ℝ) (z : ℂ) :
    ambientWeight c (ComplexModel.b * z) = ambientWeight c z / 2 := by
  have hq := correction_half_of_native ComplexModel.b z complex_b_norm (quarticImag_b z)
  simp only [ambientWeight, Complex.normSq_mul, complex_b_norm, hq]
  ring

/-- Native transfer is universal over the initial carrier for every real parameter. -/
theorem counterWeight_native (c : ℝ) : NativeTransfer (counterWeight c) := by
  refine ⟨counterWeight_one c, ?_, ?_⟩
  · intro p
    simp only [counterWeight, map_mul, complexEval_a, ambientWeight_a]
  · intro p
    simp only [counterWeight, map_mul, complexEval_b, ambientWeight_b]

theorem counterWeight_normalized_generator_transfer (c : ℝ) :
    counterWeight c a + counterWeight c b = 1 ∧
      (∀ p, counterWeight c (a * p) = counterWeight c a * counterWeight c p) ∧
      (∀ p, counterWeight c (b * p) = counterWeight c b * counterWeight c p) := by
  have ha := readout_a (counterWeight_native c)
  have hb := readout_b (counterWeight_native c)
  refine ⟨by rw [ha, hb]; norm_num, ?_, ?_⟩
  · intro p
    rw [(counterWeight_native c).left_a, ha]
    ring
  · intro p
    rw [(counterWeight_native c).left_b, hb]
    ring

/-- The canonical normalized echo uses only this family's native-transfer contract. -/
theorem counterWeight_normalized_raw_echo (c : ℝ) :
    mixer (1, 0) = (a, b) ∧ mixer (a, b) = (0, 1) ∧
      counterWeight c a = 1 / 2 ∧ counterWeight c b = 1 / 2 ∧
      counterWeight c a + counterWeight c b = 1 ∧
      0 < counterWeight c a ∧ 0 < counterWeight c b ∧
      counterWeight c 0 = 0 ∧ counterWeight c 1 = 1 :=
  normalized_raw_echo (counterWeight_native c)

theorem counterWeight_bounds (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    Complex.normSq (complexEval p) ≤ counterWeight c p ∧
      counterWeight c p ≤ (1 + c) * Complex.normSq (complexEval p) :=
  ambientWeight_bounds c hc _

theorem counterWeight_nonnegative (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    0 ≤ counterWeight c p := ambientWeight_nonnegative c hc _

theorem counterWeight_zero_iff (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    counterWeight c p = 0 ↔ p = 0 := by
  rw [counterWeight, ambientWeight_zero_iff c hc]
  constructor
  · intro hp
    apply NormalForm.complexEval_injective
    simpa using hp
  · rintro rfl
    exact map_zero complexEval

private theorem eval_reflection (p : Presentation) :
    complexEval (reflection p) = conj (complexEval p) := by
  have h : complexEval.comp reflection = (starRingEnd ℂ).comp complexEval := by
    apply hom_ext
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
  exact DFunLike.congr_fun h p

@[simp] theorem counterWeight_reflection (c : ℝ) (p : Presentation) :
    counterWeight c (reflection p) = counterWeight c p := by
  simp only [counterWeight, eval_reflection, ambientWeight_conj]

@[simp] theorem counterWeight_nat (c : ℝ) (n : ℕ) :
    counterWeight c (n : Presentation) = (n : ℝ) ^ 2 := by
  unfold counterWeight
  rw [map_natCast]
  simpa using ambientWeight_real c (n : ℝ)

theorem counterWeight_nat_order_iff (c : ℝ) (m n : ℕ) :
    counterWeight c (m : Presentation) ≤ counterWeight c (n : Presentation) ↔ m ≤ n := by
  rw [counterWeight_nat, counterWeight_nat]
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

/-- Ambient extension is stated without a topology on the initial carrier. -/
theorem counterWeight_has_continuous_extension (c : ℝ) :
    ∃ F : ℂ → ℝ, Continuous F ∧ ∀ p, counterWeight c p = F (complexEval p) :=
  ⟨ambientWeight c, ambientWeight_continuous c, fun _ => rfl⟩

/-- Native transfer also supplies the usual dyadic scaling on every input. -/
theorem counterWeight_dyadic_scale (c : ℝ) (k : ℕ) (p : Presentation) :
    counterWeight c (half ^ k * p) = counterWeight c p / (4 : ℝ) ^ k :=
  readout_half_pow_mul (counterWeight_native c) k p

section FiniteWitnesses

/-- A convenient exact coordinate expression for this explicitly supplied family. -/
theorem ambientWeight_coordinates (c x y : ℝ) :
    ambientWeight c ((x : ℂ) + (y : ℂ) * Complex.I) =
      x ^ 2 + y ^ 2 + c *
        (4 * x * y * (x ^ 2 - y ^ 2)) ^ 2 / (x ^ 2 + y ^ 2) ^ 3 := by
  simp [ambientWeight, angularCorrection, quarticImag_formula,
    Complex.normSq_add_mul_I, mul_div_assoc]

/-- The integer restriction is exactly the same readout through Gaussian histories. -/
def latticeWeight (c : ℝ) (z : IntegerLattice) : ℝ := integerReadout (counterWeight c) z

theorem latticeWeight_formula (c : ℝ) (z : IntegerLattice) :
    latticeWeight c z =
      (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 + c *
        (4 * (z.1 : ℝ) * (z.2 : ℝ) * ((z.1 : ℝ) ^ 2 - (z.2 : ℝ) ^ 2)) ^ 2 /
          ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ^ 3 := by
  unfold latticeWeight integerReadout counterWeight
  simp only [Arithmetic.gaussian, map_add, map_mul, map_intCast, complexEval_phase]
  simpa using ambientWeight_coordinates c (z.1 : ℝ) (z.2 : ℝ)

/-- Positive parameter times this rational is the common finite defect. -/
def defect (c : ℝ) : ℝ := c * (576 / 125)

theorem defect_pos (c : ℝ) (hc : 0 < c) : 0 < defect c := by
  exact mul_pos hc (by norm_num)

theorem lattice_two_plus_phase (c : ℝ) : latticeWeight c (2, 1) = 5 + defect c := by
  norm_num [latticeWeight_formula, defect]
  <;> ring

theorem counterWeight_not_norm (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p, counterWeight c p = Complex.normSq (complexEval p)) := by
  intro h
  have hw := h (Arithmetic.gaussian phase (2, 1))
  have hv : counterWeight c (Arithmetic.gaussian phase (2, 1)) = 5 + defect c :=
    lattice_two_plus_phase c
  have hn : Complex.normSq (complexEval (Arithmetic.gaussian phase (2, 1))) = 5 := by
    norm_num [Arithmetic.gaussian, Complex.normSq_apply, map_ofNat]
  rw [hv, hn] at hw
  have hd := defect_pos c hc
  linarith

abbrev cornerProbes (c : ℝ) := fixedCornerProbes (latticeWeight c)

theorem corner_seed_values (c : ℝ) :
    cornerProbes c (0, 0) + cornerProbes c (-1, -1) = ![2, 2, 2, 2] ∧
      cornerProbes c (-1, 0) + cornerProbes c (0, -1) = ![2, 2, 2, 2] := by
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_formula]

theorem corner_seed_packet (c : ℝ) :
    cornerProbes c (0, 0) + cornerProbes c (-1, -1) =
      cornerProbes c (-1, 0) + cornerProbes c (0, -1) :=
  (corner_seed_values c).1.trans (corner_seed_values c).2.symm

theorem shifted_corner_packet_left (c : ℝ) :
    cornerProbes c (1, 0) + cornerProbes c (0, -1) = ![2, 6, 2, 6 + defect c] := by
  funext j
  fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_formula, defect]
    <;> ring

theorem shifted_corner_packet_right (c : ℝ) :
    cornerProbes c (0, 0) + cornerProbes c (1, -1) = ![2, 6 + defect c, 2, 6] := by
  funext j
  fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_formula, defect]
    <;> ring

/-- The failure uses the concrete seed and coordinate-one shifted packets. -/
theorem counterWeight_not_single_continuation (c : ℝ) (hc : 0 < c) :
    ¬ SingleContinuationLaw (counterWeight c) := by
  intro h
  change PairCongruentUnder (cornerProbes c)
    (fun z : IntegerLattice => z + (1, 0)) at h
  have hs := h (0, 0) (-1, -1) (-1, 0) (0, -1) (corner_seed_packet c)
  have hs' : cornerProbes c (1, 0) + cornerProbes c (0, -1) =
      cornerProbes c (0, 0) + cornerProbes c (1, -1) := by simpa using hs
  rw [shifted_corner_packet_left, shifted_corner_packet_right] at hs'
  have hcoordinate := congrFun hs' (1 : Fin 4)
  norm_num at hcoordinate
  have hd := defect_pos c hc
  linarith

/-- Raw third-order coherent inclusion-exclusion on the original carrier. -/
def rawI3 (c : ℝ) (p q r : Presentation) : ℝ :=
  counterWeight c (p + q + r) - counterWeight c (p + q) -
    counterWeight c (p + r) - counterWeight c (q + r) +
    counterWeight c p + counterWeight c q + counterWeight c r

theorem rawI3_counterexample (c : ℝ) : rawI3 c 1 1 phase = defect c := by
  unfold rawI3 counterWeight
  simp only [map_add, map_one, complexEval_phase]
  norm_num [ambientWeight, angularCorrection, quarticImag_formula,
    Complex.normSq_apply, defect]
  <;> ring

theorem rawI3_nonzero (c : ℝ) (hc : 0 < c) : rawI3 c 1 1 phase ≠ 0 := by
  rw [rawI3_counterexample]
  exact ne_of_gt (defect_pos c hc)

theorem counterWeight_first_output (c : ℝ) :
    counterWeight c (a + 2 * b) = 5 / 2 + c * (288 / 125) := by
  unfold counterWeight
  simp only [map_add, map_mul, map_ofNat, complexEval_a, complexEval_b]
  norm_num [ambientWeight, angularCorrection, quarticImag_formula,
    ComplexModel.a, ComplexModel.b, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]
  <;> ring

theorem counterWeight_second_output (c : ℝ) :
    counterWeight c (b + 2 * a) = 5 / 2 + c * (288 / 125) := by
  unfold counterWeight
  simp only [map_add, map_mul, map_ofNat, complexEval_a, complexEval_b]
  norm_num [ambientWeight, angularCorrection, quarticImag_formula,
    ComplexModel.a, ComplexModel.b, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]
  <;> ring

theorem mixer_conservation_counterexample (c : ℝ) :
    counterWeight c (1 : Presentation) + counterWeight c (2 : Presentation) = 5 ∧
      counterWeight c (mixer (1, 2)).1 + counterWeight c (mixer (1, 2)).2 =
        5 + defect c := by
  constructor
  · have htwo : counterWeight c (2 : Presentation) = 4 := by
      convert counterWeight_nat c 2 using 1 <;> norm_num
    norm_num [htwo]
  · change counterWeight c (a * 1 + b * 2) +
      counterWeight c (b * 1 + a * 2) = _
    simp only [mul_one]
    rw [mul_comm b (2 : Presentation), mul_comm a (2 : Presentation)]
    rw [counterWeight_first_output, counterWeight_second_output]
    unfold defect
    ring

theorem mixer_not_conservative (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p : Presentation × Presentation,
      counterWeight c (mixer p).1 + counterWeight c (mixer p).2 =
        counterWeight c p.1 + counterWeight c p.2) := by
  intro h
  have hw := h (1, 2)
  obtain ⟨hi, ho⟩ := mixer_conservation_counterexample c
  rw [ho, hi] at hw
  have hd := defect_pos c hc
  linarith

/-- This is an ambient identity at a single pair, with the parameter retained. -/
theorem ambient_multiplication_defect (c : ℝ) :
    ambientWeight c (2 + Complex.I) ^ 2 - ambientWeight c (3 + 4 * Complex.I) =
      1152 * c * (527 + 288 * c) / 15625 := by
  norm_num [ambientWeight, angularCorrection, quarticImag_formula,
    Complex.normSq_apply]
  <;> ring

private theorem gaussian_two_plus_phase_square :
    (Arithmetic.gaussian phase (2, 1)) ^ 2 = Arithmetic.gaussian phase (3, 4) := by
  norm_num [Arithmetic.gaussian]
  linear_combination phase_square

/-- Global multiplication fails on the same initial carrier at `(2+phase)^2`. -/
theorem counterWeight_multiplication_defect (c : ℝ) :
    counterWeight c (Arithmetic.gaussian phase (2, 1)) ^ 2 -
      counterWeight c ((Arithmetic.gaussian phase (2, 1)) ^ 2) =
        1152 * c * (527 + 288 * c) / 15625 := by
  rw [gaussian_two_plus_phase_square]
  unfold counterWeight
  simp only [Arithmetic.gaussian, map_add, map_mul, map_intCast, complexEval_phase]
  simpa using ambient_multiplication_defect c

theorem counterWeight_not_multiplicative (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p q, counterWeight c (p * q) = counterWeight c p * counterWeight c q) := by
  intro h
  let p := Arithmetic.gaussian phase (2, 1)
  have hm : counterWeight c (p ^ 2) = counterWeight c p ^ 2 := by
    simpa only [pow_two] using h p p
  have hd := counterWeight_multiplication_defect c
  have hp : 0 < 1152 * c * (527 + 288 * c) / 15625 := by positivity
  change counterWeight c p ^ 2 - counterWeight c (p ^ 2) = _ at hd
  rw [hm] at hd
  linarith

end FiniteWitnesses

end IDT.QMClosure.NativeRegularReadoutCountercontrol
