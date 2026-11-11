import Proofs.QMClosure.NativeInitialHistoryPresentation
import Proofs.QMClosure.FixedCornerHalfMixtureReadout
import Mathlib.Algebra.Field.ZMod

/-!
# A globally multiplicative native-transfer readout countercontrol

This concrete function is defined on the initial coefficient presentation.
It combines its complex-model squared norm with a reflection-invariant
finite-field zero mask. It is nonnegative, unital, reflection invariant and
globally multiplicative. Both native coefficients divide every readout by two.
Its balanced canonical raw echo is normalized.

The function has nonzero nulls. It fails count monotonicity, conservation for
all two-channel inputs, and equal-half pair congruence of its four prescribed
integer corner probes. The complex norm defines this particular control.
No selection theorem for an arbitrary readout is assumed or established here.
No event-frequency, physical realization or QM closure claim is made.
-/

noncomputable section

namespace IDT.QMClosure.NativeGeneratorReadoutCountercontrol

open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open FiniteMixtureContinuationRank

attribute [local instance] presentationCommRing presentationCharZero

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

open scoped ComplexConjugate

abbrev A := Presentation
abbrev F5 := Controls.F5

/-- The finite character is evaluated after syntactic reflection pairing. -/
def residueNorm (p : A) : F5 := Controls.finiteEval (p * reflection p)

/-- The ordinary algebraic norm is used only to define this concrete control. -/
def baseWeight (p : A) : ℝ := Complex.normSq (complexEval p)

/-- A multiplicative finite-field mask of the ordinary algebraic norm. -/
def counterWeight (p : A) : ℝ :=
  if residueNorm p = 0 then 0 else baseWeight p

@[simp] theorem residueNorm_zero : residueNorm 0 = 0 := by
  simp [residueNorm]

@[simp] theorem residueNorm_one : residueNorm 1 = 1 := by
  simp [residueNorm]

theorem residueNorm_mul (p q : A) :
    residueNorm (p * q) = residueNorm p * residueNorm q := by
  simp only [residueNorm, map_mul]
  ring

@[simp] theorem residueNorm_reflection (p : A) :
    residueNorm (reflection p) = residueNorm p := by
  unfold residueNorm
  rw [reflection_involutive p, mul_comm]

@[simp] theorem residueNorm_a : residueNorm a = 3 := by
  simp only [residueNorm, map_mul, reflection_a, Controls.finiteEval_a,
    Controls.finiteEval_b]
  decide

@[simp] theorem residueNorm_b : residueNorm b = 3 := by
  simp only [residueNorm, map_mul, reflection_b, Controls.finiteEval_a,
    Controls.finiteEval_b]
  decide

theorem complexEval_reflection (p : A) :
    complexEval (reflection p) = conj (complexEval p) := by
  have h : complexEval.comp reflection = (starRingEnd ℂ).comp complexEval := by
    apply hom_ext
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
  exact DFunLike.congr_fun h p

@[simp] theorem baseWeight_zero : baseWeight 0 = 0 := by
  simp [baseWeight]

@[simp] theorem baseWeight_one : baseWeight 1 = 1 := by
  simp [baseWeight]

theorem baseWeight_nonnegative (p : A) : 0 ≤ baseWeight p :=
  Complex.normSq_nonneg _

theorem baseWeight_mul (p q : A) :
    baseWeight (p * q) = baseWeight p * baseWeight q := by
  simp only [baseWeight, map_mul, Complex.normSq_mul]

@[simp] theorem baseWeight_reflection (p : A) :
    baseWeight (reflection p) = baseWeight p := by
  simp only [baseWeight, complexEval_reflection, Complex.normSq_conj]

@[simp] theorem baseWeight_a : baseWeight a = 1 / 2 := by
  rw [baseWeight, complexEval_a]
  change Complex.normSq ((1 + Complex.I) / 2) = 1 / 2
  rw [Complex.normSq_div]
  norm_num [Complex.normSq_apply]

@[simp] theorem baseWeight_b : baseWeight b = 1 / 2 := by
  rw [← reflection_a, baseWeight_reflection, baseWeight_a]

@[simp] theorem counterWeight_zero : counterWeight 0 = 0 := by
  simp [counterWeight]

@[simp] theorem counterWeight_one : counterWeight 1 = 1 := by
  have hone : (1 : F5) ≠ 0 := by decide
  simp [counterWeight, hone]

theorem counterWeight_nonnegative (p : A) : 0 ≤ counterWeight p := by
  by_cases h : residueNorm p = 0
  · simp [counterWeight, h]
  · simpa [counterWeight, h] using baseWeight_nonnegative p

@[simp] theorem counterWeight_reflection (p : A) :
    counterWeight (reflection p) = counterWeight p := by
  simp [counterWeight]

theorem counterWeight_mul (p q : A) :
    counterWeight (p * q) = counterWeight p * counterWeight q := by
  by_cases hp : residueNorm p = 0 <;>
    by_cases hq : residueNorm q = 0 <;>
    simp [counterWeight, residueNorm_mul, mul_eq_zero, hp, hq, baseWeight_mul]

@[simp] theorem counterWeight_a : counterWeight a = 1 / 2 := by
  have h : (3 : F5) ≠ 0 := by decide
  simp [counterWeight, h]

@[simp] theorem counterWeight_b : counterWeight b = 1 / 2 := by
  rw [← reflection_a, counterWeight_reflection, counterWeight_a]

/-- Universal native transfer for the first grammar coefficient. -/
theorem native_transfer_a (p : A) :
    counterWeight (a * p) = counterWeight p / 2 := by
  rw [counterWeight_mul, counterWeight_a]
  ring

/-- Universal native transfer for the second grammar coefficient. -/
theorem native_transfer_b (p : A) :
    counterWeight (b * p) = counterWeight p / 2 := by
  rw [counterWeight_mul, counterWeight_b]
  ring

/-- The coherent two-channel grammar update. -/
def nativeForward (p : A × A) : A × A :=
  (a * p.1 + b * p.2, b * p.1 + a * p.2)

theorem canonical_raw_echo : nativeForward (a, b) = (0, 1) := by
  apply Prod.ext
  · exact destructive
  · change b * a + a * b = 1
    simpa only [mul_comm, add_comm] using laws.cross

theorem canonical_raw_echo_normalized :
    counterWeight a + counterWeight b = 1 ∧
      counterWeight (nativeForward (a, b)).1 +
        counterWeight (nativeForward (a, b)).2 = 1 := by
  rw [canonical_raw_echo]
  norm_num

@[simp] theorem residueNorm_five : residueNorm (5 : A) = 0 := by
  simp only [residueNorm, map_mul, map_ofNat, Controls.finiteEval_five]
  decide

@[simp] theorem counterWeight_five : counterWeight (5 : A) = 0 := by
  simp [counterWeight]

theorem nonzero_null : ∃ p : A, p ≠ 0 ∧ counterWeight p = 0 :=
  ⟨5, Controls.five_nonzero, counterWeight_five⟩

theorem not_count_monotone : ¬ Monotone (fun n : ℕ => counterWeight (n : A)) := by
  intro h
  have h15 := h (show (1 : ℕ) ≤ 5 by norm_num)
  norm_num at h15

/-- Integer restriction of the same function on the native presentation. -/
def latticeWeight (z : IntegerLattice) : ℝ :=
  counterWeight (Arithmetic.gaussian phase z)

theorem latticeWeight_multiplicative :
    IDT.MultiplicativeMixtureReadout.GaussianMultiplicative latticeWeight := by
  intro z w
  have h : Arithmetic.gaussian phase
      (IDT.MultiplicativeMixtureReadout.gaussianMul z w) =
      Arithmetic.gaussian phase z * Arithmetic.gaussian phase w := by
    simpa only [IDT.MultiplicativeMixtureReadout.gaussianMul,
      LocalHistoryReadoutOrderWall.serial] using
        Arithmetic.gaussian_serial phase phase_square z w
  simp only [latticeWeight, h, counterWeight_mul]

theorem finiteEval_phase : Controls.finiteEval phase = 2 := by
  change Controls.finiteEval (a * a + a * a) = _
  simp only [map_add, map_mul, Controls.finiteEval_a]
  decide

theorem residueNorm_gaussian (z : IntegerLattice) :
    residueNorm (Arithmetic.gaussian phase z) =
      (z.1 : F5) ^ 2 + (z.2 : F5) ^ 2 := by
  have htwo : (2 : F5) ^ 2 = -1 := by decide
  simp only [residueNorm, Arithmetic.gaussian, map_mul, map_add, map_intCast,
    reflection_phase, map_neg, finiteEval_phase]
  calc
    ((z.1 : F5) + (z.2 : F5) * 2) *
        ((z.1 : F5) + (z.2 : F5) * -2) =
      (z.1 : F5) ^ 2 - (z.2 : F5) ^ 2 * (2 : F5) ^ 2 := by ring
    _ = (z.1 : F5) ^ 2 + (z.2 : F5) ^ 2 := by rw [htwo]; ring

theorem baseWeight_gaussian (z : IntegerLattice) :
    baseWeight (Arithmetic.gaussian phase z) =
      (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  simp [baseWeight, Arithmetic.gaussian, Complex.normSq_apply, pow_two]

theorem latticeWeight_formula (z : IntegerLattice) :
    latticeWeight z =
      if (z.1 : F5) ^ 2 + (z.2 : F5) ^ 2 = 0 then 0
      else (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  simp only [latticeWeight, counterWeight, residueNorm_gaussian, baseWeight_gaussian]

private theorem latticeWeight_int_formula (z : IntegerLattice) :
    latticeWeight z =
      if (5 : ℤ) ∣ z.1 ^ 2 + z.2 ^ 2 then 0
      else (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  have hcast : (z.1 : F5) ^ 2 + (z.2 : F5) ^ 2 =
      ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : F5) := by
    simp only [Int.cast_add, Int.cast_pow]
  have hzero : (z.1 : F5) ^ 2 + (z.2 : F5) ^ 2 = 0 ↔
      (5 : ℤ) ∣ z.1 ^ 2 + z.2 ^ 2 := by
    rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  rw [latticeWeight_formula]
  simp only [hzero]

theorem lattice_unit : latticeWeight (1, 0) = 1 := by
  norm_num [latticeWeight_int_formula]

theorem lattice_two : latticeWeight (2, 0) = 4 := by
  norm_num [latticeWeight_int_formula]

theorem lattice_diagonal : latticeWeight (1, 1) = 2 := by
  norm_num [latticeWeight_int_formula]

theorem lattice_two_plus_phase : latticeWeight (2, 1) = 0 := by
  norm_num [latticeWeight_int_formula]

/-- Inclusion-exclusion on raw coherent Gaussian sums for this same control. -/
def latticeRawI3 (x y z : IntegerLattice) : ℝ :=
  latticeWeight (x + y + z) - latticeWeight (x + y) -
    latticeWeight (x + z) - latticeWeight (y + z) +
    latticeWeight x + latticeWeight y + latticeWeight z

theorem latticeRawI3_counterexample :
    latticeRawI3 (1, 0) (1, 0) (0, 1) = -5 := by
  norm_num [latticeRawI3, latticeWeight_int_formula]

theorem counterWeight_two : counterWeight (2 : A) = 4 := by
  simpa [latticeWeight, Arithmetic.gaussian] using lattice_two

theorem first_output_null : counterWeight (a + 2 * b) = 0 := by
  have h : residueNorm (a + 2 * b) = 0 := by
    simp only [residueNorm, map_mul, map_add, map_ofNat, reflection_a,
      reflection_b, Controls.finiteEval_a, Controls.finiteEval_b]
    decide
  simp [counterWeight, h]

theorem second_output_null : counterWeight (b + 2 * a) = 0 := by
  have h : residueNorm (b + 2 * a) = 0 := by
    simp only [residueNorm, map_mul, map_add, map_ofNat, reflection_a,
      reflection_b, Controls.finiteEval_a, Controls.finiteEval_b]
    decide
  simp [counterWeight, h]

/-- The integer input `(1,2)` has total five and output total zero. -/
theorem conservation_counterexample :
    counterWeight (1 : A) + counterWeight (2 : A) = 5 ∧
      counterWeight (nativeForward (1, 2)).1 +
        counterWeight (nativeForward (1, 2)).2 = 0 := by
  constructor
  · norm_num [counterWeight_two]
  · simpa [nativeForward, mul_comm] using
      show counterWeight (a + 2 * b) + counterWeight (b + 2 * a) = 0 by
        rw [first_output_null, second_output_null]
        norm_num

open IDT.FixedCornerHalfMixtureReadout

abbrev cornerProbes := fixedCornerProbes latticeWeight

theorem corner_seed_values :
    cornerProbes (0, 0) + cornerProbes (-1, -1) = ![2, 2, 2, 2] ∧
      cornerProbes (-1, 0) + cornerProbes (0, -1) = ![2, 2, 2, 2] := by
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_int_formula]

/-- The corner seed is equal as a four-coordinate raw pair packet. -/
theorem corner_seed_packet :
    cornerProbes (0, 0) + cornerProbes (-1, -1) =
      cornerProbes (-1, 0) + cornerProbes (0, -1) := by
  exact corner_seed_values.1.trans corner_seed_values.2.symm

theorem shifted_corner_packet_left :
    cornerProbes (1, 0) + cornerProbes (0, -1) = ![2, 6, 2, 1] := by
  funext j
  fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_int_formula]

theorem shifted_corner_packet_right :
    cornerProbes (0, 0) + cornerProbes (1, -1) = ![2, 1, 2, 6] := by
  funext j
  fin_cases j <;>
    norm_num [cornerProbes, fixedCornerProbes, normCorner, latticeWeight_int_formula]

/-- A fixed-corner seed does not propagate under the positive real unit step. -/
theorem not_pairCongruent_unit_shift :
    ¬ PairCongruentUnder cornerProbes
      (fun z : IntegerLattice => z + (1, 0)) := by
  intro h
  have hs := h (0, 0) (-1, -1) (-1, 0) (0, -1) corner_seed_packet
  have hs' : cornerProbes (1, 0) + cornerProbes (0, -1) =
      cornerProbes (0, 0) + cornerProbes (1, -1) := by
    simpa using hs
  rw [shifted_corner_packet_left, shifted_corner_packet_right] at hs'
  have hcoordinate := congrFun hs' (1 : Fin 4)
  norm_num at hcoordinate

end IDT.QMClosure.NativeGeneratorReadoutCountercontrol
