import Proofs.QMClosure.NativeRegularReadoutCountercontrol
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Competing uniformly transverse polynomial guards

Four nonnegative coordinate quadratics supply a continuous minimum response.
Both native contexts permute and halve the four readings. The resulting raw
response has universal native transfer and an explicit positive-parameter
norm defect, raw third-order defect and mixer-conservation defect.

A single initialized register follows `q(t) = (1 + normSq z) * t`. Each of four
polynomial guards has time slope at least one, including at vacuum. The first
hit of any guard occurs in `[1, 3/2)`, and all guards are strictly negative
before that time. The polynomial terminal output equals the minimum response.
Competition between the observation branches remains in the complete stopping
operation despite the uniform transversality of each individual guard.

The construction supplies aggregate coordinates, an ideal analog register and
continuous time, initialization, exact first-event comparison, baseline
subtraction and interpretation as a raw response. Discrete-token realization,
physical detector construction and full QM closure remain open. The minimum
response is generally nonsmooth away from vacuum. No C1, Peano-tangent or C2
claim is included in the theorem list.
-/

noncomputable section

namespace IDT.QMClosure.NativeCompetingGuardReadoutCountercontrol

open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout
open scoped ComplexConjugate

attribute [local instance] presentationCommRing presentationCharZero
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Four fixed coordinate quadratics, indexed by the guard branches. -/
def probe (z : ℂ) : Fin 4 → ℝ :=
  ![z.re ^ 2, z.im ^ 2, (z.re + z.im) ^ 2 / 2, (z.re - z.im) ^ 2 / 2]

/-- A nested finite minimum with explicit attainment below. -/
def minimum (z : ℂ) : ℝ :=
  min (min (probe z 0) (probe z 1)) (min (probe z 2) (probe z 3))

def ambientResponse (c : ℝ) (z : ℂ) : ℝ := Complex.normSq z + c * minimum z

def counterResponse (c : ℝ) (p : Presentation) : ℝ :=
  ambientResponse c (complexEval p)

theorem probe_nonnegative (z : ℂ) (j : Fin 4) : 0 ≤ probe z j := by
  fin_cases j <;> norm_num [probe] <;> positivity

theorem probe_continuous (j : Fin 4) : Continuous (fun z : ℂ => probe z j) := by
  fin_cases j
  · exact Complex.continuous_re.pow 2
  · exact Complex.continuous_im.pow 2
  · exact ((Complex.continuous_re.add Complex.continuous_im).pow 2).div_const 2
  · exact ((Complex.continuous_re.sub Complex.continuous_im).pow 2).div_const 2

theorem minimum_nonnegative (z : ℂ) : 0 ≤ minimum z :=
  le_min (le_min (probe_nonnegative z 0) (probe_nonnegative z 1))
    (le_min (probe_nonnegative z 2) (probe_nonnegative z 3))

theorem minimum_le_probe (z : ℂ) (j : Fin 4) : minimum z ≤ probe z j := by
  fin_cases j
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem minimum_attained (z : ℂ) : ∃ j : Fin 4, minimum z = probe z j := by
  have h01 : ∃ j : Fin 4, min (probe z 0) (probe z 1) = probe z j := by
    rcases le_total (probe z 0) (probe z 1) with h | h
    · exact ⟨0, min_eq_left h⟩
    · exact ⟨1, min_eq_right h⟩
  have h23 : ∃ j : Fin 4, min (probe z 2) (probe z 3) = probe z j := by
    rcases le_total (probe z 2) (probe z 3) with h | h
    · exact ⟨2, min_eq_left h⟩
    · exact ⟨3, min_eq_right h⟩
  rcases le_total (min (probe z 0) (probe z 1))
      (min (probe z 2) (probe z 3)) with h | h
  · rcases h01 with ⟨j, hj⟩
    exact ⟨j, (min_eq_left h).trans hj⟩
  · rcases h23 with ⟨j, hj⟩
    exact ⟨j, (min_eq_right h).trans hj⟩

theorem minimum_le_half_norm (z : ℂ) : minimum z ≤ Complex.normSq z / 2 := by
  have h0 : minimum z ≤ z.re ^ 2 := minimum_le_probe z 0
  have h1 : minimum z ≤ z.im ^ 2 := minimum_le_probe z 1
  rw [Complex.normSq_apply]
  nlinarith

theorem minimum_continuous : Continuous minimum :=
  ((probe_continuous 0).min (probe_continuous 1)).min
    ((probe_continuous 2).min (probe_continuous 3))

theorem ambientResponse_continuous (c : ℝ) : Continuous (ambientResponse c) :=
  Complex.continuous_normSq.add (continuous_const.mul minimum_continuous)

theorem probe_conj (z : ℂ) :
    probe (conj z) = ![probe z 0, probe z 1, probe z 3, probe z 2] := by
  funext j
  fin_cases j <;> norm_num [probe] <;> ring

@[simp] theorem minimum_conj (z : ℂ) : minimum (conj z) = minimum z := by
  unfold minimum
  simp only [probe_conj]
  change min (min (probe z 0) (probe z 1)) (min (probe z 3) (probe z 2)) = _
  rw [min_comm (probe z 3) (probe z 2)]

@[simp] theorem ambientResponse_conj (c : ℝ) (z : ℂ) :
    ambientResponse c (conj z) = ambientResponse c z := by
  simp [ambientResponse]

@[simp] theorem minimum_real (s : ℝ) : minimum (s : ℂ) = 0 := by
  apply le_antisymm
  · simpa [probe] using minimum_le_probe (s : ℂ) 1
  · exact minimum_nonnegative _

@[simp] theorem minimum_zero : minimum 0 = 0 := by simpa using minimum_real 0

@[simp] theorem probe_zero (j : Fin 4) : probe 0 j = 0 := by
  fin_cases j <;> norm_num [probe]

@[simp] theorem ambientResponse_zero (c : ℝ) : ambientResponse c 0 = 0 := by
  simp [ambientResponse]

@[simp] theorem ambientResponse_real (c s : ℝ) : ambientResponse c (s : ℂ) = s ^ 2 := by
  simp [ambientResponse, Complex.normSq_apply, pow_two]

@[simp] theorem ambientResponse_one (c : ℝ) : ambientResponse c 1 = 1 := by
  simpa using ambientResponse_real c 1

theorem probe_native_a (z : ℂ) :
    probe (ComplexModel.a * z) =
      ![probe z 3 / 2, probe z 2 / 2, probe z 0 / 2, probe z 1 / 2] := by
  funext j
  fin_cases j <;>
    norm_num [probe, ComplexModel.a, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem probe_native_b (z : ℂ) :
    probe (ComplexModel.b * z) =
      ![probe z 2 / 2, probe z 3 / 2, probe z 1 / 2, probe z 0 / 2] := by
  funext j
  fin_cases j <;>
    norm_num [probe, ComplexModel.b, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem minimum_native_a (z : ℂ) :
    minimum (ComplexModel.a * z) = minimum z / 2 := by
  unfold minimum
  simp only [probe_native_a]
  change min (min (probe z 3 / 2) (probe z 2 / 2))
    (min (probe z 0 / 2) (probe z 1 / 2)) = _
  simp only [min_div_div_right (show (0 : ℝ) ≤ 2 by norm_num)]
  congr 1
  ac_rfl

@[simp] theorem minimum_native_b (z : ℂ) :
    minimum (ComplexModel.b * z) = minimum z / 2 := by
  unfold minimum
  simp only [probe_native_b]
  change min (min (probe z 2 / 2) (probe z 3 / 2))
    (min (probe z 1 / 2) (probe z 0 / 2)) = _
  simp only [min_div_div_right (show (0 : ℝ) ≤ 2 by norm_num)]
  congr 1
  ac_rfl

private theorem norm_native_a : Complex.normSq ComplexModel.a = 1 / 2 := by
  norm_num [ComplexModel.a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem norm_native_b : Complex.normSq ComplexModel.b = 1 / 2 := by
  norm_num [ComplexModel.b, Complex.normSq_apply, Complex.div_re, Complex.div_im]

@[simp] theorem ambientResponse_native_a (c : ℝ) (z : ℂ) :
    ambientResponse c (ComplexModel.a * z) = ambientResponse c z / 2 := by
  simp only [ambientResponse, Complex.normSq_mul, norm_native_a, minimum_native_a]
  ring

@[simp] theorem ambientResponse_native_b (c : ℝ) (z : ℂ) :
    ambientResponse c (ComplexModel.b * z) = ambientResponse c z / 2 := by
  simp only [ambientResponse, Complex.normSq_mul, norm_native_b, minimum_native_b]
  ring

theorem ambientResponse_bounds (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    Complex.normSq z ≤ ambientResponse c z ∧
      ambientResponse c z ≤ (1 + c / 2) * Complex.normSq z := by
  have h0 := mul_nonneg hc (minimum_nonnegative z)
  have h1 := mul_le_mul_of_nonneg_left (minimum_le_half_norm z) hc
  dsimp [ambientResponse]
  constructor <;> nlinarith

theorem ambientResponse_nonnegative (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    0 ≤ ambientResponse c z :=
  (Complex.normSq_nonneg z).trans (ambientResponse_bounds c hc z).1

theorem ambientResponse_zero_iff (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ambientResponse c z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Complex.normSq_eq_zero.mp
    have hb := (ambientResponse_bounds c hc z).1
    rw [h] at hb
    exact le_antisymm hb (Complex.normSq_nonneg z)
  · rintro rfl
    exact ambientResponse_zero c

@[simp] theorem counterResponse_zero (c : ℝ) : counterResponse c 0 = 0 := by
  simp [counterResponse]

@[simp] theorem counterResponse_one (c : ℝ) : counterResponse c 1 = 1 := by
  simp [counterResponse]

theorem counterResponse_native (c : ℝ) : NativeTransfer (counterResponse c) := by
  refine ⟨counterResponse_one c, ?_, ?_⟩
  · intro p
    simp only [counterResponse, map_mul, complexEval_a, ambientResponse_native_a]
  · intro p
    simp only [counterResponse, map_mul, complexEval_b, ambientResponse_native_b]

theorem counterResponse_nonnegative (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    0 ≤ counterResponse c p := ambientResponse_nonnegative c hc _

theorem counterResponse_zero_iff (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    counterResponse c p = 0 ↔ p = 0 := by
  rw [counterResponse, ambientResponse_zero_iff c hc]
  constructor
  · intro h
    apply NormalForm.complexEval_injective
    simpa using h
  · rintro rfl
    exact map_zero complexEval

private theorem eval_reflection (p : Presentation) :
    complexEval (reflection p) = conj (complexEval p) := by
  have h : complexEval.comp reflection = (starRingEnd ℂ).comp complexEval := by
    apply hom_ext
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
    · simp [ComplexModel.a, ComplexModel.b, map_ofNat, sub_eq_add_neg]
  exact DFunLike.congr_fun h p

@[simp] theorem counterResponse_reflection (c : ℝ) (p : Presentation) :
    counterResponse c (reflection p) = counterResponse c p := by
  simp only [counterResponse, eval_reflection, ambientResponse_conj]

theorem counterResponse_has_continuous_extension (c : ℝ) :
    ∃ F : ℂ → ℝ, Continuous F ∧ ∀ p, counterResponse c p = F (complexEval p) :=
  ⟨ambientResponse c, ambientResponse_continuous c, fun _ => rfl⟩

theorem ambientResponse_witness (c : ℝ) : ambientResponse c (2 + Complex.I) = 5 + c / 2 := by
  norm_num [ambientResponse, minimum, probe, Complex.normSq_apply]
  <;> ring

theorem ambientResponse_witness_ne (c : ℝ) (hc : 0 < c) :
    ambientResponse c (2 + Complex.I) ≠ 5 := by
  rw [ambientResponse_witness]
  linarith

private theorem eval_gaussian_witness :
    complexEval (Arithmetic.gaussian phase (2, 1)) = 2 + Complex.I := by
  norm_num [Arithmetic.gaussian, map_ofNat]

theorem counterResponse_not_norm (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p, counterResponse c p = Complex.normSq (complexEval p)) := by
  intro h
  have hw := h (Arithmetic.gaussian phase (2, 1))
  rw [counterResponse, eval_gaussian_witness, ambientResponse_witness] at hw
  norm_num [Complex.normSq_apply] at hw
  linarith

def rawI3 (c : ℝ) (p q r : Presentation) : ℝ :=
  counterResponse c (p + q + r) - counterResponse c (p + q) -
    counterResponse c (p + r) - counterResponse c (q + r) +
    counterResponse c p + counterResponse c q + counterResponse c r

theorem rawI3_counterexample (c : ℝ) : rawI3 c 1 1 phase = c / 2 := by
  unfold rawI3 counterResponse
  simp only [map_add, map_one, complexEval_phase]
  norm_num [ambientResponse, minimum, probe, Complex.normSq_apply]
  <;> ring

theorem rawI3_nonzero (c : ℝ) (hc : 0 < c) : rawI3 c 1 1 phase ≠ 0 := by
  rw [rawI3_counterexample]
  positivity

theorem counterResponse_first_output (c : ℝ) :
    counterResponse c (a + 2 * b) = 5 / 2 + c / 4 := by
  unfold counterResponse
  simp only [map_add, map_mul, map_ofNat, complexEval_a, complexEval_b]
  norm_num [ambientResponse, minimum, probe, ComplexModel.a, ComplexModel.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  <;> ring

theorem counterResponse_second_output (c : ℝ) :
    counterResponse c (b + 2 * a) = 5 / 2 + c / 4 := by
  unfold counterResponse
  simp only [map_add, map_mul, map_ofNat, complexEval_a, complexEval_b]
  norm_num [ambientResponse, minimum, probe, ComplexModel.a, ComplexModel.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  <;> ring

theorem mixer_conservation_counterexample (c : ℝ) :
    counterResponse c (1 : Presentation) + counterResponse c (2 : Presentation) = 5 ∧
      counterResponse c (mixer (1, 2)).1 + counterResponse c (mixer (1, 2)).2 = 5 + c / 2 := by
  constructor
  · norm_num [counterResponse, ambientResponse, minimum, probe, Complex.normSq_apply, map_ofNat]
  · change counterResponse c (a * 1 + b * 2) + counterResponse c (b * 1 + a * 2) = _
    simp only [mul_one]
    rw [mul_comm b (2 : Presentation), mul_comm a (2 : Presentation),
      counterResponse_first_output, counterResponse_second_output]
    ring

theorem mixer_not_conservative (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p : Presentation × Presentation,
      counterResponse c (mixer p).1 + counterResponse c (mixer p).2 =
        counterResponse c p.1 + counterResponse c p.2) := by
  intro h
  have hw := h (1, 2)
  obtain ⟨hi, ho⟩ := mixer_conservation_counterexample c
  rw [ho, hi] at hw
  linarith

theorem ambientResponse_multiplication_gap (c : ℝ) :
    ambientResponse c (2 + Complex.I) ^ 2 - ambientResponse c (3 + 4 * Complex.I) =
      9 * c / 2 + c ^ 2 / 4 := by
  norm_num [ambientResponse, minimum, probe, Complex.normSq_apply]
  <;> ring

/-- The coefficient in the single-register polynomial trajectory. -/
def rate (z : ℂ) : ℝ := 1 + Complex.normSq z

def register (z : ℂ) (t : ℝ) : ℝ := rate z * t

/-- Four polynomial guards acting on the same register. -/
def polynomialGuards (x y q : ℝ) : Fin 4 → ℝ :=
  ![q - (1 + (x ^ 2 + y ^ 2)) - x ^ 2,
    q - (1 + (x ^ 2 + y ^ 2)) - y ^ 2,
    q - (1 + (x ^ 2 + y ^ 2)) - (x + y) ^ 2 / 2,
    q - (1 + (x ^ 2 + y ^ 2)) - (x - y) ^ 2 / 2]

def polynomialOutput (c x y q : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + c * (q - (1 + (x ^ 2 + y ^ 2)))

def guardOnFlow (z : ℂ) (t : ℝ) (j : Fin 4) : ℝ :=
  polynomialGuards z.re z.im (register z t) j

def outputOnFlow (c : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  polynomialOutput c z.re z.im (register z t)

def individualTime (z : ℂ) (j : Fin 4) : ℝ := 1 + probe z j / rate z

def solvedTime (z : ℂ) : ℝ := 1 + minimum z / rate z

theorem rate_ge_one (z : ℂ) : 1 ≤ rate z := by
  dsimp [rate]
  linarith [Complex.normSq_nonneg z]

theorem rate_positive (z : ℂ) : 0 < rate z := lt_of_lt_of_le zero_lt_one (rate_ge_one z)

theorem rate_continuous : Continuous rate :=
  continuous_const.add Complex.continuous_normSq

theorem solvedTime_continuous : Continuous solvedTime :=
  continuous_const.add (minimum_continuous.div rate_continuous (fun z => (rate_positive z).ne'))

@[simp] theorem register_initial (z : ℂ) : register z 0 = 0 := by simp [register]

theorem register_hasDerivAt (z : ℂ) (t : ℝ) : HasDerivAt (register z) (rate z) t :=
  hasDerivAt_const_mul _

theorem guardOnFlow_eq (z : ℂ) (t : ℝ) (j : Fin 4) :
    guardOnFlow z t j = rate z * (t - 1) - probe z j := by
  fin_cases j <;>
    simp [guardOnFlow, polynomialGuards, register, rate, probe, Complex.normSq_apply,
      pow_two] <;> ring

theorem guard_initial_negative (z : ℂ) (j : Fin 4) : guardOnFlow z 0 j < 0 := by
  rw [guardOnFlow_eq]
  have hr := rate_positive z
  have hQ := probe_nonnegative z j
  nlinarith

theorem guardOnFlow_hasDerivAt (z : ℂ) (t : ℝ) (j : Fin 4) :
    HasDerivAt (fun s => guardOnFlow z s j) (rate z) t := by
  have hfun : (fun s => guardOnFlow z s j) =
      (fun s : ℝ => rate z * (s - 1) - probe z j) :=
    funext (fun s => guardOnFlow_eq z s j)
  rw [hfun]
  simpa only [mul_one] using
    (((hasDerivAt_id' t).sub_const 1).const_mul (rate z)).sub_const (probe z j)

theorem individualTime_ge_one (z : ℂ) (j : Fin 4) : 1 ≤ individualTime z j := by
  have h := div_nonneg (probe_nonnegative z j) (rate_positive z).le
  dsimp [individualTime]
  linarith

theorem individual_hit_balance (z : ℂ) (j : Fin 4) :
    rate z * (individualTime z j - 1) = probe z j := by
  unfold individualTime
  field_simp [(rate_positive z).ne']
  <;> ring

theorem guard_individual_hit (z : ℂ) (j : Fin 4) :
    guardOnFlow z (individualTime z j) j = 0 := by
  rw [guardOnFlow_eq, individual_hit_balance]
  ring

theorem guard_hit_iff (z : ℂ) (t : ℝ) (j : Fin 4) :
    guardOnFlow z t j = 0 ↔ t = individualTime z j := by
  constructor
  · intro h
    have hroot := individual_hit_balance z j
    rw [guardOnFlow_eq] at h
    have hmul : rate z * (t - individualTime z j) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (rate_positive z).ne')
  · intro h
    rw [h]
    exact guard_individual_hit z j

theorem solvedTime_ge_one (z : ℂ) : 1 ≤ solvedTime z := by
  have h := div_nonneg (minimum_nonnegative z) (rate_positive z).le
  dsimp [solvedTime]
  linarith

theorem solvedTime_lt_three_halves (z : ℂ) : solvedTime z < 3 / 2 := by
  have hfrac : minimum z / rate z < 1 / 2 := by
    apply (div_lt_iff₀ (rate_positive z)).mpr
    dsimp [rate]
    nlinarith [minimum_le_half_norm z]
  dsimp [solvedTime]
  linarith

theorem solvedTime_bounds (z : ℂ) : 1 ≤ solvedTime z ∧ solvedTime z < 3 / 2 :=
  ⟨solvedTime_ge_one z, solvedTime_lt_three_halves z⟩

theorem solvedTime_positive (z : ℂ) : 0 < solvedTime z :=
  lt_of_lt_of_le zero_lt_one (solvedTime_ge_one z)

theorem solvedTime_le_individualTime (z : ℂ) (j : Fin 4) :
    solvedTime z ≤ individualTime z j := by
  have h := div_le_div_of_nonneg_right (minimum_le_probe z j) (rate_positive z).le
  dsimp [solvedTime, individualTime]
  linarith

theorem solved_hit_balance (z : ℂ) : rate z * (solvedTime z - 1) = minimum z := by
  unfold solvedTime
  field_simp [(rate_positive z).ne']
  <;> ring

theorem guard_at_first_iff (z : ℂ) (j : Fin 4) :
    guardOnFlow z (solvedTime z) j = 0 ↔ probe z j = minimum z := by
  rw [guardOnFlow_eq, solved_hit_balance]
  constructor <;> intro h <;> linarith

theorem some_guard_hits (z : ℂ) : ∃ j : Fin 4, guardOnFlow z (solvedTime z) j = 0 := by
  rcases minimum_attained z with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [guardOnFlow_eq, solved_hit_balance, hj]
  ring

theorem any_guard_hit_after_first (z : ℂ) (t : ℝ) (j : Fin 4)
    (hhit : guardOnFlow z t j = 0) : solvedTime z ≤ t := by
  rw [(guard_hit_iff z t j).mp hhit]
  exact solvedTime_le_individualTime z j

theorem all_guards_negative_before_first (z : ℂ) (t : ℝ)
    (hlt : t < solvedTime z) : ∀ j : Fin 4, guardOnFlow z t j < 0 := by
  intro j
  have hm := mul_lt_mul_of_pos_left hlt (rate_positive z)
  have hbalance := solved_hit_balance z
  have hmin := minimum_le_probe z j
  rw [guardOnFlow_eq]
  nlinarith

/-- The earliest nonnegative hit among all four competing guard branches. -/
def IsFirstGuardHit (z : ℂ) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∃ j : Fin 4, guardOnFlow z t j = 0) ∧
    ∀ s : ℝ, 0 ≤ s → (∃ j : Fin 4, guardOnFlow z s j = 0) → t ≤ s

theorem solvedTime_first_guard_hit (z : ℂ) : IsFirstGuardHit z (solvedTime z) := by
  refine ⟨(solvedTime_positive z).le, some_guard_hits z, ?_⟩
  intro s _ hhit
  rcases hhit with ⟨j, hj⟩
  exact any_guard_hit_after_first z s j hj

theorem first_guard_hit_iff (z : ℂ) (t : ℝ) :
    IsFirstGuardHit z t ↔ t = solvedTime z := by
  have hT := solvedTime_first_guard_hit z
  constructor
  · intro ht
    exact le_antisymm (ht.2.2 _ hT.1 hT.2.1) (hT.2.2 _ ht.1 ht.2.1)
  · intro ht
    rw [ht]
    exact hT

@[simp] theorem solvedTime_vacuum : solvedTime 0 = 1 := by
  simp [solvedTime, rate]

theorem vacuum_all_guards_tie :
    solvedTime 0 = 1 ∧ ∀ j : Fin 4, guardOnFlow 0 1 j = 0 := by
  refine ⟨solvedTime_vacuum, ?_⟩
  intro j
  simp [guardOnFlow_eq, rate]

theorem register_at_solvedTime (z : ℂ) :
    register z (solvedTime z) = rate z + minimum z := by
  have h := solved_hit_balance z
  dsimp [register]
  nlinarith

theorem outputOnFlow_eq (c : ℝ) (z : ℂ) (t : ℝ) :
    outputOnFlow c z t = Complex.normSq z + c * (register z t - rate z) := by
  simp [outputOnFlow, polynomialOutput, rate, Complex.normSq_apply, pow_two]

def terminalWeight (c : ℝ) (z : ℂ) : ℝ := outputOnFlow c z (solvedTime z)

theorem terminalWeight_eq (c : ℝ) (z : ℂ) :
    terminalWeight c z = ambientResponse c z := by
  rw [terminalWeight, outputOnFlow_eq, register_at_solvedTime]
  dsimp [ambientResponse]
  ring

/-- Every branch tied at the first event gives the same state and output. -/
theorem active_branch_terminal_output (c : ℝ) (z : ℂ) (j : Fin 4)
    (hj : guardOnFlow z (solvedTime z) j = 0) :
    register z (individualTime z j) = rate z + minimum z ∧
      outputOnFlow c z (individualTime z j) = ambientResponse c z := by
  have ht : solvedTime z = individualTime z j :=
    (guard_hit_iff z (solvedTime z) j).mp hj
  rw [← ht]
  exact ⟨register_at_solvedTime z, terminalWeight_eq c z⟩

def terminalCounterWeight (c : ℝ) (p : Presentation) : ℝ :=
  terminalWeight c (complexEval p)

theorem terminalCounterWeight_eq (c : ℝ) : terminalCounterWeight c = counterResponse c := by
  funext p
  exact terminalWeight_eq c (complexEval p)

theorem terminalCounterWeight_native (c : ℝ) : NativeTransfer (terminalCounterWeight c) := by
  rw [terminalCounterWeight_eq]
  exact counterResponse_native c

theorem terminalCounterWeight_not_norm (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p, terminalCounterWeight c p = Complex.normSq (complexEval p)) := by
  rw [terminalCounterWeight_eq]
  exact counterResponse_not_norm c hc

end IDT.QMClosure.NativeCompetingGuardReadoutCountercontrol
