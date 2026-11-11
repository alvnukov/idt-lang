import Proofs.QMClosure.NativeRegularReadoutCountercontrol
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# A supplied polynomial relaxation mechanism

The single real register has frozen aggregate complex input `z`. Its velocity
is a polynomial in the two real input coordinates and the register value.
`register` is an explicit initialized solution. An equilibrium observation
recovers the previously supplied regular family. A finite common observation
time obeys native transfer with time rescaling by eight. A positive
input-dependent timer recovers that family with a smaller positive parameter
away from vacuum. `stoppedWeight` explicitly supplies a zero-output convention
at vacuum, where the timer never reaches a positive threshold.

Aggregate-coordinate access, continuous real time, a real register,
initialization, the polynomial dynamics, observation scheduling and event
interpretation are additional supplied structures. This artifact proves an
explicit mathematical mechanism. Primitive-history realization, physical
detector construction, ODE existence and uniqueness, a general finite-time
regularity selector and full QM closure remain separate obligations.

The finite-time outputs have a common quadratic leading term as quantified
by `finiteWeight_remainder`. Native transfer uses the same observation
protocol. Equilibrium observation and the singular stopping schedule change
that protocol. No statement about uniform convergence is made here.
-/

noncomputable section

namespace IDT.QMClosure.NativeRelaxationReadoutCountercontrol

open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout
open NativeRegularReadoutCountercontrol
open Filter
open scoped Topology

attribute [local instance] presentationCommRing presentationCharZero

/-- A finite polynomial expression in frozen coordinates and one register. -/
def polynomialVelocity (x y v : ℝ) : ℝ :=
  (4 * x * y * (x ^ 2 - y ^ 2)) ^ 2 - (x ^ 2 + y ^ 2) ^ 3 * v

/-- The initialized explicit solution, using the existing total division. -/
def register (z : ℂ) (t : ℝ) : ℝ :=
  angularCorrection z * (1 - Real.exp (-(Complex.normSq z ^ 3 * t)))

/-- The common-time observation of the supplied register. -/
def finiteWeight (c : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq z + c * register z t

theorem polynomialVelocity_coordinates (z : ℂ) (v : ℝ) :
    polynomialVelocity z.re z.im v =
      quarticImag z ^ 2 - Complex.normSq z ^ 3 * v := by
  simp [polynomialVelocity, quarticImag_formula, Complex.normSq_apply, pow_two]

/-- Cancellation also holds at vacuum, where the numerator vanishes. -/
theorem correction_balance (z : ℂ) :
    Complex.normSq z ^ 3 * angularCorrection z = quarticImag z ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
  unfold angularCorrection
  field_simp [hn]
  <;> ring

@[simp] theorem register_initial (z : ℂ) : register z 0 = 0 := by
  simp [register]

@[simp] theorem register_vacuum (t : ℝ) : register 0 t = 0 := by
  simp [register]

@[simp] theorem finiteWeight_vacuum (c t : ℝ) : finiteWeight c 0 t = 0 := by
  simp [finiteWeight]

@[simp] theorem finiteWeight_initial (c : ℝ) (z : ℂ) :
    finiteWeight c z 0 = Complex.normSq z := by
  simp [finiteWeight]

/-- This proves the explicit solution's equation at every real time. -/
theorem register_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (register z)
      (quarticImag z ^ 2 - Complex.normSq z ^ 3 * register z t) t := by
  have harg : HasDerivAt (fun s : ℝ => -(Complex.normSq z ^ 3 * s))
      (-Complex.normSq z ^ 3) t := by
    simpa only [mul_one, neg_mul] using
      (hasDerivAt_id' t).const_mul (-Complex.normSq z ^ 3)
  have hd := (harg.exp.const_sub 1).const_mul (angularCorrection z)
  change HasDerivAt (register z) _ t at hd
  apply hd.congr_deriv
  dsimp [register]
  calc
    angularCorrection z *
        -(Real.exp (-(Complex.normSq z ^ 3 * t)) * -Complex.normSq z ^ 3) =
        Complex.normSq z ^ 3 * angularCorrection z *
          Real.exp (-(Complex.normSq z ^ 3 * t)) := by ring
    _ = quarticImag z ^ 2 - Complex.normSq z ^ 3 *
        (angularCorrection z * (1 - Real.exp (-(Complex.normSq z ^ 3 * t)))) := by
      linear_combination correction_balance z

theorem register_polynomial_ODE (z : ℂ) (t : ℝ) :
    HasDerivAt (register z)
      (polynomialVelocity z.re z.im (register z t)) t := by
  rw [polynomialVelocity_coordinates]
  exact register_hasDerivAt z t

theorem correction_is_equilibrium (z : ℂ) :
    polynomialVelocity z.re z.im (angularCorrection z) = 0 := by
  rw [polynomialVelocity_coordinates, correction_balance]
  ring

/-- Every constant is an equilibrium at vacuum. Initialization selects zero. -/
theorem vacuum_constant_solution (v t : ℝ) :
    HasDerivAt (fun _ : ℝ => v) (polynomialVelocity 0 0 v) t := by
  simpa [polynomialVelocity] using (hasDerivAt_const t v)

theorem register_bounds (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ register z t ∧ register z t ≤ angularCorrection z := by
  have hQ := angularCorrection_nonnegative z
  have ha : 0 ≤ Complex.normSq z ^ 3 * t :=
    mul_nonneg (pow_nonneg (Complex.normSq_nonneg z) 3) ht
  have he : Real.exp (-(Complex.normSq z ^ 3 * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have he0 := (Real.exp_pos (-(Complex.normSq z ^ 3 * t))).le
  dsimp [register]
  constructor
  · exact mul_nonneg hQ (sub_nonneg.mpr he)
  · nlinarith [mul_nonneg hQ he0]

theorem register_le_norm (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    register z t ≤ Complex.normSq z :=
  (register_bounds z t ht).2.trans (angularCorrection_le_norm z)

theorem register_tendsto_of_nonzero (z : ℂ) (hz : z ≠ 0) :
    Tendsto (register z) atTop (𝓝 (angularCorrection z)) := by
  have ha : 0 < Complex.normSq z ^ 3 := pow_pos (Complex.normSq_pos.mpr hz) 3
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(Complex.normSq z ^ 3 * t)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have hQ : Tendsto (fun _ : ℝ => angularCorrection z) atTop
      (𝓝 (angularCorrection z)) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [register, sub_zero, mul_one] using hQ.mul (h1.sub hexp)

theorem register_tendsto (z : ℂ) :
    Tendsto (register z) atTop (𝓝 (angularCorrection z)) := by
  by_cases hz : z = 0
  · subst z
    have hzero : register 0 = (fun _ : ℝ => 0) := by
      funext t
      exact register_vacuum t
    rw [hzero, angularCorrection_zero]
    exact tendsto_const_nhds
  · exact register_tendsto_of_nonzero z hz

theorem finiteWeight_tendsto (c : ℝ) (z : ℂ) :
    Tendsto (finiteWeight c z) atTop (𝓝 (ambientWeight c z)) := by
  have hN : Tendsto (fun _ : ℝ => Complex.normSq z) atTop
      (𝓝 (Complex.normSq z)) := tendsto_const_nhds
  have hc : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  exact hN.add (hc.mul (register_tendsto z))

theorem norm_native_a (z : ℂ) :
    Complex.normSq (ComplexModel.a * z) = Complex.normSq z / 2 := by
  simpa [ambientWeight] using ambientWeight_a 0 z

theorem norm_native_b (z : ℂ) :
    Complex.normSq (ComplexModel.b * z) = Complex.normSq z / 2 := by
  simpa [ambientWeight] using ambientWeight_b 0 z

theorem correction_native_a (z : ℂ) :
    angularCorrection (ComplexModel.a * z) = angularCorrection z / 2 := by
  have h := ambientWeight_a 1 z
  dsimp [ambientWeight] at h
  rw [norm_native_a] at h
  linarith

theorem correction_native_b (z : ℂ) :
    angularCorrection (ComplexModel.b * z) = angularCorrection z / 2 := by
  have h := ambientWeight_b 1 z
  dsimp [ambientWeight] at h
  rw [norm_native_b] at h
  linarith

private theorem register_native_rescaled (g z : ℂ) (t : ℝ)
    (hn : Complex.normSq (g * z) = Complex.normSq z / 2)
    (hQ : angularCorrection (g * z) = angularCorrection z / 2) :
    register (g * z) t = register z (t / 8) / 2 := by
  unfold register
  rw [hn, hQ]
  rw [show -((Complex.normSq z / 2) ^ 3 * t) =
    -(Complex.normSq z ^ 3 * (t / 8)) by ring]
  ring

theorem register_native_a (z : ℂ) (t : ℝ) :
    register (ComplexModel.a * z) t = register z (t / 8) / 2 :=
  register_native_rescaled _ z t (norm_native_a z) (correction_native_a z)

theorem register_native_b (z : ℂ) (t : ℝ) :
    register (ComplexModel.b * z) t = register z (t / 8) / 2 :=
  register_native_rescaled _ z t (norm_native_b z) (correction_native_b z)

theorem finiteWeight_native_a (c : ℝ) (z : ℂ) (t : ℝ) :
    finiteWeight c (ComplexModel.a * z) t = finiteWeight c z (t / 8) / 2 := by
  simp only [finiteWeight, norm_native_a, register_native_a]
  ring

theorem finiteWeight_native_b (c : ℝ) (z : ℂ) (t : ℝ) :
    finiteWeight c (ComplexModel.b * z) t = finiteWeight c z (t / 8) / 2 := by
  simp only [finiteWeight, norm_native_b, register_native_b]
  ring

theorem register_strictMono (z : ℂ) (hh : quarticImag z ≠ 0) :
    StrictMono (register z) := by
  have hz : z ≠ 0 := by
    intro hz
    apply hh
    simp [hz]
  have ha : 0 < Complex.normSq z ^ 3 := pow_pos (Complex.normSq_pos.mpr hz) 3
  have hQ : 0 < angularCorrection z :=
    div_pos (sq_pos_of_ne_zero hh) ha
  intro s t hst
  have he : Real.exp (-(Complex.normSq z ^ 3 * t)) <
      Real.exp (-(Complex.normSq z ^ 3 * s)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  exact mul_lt_mul_of_pos_left (sub_lt_sub_left he 1) hQ

/-- Common positive times give a strict transfer defect on nonzero harmonics. -/
theorem finiteWeight_same_time_a_lt (c : ℝ) (hc : 0 < c) (z : ℂ)
    (hh : quarticImag z ≠ 0) (t : ℝ) (ht : 0 < t) :
    finiteWeight c (ComplexModel.a * z) t < finiteWeight c z t / 2 := by
  rw [finiteWeight_native_a]
  have hq := register_strictMono z hh (show t / 8 < t by linarith)
  have hp := mul_pos hc (sub_pos.mpr hq)
  dsimp [finiteWeight]
  nlinarith

theorem finiteWeight_same_time_b_lt (c : ℝ) (hc : 0 < c) (z : ℂ)
    (hh : quarticImag z ≠ 0) (t : ℝ) (ht : 0 < t) :
    finiteWeight c (ComplexModel.b * z) t < finiteWeight c z t / 2 := by
  rw [finiteWeight_native_b]
  have hq := register_strictMono z hh (show t / 8 < t by linarith)
  have hp := mul_pos hc (sub_pos.mpr hq)
  dsimp [finiteWeight]
  nlinarith

theorem finiteWeight_same_time_witness (c : ℝ) (hc : 0 < c)
    (t : ℝ) (ht : 0 < t) :
    finiteWeight c (ComplexModel.a * (2 + Complex.I)) t <
      finiteWeight c (2 + Complex.I) t / 2 := by
  apply finiteWeight_same_time_a_lt c hc _ _ t ht
  norm_num [quarticImag_formula]

theorem register_of_harmonic_zero (z : ℂ) (hh : quarticImag z = 0) (t : ℝ) :
    register z t = 0 := by
  simp [register, angularCorrection, hh]

theorem finiteWeight_calibration (c t : ℝ) :
    finiteWeight c 0 t = 0 ∧ finiteWeight c 1 t = 1 ∧
      finiteWeight c ComplexModel.a t = 1 / 2 ∧
      finiteWeight c ComplexModel.b t = 1 / 2 := by
  have h1 : quarticImag (1 : ℂ) = 0 := by simp [quarticImag]
  have ha : quarticImag ComplexModel.a = 0 := by
    simpa [h1] using quarticImag_a 1
  have hb : quarticImag ComplexModel.b = 0 := by
    simpa [h1] using quarticImag_b 1
  have hna : Complex.normSq ComplexModel.a = 1 / 2 := by
    simpa using norm_native_a 1
  have hnb : Complex.normSq ComplexModel.b = 1 / 2 := by
    simpa using norm_native_b 1
  simp [finiteWeight, register_of_harmonic_zero _ h1,
    register_of_harmonic_zero _ ha, register_of_harmonic_zero _ hb, hna, hnb]

/-- An explicit fixed-time remainder certificate around the common quadratic. -/
theorem finiteWeight_remainder (c : ℝ) (hc : 0 ≤ c) (z : ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ finiteWeight c z t - Complex.normSq z ∧
      finiteWeight c z t - Complex.normSq z ≤ c * t * Complex.normSq z ^ 4 := by
  have ha : 0 ≤ Complex.normSq z ^ 3 * t :=
    mul_nonneg (pow_nonneg (Complex.normSq_nonneg z) 3) ht
  have he : 1 - Real.exp (-(Complex.normSq z ^ 3 * t)) ≤
      Complex.normSq z ^ 3 * t := by
    linarith [Real.add_one_le_exp (-(Complex.normSq z ^ 3 * t))]
  have hq : register z t ≤ t * Complex.normSq z ^ 4 := by
    calc
      register z t ≤ angularCorrection z * (Complex.normSq z ^ 3 * t) :=
        mul_le_mul_of_nonneg_left he (angularCorrection_nonnegative z)
      _ ≤ Complex.normSq z * (Complex.normSq z ^ 3 * t) :=
        mul_le_mul_of_nonneg_right (angularCorrection_le_norm z) ha
      _ = t * Complex.normSq z ^ 4 := by ring
  have h0 := mul_nonneg hc (register_bounds z t ht).1
  have hbound := mul_le_mul_of_nonneg_left hq hc
  dsimp [finiteWeight]
  constructor <;> nlinarith

/-- A second polynomial register supplies the input-dependent observation clock. -/
def timer (z : ℂ) (t : ℝ) : ℝ := Complex.normSq z ^ 3 * t

def stoppingTime (tau : ℝ) (z : ℂ) : ℝ := tau / Complex.normSq z ^ 3

theorem timer_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (timer z) (Complex.normSq z ^ 3) t := by
  exact hasDerivAt_const_mul _

@[simp] theorem timer_initial (z : ℂ) : timer z 0 = 0 := by simp [timer]

theorem stoppingTime_positive (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : z ≠ 0) :
    0 < stoppingTime tau z :=
  div_pos htau (pow_pos (Complex.normSq_pos.mpr hz) 3)

theorem timer_at_stoppingTime (tau : ℝ) (z : ℂ) (hz : z ≠ 0) :
    timer z (stoppingTime tau z) = tau := by
  have hn : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
  unfold timer stoppingTime
  field_simp [hn]
  <;> ring

theorem positive_timer_hit (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ timer z t = tau :=
  ⟨stoppingTime tau z, stoppingTime_positive tau htau z hz,
    timer_at_stoppingTime tau z hz⟩

theorem timer_vacuum_never_reaches (tau : ℝ) (htau : 0 < tau) :
    ∀ t : ℝ, timer 0 t ≠ tau := by
  intro t
  simpa [timer] using ne_of_lt htau

private theorem stoppingTime_native_rescaled (tau : ℝ) (g z : ℂ)
    (hn : Complex.normSq (g * z) = Complex.normSq z / 2) :
    stoppingTime tau (g * z) = 8 * stoppingTime tau z := by
  unfold stoppingTime
  rw [hn]
  by_cases hz : Complex.normSq z = 0
  · simp [hz]
  · field_simp [hz]
    <;> ring

theorem stoppingTime_native_a (tau : ℝ) (z : ℂ) :
    stoppingTime tau (ComplexModel.a * z) = 8 * stoppingTime tau z :=
  stoppingTime_native_rescaled tau _ z (norm_native_a z)

theorem stoppingTime_native_b (tau : ℝ) (z : ℂ) :
    stoppingTime tau (ComplexModel.b * z) = 8 * stoppingTime tau z :=
  stoppingTime_native_rescaled tau _ z (norm_native_b z)

/-- Exact waiting-time amplification under repeated native attenuation. -/
theorem stoppingTime_native_a_pow (tau : ℝ) (k : ℕ) (z : ℂ) :
    stoppingTime tau (ComplexModel.a ^ k * z) =
      (8 : ℝ) ^ k * stoppingTime tau z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_comm (ComplexModel.a ^ k) ComplexModel.a, mul_assoc,
        stoppingTime_native_a, ih]
      rw [pow_succ]
      ring

def effectiveParameter (c tau : ℝ) : ℝ := c * (1 - Real.exp (-tau))

theorem effectiveParameter_positive (c : ℝ) (hc : 0 < c)
    (tau : ℝ) (htau : 0 < tau) : 0 < effectiveParameter c tau := by
  exact mul_pos hc (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

theorem finiteWeight_at_stoppingTime (c tau : ℝ) (z : ℂ) (hz : z ≠ 0) :
    finiteWeight c z (stoppingTime tau z) = ambientWeight (effectiveParameter c tau) z := by
  have hclock : Complex.normSq z ^ 3 * stoppingTime tau z = tau :=
    timer_at_stoppingTime tau z hz
  dsimp [finiteWeight, register]
  rw [hclock]
  dsimp [ambientWeight, effectiveParameter]
  ring

/-- Zero at vacuum is an additional totalization convention for this response. -/
def stoppedWeight (c tau : ℝ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else finiteWeight c z (stoppingTime tau z)

theorem stoppedWeight_eq (c tau : ℝ) (z : ℂ) :
    stoppedWeight c tau z = ambientWeight (effectiveParameter c tau) z := by
  by_cases hz : z = 0
  · simp [stoppedWeight, hz]
  · simp only [stoppedWeight, if_neg hz]
    exact finiteWeight_at_stoppingTime c tau z hz

def stoppedCounterWeight (c tau : ℝ) (p : Presentation) : ℝ :=
  stoppedWeight c tau (complexEval p)

theorem stoppedCounterWeight_eq (c tau : ℝ) :
    stoppedCounterWeight c tau = counterWeight (effectiveParameter c tau) := by
  funext p
  exact stoppedWeight_eq c tau (complexEval p)

theorem stoppedCounterWeight_native (c tau : ℝ) :
    NativeTransfer (stoppedCounterWeight c tau) := by
  rw [stoppedCounterWeight_eq]
  exact counterWeight_native _

theorem stoppedCounterWeight_not_norm (c : ℝ) (hc : 0 < c)
    (tau : ℝ) (htau : 0 < tau) :
    ¬ (∀ p, stoppedCounterWeight c tau p = Complex.normSq (complexEval p)) := by
  rw [stoppedCounterWeight_eq]
  exact counterWeight_not_norm _ (effectiveParameter_positive c hc tau htau)

theorem stoppedCounterWeight_not_single_continuation (c : ℝ) (hc : 0 < c)
    (tau : ℝ) (htau : 0 < tau) :
    ¬ SingleContinuationLaw (stoppedCounterWeight c tau) := by
  rw [stoppedCounterWeight_eq]
  exact counterWeight_not_single_continuation _ (effectiveParameter_positive c hc tau htau)

theorem stoppedCounterWeight_mixer_not_conservative (c : ℝ) (hc : 0 < c)
    (tau : ℝ) (htau : 0 < tau) :
    ¬ (∀ p : Presentation × Presentation,
      stoppedCounterWeight c tau (mixer p).1 + stoppedCounterWeight c tau (mixer p).2 =
        stoppedCounterWeight c tau p.1 + stoppedCounterWeight c tau p.2) := by
  rw [stoppedCounterWeight_eq]
  exact mixer_not_conservative _ (effectiveParameter_positive c hc tau htau)

theorem stoppedCounterWeight_not_multiplicative (c : ℝ) (hc : 0 < c)
    (tau : ℝ) (htau : 0 < tau) :
    ¬ (∀ p q, stoppedCounterWeight c tau (p * q) =
      stoppedCounterWeight c tau p * stoppedCounterWeight c tau q) := by
  rw [stoppedCounterWeight_eq]
  exact counterWeight_not_multiplicative _ (effectiveParameter_positive c hc tau htau)

def stoppedRawI3 (c tau : ℝ) (p q r : Presentation) : ℝ :=
  stoppedCounterWeight c tau (p + q + r) - stoppedCounterWeight c tau (p + q) -
    stoppedCounterWeight c tau (p + r) - stoppedCounterWeight c tau (q + r) +
    stoppedCounterWeight c tau p + stoppedCounterWeight c tau q +
      stoppedCounterWeight c tau r

theorem stoppedRawI3_nonzero (c : ℝ) (hc : 0 < c) (tau : ℝ) (htau : 0 < tau) :
    stoppedRawI3 c tau 1 1 phase ≠ 0 := by
  simpa only [stoppedRawI3, stoppedCounterWeight_eq, rawI3] using
    rawI3_nonzero (effectiveParameter c tau) (effectiveParameter_positive c hc tau htau)

end IDT.QMClosure.NativeRelaxationReadoutCountercontrol
