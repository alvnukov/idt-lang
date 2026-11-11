import Proofs.QMClosure.NativeRegularReadoutCountercontrol
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Bounded polynomial evolution with a singular first-hit observation

The two initialized real registers follow `(q,r) = (x^2*t,t)`. Their velocities,
the guard and the output are finite polynomial expressions in the frozen
aggregate coordinates and the register values. Solving the guard gives a time
in `[0,16]` for every input, including vacuum. The first nonnegative hit includes
an already satisfied guard at time zero. Its terminal output is exactly the
existing regular countercontrol for every complex input.

Division occurs in the solved observation time. The evolution, guard and
output definitions use polynomial formulas. The stopping time is singular at
vacuum. The exact axis values below exhibit the singularity, while the terminal
output has the previously checked continuous ambient extension. Bounded
observation times alone therefore leave the regular family's response
available. Quadratic-tangent analysis and the regularity of a common fixed-time
readout remain separate questions.

This construction supplies aggregate-coordinate access, ideal real registers
and continuous real time, initialization, exact first-hit detection and an
interpretation of the analog output. A discrete-token implementation, physical
event counts and full QM closure remain separate obligations. Time-zero hits
are part of the stated observation semantics.
-/

noncomputable section

namespace IDT.QMClosure.NativePolynomialStoppingCountercontrol

open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open NativeSingleContinuationReadout
open NativeRegularReadoutCountercontrol

attribute [local instance] presentationCommRing presentationCharZero

/-- The nonnegative polynomial that determines the guard's initial offset. -/
def guardNumerator (z : ℂ) : ℝ :=
  16 * z.im ^ 2 * (z.re ^ 2 - z.im ^ 2) ^ 2

/-- Polynomial initialized flow for the output register. -/
def valueRegister (z : ℂ) (t : ℝ) : ℝ := z.re ^ 2 * t

/-- Polynomial initialized flow for the clock register. -/
def clockRegister (t : ℝ) : ℝ := t

/-- Polynomial guard in the frozen coordinates and the clock register. -/
def polynomialGuard (x y r : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) ^ 3 * r - 16 * y ^ 2 * (x ^ 2 - y ^ 2) ^ 2

/-- Polynomial analog output in frozen coordinates and the output register. -/
def polynomialOutput (c x y q : ℝ) : ℝ := x ^ 2 + y ^ 2 + c * q

def guardOnFlow (z : ℂ) (t : ℝ) : ℝ :=
  polynomialGuard z.re z.im (clockRegister t)

def outputOnFlow (c : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  polynomialOutput c z.re z.im (valueRegister z t)

/-- Division solves the guard relation and is totalized at zero. -/
def solvedTime (z : ℂ) : ℝ := guardNumerator z / Complex.normSq z ^ 3

theorem guardOnFlow_eq (z : ℂ) (t : ℝ) :
    guardOnFlow z t = Complex.normSq z ^ 3 * t - guardNumerator z := by
  simp [guardOnFlow, polynomialGuard, clockRegister, guardNumerator,
    Complex.normSq_apply, pow_two]

theorem guardOnFlow_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (guardOnFlow z) (Complex.normSq z ^ 3) t := by
  have hfun : guardOnFlow z =
      (fun s : ℝ => Complex.normSq z ^ 3 * s - guardNumerator z) :=
    funext (guardOnFlow_eq z)
  rw [hfun]
  exact (hasDerivAt_const_mul _).sub_const _

theorem guard_time_slope_positive (z : ℂ) (hz : z ≠ 0) :
    0 < Complex.normSq z ^ 3 := pow_pos (Complex.normSq_pos.mpr hz) 3

@[simp] theorem guard_time_slope_vacuum : Complex.normSq (0 : ℂ) ^ 3 = 0 := by simp

theorem outputOnFlow_eq (c : ℝ) (z : ℂ) (t : ℝ) :
    outputOnFlow c z t = Complex.normSq z + c * valueRegister z t := by
  simp [outputOnFlow, polynomialOutput, Complex.normSq_apply, pow_two]

@[simp] theorem valueRegister_initial (z : ℂ) : valueRegister z 0 = 0 := by
  simp [valueRegister]

@[simp] theorem clockRegister_initial : clockRegister 0 = 0 := rfl

theorem valueRegister_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (valueRegister z) (z.re ^ 2) t :=
  hasDerivAt_const_mul _

theorem clockRegister_hasDerivAt (t : ℝ) :
    HasDerivAt clockRegister 1 t := hasDerivAt_id' t

@[simp] theorem guardNumerator_zero : guardNumerator 0 = 0 := by
  simp [guardNumerator]

@[simp] theorem solvedTime_zero : solvedTime 0 = 0 := by
  simp [solvedTime]

theorem quartic_square_factor (z : ℂ) :
    quarticImag z ^ 2 = z.re ^ 2 * guardNumerator z := by
  rw [quarticImag_formula]
  unfold guardNumerator
  ring

theorem guardNumerator_nonnegative (z : ℂ) : 0 ≤ guardNumerator z := by
  unfold guardNumerator
  positivity

/-- The explicit remainder is a sum of nonnegative monomials. -/
theorem guardNumerator_upper_remainder (z : ℂ) :
    16 * Complex.normSq z ^ 3 - guardNumerator z =
      16 * z.re ^ 2 * (z.re ^ 4 + 2 * z.re ^ 2 * z.im ^ 2 + 5 * z.im ^ 4) := by
  simp only [Complex.normSq_apply, guardNumerator]
  ring

theorem guardNumerator_le (z : ℂ) :
    guardNumerator z ≤ 16 * Complex.normSq z ^ 3 := by
  have h : 0 ≤ 16 * Complex.normSq z ^ 3 - guardNumerator z := by
    rw [guardNumerator_upper_remainder]
    positivity
  linarith

theorem solvedTime_nonnegative (z : ℂ) : 0 ≤ solvedTime z :=
  div_nonneg (guardNumerator_nonnegative z)
    (pow_nonneg (Complex.normSq_nonneg z) 3)

theorem solvedTime_le_sixteen (z : ℂ) : solvedTime z ≤ 16 := by
  by_cases hz : z = 0
  · simp [hz]
  · apply (div_le_iff₀ (pow_pos (Complex.normSq_pos.mpr hz) 3)).mpr
    nlinarith [guardNumerator_le z]

theorem solvedTime_bounds (z : ℂ) : 0 ≤ solvedTime z ∧ solvedTime z ≤ 16 :=
  ⟨solvedTime_nonnegative z, solvedTime_le_sixteen z⟩

theorem guard_at_solvedTime (z : ℂ) : guardOnFlow z (solvedTime z) = 0 := by
  rw [guardOnFlow_eq]
  by_cases hz : z = 0
  · simp [hz]
  · have hn : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
    unfold solvedTime
    field_simp [hn]
    <;> ring

theorem guard_vacuum_every_time (t : ℝ) : guardOnFlow 0 t = 0 := by
  simp [guardOnFlow_eq]

theorem guard_hit_iff_of_nonzero (z : ℂ) (hz : z ≠ 0) (t : ℝ) :
    guardOnFlow z t = 0 ↔ t = solvedTime z := by
  have hn : Complex.normSq z ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (Complex.normSq_pos.mpr hz))
  constructor
  · intro h
    change t = guardNumerator z / Complex.normSq z ^ 3
    apply (eq_div_iff hn).mpr
    rw [guardOnFlow_eq] at h
    nlinarith
  · intro h
    rw [h]
    exact guard_at_solvedTime z

/-- Equality hits include the initial time when its guard is already zero. -/
def IsFirstNonnegativeHit (z : ℂ) (t : ℝ) : Prop :=
  0 ≤ t ∧ guardOnFlow z t = 0 ∧
    ∀ s : ℝ, 0 ≤ s → guardOnFlow z s = 0 → t ≤ s

theorem solvedTime_first_hit (z : ℂ) : IsFirstNonnegativeHit z (solvedTime z) := by
  refine ⟨solvedTime_nonnegative z, guard_at_solvedTime z, ?_⟩
  intro s hs hhit
  by_cases hz : z = 0
  · simpa [hz] using hs
  · exact le_of_eq ((guard_hit_iff_of_nonzero z hz s).mp hhit).symm

/-- The least hit is unique even though every vacuum time satisfies the guard. -/
theorem first_hit_iff (z : ℂ) (t : ℝ) :
    IsFirstNonnegativeHit z t ↔ t = solvedTime z := by
  have hT := solvedTime_first_hit z
  constructor
  · intro ht
    exact le_antisymm (ht.2.2 _ hT.1 hT.2.1) (hT.2.2 _ ht.1 ht.2.1)
  · intro ht
    rw [ht]
    exact hT

theorem vacuum_first_hit_iff (t : ℝ) : IsFirstNonnegativeHit 0 t ↔ t = 0 := by
  simpa using first_hit_iff 0 t

theorem guard_negative_before_first_hit (z : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hlt : t < solvedTime z) : guardOnFlow z t < 0 := by
  by_cases hz : z = 0
  · simp only [hz, solvedTime_zero] at hlt
    linarith
  · have ha : 0 < Complex.normSq z ^ 3 := pow_pos (Complex.normSq_pos.mpr hz) 3
    have hm := mul_lt_mul_of_pos_left hlt ha
    have hroot := guard_at_solvedTime z
    rw [guardOnFlow_eq] at hroot ⊢
    linarith

/-- Closed-inequality hits use the same least nonnegative observation time. -/
def IsFirstNonnegativeClosedHit (z : ℂ) (t : ℝ) : Prop :=
  0 ≤ t ∧ 0 ≤ guardOnFlow z t ∧
    ∀ s : ℝ, 0 ≤ s → 0 ≤ guardOnFlow z s → t ≤ s

theorem solvedTime_first_closed_hit (z : ℂ) :
    IsFirstNonnegativeClosedHit z (solvedTime z) := by
  refine ⟨solvedTime_nonnegative z, ?_, ?_⟩
  · exact le_of_eq (guard_at_solvedTime z).symm
  · intro s hs hguard
    by_contra hbad
    have hneg := guard_negative_before_first_hit z s hs (lt_of_not_ge hbad)
    linarith

theorem first_closed_hit_iff (z : ℂ) (t : ℝ) :
    IsFirstNonnegativeClosedHit z t ↔ t = solvedTime z := by
  have hT := solvedTime_first_closed_hit z
  constructor
  · intro ht
    exact le_antisymm (ht.2.2 _ hT.1 hT.2.1) (hT.2.2 _ ht.1 ht.2.1)
  · intro ht
    rw [ht]
    exact hT

theorem terminal_register_eq (z : ℂ) :
    valueRegister z (solvedTime z) = angularCorrection z := by
  unfold valueRegister solvedTime angularCorrection
  rw [quartic_square_factor]
  ring

/-- The observed response uses the exact first nonnegative guard hit. -/
def terminalWeight (c : ℝ) (z : ℂ) : ℝ := outputOnFlow c z (solvedTime z)

theorem terminalWeight_eq (c : ℝ) (z : ℂ) :
    terminalWeight c z = ambientWeight c z := by
  rw [terminalWeight, outputOnFlow_eq, terminal_register_eq]
  rfl

theorem terminalWeight_continuous (c : ℝ) : Continuous (terminalWeight c) := by
  have h : terminalWeight c = ambientWeight c := funext (terminalWeight_eq c)
  rw [h]
  exact ambientWeight_continuous c

theorem terminalWeight_zero_iff (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    terminalWeight c z = 0 ↔ z = 0 := by
  rw [terminalWeight_eq]
  exact ambientWeight_zero_iff c hc z

def terminalCounterWeight (c : ℝ) (p : Presentation) : ℝ :=
  terminalWeight c (complexEval p)

theorem terminalCounterWeight_eq (c : ℝ) : terminalCounterWeight c = counterWeight c := by
  funext p
  exact terminalWeight_eq c (complexEval p)

theorem terminalCounterWeight_native (c : ℝ) : NativeTransfer (terminalCounterWeight c) := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_native c

theorem terminalCounterWeight_nonnegative (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    0 ≤ terminalCounterWeight c p := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_nonnegative c hc p

theorem terminalCounterWeight_zero_iff (c : ℝ) (hc : 0 ≤ c) (p : Presentation) :
    terminalCounterWeight c p = 0 ↔ p = 0 := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_zero_iff c hc p

theorem terminalCounterWeight_has_continuous_extension (c : ℝ) :
    ∃ F : ℂ → ℝ, Continuous F ∧ ∀ p, terminalCounterWeight c p = F (complexEval p) := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_has_continuous_extension c

theorem terminalCounterWeight_not_norm (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p, terminalCounterWeight c p = Complex.normSq (complexEval p)) := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_not_norm c hc

theorem terminalCounterWeight_not_single_continuation (c : ℝ) (hc : 0 < c) :
    ¬ SingleContinuationLaw (terminalCounterWeight c) := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_not_single_continuation c hc

theorem terminalCounterWeight_mixer_not_conservative (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p : Presentation × Presentation,
      terminalCounterWeight c (mixer p).1 + terminalCounterWeight c (mixer p).2 =
        terminalCounterWeight c p.1 + terminalCounterWeight c p.2) := by
  rw [terminalCounterWeight_eq]
  exact mixer_not_conservative c hc

theorem terminalCounterWeight_not_multiplicative (c : ℝ) (hc : 0 < c) :
    ¬ (∀ p q, terminalCounterWeight c (p * q) =
      terminalCounterWeight c p * terminalCounterWeight c q) := by
  rw [terminalCounterWeight_eq]
  exact counterWeight_not_multiplicative c hc

def terminalRawI3 (c : ℝ) (p q r : Presentation) : ℝ :=
  terminalCounterWeight c (p + q + r) - terminalCounterWeight c (p + q) -
    terminalCounterWeight c (p + r) - terminalCounterWeight c (q + r) +
    terminalCounterWeight c p + terminalCounterWeight c q + terminalCounterWeight c r

theorem terminalRawI3_nonzero (c : ℝ) (hc : 0 < c) :
    terminalRawI3 c 1 1 phase ≠ 0 := by
  simpa only [terminalRawI3, terminalCounterWeight_eq, rawI3] using rawI3_nonzero c hc

theorem solvedTime_real (s : ℝ) : solvedTime (s : ℂ) = 0 := by
  simp [solvedTime, guardNumerator]

theorem solvedTime_imag (s : ℝ) (hs : s ≠ 0) :
    solvedTime ((s : ℂ) * Complex.I) = 16 := by
  simp [solvedTime, guardNumerator, Complex.normSq_apply]
  field_simp [hs]
  <;> ring

theorem solvedTime_diagonal (z : ℂ) (hz : z.re ^ 2 = z.im ^ 2) :
    solvedTime z = 0 := by
  simp [solvedTime, guardNumerator, hz]

end IDT.QMClosure.NativePolynomialStoppingCountercontrol
