import Mathlib.Tactic

namespace IDT.QMClosure.PositiveMixerReadoutCountermodels

noncomputable section

/-!
# Exact controls for positivity, vacuum zero, and conservation domain

These are supplied concrete real-coordinate models, not a derivation of their
carrier, mixer, or physical interpretation. The positive quadratic selection
theorem removes serial multiplicativity but requires conservation on every
refined input pair. It therefore does not uniformly weaken a theorem requiring
only raw-integer conservation. The third control proves raw conservation for
all integer inputs, not a finite sample, and exhibits exact refined failure.

Positivity and vacuum zero are also substantive: signed linear readout and
constant positive readout respectively pass conservation without them. None
of these controls establishes detector actualization, physical Born readout,
Hilbert representation, dynamics, composite closure, or full QM.
-/

abbrev Plane := ℝ × ℝ

def quarterTurn : Plane →+ Plane where
  toFun x := (-x.2, x.1)
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext <;> dsimp
    ring

def half : Plane →+ Plane where
  toFun x := (x.1 / 2, x.2 / 2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> dsimp <;> ring

theorem half_genuine (x : Plane) : half x + half x = x := by
  ext <;> dsimp [half] <;> ring

theorem quarterTurn_square (x : Plane) : quarterTurn (quarterTurn x) = -x := by
  ext <;> simp [quarterTurn]

def coefficientA (x : Plane) : Plane := ((x.1 - x.2) / 2, (x.1 + x.2) / 2)
def coefficientB (x : Plane) : Plane := ((x.1 + x.2) / 2, (x.2 - x.1) / 2)

theorem coefficientA_from_half (x : Plane) :
    coefficientA x = half (x + quarterTurn x) := by
  ext <;> dsimp [coefficientA, half, quarterTurn] <;> ring

theorem coefficientB_from_half (x : Plane) :
    coefficientB x = half (x - quarterTurn x) := by
  ext <;> dsimp [coefficientB, half, quarterTurn]
  ring

def mixer (x y : Plane) : Plane × Plane :=
  (coefficientA x + coefficientB y, coefficientB x + coefficientA y)

def Conserved (W : Plane → ℝ) : Prop :=
  ∀ x y, W (mixer x y).1 + W (mixer x y).2 = W x + W y

theorem mixer_component_sum (x y : Plane) :
    (mixer x y).1 + (mixer x y).2 = x + y := by
  ext <;> dsimp [mixer, coefficientA, coefficientB] <;> ring

def normSq (x : Plane) : ℝ := x.1 ^ 2 + x.2 ^ 2

theorem normSq_conserved : Conserved normSq := by
  intro x y
  dsimp [normSq, mixer, coefficientA, coefficientB]
  ring

/-! Without positivity, a zero-vacuum conserved readout can be linear. -/

def signedReadout (x : Plane) : ℝ := x.1

theorem signedReadout_zero : signedReadout 0 = 0 := rfl

theorem signedReadout_conserved : Conserved signedReadout := by
  intro x y
  dsimp [signedReadout, mixer, coefficientA, coefficientB]
  ring

theorem signedReadout_negative : signedReadout (-1, 0) = -1 := rfl

theorem signedReadout_not_nonnegative : ¬ ∀ x, 0 ≤ signedReadout x := by
  intro h
  have := h (-1, 0)
  norm_num [signedReadout] at this

theorem signedReadout_not_parallelogram :
    ¬ ∀ x y, signedReadout (x + y) + signedReadout (x - y) =
      2 * (signedReadout x + signedReadout y) := by
  intro h
  have := h (1, 0) (1, 0)
  norm_num [signedReadout] at this

/-! Without vacuum zero, a constant positive readout passes conservation. -/

def constantReadout (_ : Plane) : ℝ := 1

theorem constantReadout_nonnegative (x : Plane) : 0 ≤ constantReadout x := by
  norm_num [constantReadout]

theorem constantReadout_conserved : Conserved constantReadout := by
  intro x y
  rfl

theorem constantReadout_not_zero : constantReadout 0 ≠ 0 := by
  norm_num [constantReadout]

/-! Raw-only conservation, positivity and normalization do not suffice. -/

def polynomial (x : Plane) : ℝ := normSq x + x.1 / 2
def rawReadout (x : Plane) : ℝ := (2 / 3 : ℝ) * max 0 (polynomial x)

theorem polynomial_conserved : Conserved polynomial := by
  intro x y
  dsimp [polynomial, normSq, mixer, coefficientA, coefficientB]
  ring

theorem rawReadout_nonnegative (x : Plane) : 0 ≤ rawReadout x := by
  exact mul_nonneg (by norm_num) (le_max_left _ _)

theorem rawReadout_zero : rawReadout 0 = 0 := by
  norm_num [rawReadout, polynomial, normSq]

theorem rawReadout_unit : rawReadout (1, 0) = 1 := by
  norm_num [rawReadout, polynomial, normSq]

def rawPoint (a b : ℤ) : Plane := ((a : ℝ), (b : ℝ))
def halfPoint (a b : ℤ) : Plane := ((a : ℝ) / 2, (b : ℝ) / 2)

theorem integer_consecutive_nonnegative (n : ℤ) :
    0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  by_cases h : 0 ≤ n
  · have hr : 0 ≤ (n : ℝ) := by exact_mod_cast h
    exact mul_nonneg hr (by linarith)
  · have hn : n ≤ -1 := by omega
    have hr : (n : ℝ) ≤ -1 := by exact_mod_cast hn
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

theorem polynomial_halfPoint (a b : ℤ) :
    polynomial (halfPoint a b) =
      ((a : ℝ) * ((a : ℝ) + 1) + (b : ℝ) ^ 2) / 4 := by
  dsimp [polynomial, normSq, halfPoint]
  ring

theorem polynomial_halfPoint_nonnegative (a b : ℤ) :
    0 ≤ polynomial (halfPoint a b) := by
  rw [polynomial_halfPoint]
  exact div_nonneg (add_nonneg (integer_consecutive_nonnegative a) (sq_nonneg _))
    (by norm_num)

theorem rawReadout_halfPoint (a b : ℤ) :
    rawReadout (halfPoint a b) = (2 / 3 : ℝ) * polynomial (halfPoint a b) := by
  unfold rawReadout
  rw [max_eq_right (polynomial_halfPoint_nonnegative a b)]

theorem rawPoint_as_halfPoint (a b : ℤ) :
    rawPoint a b = halfPoint (2 * a) (2 * b) := by
  ext <;> simp [rawPoint, halfPoint]

theorem rawReadout_rawPoint (a b : ℤ) :
    rawReadout (rawPoint a b) = (2 / 3 : ℝ) * polynomial (rawPoint a b) := by
  rw [rawPoint_as_halfPoint, rawReadout_halfPoint]

theorem mixer_raw_first (a b c d : ℤ) :
    (mixer (rawPoint a b) (rawPoint c d)).1 =
      halfPoint (a - b + c + d) (a + b + d - c) := by
  ext <;> dsimp [mixer, coefficientA, coefficientB, rawPoint, halfPoint] <;>
    push_cast <;> ring

theorem mixer_raw_second (a b c d : ℤ) :
    (mixer (rawPoint a b) (rawPoint c d)).2 =
      halfPoint (a + b + c - d) (b - a + c + d) := by
  ext <;> dsimp [mixer, coefficientA, coefficientB, rawPoint, halfPoint] <;>
    push_cast <;> ring

def RawConserved (W : Plane → ℝ) : Prop :=
  ∀ a b c d : ℤ,
    W (mixer (rawPoint a b) (rawPoint c d)).1 +
      W (mixer (rawPoint a b) (rawPoint c d)).2 =
        W (rawPoint a b) + W (rawPoint c d)

theorem rawReadout_raw_conserved : RawConserved rawReadout := by
  intro a b c d
  have h := polynomial_conserved (rawPoint a b) (rawPoint c d)
  rw [mixer_raw_first, mixer_raw_second] at h
  rw [mixer_raw_first, mixer_raw_second, rawReadout_halfPoint,
    rawReadout_halfPoint, rawReadout_rawPoint, rawReadout_rawPoint]
  linarith

theorem rawReadout_negative_unit : rawReadout (-1, 0) = 1 / 3 := by
  norm_num [rawReadout, polynomial, normSq]

theorem rawReadout_not_even : ¬ ∀ x, rawReadout (-x) = rawReadout x := by
  intro h
  have := h (1, 0)
  norm_num [rawReadout, polynomial, normSq] at this

theorem rawReadout_not_parallelogram :
    ¬ ∀ x y, rawReadout (x + y) + rawReadout (x - y) =
      2 * (rawReadout x + rawReadout y) := by
  intro h
  have := h (1, 0) (1, 0)
  norm_num [rawReadout, polynomial, normSq] at this

theorem refined_failure_mixer :
    mixer ((1 / 4 : ℝ), 0) ((-1 / 4 : ℝ), 0) =
      (((0 : ℝ), 1 / 4), ((0 : ℝ), -1 / 4)) := by
  norm_num [mixer, coefficientA, coefficientB]

theorem refined_failure_input :
    rawReadout ((1 / 4 : ℝ), 0) + rawReadout ((-1 / 4 : ℝ), 0) = 1 / 8 := by
  norm_num [rawReadout, polynomial, normSq]

theorem refined_failure_output :
    rawReadout (mixer ((1 / 4 : ℝ), 0) ((-1 / 4 : ℝ), 0)).1 +
      rawReadout (mixer ((1 / 4 : ℝ), 0) ((-1 / 4 : ℝ), 0)).2 = 1 / 12 := by
  rw [refined_failure_mixer]
  norm_num [rawReadout, polynomial, normSq]

theorem rawReadout_not_conserved : ¬ Conserved rawReadout := by
  intro h
  have hf := h ((1 / 4 : ℝ), 0) ((-1 / 4 : ℝ), 0)
  rw [refined_failure_output, refined_failure_input] at hf
  norm_num at hf

/-- All of the positive normalized raw-domain conditions hold together,
while full-domain conservation and the quadratic identity both fail. -/
theorem raw_domain_boundary :
    (∀ x, 0 ≤ rawReadout x) ∧ rawReadout 0 = 0 ∧ rawReadout (1, 0) = 1 ∧
      RawConserved rawReadout ∧ ¬ Conserved rawReadout ∧
      (¬ ∀ x, rawReadout (-x) = rawReadout x) ∧
      (¬ ∀ x y, rawReadout (x + y) + rawReadout (x - y) =
        2 * (rawReadout x + rawReadout y)) :=
  ⟨rawReadout_nonnegative, rawReadout_zero, rawReadout_unit,
    rawReadout_raw_conserved, rawReadout_not_conserved,
    rawReadout_not_even, rawReadout_not_parallelogram⟩

end

end IDT.QMClosure.PositiveMixerReadoutCountermodels
