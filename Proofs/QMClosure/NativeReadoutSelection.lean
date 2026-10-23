import Proofs.QMClosure.NativeBellScaledBridge
import Mathlib.Data.Real.Basic

namespace IDT.QMClosure.NativeReadoutSelection

open NativeBellScaledBridge

noncomputable section

/-!
# Conditional selection of an arbitrary native integer detector response

The primitive pair-history weight remains `W n = n²`. A detector response is
additional data, not a replacement pair-history measure. Supplied integer joint
tables, the local action, entrywise response, normalization, and accessibility
of every integer preparation are operational bridges, not primitive-derived
physics. `hadamard` is not a bijection of the integer lattice; no physical
reversibility is asserted.

The universal result concerns arbitrary real-valued responses on INTEGER
amplitudes, not just monomial powers. No continuity, evenness, homogeneity or
power-family assumption is supplied. Gaussian off-real amplitudes, rational or
continuous amplitude domains, actual detector dynamics and outcome selection
remain outside this theorem. In particular, this does not close the old combined
readout obligation or prove QM.
-/

structure Admissible (g : ℤ → ℝ) : Prop where
  nonnegative : ∀ n, 0 ≤ g n
  zero : g 0 = 0
  onePositive : 0 < g 1

def responseTotal (g : ℤ → ℝ) (t : NativeTable) : ℝ :=
  g t.aa + g t.ab + g t.ba + g t.bb

def responseRow (g : ℤ → ℝ) (t : NativeTable) (left : Bool) : ℝ :=
  (if left then g t.ba + g t.bb else g t.aa + g t.ab) / responseTotal g t

def responseCell (g : ℤ → ℝ) (t : NativeTable) : ℝ :=
  g t.aa / responseTotal g t

def referenceTable (x y : ℤ) : NativeTable := ⟨x, y, 1, 0⟩

def referenceBefore (g : ℤ → ℝ) (x y : ℤ) : ℝ :=
  g 1 / (g x + g y + g 1)

def referenceAfter (g : ℤ → ℝ) (x y : ℤ) : ℝ :=
  (2 * g 1) / (g (x + y) + g (x - y) + 2 * g 1)

/-- A universal equality of actual normalized marginals, not a status flag. -/
def ReferenceInvariant (g : ℤ → ℝ) : Prop :=
  ∀ x y : ℤ, referenceBefore g x y = referenceAfter g x y

/-- One exact reference-row violation refutes this supplied universal equality,
not the underlying primitive theory or the physical admissibility of a detector. -/
theorem reference_counterexample_refutes_invariance {g : ℤ → ℝ} {x y : ℤ}
    (h : referenceBefore g x y ≠ referenceAfter g x y) : ¬ ReferenceInvariant g :=
  fun all => h (all x y)

theorem reference_denominators_positive (g : ℤ → ℝ) (a : Admissible g)
    (x y : ℤ) :
    0 < g x + g y + g 1 ∧
      0 < g (x + y) + g (x - y) + 2 * g 1 := by
  constructor <;> nlinarith [a.nonnegative x, a.nonnegative y,
    a.nonnegative (x + y), a.nonnegative (x - y), a.onePositive]

theorem reference_formulas_are_native_local_readouts
    (g : ℤ → ℝ) (a : Admissible g) (x y : ℤ) :
    responseRow g (localAction identity (referenceTable x y) identity) true =
        referenceBefore g x y ∧
      responseRow g (localAction identity (referenceTable x y) hadamard) true =
        referenceAfter g x y := by
  simp [responseRow, responseTotal, localAction, identity, hadamard,
    referenceTable, multiply, transpose, referenceBefore, referenceAfter,
    a.zero, two_mul, sub_eq_add_neg, add_assoc]

theorem invariant_implies_parallelogram (g : ℤ → ℝ) (a : Admissible g)
    (h : ReferenceInvariant g) (x y : ℤ) :
    g (x + y) + g (x - y) = 2 * (g x + g y) := by
  have pos := reference_denominators_positive g a x y
  have cross := (div_eq_div_iff (ne_of_gt pos.1) (ne_of_gt pos.2)).mp (h x y)
  have product : g 1 * (g (x + y) + g (x - y) - 2 * (g x + g y)) = 0 := by
    nlinarith [cross]
  have difference := (mul_eq_zero.mp product).resolve_left (ne_of_gt a.onePositive)
  linarith

theorem invariant_implies_even (g : ℤ → ℝ) (a : Admissible g)
    (h : ReferenceInvariant g) (n : ℤ) : g (-n) = g n := by
  have p := invariant_implies_parallelogram g a h 0 n
  simp only [zero_add, zero_sub, a.zero] at p
  linarith

/-- The recurrence is derived, not assumed as detector homogeneity. -/
theorem invariant_implies_recurrence (g : ℤ → ℝ) (a : Admissible g)
    (h : ReferenceInvariant g) (n : ℤ) :
    g (n + 1) + g (n - 1) = 2 * (g n + g 1) :=
  invariant_implies_parallelogram g a h n 1

theorem invariant_implies_quadratic_nat (g : ℤ → ℝ) (a : Admissible g)
    (h : ReferenceInvariant g) (n : ℕ) :
    g (n : ℤ) = g 1 * (n : ℝ) ^ 2 := by
  have pair : ∀ k : ℕ,
      g (k : ℤ) = g 1 * (k : ℝ) ^ 2 ∧
        g ((k : ℤ) + 1) = g 1 * ((k : ℝ) + 1) ^ 2 := by
    intro k
    induction k with
    | zero => simp [a.zero]
    | succ k ih =>
      have recurrence := invariant_implies_recurrence g a h ((k : ℤ) + 1)
      have cancel : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
      rw [cancel, ih.1, ih.2] at recurrence
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      · push_cast
        nlinarith [recurrence]
  exact (pair n).1

theorem invariant_implies_quadratic (g : ℤ → ℝ) (a : Admissible g)
    (h : ReferenceInvariant g) (n : ℤ) : g n = g 1 * (n : ℝ) ^ 2 := by
  cases n with
  | ofNat k => simpa using invariant_implies_quadratic_nat g a h k
  | negSucc k =>
      have even := invariant_implies_even g a h ((k : ℤ) + 1)
      have natValue := invariant_implies_quadratic_nat g a h (k + 1)
      have negCast : (Int.negSucc k : ℝ) = -((k : ℝ) + 1) := by simp
      rw [negCast]
      change g (-((k : ℤ) + 1)) = _
      rw [even]
      convert natValue using 1
      push_cast
      ring

theorem quadratic_implies_invariant (g : ℤ → ℝ) (a : Admissible g)
    (quadratic : ∀ n : ℤ, g n = g 1 * (n : ℝ) ^ 2) : ReferenceInvariant g := by
  intro x y
  have pos := reference_denominators_positive g a x y
  apply (div_eq_div_iff (ne_of_gt pos.1) (ne_of_gt pos.2)).mpr
  dsimp [referenceBefore, referenceAfter]
  rw [quadratic x, quadratic y, quadratic (x + y), quadratic (x - y)]
  push_cast
  ring

/-- Exactly the supplied reference family, not unconditional physical selection. -/
theorem reference_invariant_iff_quadratic (g : ℤ → ℝ) (a : Admissible g) :
    ReferenceInvariant g ↔ ∀ n : ℤ, g n = g 1 * (n : ℝ) ^ 2 :=
  ⟨invariant_implies_quadratic g a, quadratic_implies_invariant g a⟩

/-- For a response to native weight, only reachable square weights are selected;
this says nothing about `f` at other integer weights or off-real Gaussian data. -/
theorem weight_response_invariant_iff_on_reachable_squares (f : ℤ → ℝ)
    (a : Admissible (fun n => f (W n))) :
    ReferenceInvariant (fun n => f (W n)) ↔
      ∀ n : ℤ, f (W n) = f (W 1) * (n : ℝ) ^ 2 :=
  reference_invariant_iff_quadratic (fun n => f (W n)) a

/-- These are responses TO the same native measure, not two primitive weights. -/
def squareResponse (n : ℤ) : ℝ := (W n : ℝ)
def fourthResponse (n : ℤ) : ℝ := (W n : ℝ) ^ 2

theorem native_weight_is_unchanged (n : ℤ) :
    W n = n ^ 2 ∧ squareResponse n = (n : ℝ) ^ 2 ∧
      fourthResponse n = (n : ℝ) ^ 4 := by
  simp [W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight,
    squareResponse, fourthResponse]
  ring

theorem square_response_admissible : Admissible squareResponse := by
  constructor
  · intro n; rw [(native_weight_is_unchanged n).2.1]; positivity
  · norm_num [squareResponse, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]
  · norm_num [squareResponse, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

theorem fourth_response_admissible : Admissible fourthResponse := by
  constructor
  · intro n; unfold fourthResponse; positivity
  · norm_num [fourthResponse, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]
  · norm_num [fourthResponse, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

def samePreparation : NativeTable := ⟨1, 0, 1, 1⟩
def beforeH : NativeTable := localAction identity samePreparation identity
def afterH : NativeTable := localAction identity samePreparation hadamard

theorem same_preparation_positive_totals :
    responseTotal squareResponse beforeH = 3 ∧
      responseTotal squareResponse afterH = 6 ∧
      responseTotal fourthResponse beforeH = 3 ∧
      responseTotal fourthResponse afterH = 18 ∧
      0 < responseTotal squareResponse beforeH ∧
      0 < responseTotal squareResponse afterH ∧
      0 < responseTotal fourthResponse beforeH ∧
      0 < responseTotal fourthResponse afterH := by
  norm_num [responseTotal, squareResponse, fourthResponse, W,
    signedScalarPairHistoryGate, pairHistoryQuadraticWeight,
    beforeH, afterH, samePreparation, localAction, identity, hadamard, multiply, transpose]

theorem same_native_preparation_separates_detector_responses :
    responseRow squareResponse beforeH false = 1 / 3 ∧
      responseRow squareResponse afterH false = 1 / 3 ∧
      responseRow fourthResponse beforeH false = 1 / 3 ∧
      responseRow fourthResponse afterH false = 1 / 9 ∧
      responseCell squareResponse afterH = 1 / 6 ∧
      responseCell fourthResponse afterH = 1 / 18 := by
  norm_num [responseRow, responseCell, responseTotal, squareResponse, fourthResponse, W,
    signedScalarPairHistoryGate, pairHistoryQuadraticWeight,
    beforeH, afterH, samePreparation, localAction, identity, hadamard, multiply, transpose]

/-- Two admissible completions of the same native weight/preparation/action
disagree. This does NOT assert that both pass every retained empirical gate;
the fourth-power detector response is not a zero-I3 law. -/
theorem native_weight_alone_does_not_select_this_readout :
    ¬ (∀ g h : ℤ → ℝ, Admissible g → Admissible h →
      responseRow g afterH false = responseRow h afterH false) := by
  intro unique
  have equality := unique squareResponse fourthResponse
    square_response_admissible fourth_response_admissible
  rw [same_native_preparation_separates_detector_responses.2.1,
    same_native_preparation_separates_detector_responses.2.2.2.1] at equality
  norm_num at equality

/-! A finite-spoof guard: bounded tests are not the universal hypothesis. -/

def spikeResponse (n : ℤ) : ℝ :=
  if n = 7 ∨ n = -7 then 50 else squareResponse n

theorem spike_response_admissible : Admissible spikeResponse := by
  constructor
  · intro n
    unfold spikeResponse
    split_ifs
    · norm_num
    · exact square_response_admissible.nonnegative n
  · norm_num [spikeResponse, squareResponse, W,
      signedScalarPairHistoryGate, pairHistoryQuadraticWeight]
  · norm_num [spikeResponse, squareResponse, W,
      signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

theorem spike_agrees_with_square_on_bounded_inputs (n : ℤ)
    (lower : -6 ≤ n) (upper : n ≤ 6) : spikeResponse n = squareResponse n := by
  have outside : ¬ (n = 7 ∨ n = -7) := by omega
  simp [spikeResponse, outside]

theorem spike_keeps_native_weight_but_changes_detector_response :
    W 7 = 49 ∧ spikeResponse 7 = 50 := by
  norm_num [spikeResponse, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

/-- Input entries 3,4,1,0 lie in [-4,4], but H reaches amplitude 7. -/
theorem bounded_input_reference_exposes_spike :
    referenceBefore spikeResponse 3 4 = 1 / 26 ∧
      referenceAfter spikeResponse 3 4 = 2 / 53 ∧
      referenceBefore spikeResponse 3 4 ≠ referenceAfter spikeResponse 3 4 := by
  norm_num [referenceBefore, referenceAfter, spikeResponse, squareResponse, W,
    signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

theorem bounded_agreement_does_not_imply_reference_invariance :
    ¬ ReferenceInvariant spikeResponse := by
  intro h
  exact bounded_input_reference_exposes_spike.2.2 (h 3 4)

end

end IDT.QMClosure.NativeReadoutSelection
