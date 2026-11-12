import Proofs.QMClosure.InitialColumnOrderReadoutCore

/-!
Five-premise readout selection on the literal initial P4 carrier.
The finite-cycle adapter supplies the branch balance theorem internally.
Its numerical rigidity argument is part of the imported proof.
-/
namespace IDT.QMClosure.InitialColumnOrderEchoSelection

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open TransparentFourthReflectionEcho
open InitialCountGeometry InitialPreparedCountOrder
open InitialEchoCoordinates InitialDyadicRelativeLanding

/-- The exact terminal package. Every quantifier ranges over actual initial
preparations. Canonical self-echo is an explicit supplied operation law. -/
structure Contract (W : P → ℝ) : Prop where
  normalized : W 1 = 1
  column : ∀ p, W (a * p) + W (b * p) = W p
  cIncreasing : ResponseIncreasing W c
  preparedOrder : PreparedCountOrder W
  selfEcho : ∀ p, W (p * J p) = W p ^ 2

variable {W : P → ℝ}

/-- Forget the supplied echo law while retaining the four common response laws. -/
def Contract.toBase (H : Contract W) : InitialColumnOrderReadoutCore.BaseContract W where
  normalized := H.normalized
  column := H.column
  cIncreasing := H.cIncreasing
  preparedOrder := H.preparedOrder

/-- The echo response law supplies squaring on each real-coordinate preparation. -/
theorem Contract.realAxisSquare (H : Contract W) :
    InitialColumnOrderReadoutCore.RealAxisSquare W := by
  intro p x hp
  have hh := H.selfEcho p
  change W (echo p) = W p ^ 2 at hh
  rw [echo_eq_square_of_real p x hp] at hh
  exact hh

/-- Vacuum zero follows from the conservation equation at actual zero. -/
theorem response_zero (H : Contract W) : W 0 = 0 := by
  exact InitialColumnOrderReadoutCore.response_zero H.toBase

theorem response_nonnegative (H : Contract W) (p : P) : 0 ≤ W p := by
  exact InitialColumnOrderReadoutCore.response_nonnegative H.toBase p

/-- Finite-cycle balance supplies the half laws after nonnegativity is proved. -/
theorem half_responses (H : Contract W) (p : P) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 := by
  exact InitialColumnOrderReadoutCore.half_responses H.toBase p

theorem h_response (H : Contract W) (p : P) : W (h * p) = W p / 4 := by
  exact InitialColumnOrderReadoutCore.h_response H.toBase p

theorem hInv_response (H : Contract W) (p : P) : W (hInv * p) = 4 * W p := by
  exact InitialColumnOrderReadoutCore.hInv_response H.toBase p

theorem h_power_response (H : Contract W) (k : ℕ) (p : P) :
    W (h ^ k * p) = W p / (4 : ℝ) ^ k := by
  exact InitialColumnOrderReadoutCore.h_power_response H.toBase k p

theorem hInv_power_response (H : Contract W) (k : ℕ) (p : P) :
    W (hInv ^ k * p) = (4 : ℝ) ^ k * W p := by
  exact InitialColumnOrderReadoutCore.hInv_power_response H.toBase k p

/-- The one-sided c premise has the orientation used by this doubling bound. -/
theorem doubling_lower (H : Contract W) (p : P) : 4 * W p ≤ W ((2 : P) * p) := by
  exact InitialColumnOrderReadoutCore.doubling_lower H.toBase p

/-- All positive-null responses vanish using column conservation and Sc+. -/
theorem null_response (H : Contract W) (p : P) (hp : E p = 0) : W p = 0 := by
  exact InitialColumnOrderReadoutCore.null_response H.toBase p hp

/-- Echo powers are derived on each real axis without assuming multiplicativity. -/
theorem real_axis_echo_powers (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (j : ℕ) : W (p ^ (2 ^ j)) = W p ^ (2 ^ j) := by
  exact InitialColumnOrderReadoutCore.real_axis_square_powers H.realAxisSquare p x hp j

/-- Pure numerical amplification. The upper bound is uniform in j, and there
is no regularity hypothesis on any response function. -/
private theorem le_of_dyadic_power_bound (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hbound : ∀ j : ℕ, A ^ (2 ^ j) ≤ C * B ^ (2 ^ j)) : A ≤ B := by
  exact InitialColumnOrderReadoutCore.le_of_dyadic_power_bound A B C hA hB hbound

private theorem four_pow (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  exact InitialColumnOrderReadoutCore.four_pow k

/-- One finite upper landing bounds every real-axis preparation in the annulus,
including arbitrary positive shadows, by the same real number W(3). -/
theorem annulus_upper (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 1 ≤ x) (hx2 : x ≤ 2) : W p ≤ W 3 := by
  exact InitialColumnOrderReadoutCore.annulus_upper H.toBase p x hp hx hx2

theorem annulus_constant_positive (H : Contract W) : 1 ≤ W 3 := by
  exact InitialColumnOrderReadoutCore.annulus_constant_positive H.toBase

/-- Binary normalization uses natural powers of h or its actual inverse.
The coarse upper factor remains W(3) for every positive axis amplitude. -/
theorem real_axis_coarse_upper (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p ≤ W 3 * x ^ 2 := by
  exact InitialColumnOrderReadoutCore.real_axis_coarse_upper H.toBase p x hp hx

/-- Echo amplification removes the fixed annulus constant. -/
theorem real_axis_upper (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p ≤ x ^ 2 := by
  exact InitialColumnOrderReadoutCore.real_axis_upper H.toBase H.realAxisSquare p x hp hx

/-- All preparations obey the norm upper bound before any integer calibration. -/
theorem global_upper (H : Contract W) (p : P) : W p ≤ N p := by
  by_cases hp : E p = 0
  · rw [null_response H p hp]
    exact normSq_nonnegative p
  have hN : 0 < N p := Complex.normSq_pos.mpr hp
  have hu := real_axis_upper H (echo p) (N p) (E_echo p) hN
  change W (p * J p) ≤ N p ^ 2 at hu
  rw [H.selfEcho] at hu
  have hW := response_nonnegative H p
  have hN0 := normSq_nonnegative p
  nlinarith

/-- Powers of scalar two are calibrated using doubling and the prior upper bound. -/
theorem powers_two_calibrated (H : Contract W) (k : ℕ) :
    W ((2 : P) ^ k) = (4 : ℝ) ^ k := by
  exact InitialColumnOrderReadoutCore.powers_two_calibrated H.toBase (global_upper H) k

/-- Positive scalar integers are calibrated by a finite binary sandwich at each
self-echo power. Raw mixed-zero calibration has not been assumed. -/
theorem naturals_calibrated (H : Contract W) (M : ℕ) : W (M : P) = (M : ℝ) ^ 2 := by
  exact InitialColumnOrderReadoutCore.naturals_calibrated H.toBase H.realAxisSquare (global_upper H) M

/-- A fixed 1/16 lower fraction is obtained by one finite relative landing.
The source response is calibrated before any c shift. -/
theorem real_axis_lower_fraction (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : x ^ 2 / 16 ≤ W p := by
  exact InitialColumnOrderReadoutCore.real_axis_lower_fraction H.toBase (naturals_calibrated H) p x hp hx

/-- Self-echo removes the fixed positive lower fraction. -/
theorem real_axis_selected (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p = x ^ 2 := by
  exact InitialColumnOrderReadoutCore.real_axis_selected H.toBase H.realAxisSquare (global_upper H) p x hp hx

/-- Conditional numerical selection for every literal initial preparation. -/
theorem selected (H : Contract W) (p : P) : W p = Complex.normSq (E p) := by
  by_cases hp : E p = 0
  · rw [null_response H p hp, hp]
    simp
  have hN : 0 < N p := Complex.normSq_pos.mpr hp
  have hh := real_axis_selected H (echo p) (N p) (E_echo p) hN
  change W (p * J p) = N p ^ 2 at hh
  rw [H.selfEcho] at hh
  have hn := response_nonnegative H p
  have hnorm := normSq_nonnegative p
  change W p = N p
  nlinarith

/-- The norm-square model inhabits the exact five-field package. -/
theorem norm_model : Contract N where
  normalized := InitialColumnOrderReadoutCore.norm_model.normalized
  column := InitialColumnOrderReadoutCore.norm_model.column
  cIncreasing := InitialColumnOrderReadoutCore.norm_model.cIncreasing
  preparedOrder := InitialColumnOrderReadoutCore.norm_model.preparedOrder
  selfEcho := by intro p; exact N_echo p

/-- Nonvacuous uniqueness of the numerical readout satisfying the package. -/
theorem exists_unique_response : ∃! W : P → ℝ, Contract W := by
  refine ⟨N, norm_model, ?_⟩
  intro W H
  exact funext (selected H)

/-- Global c equality is a consequence of selection. -/
theorem c_equality (H : Contract W) (p : P) : W (c * p) = W p := by
  rw [selected H, selected H, map_mul, evaluation_c, one_mul]

/-- Numerical multiplicativity is derived after the selection theorem. -/
theorem multiplicative (H : Contract W) (p r : P) : W (p * r) = W p * W r := by
  simp only [selected H, map_mul, Complex.normSq_mul]

/-- Null insertion does not change the selected response. -/
theorem null_insertion (H : Contract W) (p z : P) (hz : E z = 0) : W (p + z) = W p := by
  simp only [selected H, map_add, hz, add_zero]

/-- Prepared raw mixed differences vanish only as a derived identity. -/
theorem raw_mixed_zero (H : Contract W) (p : P) (n m : ℕ) :
    W (bag (n + 1) (m + 1) * p) + W (bag n m * p) =
      W (bag (n + 1) m * p) + W (bag n (m + 1) * p) := by
  have hn : ∀ u v : ℕ, W (bag u v * p) = (((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / 2) * N p := by
    intro u v
    rw [selected H]
    change InitialCountGeometry.normSq (bag u v * p) = _
    rw [InitialCountGeometry.normSq_mul, InitialCountGeometry.normSq_bag]
  rw [hn, hn, hn, hn]
  push_cast
  ring

end
end IDT.QMClosure.InitialColumnOrderEchoSelection
