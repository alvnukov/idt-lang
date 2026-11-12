import Proofs.QMClosure.InitialColumnOrderReadoutCore
import Proofs.QMClosure.InitialCountSectorBounds

/-!
Conditional numerical readout selection on the literal initial P4 carrier.

The four-law base contract is supplemented by one universal numerical law,
W (p ^ 2) = W p ^ 2, for every actual initial preparation p. Repeated squares
have an interpretation limited to finite syntactic serial uses of a preparation.

The imported coordinates include algebraic reflection. The supplied fifth
response premise is self-squaring. Paired echo is recovered as a numerical
consequence after selection. The conclusion concerns this fixed carrier and
its coordinate norm-square.
-/
namespace IDT.QMClosure.InitialSquareReadoutSelection

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open TransparentFourthReflectionEcho
open InitialCountGeometry InitialPreparedCountOrder
open InitialEchoCoordinates

/-- The four base laws and universal numerical self-squaring. -/
structure Contract (W : P → ℝ) : Prop extends InitialColumnOrderReadoutCore.BaseContract W where
  selfSquare : ∀ p, W (p ^ 2) = W p ^ 2

variable {W : P → ℝ}

/-- Universal self-squaring supplies the core's restricted real-axis premise. -/
theorem real_axis_square (H : Contract W) : InitialColumnOrderReadoutCore.RealAxisSquare W := by
  intro p x hp
  exact H.selfSquare p

/-- Every finite repeated-square exponent has the corresponding response power. -/
theorem square_powers (H : Contract W) (p : P) (j : ℕ) :
    W (p ^ (2 ^ j)) = W p ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hh := H.selfSquare (p ^ (2 ^ j))
      simp only [pow_succ]
      rw [pow_mul, hh, ih, pow_mul]

/-- Coordinate norm-square respects every natural serial power independently
of the response contract. -/
theorem norm_power (p : P) (n : ℕ) : N (p ^ n) = N p ^ n := by
  induction n with
  | zero => simp [N, InitialCountGeometry.normSq]
  | succ n ih =>
      calc
        N (p ^ (n + 1)) = N (p ^ n * p) := by rw [pow_succ]
        _ = N (p ^ n) * N p := InitialCountGeometry.normSq_mul _ _
        _ = N p ^ (n + 1) := by rw [ih, pow_succ]

/-- The fixed sector upper constant disappears under universal self-squaring. -/
theorem global_upper (H : Contract W) (p : P) : W p ≤ N p := by
  by_cases hp : E p = 0
  · rw [InitialColumnOrderReadoutCore.null_response H.toBaseContract p hp]
    exact InitialCountGeometry.normSq_nonnegative p
  have hN : 0 < N p := Complex.normSq_pos.mpr hp
  apply InitialColumnOrderReadoutCore.le_of_dyadic_power_bound (W p) (N p) 256
    (InitialColumnOrderReadoutCore.response_nonnegative H.toBaseContract p) hN
  intro j
  have hu := InitialCountSectorBounds.global_coarse_upper H.toBaseContract
    (InitialColumnOrderReadoutCore.real_axis_upper H.toBaseContract (real_axis_square H))
    (p ^ (2 ^ j))
  rw [square_powers H, norm_power] at hu
  exact hu

/-- Exact positive-real calibration follows after the global upper bound. -/
theorem real_axis_selected (H : Contract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p = x ^ 2 :=
  InitialColumnOrderReadoutCore.real_axis_selected H.toBaseContract (real_axis_square H)
    (global_upper H) p x hp hx

/-- Exact positive-real calibration supplies the fixed global lower fraction. -/
theorem global_lower_fraction (H : Contract W) (p : P) : N p / 16 ≤ W p :=
  InitialCountSectorBounds.global_coarse_lower H.toBaseContract (real_axis_selected H) p

/-- The five supplied laws select coordinate norm-square on every preparation. -/
theorem selected (H : Contract W) (p : P) : W p = N p := by
  by_cases hp : E p = 0
  · rw [InitialColumnOrderReadoutCore.null_response H.toBaseContract p hp]
    simp [N, InitialCountGeometry.normSq, hp]
  have hN : 0 < N p := Complex.normSq_pos.mpr hp
  have hfrac := global_lower_fraction H p
  have hW : 0 < W p := by linarith
  apply le_antisymm (global_upper H p)
  apply InitialColumnOrderReadoutCore.le_of_dyadic_power_bound (N p) (W p) 16
    (InitialCountGeometry.normSq_nonnegative p) hW
  intro j
  have hh := global_lower_fraction H (p ^ (2 ^ j))
  rw [norm_power, square_powers H] at hh
  linarith

/-- Coordinate norm-square inhabits the exact supplied contract. -/
theorem norm_model : Contract N where
  toBaseContract := InitialColumnOrderReadoutCore.norm_model
  selfSquare := by
    intro p
    exact norm_power p 2

/-- The numerical response satisfying the supplied contract exists uniquely. -/
theorem exists_unique_response : ∃! W : P → ℝ, Contract W := by
  refine ⟨N, norm_model, ?_⟩
  intro W H
  exact funext (selected H)

/-- The paired-echo numerical law follows from the selected response. -/
theorem paired_echo (H : Contract W) (p : P) : W (p * J p) = W p ^ 2 := by
  change W (echo p) = W p ^ 2
  rw [selected H, selected H, N_echo]

/-- Global c equality follows from the selected response. -/
theorem c_equality (H : Contract W) (p : P) : W (c * p) = W p := by
  simp only [selected H, N, InitialCountGeometry.normSq, map_mul, evaluation_c, one_mul]

/-- Numerical multiplicativity follows from the selected response. -/
theorem multiplicative (H : Contract W) (p r : P) : W (p * r) = W p * W r := by
  rw [selected H, selected H, selected H]
  exact InitialCountGeometry.normSq_mul p r

/-- Coordinate-null insertion preserves the selected response. -/
theorem null_insertion (H : Contract W) (p z : P) (hz : E z = 0) : W (p + z) = W p := by
  simp only [selected H, N, InitialCountGeometry.normSq, map_add, hz, add_zero]

end
end IDT.QMClosure.InitialSquareReadoutSelection
