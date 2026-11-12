import Proofs.QMClosure.InitialEchoCoordinates
import Proofs.QMClosure.InitialPreparedCountOrder
import Mathlib.Data.Real.Sqrt

/-!
An initial-carrier countermodel with a finite witness to the specified replacement of universal
serial c-increase by unit c-calibration together with all complex-null silence.
The coordinate readout is continuous on ℝ × ℝ. No topology on the initial
carrier and no physical repetition interpretation are supplied here.
-/
namespace IDT.QMClosure.InitialSquareFiniteCalibrationCountermodel

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry
open InitialEchoCoordinates
open InitialPreparedCountOrder

/-- Polynomial maximum underlying the readout. -/
def squareKernel (x y : ℝ) : ℝ := max (x ^ 2) (x * y)

/-- Continuous algebraic-coordinate formula. -/
def coordinateReadout (z : ℝ × ℝ) : ℝ := Real.sqrt (squareKernel z.1 z.2)

/-- The squared countermodel readout on the literal initial carrier. -/
def G (p : P) : ℝ := squareKernel (N p) (q p)

/-- The countermodel readout on the literal initial carrier. -/
def F (p : P) : ℝ := Real.sqrt (G p)

theorem squareKernel_nonnegative (x y : ℝ) : 0 ≤ squareKernel x y :=
  (sq_nonneg x).trans (le_max_left _ _)

theorem F_nonnegative (p : P) : 0 ≤ F p := Real.sqrt_nonneg _

theorem F_sq (p : P) : F p ^ 2 = G p :=
  Real.sq_sqrt (squareKernel_nonnegative _ _)

/-- Continuity concerns precisely the explicitly displayed coordinate domain. -/
theorem coordinateReadout_continuous : Continuous coordinateReadout := by
  exact Real.continuous_sqrt.comp
    ((continuous_fst.pow 2).max (continuous_fst.mul continuous_snd))

theorem F_coordinate_formula (p : P) : F p = coordinateReadout (N p, q p) := rfl

private theorem squareKernel_half (x y : ℝ) :
    squareKernel (x / 2) (y / 2) = squareKernel x y / 4 := by
  have he : squareKernel (x / 2) (y / 2) = max (x ^ 2 / 4) (x * y / 4) := by
    unfold squareKernel
    congr 1 <;> ring
  rw [he]
  unfold squareKernel
  by_cases h : x ^ 2 ≤ x * y
  · have hh : x ^ 2 / 4 ≤ x * y / 4 := by linarith
    rw [max_eq_right h, max_eq_right hh]
  · have h' : x * y ≤ x ^ 2 := le_of_not_ge h
    have hh : x * y / 4 ≤ x ^ 2 / 4 := by linarith
    rw [max_eq_left h', max_eq_left hh]

private theorem max_sq_of_nonnegative {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max (x ^ 2) (y ^ 2) = max x y ^ 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith : x ^ 2 ≤ y ^ 2)]
  · rw [max_eq_left h, max_eq_left (by nlinarith : y ^ 2 ≤ x ^ 2)]

private theorem squareKernel_square (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    squareKernel (x ^ 2) (y ^ 2) = squareKernel x y ^ 2 := by
  calc
    squareKernel (x ^ 2) (y ^ 2) = max ((x ^ 2) ^ 2) ((x * y) ^ 2) := by
      unfold squareKernel
      congr 1 <;> ring
    _ = squareKernel x y ^ 2 :=
      max_sq_of_nonnegative (sq_nonneg x) (mul_nonneg hx hy)

private theorem squareKernel_mono {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxx : x ≤ x') (hyy : y ≤ y') :
    squareKernel x y ≤ squareKernel x' y' := by
  apply max_le_max
  · simpa only [pow_two] using mul_le_mul hxx hxx hx (hx.trans hxx)
  · exact mul_le_mul hxx hyy hy (hx.trans hxx)

private theorem N_a : N a = 1 / 2 := by
  norm_num [N, normSq, evaluation_a, complexA, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

private theorem N_b : N b = 1 / 2 := by
  norm_num [N, normSq, evaluation_b, complexB, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

private theorem N_one : N (1 : P) = 1 := by simp [N, normSq]

private theorem N_c : N c = 1 := by simp [N, normSq, evaluation_c]

private theorem G_a_mul (p : P) : G (a * p) = G p / 4 := by
  change squareKernel (normSq (a * p)) (q (a * p)) = G p / 4
  rw [normSq_mul]
  change squareKernel (N a * N p) (q (a * p)) = G p / 4
  rw [N_a, map_mul, realShadow_a]
  simpa only [G, div_eq_mul_inv, one_mul, mul_comm] using squareKernel_half (N p) (q p)

private theorem G_b_mul (p : P) : G (b * p) = G p / 4 := by
  change squareKernel (normSq (b * p)) (q (b * p)) = G p / 4
  rw [normSq_mul]
  change squareKernel (N b * N p) (q (b * p)) = G p / 4
  rw [N_b, map_mul, realShadow_b]
  simpa only [G, div_eq_mul_inv, one_mul, mul_comm] using squareKernel_half (N p) (q p)

/-- Both literal generator columns halve this response. -/
theorem F_a_mul (p : P) : F (a * p) = F p / 2 := by
  apply (sq_eq_sq₀ (F_nonnegative (a * p))
    (div_nonneg (F_nonnegative p) (by norm_num))).mp
  rw [F_sq, G_a_mul, div_pow, F_sq]
  norm_num

theorem F_b_mul (p : P) : F (b * p) = F p / 2 := by
  apply (sq_eq_sq₀ (F_nonnegative (b * p))
    (div_nonneg (F_nonnegative p) (by norm_num))).mp
  rw [F_sq, G_b_mul, div_pow, F_sq]
  norm_num

theorem F_column (p : P) : F (a * p) + F (b * p) = F p := by
  rw [F_a_mul, F_b_mul]
  ring

/-- Algebraic same-program squaring, with every initial preparation quantified. -/
theorem F_self_square (p : P) : F (p ^ 2) = F p ^ 2 := by
  have hN : N (p ^ 2) = N p ^ 2 := by
    simpa only [pow_two] using normSq_mul p p
  have hq : q (p ^ 2) = q p ^ 2 := map_pow q p 2
  have hG : G (p ^ 2) = G p ^ 2 := by
    unfold G
    rw [hN, hq]
    exact squareKernel_square _ _ (normSq_nonnegative p) (q_nonnegative p)
  have hGnonneg : 0 ≤ G p := squareKernel_nonnegative _ _
  rw [F, hG, Real.sqrt_sq hGnonneg, F_sq]

/-- Both coordinate factors increase with either natural raw count. -/
theorem F_preparedCountOrder : PreparedCountOrder F := by
  intro p n m n' m' hn hm
  have hnR : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA : ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 ≤
      ((n' : ℝ) ^ 2 + (m' : ℝ) ^ 2) / 2 := by
    have hns : (n : ℝ) ^ 2 ≤ (n' : ℝ) ^ 2 := by nlinarith
    have hms : (m : ℝ) ^ 2 ≤ (m' : ℝ) ^ 2 := by nlinarith
    linarith
  have hB : ((n : ℝ) + (m : ℝ)) / 2 ≤ ((n' : ℝ) + (m' : ℝ)) / 2 := by
    linarith
  apply Real.sqrt_le_sqrt
  apply squareKernel_mono (normSq_nonnegative _) (q_nonnegative _)
  · change normSq (bag n m * p) ≤ normSq (bag n' m' * p)
    rw [normSq_mul, normSq_mul, normSq_bag, normSq_bag]
    exact mul_le_mul_of_nonneg_right hA (normSq_nonnegative p)
  · change realShadow (bag n m * p) ≤ realShadow (bag n' m' * p)
    rw [map_mul, map_mul, bag_shadow, bag_shadow]
    exact mul_le_mul_of_nonneg_right hB (q_nonnegative p)

/-- Silence holds for every complex-null initial preparation. -/
theorem F_null_silent (p : P) (hp : E p = 0) : F p = 0 := by
  have hN : N p = 0 := by simp [N, normSq, hp]
  simp [F, G, squareKernel, hN]

@[simp] theorem F_zero : F (0 : P) = 0 := F_null_silent 0 (map_zero E)

@[simp] theorem F_one : F (1 : P) = 1 := by
  norm_num [F, G, squareKernel, N_one]

/-- This calibration is even equality, hence satisfies the proposed inequality. -/
@[simp] theorem F_c : F c = 1 := by
  norm_num [F, G, squareKernel, N_c, shadow_c]

theorem unit_c_calibration : 1 ≤ F c := by rw [F_c]

/-- A literal positive finite preparation used by the witness. -/
def witness : P := 1 + e

private theorem E_e : E e = 0 := by
  rw [e, T, map_mul, map_add, map_pow, map_pow, map_ofNat, evaluation_a, evaluation_b]
  apply Complex.ext <;>
    norm_num [complexA, complexB, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, pow_two]

private theorem q_e : q e = 1 := by
  change (shadow e : ℝ) = 1
  rw [shadow_e]
  norm_num

theorem witness_coordinates : E witness = 1 ∧ q witness = 2 := by
  constructor
  · simp [witness, E_e]
  · norm_num [witness, q_e]

theorem witness_normSq : N witness = 1 := by
  simp [N, normSq, witness_coordinates.1]

theorem c_witness_coordinates : E (c * witness) = 1 ∧ q (c * witness) = 1 := by
  constructor
  · rw [map_mul, evaluation_c, witness_coordinates.1, one_mul]
  · rw [map_mul, shadow_c, witness_coordinates.2]
    norm_num

theorem F_witness : F witness = Real.sqrt 2 := by
  norm_num [F, G, squareKernel, witness_normSq, witness_coordinates.2]

theorem F_c_witness : F (c * witness) = 1 := by
  have hN : N (c * witness) = 1 := by
    simp [N, normSq, c_witness_coordinates.1]
  norm_num [F, G, squareKernel, hN, c_witness_coordinates.2]

theorem F_e : F e = 0 := F_null_silent e E_e

theorem F_c_strict_failure : F (c * witness) < F witness := by
  rw [F_c_witness, F_witness]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem F_not_cIncreasing : ¬ ResponseIncreasing F c := by
  intro hc
  exact (not_le_of_gt F_c_strict_failure) (hc witness)

theorem F_ne_normSq : F ≠ normSq := by
  intro he
  have hw : F witness = 1 := by rw [he]; exact witness_normSq
  have hh := F_c_strict_failure
  rw [F_c_witness, hw] at hh
  exact (lt_irrefl (1 : ℝ)) hh

/-- Null insertion changes the response despite silence of the inserted null. -/
theorem F_null_insertion_failure :
    E e = 0 ∧ F e = 0 ∧ F (1 + e) > F (1 : P) := by
  refine ⟨E_e, F_e, ?_⟩
  change F witness > F (1 : P)
  rw [F_one, ← F_c_witness]
  exact F_c_strict_failure

theorem F_not_multiplicative : ¬ ∀ p r : P, F (p * r) = F p * F r := by
  intro hm
  have he := hm c witness
  rw [F_c, one_mul] at he
  exact (ne_of_lt F_c_strict_failure) he

/-- The specified replacement premises do not select the norm-square response. -/
theorem calibration_replacement_does_not_select :
    ¬ (∀ W : P → ℝ,
      W 0 = 0 → W 1 = 1 →
      (∀ p, W (a * p) + W (b * p) = W p) →
      PreparedCountOrder W →
      (∀ p, W (p ^ 2) = W p ^ 2) →
      1 ≤ W c →
      (∀ p, E p = 0 → W p = 0) →
      W = normSq) := by
  intro h
  exact F_ne_normSq (h F F_zero F_one F_column F_preparedCountOrder
    F_self_square unit_c_calibration F_null_silent)

end
end IDT.QMClosure.InitialSquareFiniteCalibrationCountermodel
