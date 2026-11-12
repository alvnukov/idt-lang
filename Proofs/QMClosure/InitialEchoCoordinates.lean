import Proofs.QMClosure.InitialCountGeometry
import Proofs.QMClosure.TransparentFourthReflectionEcho

/-!
Pure coordinates of the canonical initial-carrier generator swap and echo.
This module has no response contract and no physical operational premise.
-/
namespace IDT.QMClosure.InitialEchoCoordinates

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open TransparentFourthReflectionEcho
open InitialCountGeometry

abbrev E := complexEvaluation
abbrev q := realShadow
abbrev N := InitialCountGeometry.normSq

/-- The two presentation homomorphisms agree on both generators. -/
theorem E_comp_J : E.comp J = (starRingEnd ℂ).comp E := by
  have htwo : (starRingEnd ℂ) 2 = 2 := by
    calc
      (starRingEnd ℂ) 2 = (starRingEnd ℂ) (1 + 1) := by norm_num
      _ = 1 + 1 := by rw [map_add, map_one]
      _ = 2 := by norm_num
  apply hom_ext
  · change E (J a) = (starRingEnd ℂ) (E a)
    rw [J_a, evaluation_b, evaluation_a]
    simp [complexA, complexB, map_div, map_add, sub_eq_add_neg, htwo]
  · change E (J b) = (starRingEnd ℂ) (E b)
    rw [J_b, evaluation_a, evaluation_b]
    simp [complexA, complexB, map_div, map_sub, sub_eq_add_neg, htwo]

@[simp] theorem E_J (p : P) : E (J p) = (starRingEnd ℂ) (E p) :=
  DFunLike.congr_fun E_comp_J p

@[simp] theorem q_J (p : P) : q (J p) = q p := by
  change (shadow (J p) : ℝ) = (shadow p : ℝ)
  rw [shadow_J]

theorem q_zero_iff (p : P) : q p = 0 ↔ p = 0 := by
  change (shadow p : ℝ) = 0 ↔ p = 0
  rw [NNReal.coe_eq_zero, shadow_zero_iff]

theorem q_nonnegative (p : P) : 0 ≤ q p := by
  change (0 : ℝ) ≤ (shadow p : ℝ)
  exact (shadow p).property

theorem q_positive (p : P) (hp : p ≠ 0) : 0 < q p := by
  change (0 : ℝ) < (shadow p : ℝ)
  exact NNReal.coe_pos.mpr (shadow_positive p hp)

@[simp] theorem E_echo (p : P) : E (echo p) = ((N p : ℝ) : ℂ) := by
  rw [echo, map_mul, E_J]
  apply Complex.ext <;>
    simp [N, InitialCountGeometry.normSq, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem q_echo (p : P) : q (echo p) = q p ^ 2 := by
  simp only [echo, map_mul, q_J, pow_two]

@[simp] theorem N_J (p : P) : N (J p) = N p := by
  simp [N, InitialCountGeometry.normSq, Complex.normSq_conj]

@[simp] theorem N_echo (p : P) : N (echo p) = N p ^ 2 := by
  simp only [echo, normSq_mul, N_J, pow_two]

/-- Real-axis fixedness is reflected using the complex coordinate and shadow. -/
theorem J_fixed_of_real (p : P) (x : ℝ) (hp : E p = (x : ℂ)) : J p = p := by
  apply eq_of_combined_coordinates
  · rw [E_J, hp]
    simp
  · exact q_J p

theorem echo_eq_square_of_real (p : P) (x : ℝ) (hp : E p = (x : ℂ)) :
    echo p = p ^ 2 := by
  rw [echo, J_fixed_of_real p x hp, pow_two]

/-- Powers stay on the real axis without any response-level assumption. -/
theorem E_pow_of_real (p : P) (x : ℝ) (hp : E p = (x : ℂ)) (n : ℕ) :
    E (p ^ n) = ((x ^ n : ℝ) : ℂ) := by
  rw [map_pow, hp, Complex.ofReal_pow]

theorem N_of_real (p : P) (x : ℝ) (hp : E p = (x : ℂ)) : N p = x ^ 2 := by
  simp [N, InitialCountGeometry.normSq, hp, Complex.normSq_apply, pow_two]

/-- The positive finite inverse of h is an actual initial preparation. -/
def hInv : P := aInv * bInv

theorem h_mul_hInv : h * hInv = 1 := by
  calc
    h * hInv = (a * aInv) * (b * bInv) := by dsimp [h, hInv]; ring
    _ = 1 := by rw [a_mul_aInv, b_mul_bInv]; simp

theorem hInv_mul_h : hInv * h = 1 := by rw [mul_comm, h_mul_hInv]

@[simp] theorem E_hInv : E hInv = (2 : ℂ) := by
  have he := congrArg E h_mul_hInv
  rw [map_mul, evaluation_h, map_one] at he
  have hh := congrArg Complex.re he
  have hi := congrArg Complex.im he
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im] at hh hi ⊢ <;> linarith

@[simp] theorem q_hInv : q hInv = 4 := by
  have he := congrArg q h_mul_hInv
  rw [map_mul, shadow_h, map_one] at he
  linarith

/-- All three null products agree only after checking both coordinates. -/
theorem null_products (p : P) (hp : E p = 0) :
    a * p = c * p ∧ b * p = c * p := by
  constructor <;> apply eq_of_combined_coordinates
  · simp only [map_mul, hp, mul_zero]
  · rw [map_mul, map_mul, realShadow_a, shadow_c]
  · simp only [map_mul, hp, mul_zero]
  · rw [map_mul, map_mul, realShadow_b, shadow_c]

end
end IDT.QMClosure.InitialEchoCoordinates
