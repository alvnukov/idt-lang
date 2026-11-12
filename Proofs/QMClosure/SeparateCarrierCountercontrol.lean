import Proofs.QMClosure.AtomicitySpectralBoundary
import Mathlib.Analysis.Normed.Operator.Prod

namespace IDT.QMClosure.SeparateCarrierCountercontrol

/-!
Two positive complementary diagonal operators have small exact power rates on
different nonzero invariant axes. Those axes have zero intersection, and neither
operator has the same small rate on the whole ambient space. This supplies a
countercontrol to inferring a common nonzero carrier from separate endpoint
bounds. It supplies no physical process family or general quotient obstruction.
-/

abbrev E := ℝ × ℝ

noncomputable def q : ℝ := 1 / 4
noncomputable def c : ℝ := Real.sqrt 3 / 2
noncomputable def a : ℝ := c - q

theorem q_positive : 0 < q := by norm_num [q]

theorem a_gt_q : q < a := by
  have h := AtomicitySpectralBoundary.spinor_calibration.2.2
  dsimp [a, c, q]
  linarith

theorem a_positive : 0 < a := lt_trans q_positive a_gt_q

noncomputable def diagonal (u v : ℝ) : E →L[ℝ] E :=
  (u • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (v • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem diagonal_apply (u v : ℝ) (x : E) :
    diagonal u v x = (u * x.1, v * x.2) := rfl

theorem diagonal_pow_apply (u v : ℝ) (n : ℕ) (x : E) :
    (diagonal u v ^ n) x = (u ^ n * x.1, v ^ n * x.2) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih, diagonal_apply]
    simp only [pow_succ]
    apply Prod.ext <;> dsimp <;> ring

noncomputable def A : E →L[ℝ] E := diagonal a q
noncomputable def B : E →L[ℝ] E := diagonal q a

def verticalU (x : E) : Prop := x.1 = 0
def horizontalV (x : E) : Prop := x.2 = 0

theorem vertical_nonzero_witness : verticalU (0, 1) ∧ ((0, 1) : E) ≠ 0 := by
  norm_num [verticalU]

theorem horizontal_nonzero_witness : horizontalV (1, 0) ∧ ((1, 0) : E) ≠ 0 := by
  norm_num [horizontalV]

theorem complementary : A + B = c • ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro x
  change (a * x.1 + q * x.1, q * x.2 + a * x.2) = (c * x.1, c * x.2)
  dsimp [a]
  apply Prod.ext <;> dsimp <;> ring

theorem A_preserves_vertical (x : E) (hx : verticalU x) : verticalU (A x) := by
  change a * x.1 = 0
  rw [hx, mul_zero]

theorem B_preserves_horizontal (x : E) (hx : horizontalV x) : horizontalV (B x) := by
  change a * x.2 = 0
  rw [hx, mul_zero]

theorem A_vertical_power_norm (x : E) (hx : verticalU x) (n : ℕ) :
    ‖(A ^ n) x‖ = q ^ n * ‖x‖ := by
  have hpow : (A ^ n) x = q ^ n • x := by
    rw [A, diagonal_pow_apply]
    apply Prod.ext
    · change a ^ n * x.1 = q ^ n * x.1
      change x.1 = 0 at hx
      simp [hx]
    · rfl
  rw [hpow, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg q_positive.le n)]

theorem B_horizontal_power_norm (x : E) (hx : horizontalV x) (n : ℕ) :
    ‖(B ^ n) x‖ = q ^ n * ‖x‖ := by
  have hpow : (B ^ n) x = q ^ n • x := by
    rw [B, diagonal_pow_apply]
    apply Prod.ext
    · rfl
    · change a ^ n * x.2 = q ^ n * x.2
      change x.2 = 0 at hx
      simp [hx]
  rw [hpow, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg q_positive.le n)]

theorem axes_intersection_zero (x : E) (hu : verticalU x) (hv : horizontalV x) :
    x = 0 := by
  exact Prod.ext hu hv

theorem no_common_nonzero_axis : ¬ ∃ x : E, x ≠ 0 ∧ verticalU x ∧ horizontalV x := by
  rintro ⟨x, hx, hu, hv⟩
  exact hx (axes_intersection_zero x hu hv)

def standardOrthant (x : E) : Prop := 0 ≤ x.1 ∧ 0 ≤ x.2

theorem A_preserves_standardOrthant (x : E) (hx : standardOrthant x) :
    standardOrthant (A x) := by
  exact ⟨mul_nonneg a_positive.le hx.1, mul_nonneg q_positive.le hx.2⟩

theorem B_preserves_standardOrthant (x : E) (hx : standardOrthant x) :
    standardOrthant (B x) := by
  exact ⟨mul_nonneg q_positive.le hx.1, mul_nonneg a_positive.le hx.2⟩

theorem A_high_axis_power_norm (n : ℕ) : ‖(A ^ n) (1, 0)‖ = a ^ n := by
  rw [A, diagonal_pow_apply]
  simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg a_positive.le]
  exact pow_nonneg a_positive.le n

theorem B_high_axis_power_norm (n : ℕ) : ‖(B ^ n) (0, 1)‖ = a ^ n := by
  rw [B, diagonal_pow_apply]
  simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg a_positive.le]
  exact pow_nonneg a_positive.le n

theorem A_no_global_q_envelope : ¬ ∃ C : ℝ, ∀ n : ℕ, ‖A ^ n‖ ≤ C * q ^ n := by
  rintro ⟨C, hC⟩
  apply AtomicitySpectralBoundary.power_envelope_impossible q_positive a_gt_q
  intro n
  calc
    a ^ n = ‖(A ^ n) (1, 0)‖ := (A_high_axis_power_norm n).symm
    _ ≤ ‖A ^ n‖ * ‖((1, 0) : E)‖ := (A ^ n).le_opNorm _
    _ = ‖A ^ n‖ := by norm_num [Prod.norm_def]
    _ ≤ C * q ^ n := hC n

theorem B_no_global_q_envelope : ¬ ∃ C : ℝ, ∀ n : ℕ, ‖B ^ n‖ ≤ C * q ^ n := by
  rintro ⟨C, hC⟩
  apply AtomicitySpectralBoundary.power_envelope_impossible q_positive a_gt_q
  intro n
  calc
    a ^ n = ‖(B ^ n) (0, 1)‖ := (B_high_axis_power_norm n).symm
    _ ≤ ‖B ^ n‖ * ‖((0, 1) : E)‖ := (B ^ n).le_opNorm _
    _ = ‖B ^ n‖ := by norm_num [Prod.norm_def]
    _ ≤ C * q ^ n := hC n

end IDT.QMClosure.SeparateCarrierCountercontrol
