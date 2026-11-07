import Proofs.QMClosure.NativeAttenuationCircuit
import Mathlib.Analysis.Complex.Basic

/-!
# A balanced nonlinear complex mixer: algebraic core

The coefficients below are total, including on both coordinate axes. The
unnormalized square theorem freezes the coefficient through both turns. Only
the radius-preserving normalized update is asserted to square to negation.
The gate conserves the literal complex squared-norm readout and agrees with
the supplied native mixer on either vacuum input. These algebraic facts do not
assert linear dynamics, physical availability, or full quantum closure.
-/

namespace IDT.QMClosure.BalancedNonmedialMixerCore

noncomputable section

def R (s d : ℂ) : ℝ := Complex.normSq s + Complex.normSq d
def k (s d : ℂ) : ℝ := 1 + Complex.normSq s / R s d
def A (t : ℝ) : ℝ := (t + 1 / t) / 2
def B (t : ℝ) : ℝ := (1 / t - t) / 2
def q (s : ℂ) : ℂ := s / star s

def frozenTurn (t : ℝ) (s d : ℂ) : ℂ :=
  Complex.I * ((A t : ℂ) * d + (B t : ℂ) * q s * star d)

def turn (s d : ℂ) : ℂ := frozenTurn (k s d) s d
def rotated (s d : ℂ) : ℂ := (‖d‖ / ‖turn s d‖) • turn s d

def gate (p : ℂ × ℂ) : ℂ × ℂ :=
  ((p.1 + p.2 + rotated (p.1 + p.2) (p.1 - p.2)) / 2,
    (p.1 + p.2 - rotated (p.1 + p.2) (p.1 - p.2)) / 2)

theorem R_nonneg (s d : ℂ) : 0 ≤ R s d :=
  add_nonneg (Complex.normSq_nonneg s) (Complex.normSq_nonneg d)

theorem k_one_le (s d : ℂ) : 1 ≤ k s d := by
  have h := div_nonneg (Complex.normSq_nonneg s) (R_nonneg s d)
  dsimp [k]
  linarith

theorem k_pos (s d : ℂ) : 0 < k s d := lt_of_lt_of_le zero_lt_one (k_one_le s d)

theorem k_ne_zero (s d : ℂ) : k s d ≠ 0 := ne_of_gt (k_pos s d)

theorem k_le_two (s d : ℂ) : k s d ≤ 2 := by
  by_cases h : R s d = 0
  · simp [k, h]
  · have hr : 0 < R s d := lt_of_le_of_ne (R_nonneg s d) (Ne.symm h)
    have hs : Complex.normSq s ≤ R s d := by
      exact le_add_of_nonneg_right (Complex.normSq_nonneg d)
    have hh := (div_le_one hr).2 hs
    dsimp [k]
    linarith

@[simp] theorem k_zero_left (d : ℂ) : k 0 d = 1 := by simp [k]

theorem A_add_B (t : ℝ) : A t + B t = 1 / t := by unfold A B; ring

theorem A_sq_sub_B_sq (t : ℝ) (ht : t ≠ 0) : A t ^ 2 - B t ^ 2 = 1 := by
  unfold A B
  field_simp
  ring

theorem q_mul_star (s : ℂ) : q s * star s = s := by
  by_cases hs : s = 0
  · simp [q, hs]
  · exact div_mul_cancel₀ s (by simpa using hs)

theorem q_mul_star_q (s : ℂ) (hs : s ≠ 0) : q s * star (q s) = 1 := by
  simp only [q, Complex.star_def, map_div₀, Complex.conj_conj]
  have hc : (starRingEnd ℂ) s ≠ 0 := by simpa using hs
  field_simp [hs, hc]

@[simp] theorem frozenTurn_zero (t : ℝ) (s : ℂ) : frozenTurn t s 0 = 0 := by
  simp [frozenTurn]

@[simp] theorem frozenTurn_one (s z : ℂ) : frozenTurn 1 s z = Complex.I * z := by
  norm_num [frozenTurn, A, B]

theorem frozenTurn_real_smul (t r : ℝ) (s z : ℂ) :
    frozenTurn t s (r • z) = r • frozenTurn t s z := by
  simp only [frozenTurn, Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

theorem frozenTurn_square (t : ℝ) (s z : ℂ) (ht : t ≠ 0) (hs : s ≠ 0) :
    frozenTurn t s (frozenTurn t s z) = -z := by
  have hab : (A t : ℂ) ^ 2 - (B t : ℂ) ^ 2 = 1 := by
    exact_mod_cast A_sq_sub_B_sq t ht
  have hq := q_mul_star_q s hs
  calc
    frozenTurn t s (frozenTurn t s z) =
        -(((A t : ℂ) ^ 2 - (B t : ℂ) ^ 2 * (q s * star (q s))) * z) := by
      simp only [frozenTurn, Complex.star_def, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal,
        Complex.conj_I]
      ring_nf
      simp [Complex.I_sq]
    _ = -z := by rw [hq]; simp only [mul_one, hab, one_mul]

/-- The same actual coefficient is frozen in both applications, including at s=0. -/
theorem frozenTurn_square_actual (s d z : ℂ) :
    frozenTurn (k s d) s (frozenTurn (k s d) s z) = -z := by
  by_cases hs : s = 0
  · subst s
    simp only [k_zero_left, frozenTurn_one]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  · exact frozenTurn_square (k s d) s z (k_ne_zero s d) hs

@[simp] theorem turn_zero (s : ℂ) : turn s 0 = 0 := by simp [turn]

theorem turn_eq_zero_iff (s d : ℂ) : turn s d = 0 ↔ d = 0 := by
  constructor
  · intro h
    apply neg_eq_zero.mp
    calc
      -d = frozenTurn (k s d) s (turn s d) := (frozenTurn_square_actual s d d).symm
      _ = 0 := by rw [h, frozenTurn_zero]
  · rintro rfl
    exact turn_zero s

theorem real_smul_norm (r : ℝ) (z : ℂ) : ‖r • z‖ = |r| * ‖z‖ := by
  rw [Complex.real_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem real_smul_smul (r t : ℝ) (z : ℂ) : r • (t • z) = (r * t) • z := by
  simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

@[simp] theorem rotated_zero (s : ℂ) : rotated s 0 = 0 := by simp [rotated]

theorem rotated_norm (s d : ℂ) : ‖rotated s d‖ = ‖d‖ := by
  by_cases hd : d = 0
  · simp [hd]
  · have ht : ‖turn s d‖ ≠ 0 := norm_ne_zero_iff.mpr ((turn_eq_zero_iff s d).not.mpr hd)
    rw [rotated, real_smul_norm,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_mul_cancel₀ _ ht]

theorem rotated_normSq (s d : ℂ) : Complex.normSq (rotated s d) = Complex.normSq d := by
  simp only [Complex.normSq_eq_norm_sq, rotated_norm]

theorem R_rotated (s d : ℂ) : R s (rotated s d) = R s d := by
  simp only [R, rotated_normSq]

theorem k_rotated (s d : ℂ) : k s (rotated s d) = k s d := by
  simp only [k, R_rotated]

theorem turn_rotated (s d : ℂ) :
    turn s (rotated s d) = (‖d‖ / ‖turn s d‖) • (-d) := by
  unfold turn
  rw [k_rotated]
  change frozenTurn (k s d) s ((‖d‖ / ‖turn s d‖) • frozenTurn (k s d) s d) = _
  rw [frozenTurn_real_smul, frozenTurn_square_actual]
  rfl

theorem rotated_square (s d : ℂ) : rotated s (rotated s d) = -d := by
  by_cases hd : d = 0
  · simp [hd]
  · have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have ht : 0 < ‖turn s d‖ := norm_pos_iff.mpr ((turn_eq_zero_iff s d).not.mpr hd)
    have hc : 0 < ‖d‖ / ‖turn s d‖ := div_pos hn ht
    rw [rotated, turn_rotated, rotated_norm, real_smul_norm,
      abs_of_pos hc, norm_neg, real_smul_smul]
    have hh : ‖d‖ / (‖d‖ / ‖turn s d‖ * ‖d‖) * (‖d‖ / ‖turn s d‖) = 1 := by
      field_simp
    rw [hh, Complex.real_smul, Complex.ofReal_one, one_mul]

theorem k_neg_right (s d : ℂ) : k s (-d) = k s d := by simp [k, R]

theorem frozenTurn_neg (t : ℝ) (s d : ℂ) : frozenTurn t s (-d) = -frozenTurn t s d := by
  simp only [frozenTurn, star_neg, mul_neg]
  ring

theorem turn_neg (s d : ℂ) : turn s (-d) = -turn s d := by
  simp only [turn, k_neg_right, frozenTurn_neg]

theorem rotated_neg (s d : ℂ) : rotated s (-d) = -rotated s d := by
  simp only [rotated, norm_neg, turn_neg, Complex.real_smul, mul_neg]

theorem turn_self (s : ℂ) : turn s s = (1 / k s s) • (Complex.I * s) := by
  have hab : (A (k s s) : ℂ) + (B (k s s) : ℂ) = (1 / k s s : ℝ) := by
    exact_mod_cast A_add_B (k s s)
  calc
    turn s s = Complex.I * (((A (k s s) : ℂ) + (B (k s s) : ℂ)) * s) := by
      unfold turn frozenTurn
      rw [mul_assoc (B (k s s) : ℂ), q_mul_star]
      ring
    _ = (1 / k s s) • (Complex.I * s) := by rw [hab, Complex.real_smul]; ring

theorem rotated_self (s : ℂ) : rotated s s = Complex.I * s := by
  by_cases hs : s = 0
  · simp [hs]
  · have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
    have hk := k_ne_zero s s
    have hc : 0 ≤ 1 / k s s := le_of_lt (one_div_pos.mpr (k_pos s s))
    rw [rotated, turn_self, real_smul_norm, abs_of_nonneg hc,
      norm_mul, Complex.norm_I, one_mul, real_smul_smul]
    have hh : ‖s‖ / (1 / k s s * ‖s‖) * (1 / k s s) = 1 := by field_simp
    rw [hh, Complex.real_smul, Complex.ofReal_one, one_mul]

theorem gate_sum (x y : ℂ) : (gate (x, y)).1 + (gate (x, y)).2 = x + y := by
  dsimp [gate]
  ring

theorem gate_difference (x y : ℂ) :
    (gate (x, y)).1 - (gate (x, y)).2 = rotated (x + y) (x - y) := by
  dsimp [gate]
  ring

theorem gate_transparent (z : ℂ) : gate (z, z) = (z, z) := by
  apply Prod.ext <;> simp [gate]

theorem gate_square (p : ℂ × ℂ) : gate (gate p) = p.swap := by
  change (((gate p).1 + (gate p).2 + rotated ((gate p).1 + (gate p).2)
      ((gate p).1 - (gate p).2)) / 2,
    ((gate p).1 + (gate p).2 - rotated ((gate p).1 + (gate p).2)
      ((gate p).1 - (gate p).2)) / 2) = p.swap
  rw [gate_sum p.1 p.2, gate_difference p.1 p.2, rotated_square]
  apply Prod.ext <;> dsimp <;> ring

theorem gate_conserves (x y : ℂ) :
    Complex.normSq (gate (x, y)).1 + Complex.normSq (gate (x, y)).2 =
      Complex.normSq x + Complex.normSq y := by
  have h := rotated_normSq (x + y) (x - y)
  norm_num [Complex.normSq_apply] at h
  norm_num [gate, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  nlinarith

theorem gate_vacuum_right (z : ℂ) :
    gate (z, 0) = (((1 + Complex.I) / 2) * z, ((1 - Complex.I) / 2) * z) := by
  simp only [gate, add_zero, sub_zero, rotated_self]
  apply Prod.ext <;> dsimp <;> ring

theorem gate_vacuum_left (z : ℂ) :
    gate (0, z) = (((1 - Complex.I) / 2) * z, ((1 + Complex.I) / 2) * z) := by
  simp only [gate, zero_add, zero_sub, rotated_neg, rotated_self]
  apply Prod.ext <;> dsimp <;> ring

theorem native_vacuum_right (z : ℂ) :
    gate (z, 0) = NativeMixerEventConeExclusion.mixer (z, 0) := by
  rw [gate_vacuum_right]
  apply Prod.ext
  · simpa [NativeAttenuationCircuit.a] using (NativeAttenuationCircuit.mixer_fst z 0).symm
  · simpa [NativeAttenuationCircuit.b] using (NativeAttenuationCircuit.mixer_snd z 0).symm

theorem native_vacuum_left (z : ℂ) :
    gate (0, z) = NativeMixerEventConeExclusion.mixer (0, z) := by
  rw [gate_vacuum_left]
  apply Prod.ext
  · simpa [NativeAttenuationCircuit.b] using (NativeAttenuationCircuit.mixer_fst 0 z).symm
  · simpa [NativeAttenuationCircuit.a] using (NativeAttenuationCircuit.mixer_snd 0 z).symm

end

end IDT.QMClosure.BalancedNonmedialMixerCore
