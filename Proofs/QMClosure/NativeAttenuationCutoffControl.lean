import Proofs.QMClosure.NativeAttenuationReadout

/-!
# Every finite attenuation cutoff misses a calibrated countermodel

For every depth cutoff `M`, a rational-linear readout is calibrated on both
basis effects and the identity, and takes values in `[0, 1]` on all four
displayed attenuation families through depth `M`. Its real cross-coordinate
is nevertheless strictly positive, and the next depth of `E6` has a strictly
negative value. This is a parametric finite-cutoff negative control, not a
claim of positivity on all native circuit events. Availability of any displayed
coordinate as a physical event remains a separate conditional bridge.

No probability actualization, density-matrix theorem, Born derivation, or QM
closure follows from this control.
-/

namespace IDT.QMClosure.NativeAttenuationCutoffControl

noncomputable section

open NativeWireEffectSpan NativeAttenuationReadout

/-- The nonzero cross-coordinate is chosen separately for each finite cutoff. -/
def readout (M : ℕ) : V 2 →ₗ[ℚ] ℝ where
  toFun v := (v (.inl 0) : ℝ) + (t M / 16 : ℚ) * (v (.inr (pair01, false)) : ℝ)
  map_add' v w := by simp; ring
  map_smul' a v := by simp [Rat.smul_def]; ring

theorem readout_P0 (M : ℕ) : readout M (P 0) = 1 := by
  norm_num [readout, P, Pi.single_apply, Sum.inr_ne_inl]

theorem readout_P1 (M : ℕ) : readout M (P 1) = 0 := by
  norm_num [readout, P, Pi.single_apply, Sum.inr_ne_inl]

theorem readout_X (M : ℕ) : readout M (X pair01) = (t M : ℝ) / 16 := by
  simp [readout, X]

theorem readout_Y (M : ℕ) : readout M (Y pair01) = 0 := by
  simp [readout, Y]

theorem calibration (M : ℕ) :
    readout M (P 0) = 1 ∧ readout M (P 1) = 0 ∧
      readout M (identity 2) = 1 := by
  refine ⟨readout_P0 M, readout_P1 M, ?_⟩
  simp [identity, Fin.sum_univ_two, readout_P0, readout_P1]

theorem cross_coordinate_positive (M : ℕ) : 0 < readout M (X pair01) := by
  rw [readout_X]
  exact div_pos (by exact_mod_cast t_pos M) (by norm_num)

theorem readout_E0 (M m : ℕ) :
    readout M (E0 pair01 m) = (t m : ℝ) ^ 2 / 2 := by
  simp [E0, map_add, map_smul, Rat.smul_def, readout_P0, readout_P1,
    readout_Y, show pair01.val.1 = (0 : Fin 2) from rfl,
    show pair01.val.2 = (1 : Fin 2) from rfl]

theorem readout_E2 (M m : ℕ) :
    readout M (E2 pair01 m) =
      (t m : ℝ) ^ 2 / 8 + (t M : ℝ) * (t m : ℝ) / 64 := by
  simp [E2, map_add, map_smul, Rat.smul_def, readout_P0, readout_P1,
    readout_X, show pair01.val.1 = (0 : Fin 2) from rfl,
    show pair01.val.2 = (1 : Fin 2) from rfl]
  ring

theorem readout_E4 (M m : ℕ) :
    readout M (E4 pair01 m) = (t m : ℝ) ^ 2 / 32 := by
  simp [E4, map_add, map_sub, map_smul, Rat.smul_def, readout_P0,
    readout_P1, readout_Y, show pair01.val.1 = (0 : Fin 2) from rfl,
    show pair01.val.2 = (1 : Fin 2) from rfl]

theorem readout_E6 (M m : ℕ) :
    readout M (E6 pair01 m) =
      (t m : ℝ) ^ 2 / 128 - (t M : ℝ) * (t m : ℝ) / 256 := by
  simp [E6, map_add, map_sub, map_smul, Rat.smul_def, readout_P0,
    readout_P1, readout_X, show pair01.val.1 = (0 : Fin 2) from rfl,
    show pair01.val.2 = (1 : Fin 2) from rfl]
  ring

theorem t_succ (m : ℕ) : t (m + 1) = t m / 16 := by
  simp [t, pow_succ, div_eq_mul_inv]

theorem t_antitone {m M : ℕ} (h : m ≤ M) : t M ≤ t m := by
  induction M, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    calc
      t (k + 1) = t k / 16 := t_succ k
      _ ≤ t k := by have := t_pos k; linarith
      _ ≤ t m := ih

theorem t_le_one (m : ℕ) : t m ≤ 1 := by
  simpa [t] using t_antitone (Nat.zero_le m)

/-- Explicit lower margin at every tested depth. -/
theorem cutoff_E6_margin {M m : ℕ} (h : m ≤ M) :
    (t m : ℝ) ^ 2 / 256 ≤ readout M (E6 pair01 m) := by
  rw [readout_E6]
  have hs : 0 ≤ (t m : ℝ) := le_of_lt (by exact_mod_cast t_pos m)
  have hrs : (t M : ℝ) ≤ (t m : ℝ) := by exact_mod_cast t_antitone h
  have := mul_le_mul_of_nonneg_right hrs hs
  nlinarith

/-- All four displayed families, including their upper probability bound, pass
at each depth through the cutoff. This does not quantify over all circuits. -/
theorem cutoff_bounds {M m : ℕ} (h : m ≤ M) :
    (0 ≤ readout M (E0 pair01 m) ∧ readout M (E0 pair01 m) ≤ 1) ∧
    (0 ≤ readout M (E2 pair01 m) ∧ readout M (E2 pair01 m) ≤ 1) ∧
    (0 ≤ readout M (E4 pair01 m) ∧ readout M (E4 pair01 m) ≤ 1) ∧
    (0 ≤ readout M (E6 pair01 m) ∧ readout M (E6 pair01 m) ≤ 1) := by
  have hs : 0 ≤ (t m : ℝ) := le_of_lt (by exact_mod_cast t_pos m)
  have hr : 0 ≤ (t M : ℝ) := le_of_lt (by exact_mod_cast t_pos M)
  have hs1 : (t m : ℝ) ≤ 1 := by exact_mod_cast t_le_one m
  have hr1 : (t M : ℝ) ≤ 1 := by exact_mod_cast t_le_one M
  have hss : (t m : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hrs0 := mul_nonneg hr hs
  have hrs1 : (t M : ℝ) * (t m : ℝ) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hr1 hs]
  have hmargin := cutoff_E6_margin h
  rw [readout_E6] at hmargin
  rw [readout_E0, readout_E2, readout_E4, readout_E6]
  constructor
  · constructor <;> nlinarith [sq_nonneg (t m : ℝ)]
  constructor
  · constructor <;> nlinarith [sq_nonneg (t m : ℝ)]
  constructor <;> constructor <;> nlinarith [sq_nonneg (t m : ℝ)]

/-- Exact arithmetic: the next `E6` test detects the cutoff countermodel. -/
theorem next_depth_value (M : ℕ) :
    readout M (E6 pair01 (M + 1)) = -7 * (t M : ℝ) ^ 2 / 32768 := by
  rw [readout_E6, t_succ]
  push_cast
  ring

theorem next_depth_negative (M : ℕ) :
    readout M (E6 pair01 (M + 1)) < 0 := by
  rw [next_depth_value]
  have hp : 0 < (t M : ℝ) := by exact_mod_cast t_pos M
  nlinarith [sq_pos_of_pos hp]

/-- A universal parametric countermodel for every finite cutoff. -/
theorem finite_cutoff_countermodel (M : ℕ) :
    readout M (P 0) = 1 ∧ readout M (P 1) = 0 ∧
    readout M (identity 2) = 1 ∧ 0 < readout M (X pair01) ∧
    (∀ m ≤ M,
      (0 ≤ readout M (E0 pair01 m) ∧ readout M (E0 pair01 m) ≤ 1) ∧
      (0 ≤ readout M (E2 pair01 m) ∧ readout M (E2 pair01 m) ≤ 1) ∧
      (0 ≤ readout M (E4 pair01 m) ∧ readout M (E4 pair01 m) ≤ 1) ∧
      (0 ≤ readout M (E6 pair01 m) ∧ readout M (E6 pair01 m) ≤ 1)) ∧
    readout M (E6 pair01 (M + 1)) < 0 :=
  ⟨(calibration M).1, (calibration M).2.1, (calibration M).2.2,
    cross_coordinate_positive M, fun _ h => cutoff_bounds h, next_depth_negative M⟩

end

end IDT.QMClosure.NativeAttenuationCutoffControl
