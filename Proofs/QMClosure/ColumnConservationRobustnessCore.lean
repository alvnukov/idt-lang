import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
Real four-cycle estimates. All errors are unnormalized. In
particular, no division by a preparation reading occurs.
-/

namespace IDT.QMClosure.ColumnConservationRobustnessCore

noncomputable section

/-- A positive four-cycle with a relative and an absolute row-error budget. -/
structure FourCycle (c d : ℝ) where
  x : ℕ → ℝ
  y : ℕ → ℝ
  z : ℕ → ℝ
  t : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ x n ∧ 0 ≤ y n ∧ 0 ≤ z n ∧ 0 ≤ t n
  row_x : ∀ n, |x n - (2 * x (n + 1) + y (n + 1) + t (n + 1))| ≤ c * x n + d
  row_y : ∀ n, |y n - (2 * y (n + 1) + z (n + 1) + x (n + 1))| ≤ c * y n + d
  row_z : ∀ n, |z n - (2 * z (n + 1) + t (n + 1) + y (n + 1))| ≤ c * z n + d
  row_t : ∀ n, |t n - (2 * t (n + 1) + x (n + 1) + z (n + 1))| ≤ c * t n + d

namespace FourCycle

variable {c d : ℝ} (F : FourCycle c d)

def mass (n : ℕ) : ℝ := F.x n + F.y n + F.z n + F.t n

def difference (n : ℕ) : ℝ := F.y n - F.t n

theorem mass_nonnegative (n : ℕ) : 0 ≤ F.mass n := by
  obtain ⟨hx, hy, hz, ht⟩ := F.nonneg n
  dsimp [mass]
  linarith

theorem difference_le_mass (n : ℕ) : |F.difference n| ≤ F.mass n := by
  obtain ⟨hx, hy, hz, ht⟩ := F.nonneg n
  apply abs_le.mpr
  dsimp [difference, mass]
  constructor <;> linarith

theorem mass_step (n : ℕ) :
    4 * F.mass (n + 1) ≤ (1 + c) * F.mass n + 4 * d := by
  have hx := (abs_le.mp (F.row_x n)).1
  have hy := (abs_le.mp (F.row_y n)).1
  have hz := (abs_le.mp (F.row_z n)).1
  have ht := (abs_le.mp (F.row_t n)).1
  dsimp [mass]
  linarith

theorem difference_step (hc : 0 ≤ c) (n : ℕ) :
    |F.difference n| ≤ 2 * |F.difference (n + 1)| + c * F.mass n + 2 * d := by
  obtain ⟨hx, hy, hz, ht⟩ := F.nonneg n
  obtain ⟨hyl, hyu⟩ := abs_le.mp (F.row_y n)
  obtain ⟨htl, htu⟩ := abs_le.mp (F.row_t n)
  obtain ⟨hdl, hdu⟩ := abs_le.mp (le_refl |F.difference (n + 1)|)
  have hdrop : 0 ≤ c * (F.x n + F.z n) := mul_nonneg hc (by linarith)
  apply abs_le.mpr
  dsimp [difference, mass] at *
  constructor <;> linarith

end FourCycle

private theorem geometric_remainder {q s d r : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 ≤ s)
    (h : ∀ n : ℕ, d ≤ r + q ^ n * s) : d ≤ r := by
  by_contra hbad
  have hdr : 0 < d - r := by linarith
  have hqi : 1 < 1 / q := (one_lt_div hq0).mpr hq1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / (d - r)) hqi
  have hpow : 0 < q ^ n := pow_pos hq0 n
  have hlarge : s < (1 / q) ^ n * (d - r) := (div_lt_iff₀ hdr).mp hn
  have hid : (1 / q) ^ n * q ^ n = 1 := by
    rw [← mul_pow]
    field_simp [ne_of_gt hq0]
    simp
  have hsmall : q ^ n * s < d - r := by
    have hm := mul_lt_mul_of_pos_right hlarge hpow
    nlinarith [hid]
  linarith [h n]

/-- Relative row errors force a uniform opposite-slot bound at every depth.
The estimate includes zero total mass. -/
theorem relative_opposite_bound {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (F : FourCycle η 0) :
    |F.difference 0| ≤ (2 * η / (1 - η)) * F.mass 0 := by
  let q : ℝ := (1 + η) / 2
  let k : ℝ := (1 + η) / 4
  let R : ℝ := 2 * η / (1 - η)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hk0 : 0 ≤ k := by dsimp [k]; linarith
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (mul_nonneg (by norm_num) hη0) (by linarith)
  have hden : 1 - η ≠ 0 := ne_of_gt (by linarith)
  have hR : R * (1 - q) = η := by
    dsimp [R, q]
    field_simp [hden]
    <;> ring
  have hmass (n : ℕ) : F.mass n ≤ k ^ n * F.mass 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := F.mass_step n
      have hm := mul_le_mul_of_nonneg_left ih hk0
      dsimp [k] at *
      rw [pow_succ]
      nlinarith
  have hscale (n : ℕ) : (2 : ℝ) ^ n * k ^ n = q ^ n := by
    rw [← mul_pow]
    congr 1
    dsimp [k, q]
    ring
  have hfinite (n : ℕ) : |F.difference 0| ≤
      (2 : ℝ) ^ n * |F.difference n| + R * F.mass 0 * (1 - q ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := F.difference_step hη0 n
      have hp : 0 ≤ (2 : ℝ) ^ n := by positivity
      have hmul := mul_le_mul_of_nonneg_left hd hp
      have herr := mul_le_mul_of_nonneg_left (hmass n)
        (mul_nonneg hp hη0)
      have herr' : (2 : ℝ) ^ n * η * F.mass n ≤ η * q ^ n * F.mass 0 := by
        calc
          _ ≤ ((2 : ℝ) ^ n * η) * (k ^ n * F.mass 0) := herr
          _ = η * F.mass 0 * ((2 : ℝ) ^ n * k ^ n) := by ring
          _ = η * q ^ n * F.mass 0 := by rw [hscale n]; ring
      have hweighted : R * F.mass 0 * q ^ n * (1 - q) = η * F.mass 0 * q ^ n := by
        calc
          _ = (R * (1 - q)) * (F.mass 0 * q ^ n) := by ring
          _ = _ := by rw [hR]; ring
      rw [pow_succ, pow_succ]
      nlinarith
  have hbound (n : ℕ) : |F.difference 0| ≤ R * F.mass 0 + q ^ n * F.mass 0 := by
    have hd := mul_le_mul_of_nonneg_left (F.difference_le_mass n)
      (by positivity : 0 ≤ (2 : ℝ) ^ n)
    have hm : (2 : ℝ) ^ n * F.mass n ≤ q ^ n * F.mass 0 := by
      calc
        _ ≤ (2 : ℝ) ^ n * (k ^ n * F.mass 0) :=
          mul_le_mul_of_nonneg_left (hmass n) (by positivity)
        _ = q ^ n * F.mass 0 := by rw [← mul_assoc, hscale n]
    have hdrop : 0 ≤ R * F.mass 0 * q ^ n := by
      exact mul_nonneg (mul_nonneg hR0 (F.mass_nonnegative 0)) (le_of_lt (pow_pos hq0 n))
    nlinarith [hfinite n]
  exact geometric_remainder hq0 hq1 (F.mass_nonnegative 0) hbound

/-- The finite-depth absolute-error estimate keeps its depth index explicit. -/
theorem absolute_opposite_bound {e : ℝ} (he : 0 ≤ e)
    (F : FourCycle 0 (3 * e)) (n : ℕ) :
    |F.difference 0| ≤ (F.mass 0 - 4 * e) / (2 : ℝ) ^ n +
      10 * e * (2 : ℝ) ^ n - 6 * e := by
  have hmass (k : ℕ) : (4 : ℝ) ^ k * (F.mass k - 4 * e) ≤ F.mass 0 - 4 * e := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := F.mass_step k
      have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (4 : ℝ) ^ k)
      rw [pow_succ]
      nlinarith
  have hfinite (k : ℕ) : |F.difference 0| ≤
      (2 : ℝ) ^ k * |F.difference k| + 6 * e * ((2 : ℝ) ^ k - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hd := F.difference_step (by norm_num : (0 : ℝ) ≤ 0) k
      have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2 : ℝ) ^ k)
      rw [pow_succ]
      nlinarith
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      _ = ((2 : ℝ) * 2) ^ n := by norm_num
      _ = _ := by rw [mul_pow]; ring
  have hd := hfinite n
  have hab := mul_le_mul_of_nonneg_left (F.difference_le_mass n) hpow.le
  have hm := hmass n
  rw [hfour] at hm
  have hmul := mul_le_mul_of_nonneg_right (le_trans hd (by linarith :
      (2 : ℝ) ^ n * |F.difference n| + 6 * e * ((2 : ℝ) ^ n - 1) ≤
      (2 : ℝ) ^ n * F.mass n + 6 * e * ((2 : ℝ) ^ n - 1))) hpow.le
  have hclear : (|F.difference 0| - 10 * e * (2 : ℝ) ^ n + 6 * e) *
      (2 : ℝ) ^ n ≤ F.mass 0 - 4 * e := by nlinarith
  have hdiv := (le_div_iff₀ hpow).mpr hclear
  linarith

def relativeConstant (ε : ℝ) : ℝ :=
  (2 * (2 * ε + ε ^ 2) / (1 - (2 * ε + ε ^ 2))) * (1 + ε) ^ 4 +
    (1 + ε) ^ 4 - (1 + ε)

theorem relativeConstant_le_nine {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 20) :
    relativeConstant ε ≤ 9 * ε := by
  let η := 2 * ε + ε ^ 2
  have hsq : ε ^ 2 ≤ ε / 20 := by
    have h := mul_le_mul_of_nonneg_left hε1 hε0
    nlinarith
  have hcube : ε ^ 3 ≤ ε / 400 := by
    have h := mul_le_mul_of_nonneg_left hsq hε0
    nlinarith
  have hfour : ε ^ 4 ≤ ε / 8000 := by
    have h := mul_le_mul_of_nonneg_left hcube hε0
    nlinarith
  have hη : η ≤ 41 / 400 := by dsimp [η]; nlinarith
  have hηlin : η ≤ (41 / 20) * ε := by dsimp [η]; nlinarith
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hden : 0 < 1 - η := by linarith
  have hratio : 2 * η / (1 - η) ≤ (23 / 5) * ε := by
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hη hε0
    nlinarith
  have hp : (1 + ε) ^ 4 ≤ 49 / 40 := by
    have hb : (1 + ε) ^ 4 ≤ (21 / 20 : ℝ) ^ 4 := by gcongr <;> linarith
    norm_num at hb ⊢
    linarith
  have herr : (1 + ε) ^ 4 - (1 + ε) ≤ (10 / 3) * ε := by nlinarith
  have hr0 : 0 ≤ 2 * η / (1 - η) := by positivity
  have hm := mul_le_mul hratio hp (by positivity : 0 ≤ (1 + ε) ^ 4)
    (by positivity : 0 ≤ (23 / 5 : ℝ) * ε)
  dsimp [relativeConstant]
  change (2 * η / (1 - η)) * (1 + ε) ^ 4 + (1 + ε) ^ 4 - (1 + ε) ≤ 9 * ε
  nlinarith

end

end IDT.QMClosure.ColumnConservationRobustnessCore
