import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation

/-!
# Positive finite-cycle balance in the literal initial presentation

The only coefficient inputs are the two relations defining
the initial presentation. The response inputs are nonnegativity, the first
column equation, and invariance under c=2ab. All response assumptions are
explicit theorem parameters. Real Archimedean order is used on readouts.
-/

namespace IDT.QMClosure.TransparentFourthColumnBalance

noncomputable section

open TransparentFourthInitialHistoryPresentation

abbrev P := Presentation

def bInv : P := (2 : P) * a + e
def half : P := a * b + T ^ 2
def rho : P := a * bInv
def c : P := (2 : P) * (a * b)

theorem b_mul_bInv : b * bInv = 1 := by
  exact inverse_contexts.bRight

theorem bInv_mul_b : bInv * b = 1 := by
  exact inverse_contexts.bLeft

theorem two_mul_half : (2 : P) * half = 1 := by
  exact inverse_contexts.twoRight

theorem rho_mul_b : rho * b = a := by
  rw [rho, mul_assoc, bInv_mul_b, mul_one]

theorem rho_four : rho ^ 4 = 1 := by
  calc
    rho ^ 4 = a ^ 4 * bInv ^ 4 := by rw [rho, mul_pow]
    _ = b ^ 4 * bInv ^ 4 := by rw [fourth_rejoin]
    _ = (b * bInv) ^ 4 := (mul_pow _ _ _).symm
    _ = 1 := by rw [b_mul_bInv, one_pow]

theorem bInv_eq_one_add_rho : bInv = 1 + rho := by
  calc
    bInv = (a + b) * bInv := by rw [transparent, one_mul]
    _ = rho + 1 := by rw [add_mul, b_mul_bInv]; rfl
    _ = 1 + rho := add_comm _ _

theorem c_mul_bInv_sq : c * bInv ^ 2 = (2 : P) * rho := by
  calc
    c * bInv ^ 2 = (2 : P) * rho * (b * bInv) := by
      dsimp [c, rho]
      ring
    _ = (2 : P) * rho := by rw [b_mul_bInv, mul_one]

theorem rho_wrap_one (p : P) : rho * (rho ^ 3 * p) = p := by
  calc
    rho * (rho ^ 3 * p) = rho ^ 4 * p := by ring
    _ = p := by rw [rho_four, one_mul]

theorem rho_wrap_two (p : P) : rho ^ 2 * (rho ^ 3 * p) = rho * p := by
  calc
    rho ^ 2 * (rho ^ 3 * p) = rho * (rho ^ 4 * p) := by ring
    _ = rho * p := by rw [rho_four, one_mul]

def FirstColumn (W : P → ℝ) : Prop :=
  ∀ p, W (a * p) + W (b * p) = W p

def ContrastInvariant (W : P → ℝ) : Prop :=
  ∀ p, W (c * p) = W p

theorem inverse_column (W : P → ℝ) (hcolumn : FirstColumn W) (p : P) :
    W (bInv * p) = W p + W (rho * p) := by
  have hh := hcolumn (bInv * p)
  rw [← mul_assoc a bInv p, ← mul_assoc b bInv p, b_mul_bInv, one_mul] at hh
  change W (rho * p) + W p = W (bInv * p) at hh
  linarith

theorem inverse_column_twice (W : P → ℝ) (hcolumn : FirstColumn W) (p : P) :
    W (bInv ^ 2 * p) = W p + 2 * W (rho * p) + W (rho ^ 2 * p) := by
  have h0 := inverse_column W hcolumn p
  have h1 := inverse_column W hcolumn (bInv * p)
  have h2 := inverse_column W hcolumn (rho * p)
  rw [show rho * (bInv * p) = bInv * (rho * p) by ring] at h1
  rw [show bInv * (bInv * p) = bInv ^ 2 * p by ring] at h1
  rw [show rho * (rho * p) = rho ^ 2 * p by ring] at h2
  linarith

theorem contrast_inverse_row (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    W ((2 : P) * (rho * p)) =
      W p + 2 * W (rho * p) + W (rho ^ 2 * p) := by
  have hh := hcontrast (bInv ^ 2 * p)
  rw [← mul_assoc c (bInv ^ 2) p, c_mul_bInv_sq, mul_assoc] at hh
  exact hh.trans (inverse_column_twice W hcolumn p)

theorem double_row (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    W ((2 : P) * p) = W (rho ^ 3 * p) + 2 * W p + W (rho * p) := by
  have hh := contrast_inverse_row W hcolumn hcontrast (rho ^ 3 * p)
  simp only [rho_wrap_one, rho_wrap_two] at hh
  exact hh

def orbitSum (W : P → ℝ) (p : P) : ℝ :=
  W p + W (rho * p) + W (rho ^ 2 * p) + W (rho ^ 3 * p)

def differenceZero (W : P → ℝ) (p : P) : ℝ := W p - W (rho ^ 2 * p)
def differenceOne (W : P → ℝ) (p : P) : ℝ := W (rho * p) - W (rho ^ 3 * p)
def alternating (W : P → ℝ) (p : P) : ℝ :=
  W p - W (rho * p) + W (rho ^ 2 * p) - W (rho ^ 3 * p)

theorem four_double_rows (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    W ((2 : P) * p) = W (rho ^ 3 * p) + 2 * W p + W (rho * p) ∧
    W (rho * ((2 : P) * p)) = W p + 2 * W (rho * p) + W (rho ^ 2 * p) ∧
    W (rho ^ 2 * ((2 : P) * p)) =
      W (rho * p) + 2 * W (rho ^ 2 * p) + W (rho ^ 3 * p) ∧
    W (rho ^ 3 * ((2 : P) * p)) =
      W (rho ^ 2 * p) + 2 * W (rho ^ 3 * p) + W p := by
  have h0 := double_row W hcolumn hcontrast p
  have h1 := double_row W hcolumn hcontrast (rho * p)
  have h2 := double_row W hcolumn hcontrast (rho ^ 2 * p)
  have h3 := double_row W hcolumn hcontrast (rho ^ 3 * p)
  rw [show (2 : P) * (rho * p) = rho * ((2 : P) * p) by ring,
    show rho ^ 3 * (rho * p) = p by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using rho_wrap_one p,
    show rho * (rho * p) = rho ^ 2 * p by ring] at h1
  rw [show (2 : P) * (rho ^ 2 * p) = rho ^ 2 * ((2 : P) * p) by ring,
    show rho ^ 3 * (rho ^ 2 * p) = rho * p by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using rho_wrap_two p,
    show rho * (rho ^ 2 * p) = rho ^ 3 * p by ring] at h2
  rw [show (2 : P) * (rho ^ 3 * p) = rho ^ 3 * ((2 : P) * p) by ring,
    show rho ^ 3 * (rho ^ 3 * p) = rho ^ 2 * p by
      calc
        rho ^ 3 * (rho ^ 3 * p) = rho ^ 2 * (rho ^ 4 * p) := by ring
        _ = rho ^ 2 * p := by rw [rho_four, one_mul],
    rho_wrap_one] at h3
  exact ⟨h0, h1, h2, h3⟩

theorem mode_recurrences (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    orbitSum W ((2 : P) * p) = 4 * orbitSum W p ∧
    differenceZero W ((2 : P) * p) = 2 * differenceZero W p ∧
    differenceOne W ((2 : P) * p) = 2 * differenceOne W p ∧
    alternating W ((2 : P) * p) = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := four_double_rows W hcolumn hcontrast p
  dsimp [orbitSum, differenceZero, differenceOne, alternating]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem alternating_zero (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    alternating W p = 0 := by
  have hh := (mode_recurrences W hcolumn hcontrast (half * p)).2.2.2
  rw [← mul_assoc (2 : P) half p, two_mul_half, one_mul] at hh
  exact hh

theorem difference_bounds (W : P → ℝ) (hnonneg : ∀ p, 0 ≤ W p) (p : P) :
    |differenceZero W p| ≤ orbitSum W p ∧
      |differenceOne W p| ≤ orbitSum W p := by
  have h0 := hnonneg p
  have h1 := hnonneg (rho * p)
  have h2 := hnonneg (rho ^ 2 * p)
  have h3 := hnonneg (rho ^ 3 * p)
  dsimp [differenceZero, differenceOne, orbitSum]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem nat_le_two_pow_real (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      rw [Nat.cast_succ, pow_succ]
      linarith

/-- Fixed-preparation finite-sum control eliminates each expanding difference. -/
theorem vanishing_difference (S D : P → ℝ)
    (hS : ∀ p, S ((2 : P) * p) = 4 * S p)
    (hD : ∀ p, D ((2 : P) * p) = 2 * D p)
    (hbound : ∀ p, |D p| ≤ S p) (p : P) : D p = 0 := by
  have hamplified : ∀ n : ℕ, ∀ q : P, (2 : ℝ) ^ n * |D q| ≤ S q := by
    intro n
    induction n with
    | zero => simpa using hbound
    | succ n ih =>
        intro q
        have hs := hS (half * q)
        have hd := hD (half * q)
        rw [← mul_assoc (2 : P) half q, two_mul_half, one_mul] at hs hd
        have habs : |D q| = 2 * |D (half * q)| := by
          rw [hd, abs_mul]
          norm_num
        calc
          (2 : ℝ) ^ (n + 1) * |D q| =
              4 * ((2 : ℝ) ^ n * |D (half * q)|) := by rw [pow_succ, habs]; ring
          _ ≤ 4 * S (half * q) := mul_le_mul_of_nonneg_left (ih (half * q)) (by norm_num)
          _ = S q := hs.symm
  by_contra hzero
  have hdpos : 0 < |D p| := abs_pos.mpr hzero
  obtain ⟨n, hn⟩ := exists_nat_gt (S p / |D p|)
  have hlt : S p < (n : ℝ) * |D p| := (div_lt_iff₀ hdpos).mp hn
  have hle : (n : ℝ) * |D p| ≤ (2 : ℝ) ^ n * |D p| :=
    mul_le_mul_of_nonneg_right (nat_le_two_pow_real n) (abs_nonneg _)
  exact (not_lt_of_ge ((hamplified n p).trans' hle)) hlt

theorem orbit_balance (W : P → ℝ) (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    W (rho * p) = W p ∧ W (rho ^ 2 * p) = W p ∧ W (rho ^ 3 * p) = W p := by
  have hS : ∀ q, orbitSum W ((2 : P) * q) = 4 * orbitSum W q :=
    fun q => (mode_recurrences W hcolumn hcontrast q).1
  have hD0 : ∀ q, differenceZero W ((2 : P) * q) = 2 * differenceZero W q :=
    fun q => (mode_recurrences W hcolumn hcontrast q).2.1
  have hD1 : ∀ q, differenceOne W ((2 : P) * q) = 2 * differenceOne W q :=
    fun q => (mode_recurrences W hcolumn hcontrast q).2.2.1
  have hd0 := vanishing_difference (orbitSum W) (differenceZero W) hS hD0
    (fun q => (difference_bounds W hnonneg q).1) p
  have hd1 := vanishing_difference (orbitSum W) (differenceOne W) hS hD1
    (fun q => (difference_bounds W hnonneg q).2) p
  have he := alternating_zero W hcolumn hcontrast p
  dsimp [differenceZero, differenceOne, alternating] at hd0 hd1 he
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The supplied column splits equally and natural doubling has readout gain four. -/
theorem column_balance_and_double_gain (W : P → ℝ) (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (p : P) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 ∧
      W ((2 : P) * p) = 4 * W p := by
  have hab := (orbit_balance W hnonneg hcolumn hcontrast (b * p)).1
  rw [← mul_assoc rho b p, rho_mul_b] at hab
  have hc := hcolumn p
  obtain ⟨hr1, _, hr3⟩ := orbit_balance W hnonneg hcolumn hcontrast p
  have hdouble := double_row W hcolumn hcontrast p
  exact ⟨by linarith, by linarith, by linarith⟩

def bag (m n : ℕ) (p : P) : P := ((m : P) * a + (n : P) * b) * p

def PreparedCountOrder (W : P → ℝ) : Prop :=
  ∀ (p : P) (m n m' n' : ℕ), m ≤ m' → n ≤ n' →
    W (bag m n p) ≤ W (bag m' n' p)

theorem response_zero (W : P → ℝ) (hcolumn : FirstColumn W) : W 0 = 0 := by
  have hh := hcolumn 0
  simp only [mul_zero] at hh
  linarith

theorem nonnegative_of_zero_one_count_order (W : P → ℝ)
    (hcolumn : FirstColumn W)
    (horder : ∀ p, W (bag 0 0 p) ≤ W (bag 1 1 p)) : ∀ p, 0 ≤ W p := by
  intro p
  have hh := horder p
  simpa only [bag, Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul,
    transparent, response_zero W hcolumn] using hh

theorem nonnegative_of_prepared_count_order (W : P → ℝ)
    (hcolumn : FirstColumn W) (horder : PreparedCountOrder W) : ∀ p, 0 ≤ W p := by
  apply nonnegative_of_zero_one_count_order W hcolumn
  intro p
  exact horder p 0 0 1 1 (by omega) (by omega)

theorem prepared_column_balance_and_double_gain (W : P → ℝ)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W)
    (horder : PreparedCountOrder W) (p : P) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 ∧
      W ((2 : P) * p) = 4 * W p := by
  exact column_balance_and_double_gain W
    (nonnegative_of_prepared_count_order W hcolumn horder) hcolumn hcontrast p

theorem double_unit_value (W : P → ℝ) (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : FirstColumn W) (hcontrast : ContrastInvariant W) (hunit : W 1 = 1) :
    W (2 : P) = 4 := by
  have hh := (column_balance_and_double_gain W hnonneg hcolumn hcontrast 1).2.2
  simpa only [mul_one, hunit] using hh

end

end IDT.QMClosure.TransparentFourthColumnBalance
