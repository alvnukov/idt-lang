import Proofs.QMClosure.EighthRejoinInitialPresentation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Concrete eighth-rejoin readout countermodels

The three complex maps are concrete models of the literal initial semiring.
Their use supplies neither a faithful representation nor physical selection.
The minimum response W and support response V have explicit universal contracts
and short separating witnesses. No higher-rejoin family, limit, topology,
continuity, or completed quantum reconstruction is asserted here.
-/

namespace IDT.QMClosure.EighthRejoinReadoutCountermodels

noncomputable section

open EighthRejoinInitialPresentation
open scoped ComplexConjugate

abbrev P := Presentation

def r : ℝ := Real.sqrt 2

theorem r_sq : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem r_cube : r ^ 3 = 2 * r := by
  calc
    r ^ 3 = r ^ 2 * r := by ring
    _ = 2 * r := by rw [r_sq]

theorem r_fourth : r ^ 4 = 4 := by
  calc
    r ^ 4 = (r ^ 2) ^ 2 := by ring
    _ = 4 := by rw [r_sq]; norm_num

/-- Explicit real coordinates keep the only radical visible. -/
def u (t : ℝ) : ℂ := ⟨1 / 2, t / 2⟩

def v (t : ℝ) : ℂ := ⟨1 / 2, -t / 2⟩

theorem uv_sum (t : ℝ) : u t + v t = 1 := by
  apply Complex.ext <;> simp [u, v] <;> ring

theorem uv_fourth_sum (t : ℝ) :
    u t ^ 4 + v t ^ 4 = (((t ^ 4 - 6 * t ^ 2 + 1) / 8 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [u, v, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem t1_quartic : (1 - r) ^ 4 - 6 * (1 - r) ^ 2 + 1 = 0 := by
  nlinarith [r_sq, r_cube, r_fourth]

theorem t3_quartic : (-r - 1) ^ 4 - 6 * (-r - 1) ^ 2 + 1 = 0 := by
  nlinarith [r_sq, r_cube, r_fourth]

theorem eighth_of_fourth_sum_zero (t : ℝ)
    (ht : t ^ 4 - 6 * t ^ 2 + 1 = 0) : u t ^ 8 = v t ^ 8 := by
  have hz : u t ^ 4 + v t ^ 4 = 0 := by rw [uv_fourth_sum, ht]; norm_num
  have hfour : u t ^ 4 = -(v t ^ 4) := eq_neg_of_add_eq_zero_left hz
  calc
    u t ^ 8 = (u t ^ 4) ^ 2 := by ring
    _ = (-(v t ^ 4)) ^ 2 := by rw [hfour]
    _ = v t ^ 8 := by ring

theorem gaussian_eighth : u 1 ^ 8 = v 1 ^ 8 := by
  apply Complex.ext <;> norm_num [u, v, pow_succ, Complex.mul_re, Complex.mul_im]

def evalC (t : ℝ) (height : u t ^ 8 = v t ^ 8) : P →+* ℂ :=
  eval (u t) (v t) (uv_sum t) height

@[simp] theorem evalC_a (t : ℝ) (height : u t ^ 8 = v t ^ 8) :
    evalC t height a = u t := by simp [evalC]

@[simp] theorem evalC_b (t : ℝ) (height : u t ^ 8 = v t ^ 8) :
    evalC t height b = v t := by simp [evalC]

/-- Conjugation transport is proved as equality of maps from the initial object. -/
theorem evalC_swap (t : ℝ) (height : u t ^ 8 = v t ^ 8) (p : P) :
    evalC t height (J p) = conj (evalC t height p) := by
  have hm : (evalC t height).comp J =
      (starRingEnd ℂ).comp (evalC t height) := by
    apply hom_ext
    · apply Complex.ext <;> simp [u, v]
      ring
    · apply Complex.ext <;> simp [u, v]
      ring
  exact DFunLike.congr_fun hm p

def E2 : P →+* ℂ := evalC 1 gaussian_eighth

def E1 : P →+* ℂ := evalC (1 - r) (eighth_of_fourth_sum_zero _ t1_quartic)

def E3 : P →+* ℂ := evalC (-r - 1) (eighth_of_fourth_sum_zero _ t3_quartic)

@[simp] theorem E2_a : E2 a = u 1 := by simp [E2]
@[simp] theorem E2_b : E2 b = v 1 := by simp [E2]
@[simp] theorem E1_a : E1 a = u (1 - r) := by simp [E1]
@[simp] theorem E1_b : E1 b = v (1 - r) := by simp [E1]
@[simp] theorem E3_a : E3 a = u (-r - 1) := by simp [E3]
@[simp] theorem E3_b : E3 b = v (-r - 1) := by simp [E3]

def X (p : P) : ℝ := Complex.normSq (E2 p)

def Y (p : P) : ℝ := Complex.normSq (E1 p) * Complex.normSq (E3 p)

@[simp] theorem X_zero : X 0 = 0 := by simp [X]
@[simp] theorem Y_zero : Y 0 = 0 := by simp [Y]
@[simp] theorem X_one : X 1 = 1 := by simp [X]
@[simp] theorem Y_one : Y 1 = 1 := by simp [Y]

theorem X_nonnegative (p : P) : 0 ≤ X p := Complex.normSq_nonneg _

theorem Y_nonnegative (p : P) : 0 ≤ Y p :=
  mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem X_mul (p q : P) : X (p * q) = X p * X q := by
  simp [X, Complex.normSq_mul]

theorem Y_mul (p q : P) : Y (p * q) = Y p * Y q := by
  simp only [Y, map_mul]
  ring

theorem X_pow (p : P) (k : ℕ) : X (p ^ k) = X p ^ k := by
  simp [X, map_pow]

theorem Y_pow (p : P) (k : ℕ) : Y (p ^ k) = Y p ^ k := by
  simp only [Y, map_pow]
  exact (mul_pow _ _ _).symm

theorem X_swap (p : P) : X (J p) = X p := by
  simp [X, E2, evalC_swap, Complex.normSq_conj]

theorem Y_swap (p : P) : Y (J p) = Y p := by
  simp [Y, E1, E3, evalC_swap, Complex.normSq_conj]

/-- A real-coordinate identity before specializing to natural counts. -/
theorem normSq_linear (n m t : ℝ) :
    Complex.normSq ((n : ℂ) * u t + (m : ℂ) * v t) =
      ((n + m) ^ 2 + t ^ 2 * (n - m) ^ 2) / 4 := by
  simp [Complex.normSq_apply, u, v, Complex.mul_re, Complex.mul_im]
  ring

theorem quartic_norm_product (n m : ℝ) :
    Complex.normSq ((n : ℂ) * u (1 - r) + (m : ℂ) * v (1 - r)) *
      Complex.normSq ((n : ℂ) * u (-r - 1) + (m : ℂ) * v (-r - 1)) =
      (n ^ 4 + m ^ 4) / 2 := by
  rw [normSq_linear, normSq_linear]
  ring_nf
  simp only [r_sq, r_fourth]
  ring

def A (n m : ℕ) : ℝ := ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2

def Q (n m : ℕ) : ℝ := ((n : ℝ) ^ 4 + (m : ℝ) ^ 4) / 2

theorem X_B (n m : ℕ) : X (B n m) = A n m := by
  simp only [X, B, map_add, map_mul, map_natCast, E2_a, E2_b]
  change Complex.normSq (((n : ℝ) : ℂ) * u 1 + ((m : ℝ) : ℂ) * v 1) = A n m
  rw [normSq_linear]
  dsimp [A]
  ring

theorem Y_B (n m : ℕ) : Y (B n m) = Q n m := by
  simp only [Y, B, map_add, map_mul, map_natCast, E1_a, E1_b, E3_a, E3_b]
  exact quartic_norm_product _ _

theorem X_nat (n : ℕ) : X (n : P) = (n : ℝ) ^ 2 := by simp [X, pow_two]

theorem Y_nat (n : ℕ) : Y (n : P) = (n : ℝ) ^ 4 := by
  simp [Y]
  ring

@[simp] theorem X_two : X (2 : P) = 4 := by
  have he := X_nat 2
  norm_num at he
  exact he
@[simp] theorem Y_two : Y (2 : P) = 16 := by
  have he := Y_nat 2
  norm_num at he
  exact he

@[simp] theorem X_a : X a = 1 / 2 := by norm_num [X, u]
@[simp] theorem X_b : X b = 1 / 2 := by norm_num [X, v]

@[simp] theorem Y_a : Y a = 1 / 2 := by
  simp only [Y, E1_a, E3_a, Complex.normSq_mk, u]
  ring_nf
  simp only [r_fourth]
  norm_num

@[simp] theorem Y_b : Y b = 1 / 2 := by
  simp only [Y, E1_b, E3_b, Complex.normSq_mk, v]
  ring_nf
  simp only [r_fourth]
  norm_num

@[simp] theorem X_h : X h = 1 / 4 := by norm_num [h, X_mul]
@[simp] theorem Y_h : Y h = 1 / 4 := by norm_num [h, Y_mul]
@[simp] theorem X_c : X c = 1 := by norm_num [c, X_mul, X_nat]
@[simp] theorem Y_c : Y c = 4 := by norm_num [c, Y_mul, Y_nat]

theorem E2_a_fourth : E2 (a ^ 4) = (-1 / 4 : ℂ) := by
  simp only [map_pow, E2_a]
  apply Complex.ext <;> norm_num [u, pow_succ, Complex.mul_re, Complex.mul_im]

theorem E2_b_fourth : E2 (b ^ 4) = (-1 / 4 : ℂ) := by
  simp only [map_pow, E2_b]
  apply Complex.ext <;> norm_num [v, pow_succ, Complex.mul_re, Complex.mul_im]

theorem E2_s : E2 s = (-1 / 2 : ℂ) := by
  norm_num [s, map_add, E2_a_fourth, E2_b_fourth]

theorem E1_s : E1 s = 0 := by
  simp only [s, map_add, map_pow, E1_a, E1_b]
  rw [uv_fourth_sum, t1_quartic]
  norm_num

theorem E3_s : E3 s = 0 := by
  simp only [s, map_add, map_pow, E3_a, E3_b]
  rw [uv_fourth_sum, t3_quartic]
  norm_num

theorem E2_T : E2 T = 0 := by
  simp only [T, map_add, map_pow, E2_a, E2_b]
  apply Complex.ext <;> norm_num [u, v, pow_succ, Complex.mul_re, Complex.mul_im]

theorem E1_T : E1 T = ((r - 1 : ℝ) : ℂ) := by
  simp only [T, map_add, map_pow, E1_a, E1_b]
  apply Complex.ext <;> simp [u, v, pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith [r_sq]

theorem E3_T : E3 T = ((-r - 1 : ℝ) : ℂ) := by
  simp only [T, map_add, map_pow, E3_a, E3_b]
  apply Complex.ext <;> simp [u, v, pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith [r_sq]

@[simp] theorem X_s : X s = 1 / 4 := by norm_num [X, E2_s, Complex.normSq_apply]
@[simp] theorem Y_s : Y s = 0 := by simp [Y, E1_s]
@[simp] theorem X_T : X T = 0 := by simp [X, E2_T]

@[simp] theorem Y_T : Y T = 1 := by
  simp only [Y, E1_T, E3_T, Complex.normSq_ofReal]
  ring_nf
  simp only [r_sq, r_fourth]
  norm_num

@[simp] theorem X_z : X z = 9 / 16 := by
  norm_num [X, z, map_add, map_mul, map_ofNat, E2_a_fourth, E2_b_fourth, Complex.normSq_apply]

/-- In both quartic targets the summand s evaluates to zero. -/
theorem Y_z : Y z = 1 / 16 := by
  have hz : z = a ^ 4 + s := by simp [z, s, two_mul, add_assoc]
  have he1 : E1 z = E1 (a ^ 4) := by rw [hz, map_add, E1_s, add_zero]
  have he3 : E3 z = E3 (a ^ 4) := by rw [hz, map_add, E3_s, add_zero]
  calc
    Y z = Y (a ^ 4) := by simp only [Y, he1, he3]
    _ = 1 / 16 := by norm_num [Y_pow]

@[simp] theorem X_s_add_T : X (s + T) = 1 / 4 := by
  norm_num [X, map_add, E2_s, E2_T, Complex.normSq_apply]

@[simp] theorem Y_s_add_T : Y (s + T) = 1 := by
  simpa only [Y, map_add, E1_s, E3_s, zero_add] using Y_T

@[simp] theorem X_two_a_fourth : X (2 * a ^ 4) = 1 / 4 := by
  norm_num [X_mul, X_pow, X_nat]

@[simp] theorem Y_two_a_fourth : Y (2 * a ^ 4) = 1 := by
  norm_num [Y_mul, Y_pow, Y_nat]

theorem s_nonzero : s ≠ 0 := by
  intro hs
  have := X_s
  rw [hs, X_zero] at this
  norm_num at this

theorem T_nonzero : T ≠ 0 := by
  intro hT
  have := Y_T
  rw [hT, Y_zero] at this
  norm_num at this

/-- Literal fourth rejoin fails even though eighth rejoin is built in. -/
theorem fourth_rejoin_false : a ^ 4 ≠ b ^ 4 := by
  intro hab
  have hs : s = 2 * a ^ 4 := by rw [s, ← hab, two_mul]
  have hy := Y_s
  rw [hs, Y_two_a_fourth] at hy
  norm_num at hy

/-! Natural-count inequalities used by both response contracts. -/

theorem A_nonnegative (n m : ℕ) : 0 ≤ A n m := by unfold A; positivity

theorem Q_nonnegative (n m : ℕ) : 0 ≤ Q n m := by unfold Q; positivity

theorem natural_sq_le_fourth (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
  by_cases hn : n = 0
  · simp [hn]
  · have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hs : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]

theorem A_le_Q (n m : ℕ) : A n m ≤ Q n m := by
  dsimp [A, Q]
  linarith [natural_sq_le_fourth n, natural_sq_le_fourth m]

theorem A_mono {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    A n m ≤ A n' m' := by
  have hnr : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hmr : (m : ℝ) ≤ m' := by exact_mod_cast hm
  dsimp [A]
  gcongr

theorem Q_mono {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    Q n m ≤ Q n' m' := by
  have hnr : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hmr : (m : ℝ) ≤ m' := by exact_mod_cast hm
  dsimp [Q]
  gcongr

theorem Q_zero_iff (n m : ℕ) : Q n m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro hq
    have hn : (n : ℝ) ^ 4 = 0 := by
      have hm : 0 ≤ (m : ℝ) ^ 4 := by positivity
      have hn : 0 ≤ (n : ℝ) ^ 4 := by positivity
      dsimp [Q] at hq
      linarith
    have hm : (m : ℝ) ^ 4 = 0 := by
      dsimp [Q] at hq
      linarith
    constructor
    · exact_mod_cast (eq_zero_of_pow_eq_zero hn)
    · exact_mod_cast (eq_zero_of_pow_eq_zero hm)
  · rintro ⟨rfl, rfl⟩
    norm_num [Q]

/-! Named contracts expose every quantifier on actual preparations. -/

def NormalizedNonnegative (R : P → ℝ) : Prop :=
  R 0 = 0 ∧ R 1 = 1 ∧ ∀ p, 0 ≤ R p

def SerialInequality (R : P → ℝ) : Prop := ∀ p, R p ≤ R (c * p)

def ExactSerial (R : P → ℝ) : Prop := ∀ p, R (c * p) = R p

def PreparedCountOrder (R : P → ℝ) : Prop :=
  ∀ (p : P) (n m n' m' : ℕ), n ≤ n' → m ≤ m' →
    R (B n m * p) ≤ R (B n' m' * p)

def WordGrid (R : P → ℝ) : Prop :=
  ∀ k n m : ℕ, R (B n m * h ^ k) = A n m * (1 / 4 : ℝ) ^ k

def AdjacentMixed (R : P → ℝ) (p : P) (n m : ℕ) : ℝ :=
  R (B (n + 1) (m + 1) * p) - R (B (n + 1) m * p) -
    R (B n (m + 1) * p) + R (B n m * p)

def PreparedMixedZero (R : P → ℝ) : Prop :=
  ∀ (p : P) (n m : ℕ), AdjacentMixed R p n m = 0

def WordMixedZero (R : P → ℝ) : Prop :=
  ∀ k n m : ℕ, AdjacentMixed R (h ^ k) n m = 0

def GlobalHalves (R : P → ℝ) : Prop :=
  ∀ p, R (a * p) = R p / 2 ∧ R (b * p) = R p / 2

def FirstColumn (R : P → ℝ) : Prop :=
  ∀ p, R (a * p) + R (b * p) = R p

def Multiplicative (R : P → ℝ) : Prop := ∀ p q, R (p * q) = R p * R q

def SwapInvariant (R : P → ℝ) : Prop := ∀ p, R (J p) = R p

def SelfEcho (R : P → ℝ) : Prop := ∀ p, R (p * J p) = R p ^ 2

def NullAdditive (R : P → ℝ) : Prop :=
  ∀ p q, R p = 0 → R q = 0 → R (p + q) = 0

/-- This contract packages the specified six schemas and all-depth h-word grid. -/
structure SixSchemaContract (R : P → ℝ) : Prop where
  normalizedNonnegative : NormalizedNonnegative R
  serial : SerialInequality R
  countOrder : PreparedCountOrder R
  wordGrid : WordGrid R
  wordMixedZero : WordMixedZero R
  dark : R T = 0

/-! Minimum response. -/

def W (p : P) : ℝ := min (X p) (Y p)

@[simp] theorem W_zero : W 0 = 0 := by simp [W]
@[simp] theorem W_one : W 1 = 1 := by simp [W]

theorem W_nonnegative (p : P) : 0 ≤ W p :=
  le_min (X_nonnegative p) (Y_nonnegative p)

@[simp] theorem W_T : W T = 0 := by norm_num [W]
@[simp] theorem W_s : W s = 0 := by norm_num [W]
@[simp] theorem W_z : W z = 1 / 16 := by norm_num [W, Y_z]
@[simp] theorem W_c : W c = 1 := by norm_num [W]
@[simp] theorem W_s_add_T : W (s + T) = 1 / 4 := by norm_num [W]
@[simp] theorem W_two_a_fourth : W (2 * a ^ 4) = 1 / 4 := by norm_num [W]

/-- No restriction on actual preparation p occurs in this formula. -/
theorem W_prepared_formula (p : P) (n m : ℕ) :
    W (B n m * p) = min (A n m * X p) (Q n m * Y p) := by
  rw [W, X_mul, Y_mul, X_B, Y_B]

theorem W_serial : SerialInequality W := by
  intro p
  change min (X p) (Y p) ≤ min (X (c * p)) (Y (c * p))
  rw [X_mul, Y_mul, X_c, Y_c, one_mul]
  apply le_min (min_le_left _ _)
  exact (min_le_right _ _).trans (by nlinarith [Y_nonnegative p])

theorem W_prepared_count_order : PreparedCountOrder W := by
  intro p n m n' m' hn hm
  rw [W_prepared_formula, W_prepared_formula]
  exact min_le_min
    (mul_le_mul_of_nonneg_right (A_mono hn hm) (X_nonnegative p))
    (mul_le_mul_of_nonneg_right (Q_mono hn hm) (Y_nonnegative p))

theorem W_word_grid : WordGrid W := by
  intro k n m
  rw [W_prepared_formula, X_pow, Y_pow, X_h, Y_h,
    ← min_mul_of_nonneg _ _ (by positivity), min_eq_left (A_le_Q n m)]

theorem W_word_mixed_zero : WordMixedZero W := by
  intro k n m
  unfold AdjacentMixed
  rw [W_word_grid k (n + 1) (m + 1), W_word_grid k (n + 1) m,
    W_word_grid k n (m + 1), W_word_grid k n m]
  simp only [A, Nat.cast_add, Nat.cast_one]
  ring

theorem W_global_halves : GlobalHalves W := by
  intro p
  constructor
  · simp only [W, X_mul, Y_mul, X_a, Y_a]
    rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  · simp only [W, X_mul, Y_mul, X_b, Y_b]
    rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring

theorem W_first_column : FirstColumn W := by
  intro p
  rw [(W_global_halves p).1, (W_global_halves p).2]
  ring

theorem W_swap : SwapInvariant W := by intro p; simp [W, X_swap, Y_swap]

theorem min_square_nonnegative (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min (x * x) (y * y) = min x y ^ 2 := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, min_eq_left (mul_le_mul hxy hxy hx hy), pow_two]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx, min_eq_right (mul_le_mul hyx hyx hy hx), pow_two]

theorem W_self_echo : SelfEcho W := by
  intro p
  simp only [W, X_mul, Y_mul, X_swap, Y_swap]
  exact min_square_nonnegative _ _ (X_nonnegative p) (Y_nonnegative p)

theorem W_six_schema_certificate : SixSchemaContract W where
  normalizedNonnegative := ⟨W_zero, W_one, W_nonnegative⟩
  serial := W_serial
  countOrder := W_prepared_count_order
  wordGrid := W_word_grid
  wordMixedZero := W_word_mixed_zero
  dark := W_T

theorem W_enhanced_certificate :
    SixSchemaContract W ∧ GlobalHalves W ∧ FirstColumn W ∧
    SwapInvariant W ∧ SelfEcho W := by
  exact ⟨W_six_schema_certificate, W_global_halves, W_first_column,
    W_swap, W_self_echo⟩

theorem W_cz : W (c * z) = 1 / 4 := by
  norm_num [W, X_mul, Y_mul, Y_z]

theorem W_strict_serial_witness : W z < W (c * z) := by
  rw [W_z, W_cz]
  norm_num

theorem W_not_exact_serial : ¬ ExactSerial W := by
  intro h
  have he := h z
  rw [W_cz, W_z] at he
  norm_num at he

theorem W_not_multiplicative : ¬ Multiplicative W := by
  intro h
  have he := h c z
  rw [W_cz, W_c, W_z] at he
  norm_num at he

/-- The four actual prepared cell values are exact rational calculations. -/
theorem W_z_cells :
    W (B 4 1 * z) = 153 / 32 ∧ W (B 4 0 * z) = 144 / 32 ∧
    W (B 3 1 * z) = 82 / 32 ∧ W (B 3 0 * z) = 81 / 32 := by
  norm_num [W_prepared_formula, A, Q, X_z, Y_z]

theorem W_prepared_mixed_defect : AdjacentMixed W z 3 0 = 1 / 4 := by
  rcases W_z_cells with ⟨h41, h40, h31, h30⟩
  norm_num [AdjacentMixed, h41, h40, h31, h30]

theorem W_not_prepared_mixed_zero : ¬ PreparedMixedZero W := by
  intro h
  have he := h z 3 0
  rw [W_prepared_mixed_defect] at he
  norm_num at he

theorem W_not_X : W ≠ X := by
  intro he
  have hs := congrFun he s
  rw [W_s, X_s] at hs
  norm_num at hs

theorem W_not_null_additive : ¬ NullAdditive W := by
  intro h
  have he := h s T W_s W_T
  rw [W_s_add_T] at he
  norm_num at he

theorem W_no_fourth_descent : ¬ FourthDescent W := by
  apply no_fourth_descent_of_separated_sum
  rw [W_s, W_two_a_fourth]
  norm_num

/-! Support-restricted response. Its definition uses no limit or topology. -/

def V (p : P) : ℝ := if Y p = 0 then 0 else X p

@[simp] theorem V_zero : V 0 = 0 := by simp [V]
@[simp] theorem V_one : V 1 = 1 := by norm_num [V]

theorem V_nonnegative (p : P) : 0 ≤ V p := by
  unfold V
  split_ifs
  · exact le_rfl
  · exact X_nonnegative p

@[simp] theorem V_T : V T = 0 := by norm_num [V]
@[simp] theorem V_s : V s = 0 := by simp [V]
@[simp] theorem V_c : V c = 1 := by norm_num [V]
@[simp] theorem V_a : V a = 1 / 2 := by norm_num [V]
@[simp] theorem V_b : V b = 1 / 2 := by norm_num [V]
@[simp] theorem V_h : V h = 1 / 4 := by norm_num [V]
@[simp] theorem V_s_add_T : V (s + T) = 1 / 4 := by norm_num [V]
@[simp] theorem V_two_a_fourth : V (2 * a ^ 4) = 1 / 4 := by norm_num [V]

theorem V_multiplicative : Multiplicative V := by
  intro p q
  by_cases hp : Y p = 0 <;> by_cases hq : Y q = 0 <;>
    simp [V, Y_mul, X_mul, hp, hq, mul_eq_zero]

theorem V_exact_serial : ExactSerial V := by
  intro p
  rw [V_multiplicative, V_c, one_mul]

theorem V_serial : SerialInequality V := by
  intro p
  exact le_of_eq (V_exact_serial p).symm

theorem V_swap : SwapInvariant V := by intro p; simp [V, Y_swap, X_swap]

theorem V_self_echo : SelfEcho V := by
  intro p
  rw [V_multiplicative, V_swap, pow_two]

/-- The formula includes zero counts and every actual preparation. -/
theorem V_prepared_raw (p : P) (n m : ℕ) :
    V (B n m * p) = A n m * V p := by
  by_cases hp : Y p = 0
  · simp [V, Y_mul, hp]
  · by_cases hq : Q n m = 0
    · obtain ⟨rfl, rfl⟩ := (Q_zero_iff n m).mp hq
      simp [B, A, V]
    · simp [V, Y_mul, Y_B, X_mul, X_B, hp, hq, mul_eq_zero]

theorem V_prepared_count_order : PreparedCountOrder V := by
  intro p n m n' m' hn hm
  rw [V_prepared_raw, V_prepared_raw]
  exact mul_le_mul_of_nonneg_right (A_mono hn hm) (V_nonnegative p)

theorem V_prepared_mixed_zero : PreparedMixedZero V := by
  intro p n m
  simp only [AdjacentMixed, V_prepared_raw, A, Nat.cast_add, Nat.cast_one]
  ring

theorem V_word_mixed_zero : WordMixedZero V := by
  intro k n m
  exact V_prepared_mixed_zero (h ^ k) n m

theorem V_pow (p : P) (k : ℕ) : V (p ^ k) = V p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, V_multiplicative, ih, pow_succ]

theorem V_word_grid : WordGrid V := by
  intro k n m
  rw [V_prepared_raw, V_pow, V_h]

theorem V_global_halves : GlobalHalves V := by
  intro p
  constructor
  · rw [V_multiplicative, V_a]
    ring
  · rw [V_multiplicative, V_b]
    ring

theorem V_first_column : FirstColumn V := by
  intro p
  rw [(V_global_halves p).1, (V_global_halves p).2]
  ring

theorem V_natural_gain (n : ℕ) (p : P) :
    V ((n : P) * p) = (n : ℝ) ^ 2 * V p := by
  have hb : B n n = (n : P) := by
    rw [B, ← mul_add, transparent, mul_one]
  calc
    V ((n : P) * p) = A n n * V p := by rw [← hb, V_prepared_raw]
    _ = (n : ℝ) ^ 2 * V p := by dsimp [A]; ring

theorem V_six_schema_certificate : SixSchemaContract V where
  normalizedNonnegative := ⟨V_zero, V_one, V_nonnegative⟩
  serial := V_serial
  countOrder := V_prepared_count_order
  wordGrid := V_word_grid
  wordMixedZero := V_word_mixed_zero
  dark := V_T

theorem V_strong_certificate :
    SixSchemaContract V ∧ ExactSerial V ∧ Multiplicative V ∧
    GlobalHalves V ∧ FirstColumn V ∧ SwapInvariant V ∧ SelfEcho V ∧
    PreparedMixedZero V ∧
    (∀ (n : ℕ) (p : P), V ((n : P) * p) = (n : ℝ) ^ 2 * V p) ∧
    (∀ (p : P) (n m : ℕ), V (B n m * p) = A n m * V p) := by
  exact ⟨V_six_schema_certificate, V_exact_serial, V_multiplicative,
    V_global_halves, V_first_column, V_swap, V_self_echo,
    V_prepared_mixed_zero, V_natural_gain, V_prepared_raw⟩

theorem V_not_X : V ≠ X := by
  intro he
  have hs := congrFun he s
  rw [V_s, X_s] at hs
  norm_num at hs

theorem V_not_null_additive : ¬ NullAdditive V := by
  intro h
  have he := h s T V_s V_T
  rw [V_s_add_T] at he
  norm_num at he

theorem V_no_fourth_descent : ¬ FourthDescent V := by
  apply no_fourth_descent_of_separated_sum
  rw [V_s, V_two_a_fourth]
  norm_num

/-- W and V meet the stated schemas yet have explicit additive-null failures. -/
theorem concrete_countermodel_certificate :
    SixSchemaContract W ∧ SixSchemaContract V ∧ W ≠ X ∧ V ≠ X ∧
    ¬ ExactSerial W ∧ ¬ Multiplicative W ∧ ¬ PreparedMixedZero W ∧
    ¬ NullAdditive W ∧ ¬ NullAdditive V ∧
    ¬ FourthDescent W ∧ ¬ FourthDescent V ∧
    s ≠ 0 ∧ T ≠ 0 ∧ a ^ 4 ≠ b ^ 4 := by
  exact ⟨W_six_schema_certificate, V_six_schema_certificate, W_not_X, V_not_X,
    W_not_exact_serial, W_not_multiplicative, W_not_prepared_mixed_zero,
    W_not_null_additive, V_not_null_additive, W_no_fourth_descent,
    V_no_fourth_descent, s_nonzero, T_nonzero, fourth_rejoin_false⟩

/-!
Scope boundary. X itself satisfies the same basic response schemas on this
carrier. Such numerical schemas do not change the literal source equation:
`fourth_rejoin_false` still holds. The explicit W and V witnesses establish an
algebraic nonuniqueness and additive-null obstruction only. They do not identify
a necessary-and-sufficient physical selection law or derive full QM.
-/

end

end IDT.QMClosure.EighthRejoinReadoutCountermodels
