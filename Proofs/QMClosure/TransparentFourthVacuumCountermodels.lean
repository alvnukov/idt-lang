import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Vacuum-normalized countermodels on the literal initial presentation

Both responses satisfy transparency, natural prepared-count order, and raw
adjacent mixed zero. Their exact first-column failures concern this algebraic
contract. No reconstruction or physical selection is asserted.
-/

namespace IDT.QMClosure.TransparentFourthVacuumCountermodels

noncomputable section

open TransparentFourthInitialHistoryPresentation

abbrev P := Presentation

def complexA : ℂ := (1 + Complex.I) / 2

def complexB : ℂ := (1 - Complex.I) / 2

private theorem complex_transparent : complexA + complexB = 1 := by
  dsimp [complexA, complexB]
  ring

private theorem complex_fourth : complexA ^ 4 = complexB ^ 4 := by
  apply Complex.ext <;>
    norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

/-- A model of the two literal presentation equations. -/
def E : P →+* ℂ := eval complexA complexB complex_transparent complex_fourth

@[simp] theorem E_a : E a = complexA := by simp [E]
@[simp] theorem E_b : E b = complexB := by simp [E]

def N (p : P) : ℝ := Complex.normSq (E p)

def c : P := 2 * a * b

def bag (n m : ℕ) (p : P) : P := ((n : P) * a + (m : P) * b) * p

def countNorm (n m : ℕ) : ℝ := ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2

@[simp] theorem E_c : E c = 1 := by
  simp only [c, map_mul, map_ofNat, E_a, E_b]
  apply Complex.ext <;>
    norm_num [complexA, complexB, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

@[simp] theorem E_T : E T = 0 := by
  simp only [T, map_add, map_pow, E_a, E_b]
  apply Complex.ext <;>
    norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

@[simp] theorem E_e : E e = 0 := by simp [e]

@[simp] theorem N_zero : N 0 = 0 := by simp [N]
@[simp] theorem N_one : N 1 = 1 := by simp [N]

theorem N_nonnegative (p : P) : 0 ≤ N p := Complex.normSq_nonneg _

@[simp] theorem N_mul (p q : P) : N (p * q) = N p * N q := by
  simp [N, Complex.normSq_mul]

@[simp] theorem N_c : N c = 1 := by simp [N]
@[simp] theorem N_T : N T = 0 := by simp [N]

private theorem norm_count (n m : ℕ) :
    Complex.normSq ((n : ℂ) * complexA + (m : ℂ) * complexB) = countNorm n m := by
  simp [Complex.normSq_apply, complexA, complexB, Complex.mul_re, Complex.mul_im, countNorm]
  ring

theorem N_bag (n m : ℕ) (p : P) : N (bag n m p) = countNorm n m * N p := by
  simp only [bag, N_mul]
  congr 1
  simpa only [N, map_add, map_mul, map_natCast, E_a, E_b] using norm_count n m

theorem countNorm_nonnegative (n m : ℕ) : 0 ≤ countNorm n m := by
  dsimp [countNorm]
  positivity

theorem countNorm_monotone {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    countNorm n m ≤ countNorm n' m' := by
  have hn' : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hm' : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ n) (by positivity : (0 : ℝ) ≤ n')
  have ht := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ m) (by positivity : (0 : ℝ) ≤ m')
  dsimp [countNorm]
  nlinarith [hs.mpr hn', ht.mpr hm']

/-- The universal natural prepared-count schema, with every preparation retained. -/
def PreparedCountOrder (W : P → ℝ) : Prop :=
  ∀ (n m n' m' : ℕ) (p : P), n ≤ n' → m ≤ m' → W (bag n m p) ≤ W (bag n' m' p)

def RawAdjacentMixedZero (W : P → ℝ) : Prop :=
  ∀ n m : ℕ, W (bag (n + 1) (m + 1) 1) - W (bag (n + 1) m 1) -
    W (bag n (m + 1) 1) + W (bag n m 1) = 0

/-- The five retained premises. -/
structure VacuumContract (W : P → ℝ) : Prop where
  vacuum : W 0 = 0
  normalization : W 1 = 1
  transparent : ∀ p, W (c * p) = W p
  preparedOrder : PreparedCountOrder W
  rawMixedZero : RawAdjacentMixedZero W

private theorem mixed_zero_of_raw (W : P → ℝ)
    (h : ∀ n m, W (bag n m 1) = countNorm n m) : RawAdjacentMixedZero W := by
  intro n m
  simp only [h, countNorm, Nat.cast_add, Nat.cast_one]
  ring

/-- A strictly increasing continuous remapping that fixes the natural raw grid. -/
def radial (t : ℝ) : ℝ := if t ≤ 1 / 2 then t + t * (1 / 2 - t) else t

@[simp] theorem radial_zero : radial 0 = 0 := by norm_num [radial]
@[simp] theorem radial_one : radial 1 = 1 := by norm_num [radial]
@[simp] theorem radial_half : radial (1 / 2) = 1 / 2 := by norm_num [radial]

theorem radial_strictMono : StrictMono radial := by
  intro u v huv
  by_cases hv : v ≤ 1 / 2
  · have hu : u ≤ 1 / 2 := le_trans (le_of_lt huv) hv
    simp only [radial, if_pos hu, if_pos hv]
    have hprod : 0 < (v - u) * (3 / 2 - u - v) := mul_pos (by linarith) (by linarith)
    nlinarith
  · by_cases hu : u ≤ 1 / 2
    · simp only [radial, if_pos hu, if_neg hv]
      have hprod : 0 ≤ (1 / 2 - u) * (1 - u) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · simpa only [radial, if_neg hu, if_neg hv] using huv

theorem radial_continuous : Continuous radial := by
  apply continuous_if_le continuous_id continuous_const
    (continuous_id.add (continuous_id.mul (continuous_const.sub continuous_id))).continuousOn
    continuous_id.continuousOn
  intro t ht
  dsimp at ht ⊢
  rw [ht]
  ring

theorem radial_nonnegative {t : ℝ} (ht : 0 ≤ t) : 0 ≤ radial t := by
  simpa only [radial_zero] using radial_strictMono.monotone ht

theorem radial_countNorm (n m : ℕ) : radial (countNorm n m) = countNorm n m := by
  by_cases hn : n = 0
  · by_cases hm : m = 0
    · subst n; subst m; norm_num [countNorm]
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hh : 1 / 2 ≤ countNorm n m := by dsimp [countNorm]; nlinarith [sq_nonneg (n : ℝ)]
      unfold radial
      split_ifs with he
      · have heq : countNorm n m = 1 / 2 := le_antisymm he hh
        rw [heq]; ring
      · rfl
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hh : 1 / 2 ≤ countNorm n m := by dsimp [countNorm]; nlinarith [sq_nonneg (m : ℝ)]
    unfold radial
    split_ifs with he
    · have heq : countNorm n m = 1 / 2 := le_antisymm he hh
      rw [heq]; ring
    · rfl

def radialResponse (p : P) : ℝ := radial (N p)

@[simp] theorem radialResponse_raw (n m : ℕ) :
    radialResponse (bag n m 1) = countNorm n m := by
  simp [radialResponse, N_bag, radial_countNorm]

theorem radialResponse_preparedOrder : PreparedCountOrder radialResponse := by
  intro n m n' m' p hn hm
  apply radial_strictMono.monotone
  simp only [N_bag]
  exact mul_le_mul_of_nonneg_right (countNorm_monotone hn hm) (N_nonnegative p)

theorem radialResponse_contract : VacuumContract radialResponse where
  vacuum := by simp [radialResponse]
  normalization := by simp [radialResponse]
  transparent := by intro p; simp [radialResponse]
  preparedOrder := radialResponse_preparedOrder
  rawMixedZero := mixed_zero_of_raw _ radialResponse_raw

/-- Complete null insertion follows from dependence on the complex evaluation. -/
theorem radialResponse_nullInsertion (x p : P) :
    radialResponse (x + e * p) = radialResponse x := by
  simp [radialResponse, N]

@[simp] theorem N_a : N a = 1 / 2 := by
  norm_num [N, complexA, Complex.normSq_apply, Complex.div_re, Complex.div_im]

@[simp] theorem N_b : N b = 1 / 2 := by
  norm_num [N, complexB, Complex.normSq_apply, Complex.div_re, Complex.div_im]

@[simp] theorem radialResponse_a_squared : radialResponse (a ^ 2) = 5 / 16 := by
  norm_num [pow_two, radialResponse, radial]

@[simp] theorem radialResponse_ab : radialResponse (a * b) = 5 / 16 := by
  norm_num [radialResponse, radial]

/-- At this scaled raw origin cell, prepared mixed zero has a nonzero defect. -/
theorem radialResponse_scaled_origin_defect :
    radialResponse (bag 1 1 (a * b)) - radialResponse (bag 1 0 (a * b)) -
      radialResponse (bag 0 1 (a * b)) + radialResponse (bag 0 0 (a * b)) = -1 / 32 := by
  norm_num [radialResponse, N_bag, countNorm, radial]

theorem radialResponse_firstColumn_failure :
    radialResponse (a * a) + radialResponse (b * a) = 5 / 8 ∧
    radialResponse a = 1 / 2 := by
  norm_num [radialResponse, radial]

theorem radialResponse_ne_norm : radialResponse ≠ N := by
  intro h
  have hh := congrFun h (a * b)
  norm_num [radialResponse, radial] at hh

theorem radialResponse_not_firstColumn :
    ¬ (∀ p, radialResponse (a * p) + radialResponse (b * p) = radialResponse p) := by
  intro h
  have hh := h a
  have hw := radialResponse_firstColumn_failure
  rw [hw.1, hw.2] at hh
  norm_num at hh

/-- The complex multiplier of a positive natural-count bag is nonzero. -/
theorem E_counts_zero_iff (n m : ℕ) :
    E ((n : P) * a + (m : P) * b) = 0 ↔ n + m = 0 := by
  constructor
  · intro h
    have hh : countNorm n m = 0 := by
      rw [← norm_count]
      simpa only [map_add, map_mul, map_natCast, E_a, E_b, map_zero] using congrArg Complex.normSq h
    have hn : (n : ℝ) = 0 := by
      dsimp [countNorm] at hh
      nlinarith [sq_nonneg (m : ℝ), sq_nonneg (n : ℝ)]
    have hm : (m : ℝ) = 0 := by
      dsimp [countNorm] at hh
      nlinarith [sq_nonneg (m : ℝ), sq_nonneg (n : ℝ)]
    have hn' : n = 0 := by exact_mod_cast hn
    have hm' : m = 0 := by exact_mod_cast hm
    omega
  · intro h
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    simp [hn, hm]

theorem realShadow_nonnegative (p : P) : 0 ≤ realShadow p := by
  change 0 ≤ (shadow p : ℝ)
  exact (shadow p).coe_nonneg

@[simp] theorem realShadow_c : realShadow c = 1 / 2 := by
  norm_num [c, map_mul, map_ofNat]

@[simp] theorem realShadow_T : realShadow T = 1 / 2 := by
  norm_num [T]

theorem realShadow_bag (n m : ℕ) (p : P) :
    realShadow (bag n m p) = (((n : ℝ) + (m : ℝ)) / 2) * realShadow p := by
  simp only [bag, map_mul, map_add, map_natCast, realShadow_a, realShadow_b]
  ring

/-- A positive response on the nonzero-shadow complex-null sector. -/
def nullFlag (p : P) : ℝ := if E p = 0 ∧ 0 < realShadow p then 1 else 0

def nullResponse (p : P) : ℝ := N p + nullFlag p

theorem nullFlag_nonnegative (p : P) : 0 ≤ nullFlag p := by
  unfold nullFlag
  split_ifs <;> norm_num

theorem nullResponse_nonnegative (p : P) : 0 ≤ nullResponse p :=
  add_nonneg (N_nonnegative p) (nullFlag_nonnegative p)

@[simp] theorem nullFlag_zero : nullFlag 0 = 0 := by simp [nullFlag]
@[simp] theorem nullFlag_one : nullFlag 1 = 0 := by simp [nullFlag]

@[simp] theorem nullFlag_c_mul (p : P) : nullFlag (c * p) = nullFlag p := by
  simp only [nullFlag, map_mul, E_c, one_mul, realShadow_c]
  have heq : (0 : ℝ) < 1 / 2 * realShadow p ↔ 0 < realShadow p := by
    constructor <;> intro h <;> linarith
  simp only [heq]

theorem nullFlag_bag_positive (n m : ℕ) (p : P) (h : n + m ≠ 0) :
    nullFlag (bag n m p) = nullFlag p := by
  have hE : E ((n : P) * a + (m : P) * b) ≠ 0 :=
    fun hh => h ((E_counts_zero_iff n m).mp hh)
  have hpos : (0 : ℝ) < ((n : ℝ) + (m : ℝ)) / 2 := by
    have hnat : (0 : ℝ) < (n + m : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h
    push_cast at hnat
    linarith
  have hq : (0 : ℝ) < (((n : ℝ) + (m : ℝ)) / 2) * realShadow p ↔
      0 < realShadow p := by
    exact mul_pos_iff_of_pos_left hpos
  simp only [nullFlag, realShadow_bag]
  have hmul : E (bag n m p) = E ((n : P) * a + (m : P) * b) * E p := by
    exact map_mul E _ _
  simp only [hmul, mul_eq_zero, hE, false_or, hq]

theorem nullResponse_bag_positive (n m : ℕ) (p : P) (h : n + m ≠ 0) :
    nullResponse (bag n m p) = countNorm n m * N p + nullFlag p := by
  simp only [nullResponse, N_bag, nullFlag_bag_positive n m p h]

@[simp] theorem nullResponse_zero : nullResponse 0 = 0 := by simp [nullResponse]
@[simp] theorem nullResponse_one : nullResponse 1 = 1 := by simp [nullResponse]

@[simp] theorem nullResponse_raw (n m : ℕ) :
    nullResponse (bag n m 1) = countNorm n m := by
  by_cases h : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    simp [hn, hm, bag, countNorm]
  · rw [nullResponse_bag_positive n m 1 h]
    simp

theorem nullResponse_preparedOrder : PreparedCountOrder nullResponse := by
  intro n m n' m' p hn hm
  by_cases h : n + m = 0
  · have hn0 : n = 0 := by omega
    have hm0 : m = 0 := by omega
    simpa only [hn0, hm0, bag, Nat.cast_zero, zero_mul, zero_add,
      nullResponse_zero] using nullResponse_nonnegative (bag n' m' p)
  · have h' : n' + m' ≠ 0 := by omega
    rw [nullResponse_bag_positive n m p h, nullResponse_bag_positive n' m' p h']
    exact add_le_add
      (mul_le_mul_of_nonneg_right (countNorm_monotone hn hm) (N_nonnegative p)) le_rfl

theorem nullResponse_contract : VacuumContract nullResponse where
  vacuum := nullResponse_zero
  normalization := nullResponse_one
  transparent := by intro p; simp [nullResponse]
  preparedOrder := nullResponse_preparedOrder
  rawMixedZero := mixed_zero_of_raw _ nullResponse_raw

@[simp] theorem nullResponse_T : nullResponse T = 1 := by
  norm_num [nullResponse, nullFlag]

@[simp] theorem nullResponse_aT : nullResponse (a * T) = 1 := by
  norm_num [nullResponse, nullFlag]

@[simp] theorem nullResponse_bT : nullResponse (b * T) = 1 := by
  norm_num [nullResponse, nullFlag]

theorem nullResponse_firstColumn_failure :
    nullResponse (a * T) + nullResponse (b * T) = 2 ∧ nullResponse T = 1 := by
  norm_num

theorem nullResponse_ne_norm : nullResponse ≠ N := by
  intro h
  have hh := congrFun h T
  norm_num at hh

theorem nullResponse_not_firstColumn :
    ¬ (∀ p, nullResponse (a * p) + nullResponse (b * p) = nullResponse p) := by
  intro h
  have hh := h T
  norm_num at hh

/-- The retained premise bundle leaves both independent failures inhabited. -/
theorem two_vacuum_countermodels :
    (VacuumContract radialResponse ∧ radialResponse ≠ N ∧
      ¬ (∀ p, radialResponse (a * p) + radialResponse (b * p) = radialResponse p)) ∧
    (VacuumContract nullResponse ∧ nullResponse ≠ N ∧
      ¬ (∀ p, nullResponse (a * p) + nullResponse (b * p) = nullResponse p)) :=
  ⟨⟨radialResponse_contract, radialResponse_ne_norm, radialResponse_not_firstColumn⟩,
   ⟨nullResponse_contract, nullResponse_ne_norm, nullResponse_not_firstColumn⟩⟩

end
end IDT.QMClosure.TransparentFourthVacuumCountermodels
