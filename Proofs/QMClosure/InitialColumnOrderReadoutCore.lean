import Proofs.QMClosure.InitialDyadicRelativeLanding
import Proofs.QMClosure.FiniteRejoinColumnBalance

/-!
Shared four-law readout core on the literal initial P4 carrier.
Real-axis squaring and the global norm upper bound appear as explicit
additional premises exactly where their proofs require them.
-/
namespace IDT.QMClosure.InitialColumnOrderReadoutCore

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPreparedCountOrder
open InitialEchoCoordinates InitialDyadicRelativeLanding

/-- The four response laws shared by the selection routes. -/
structure BaseContract (W : P → ℝ) : Prop where
  normalized : W 1 = 1
  column : ∀ p, W (a * p) + W (b * p) = W p
  cIncreasing : ResponseIncreasing W c
  preparedOrder : PreparedCountOrder W

/-- Squaring is required here only on preparations with real complex coordinate. -/
def RealAxisSquare (W : P → ℝ) : Prop :=
  ∀ (p : P) (x : ℝ), E p = (x : ℂ) → W (p ^ 2) = W p ^ 2

variable {W : P → ℝ}

theorem le_of_dyadic_power_bound (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hbound : ∀ j : ℕ, A ^ (2 ^ j) ≤ C * B ^ (2 ^ j)) : A ≤ B := by
  by_contra hAB
  have hratio : 1 < A / B := (one_lt_div hB).mpr (lt_of_not_ge hAB)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have hn2 : n < 2 ^ n := by
    clear hn
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have hmono : (A / B) ^ n ≤ (A / B) ^ (2 ^ n) :=
    pow_le_pow_right₀ hratio.le hn2.le
  have hdiv : (A / B) ^ (2 ^ n) ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hB _)).mpr (hbound n)
  linarith

theorem four_pow (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  calc
    (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k := by norm_num
    _ = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem response_zero (H : BaseContract W) : W 0 = 0 := by
  have hh := H.column 0
  simp only [mul_zero] at hh
  linarith

theorem response_nonnegative (H : BaseContract W) (p : P) : 0 ≤ W p :=
  InitialPreparedCountOrder.response_nonnegative (response_zero H) H.preparedOrder p

theorem half_responses (H : BaseContract W) (p : P) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 := by
  exact FiniteRejoinColumnBalance.half_responses (n := 4) (by decide)
    transparent fourth_rejoin W (response_nonnegative H) H.column p

theorem h_response (H : BaseContract W) (p : P) : W (h * p) = W p / 4 := by
  have ha := (half_responses H (b * p)).1
  have hb := (half_responses H p).2
  dsimp [h]
  rw [mul_assoc, ha, hb]
  ring

theorem hInv_response (H : BaseContract W) (p : P) : W (hInv * p) = 4 * W p := by
  have hh := h_response H (hInv * p)
  rw [← mul_assoc, h_mul_hInv, one_mul] at hh
  linarith

theorem h_power_response (H : BaseContract W) (k : ℕ) (p : P) :
    W (h ^ k * p) = W p / (4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        W (h ^ (k + 1) * p) = W (h * (h ^ k * p)) := by
          congr 1
          rw [pow_succ]
          ring
        _ = W (h ^ k * p) / 4 := h_response H _
        _ = W p / (4 : ℝ) ^ (k + 1) := by
          rw [ih, pow_succ]
          field_simp
          <;> ring

theorem hInv_power_response (H : BaseContract W) (k : ℕ) (p : P) :
    W (hInv ^ k * p) = (4 : ℝ) ^ k * W p := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        W (hInv ^ (k + 1) * p) = W (hInv * (hInv ^ k * p)) := by
          congr 1
          rw [pow_succ]
          ring
        _ = 4 * W (hInv ^ k * p) := hInv_response H _
        _ = (4 : ℝ) ^ (k + 1) * W p := by rw [ih, pow_succ]; ring

theorem doubling_lower (H : BaseContract W) (p : P) : 4 * W p ≤ W ((2 : P) * p) := by
  have hid : h * ((2 : P) * p) = c * p := by dsimp [h, c]; ring
  have hh := h_response H ((2 : P) * p)
  rw [hid] at hh
  have hc := H.cIncreasing p
  linarith

theorem null_response (H : BaseContract W) (p : P) (hp : E p = 0) : W p = 0 := by
  obtain ⟨ha, hb⟩ := null_products p hp
  have hcol := H.column p
  rw [ha, hb] at hcol
  have hc := H.cIncreasing p
  have hn := response_nonnegative H p
  linarith

theorem annulus_upper (H : BaseContract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 1 ≤ x) (hx2 : x ≤ 2) : W p ≤ W 3 := by
  have hpne : p ≠ 0 := by intro hh; rw [hh, map_zero] at hp; have := congrArg Complex.re hp; simp at this; linarith
  have hxmem : x ∈ realDyadic := by
    have hh := (evaluation_real_imag_dyadic p).1
    simpa only [hp, Complex.ofReal_re] using hh
  let d : DyadicCount := ⟨x, hxmem, by linarith⟩
  obtain ⟨M, s, t, hM, hland, hs, ht, hse, hte⟩ :=
    relative_landing H.preparedOrder H.cIncreasing p 1 d (by change 0 < x; linarith)
      (q_positive p hpne) (by simp) (by simpa only [map_one, mul_one] using hp)
      (1 / 2) (by norm_num)
  have hs3 : (s : ℝ) ≤ (naturalCount 3 : ℝ) := by
    have hh := (abs_lt.mp hse).2
    norm_num only [naturalCount_value, Nat.cast_ofNat]
    change (s : ℝ) - x < 1 / 2 at hh
    linarith
  have ht3 : (t : ℝ) ≤ (naturalCount 3 : ℝ) := by
    have hh := (abs_lt.mp hte).2
    norm_num only [naturalCount_value, Nat.cast_ofNat]
    change (t : ℝ) - x < 1 / 2 at hh
    linarith
  calc
    W p ≤ W (M * p) := hM p
    _ = W (raw s t * 1) := congrArg W hland
    _ ≤ W (raw (naturalCount 3) (naturalCount 3) * 1) :=
      prepared_dyadic_order H.preparedOrder _ _ _ _ hs3 ht3 1
    _ = W 3 := by rw [raw_natural, bag_diagonal]; simp

theorem annulus_constant_positive (H : BaseContract W) : 1 ≤ W 3 := by
  have ho := H.preparedOrder 1 1 1 3 3 (by decide) (by decide)
  simpa only [bag_diagonal, Nat.cast_one, one_mul, mul_one, H.normalized] using ho

theorem real_axis_coarse_upper (H : BaseContract W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p ≤ W 3 * x ^ 2 := by
  have hC : 0 ≤ W 3 := le_trans (by norm_num) (annulus_constant_positive H)
  by_cases hx1 : 1 ≤ x
  · obtain ⟨k, hk, hkhi⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    have hscaled : E (h ^ k * p) = ((x / (2 : ℝ) ^ k : ℝ) : ℂ) := by
      rw [map_mul, map_pow, evaluation_h, hp]
      push_cast
      simp only [div_pow, one_pow]
      ring
    have hxlo : 1 ≤ x / (2 : ℝ) ^ k := (one_le_div hkpos).mpr hk
    have hxhi : x / (2 : ℝ) ^ k ≤ 2 := by
      apply (div_le_iff₀ hkpos).mpr
      rw [pow_succ] at hkhi
      linarith
    have hu := annulus_upper H _ _ hscaled hxlo hxhi
    rw [h_power_response H] at hu
    have hu' : W p ≤ W 3 * (4 : ℝ) ^ k := (div_le_iff₀ (by positivity)).mp hu
    have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := four_pow _
    rw [h4] at hu'
    exact hu'.trans (mul_le_mul_of_nonneg_left (by nlinarith) hC)
  · have hxinv : 1 ≤ 1 / x := (one_le_div hx).mpr (le_of_not_ge hx1)
    obtain ⟨k, hk, hkhi⟩ := exists_nat_pow_near hxinv (by norm_num : (1 : ℝ) < 2)
    let n := k + 1
    have hscale : E (hInv ^ n * p) = (((2 : ℝ) ^ n * x : ℝ) : ℂ) := by
      rw [map_mul, map_pow, E_hInv, hp]
      push_cast
      rfl
    have hxlo : 1 ≤ (2 : ℝ) ^ n * x := by
      have hh := (div_lt_iff₀ hx).mp hkhi
      dsimp [n]
      nlinarith
    have hxhi : (2 : ℝ) ^ n * x ≤ 2 := by
      have hh := (le_div_iff₀ hx).mp hk
      dsimp [n]
      rw [pow_succ]
      nlinarith
    have hu := annulus_upper H _ _ hscale hxlo hxhi
    rw [hInv_power_response H] at hu
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := four_pow _
    have hscaledSq : 1 ≤ (4 : ℝ) ^ n * x ^ 2 := by rw [h4]; nlinarith
    have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg x)
    have hW := response_nonnegative H p
    nlinarith [mul_nonneg hW (sub_nonneg.mpr hscaledSq)]

/-- Iterated squaring on preparations with real complex coordinate. -/
theorem real_axis_square_powers (hSquare : RealAxisSquare W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (j : ℕ) : W (p ^ (2 ^ j)) = W p ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hreal := E_pow_of_real p x hp (2 ^ j)
      have hh := hSquare (p ^ (2 ^ j)) (x ^ (2 ^ j)) hreal
      simp only [pow_succ]
      rw [pow_mul, hh, ih, pow_mul]

theorem real_axis_upper (H : BaseContract W) (hSquare : RealAxisSquare W) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p ≤ x ^ 2 := by
  apply le_of_dyadic_power_bound (W p) (x ^ 2) (W 3)
    (response_nonnegative H p) (by positivity)
  intro j
  have hu := real_axis_coarse_upper H (p ^ (2 ^ j)) (x ^ (2 ^ j))
    (E_pow_of_real p x hp _) (pow_pos hx _)
  rw [real_axis_square_powers hSquare p x hp] at hu
  simpa only [← pow_mul, Nat.mul_comm] using hu

theorem powers_two_calibrated (H : BaseContract W) (hUpper : ∀ p, W p ≤ N p) (k : ℕ) :
    W ((2 : P) ^ k) = (4 : ℝ) ^ k := by
  have hlo : (4 : ℝ) ^ k ≤ W ((2 : P) ^ k) := by
    induction k with
    | zero => simpa using H.normalized.ge
    | succ k ih =>
        calc
          (4 : ℝ) ^ (k + 1) = 4 * (4 : ℝ) ^ k := by rw [pow_succ]; ring
          _ ≤ 4 * W ((2 : P) ^ k) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ W ((2 : P) * (2 : P) ^ k) := doubling_lower H _
          _ = W ((2 : P) ^ (k + 1)) := by
            congr 1
            rw [pow_succ]
            ring

  have hu := hUpper ((2 : P) ^ k)
  have hnorm : N ((2 : P) ^ k) = (4 : ℝ) ^ k := by
    have htwo : complexEvaluation (2 : P) = (2 : ℂ) := map_natCast complexEvaluation 2
    norm_num [N, InitialCountGeometry.normSq, map_pow, htwo, Complex.normSq_apply]
  exact le_antisymm (hnorm ▸ hu) hlo

theorem naturals_calibrated (H : BaseContract W) (hSquare : RealAxisSquare W)
    (hUpper : ∀ p, W p ≤ N p) (M : ℕ) : W (M : P) = (M : ℝ) ^ 2 := by
  by_cases hM : M = 0
  · subst M
    simpa using response_zero H
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hupper : W (M : P) ≤ (M : ℝ) ^ 2 := by
    simpa [N, InitialCountGeometry.normSq, Complex.normSq_apply, pow_two] using hUpper (M : P)
  have hpositive : 0 < W (M : P) := by
    have ho := H.preparedOrder 1 1 1 M M (Nat.one_le_iff_ne_zero.mpr hM) (Nat.one_le_iff_ne_zero.mpr hM)
    rw [bag_diagonal, bag_diagonal, mul_one, mul_one, Nat.cast_one, H.normalized] at ho
    linarith
  have hlower : (M : ℝ) ^ 2 ≤ W (M : P) := by
    apply le_of_dyadic_power_bound ((M : ℝ) ^ 2) (W (M : P)) 4 (by positivity) hpositive
    intro j
    let e := 2 ^ j
    have hMpow : 1 ≤ (M : ℝ) ^ e := one_le_pow₀ hMone
    obtain ⟨k, hk, hkhi⟩ := exists_nat_pow_near hMpow (by norm_num : (1 : ℝ) < 2)
    have hnat : 2 ^ k ≤ M ^ e := by exact_mod_cast hk
    have ho := H.preparedOrder 1 (2 ^ k) (2 ^ k) (M ^ e) (M ^ e) hnat hnat
    simp only [bag_diagonal, mul_one, Nat.cast_pow, Nat.cast_ofNat] at ho
    rw [powers_two_calibrated H hUpper, real_axis_square_powers hSquare (M : P) (M : ℝ) (by simp)] at ho
    have hsquare : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := four_pow _
    have hstrict : ((M : ℝ) ^ e) ^ 2 < 4 * (4 : ℝ) ^ k := by
      have hkhi' : (M : ℝ) ^ e < (2 : ℝ) ^ k * 2 := by
        simpa only [pow_succ] using hkhi
      rw [hsquare]
      nlinarith [pow_nonneg hMpos.le e, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
    have hpow : ((M : ℝ) ^ 2) ^ e = ((M : ℝ) ^ e) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    change ((M : ℝ) ^ 2) ^ e ≤ 4 * W (M : P) ^ e
    rw [hpow]
    linarith
  exact le_antisymm hupper hlower

theorem real_axis_lower_fraction (H : BaseContract W)
    (hNat : ∀ M : ℕ, W (M : P) = (M : ℝ) ^ 2) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : x ^ 2 / 16 ≤ W p := by
  have hxmem : x ∈ realDyadic := by
    simpa only [hp, Complex.ofReal_re] using (evaluation_real_imag_dyadic p).1
  obtain ⟨D, M, hrep⟩ := nonnegative_dyadic_representation x hx.le hxmem
  have hMpos : 0 < M := by
    by_contra hh
    have hM0 : M = 0 := Nat.eq_zero_of_not_pos hh
    rw [hM0, Nat.cast_zero, zero_div] at hrep
    linarith
  let r : P := h ^ (D + 2) * (M : P)
  have hrE : E r = ((x / 4 : ℝ) : ℂ) := by
    dsimp [r]
    rw [map_mul, map_pow, evaluation_h, map_natCast, hrep]
    push_cast
    simp only [pow_add, one_div_pow]
    norm_num
    field_simp <;> ring
  have hrW : W r = x ^ 2 / 16 := by
    dsimp [r]
    rw [h_power_response H, hNat, hrep]
    have hfour : (4 : ℝ) ^ D = ((2 : ℝ) ^ D) ^ 2 := four_pow _
    rw [pow_add, hfour]
    norm_num
    field_simp <;> ring
  have hrne : r ≠ 0 := by intro hh; rw [hh, map_zero] at hrE; have := congrArg Complex.re hrE; simp at this; linarith
  have hpne : p ≠ 0 := by intro hh; rw [hh, map_zero] at hp; have := congrArg Complex.re hp; simp at this; linarith
  let quarter : DyadicCount := dyadicCount 2 1
  obtain ⟨Mprog, s, t, hMprog, hland, hs, ht, hse, hte⟩ :=
    relative_landing H.preparedOrder H.cIncreasing r p quarter (by norm_num [quarter])
      (q_positive r hrne) (q_positive p hpne) (by rw [hrE, hp]; norm_num [quarter]; push_cast; ring)
      (1 / 4) (by norm_num)
  have hs1 : (s : ℝ) ≤ (naturalCount 1 : ℝ) := by
    have hh := (abs_lt.mp hse).2
    norm_num [quarter] at hh ⊢
    linarith
  have ht1 : (t : ℝ) ≤ (naturalCount 1 : ℝ) := by
    have hh := (abs_lt.mp hte).2
    norm_num [quarter] at hh ⊢
    linarith
  calc
    x ^ 2 / 16 = W r := hrW.symm
    _ ≤ W (Mprog * r) := hMprog r
    _ = W (raw s t * p) := congrArg W hland
    _ ≤ W (raw (naturalCount 1) (naturalCount 1) * p) :=
      prepared_dyadic_order H.preparedOrder _ _ _ _ hs1 ht1 p
    _ = W p := by rw [raw_natural, bag_diagonal]; simp

theorem real_axis_selected (H : BaseContract W) (hSquare : RealAxisSquare W)
    (hUpper : ∀ p, W p ≤ N p) (p : P) (x : ℝ)
    (hp : E p = (x : ℂ)) (hx : 0 < x) : W p = x ^ 2 := by
  have hfrac := real_axis_lower_fraction H (naturals_calibrated H hSquare hUpper) p x hp hx
  have hWpos : 0 < W p := by nlinarith [sq_pos_of_pos hx]
  have hlo : x ^ 2 ≤ W p := by
    apply le_of_dyadic_power_bound (x ^ 2) (W p) 16 (sq_nonneg x) hWpos
    intro j
    have hh := real_axis_lower_fraction H (naturals_calibrated H hSquare hUpper) (p ^ (2 ^ j)) (x ^ (2 ^ j))
      (E_pow_of_real p x hp _) (pow_pos hx _)
    rw [real_axis_square_powers hSquare p x hp] at hh
    have hpow : (x ^ (2 ^ j)) ^ 2 = (x ^ 2) ^ (2 ^ j) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow] at hh
    linarith
  exact le_antisymm (real_axis_upper H hSquare p x hp hx) hlo

theorem norm_model : BaseContract N where
  normalized := by simp [N, InitialCountGeometry.normSq]
  column := by
    intro p
    change InitialCountGeometry.normSq (a * p) + InitialCountGeometry.normSq (b * p) = _
    rw [InitialCountGeometry.normSq_mul, InitialCountGeometry.normSq_mul]
    have ha : N a = 1 / 2 := by
      norm_num [N, InitialCountGeometry.normSq, evaluation_a, complexA, Complex.normSq_apply]
    have hb : N b = 1 / 2 := by
      norm_num [N, InitialCountGeometry.normSq, evaluation_b, complexB, Complex.normSq_apply]
    change N a * N p + N b * N p = N p
    rw [ha, hb]
    ring
  cIncreasing := by
    intro p
    change InitialCountGeometry.normSq p ≤ InitialCountGeometry.normSq (c * p)
    rw [InitialCountGeometry.normSq_mul]
    simp [N, InitialCountGeometry.normSq, evaluation_c]
  preparedOrder := by
    intro p n m n' m' hn hm
    change InitialCountGeometry.normSq (bag n m * p) ≤ InitialCountGeometry.normSq (bag n' m' * p)
    rw [InitialCountGeometry.normSq_mul, InitialCountGeometry.normSq_mul,
      InitialCountGeometry.normSq_bag, InitialCountGeometry.normSq_bag]
    have hnR : (n : ℝ) ≤ n' := by exact_mod_cast hn
    have hmR : (m : ℝ) ≤ m' := by exact_mod_cast hm
    apply mul_le_mul_of_nonneg_right _ (normSq_nonnegative p)
    nlinarith [show (0 : ℝ) ≤ n by positivity, show (0 : ℝ) ≤ m by positivity]

end
end IDT.QMClosure.InitialColumnOrderReadoutCore
