import Proofs.QMClosure.InitialColumnOrderReadoutCore
import Proofs.QMClosure.InitialCountGeometry
import Proofs.QMClosure.InitialPreparedCountOrder
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Ring.Parity

/-!
Count calibration from one stationary serial tripler on the literal initial
carrier. Every response comparison uses a finite actual preparation.
-/
namespace IDT.QMClosure.InitialStationaryTriplerCountCalibration

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPreparedCountOrder
open InitialEchoCoordinates InitialDyadicRelativeLanding

/-- The shared four-law base, extended by one fixed serial tripler law. -/
structure Contract (W : P → ℝ) : Prop extends InitialColumnOrderReadoutCore.BaseContract W where
  tripler : ∀ p, W ((3 : P) * p) = W (3 : P) * W p

variable {W : P → ℝ}

private theorem natural_order (H : InitialColumnOrderReadoutCore.BaseContract W) (i j : ℕ)
    (hij : i ≤ j) (p : P) : W ((i : P) * p) ≤ W ((j : P) * p) := by
  simpa only [bag_diagonal] using H.preparedOrder p i i j j hij hij

private theorem doubling_powers_lower (H : InitialColumnOrderReadoutCore.BaseContract W) (k : ℕ) (p : P) :
    (4 : ℝ) ^ k * W p ≤ W ((2 : P) ^ k * p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (4 : ℝ) ^ (k + 1) * W p = 4 * ((4 : ℝ) ^ k * W p) := by
          rw [pow_succ]
          ring
        _ ≤ 4 * W ((2 : P) ^ k * p) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ W ((2 : P) * ((2 : P) ^ k * p)) := InitialColumnOrderReadoutCore.doubling_lower H _
        _ = W ((2 : P) ^ (k + 1) * p) := by
          congr 1
          rw [pow_succ]
          ring

private theorem nine_pow (k : ℕ) : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by
  calc
    (9 : ℝ) ^ k = ((3 : ℝ) ^ 2) ^ k := by norm_num
    _ = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Iteration applies only the fixed tripler at each actual preparation. -/
theorem tripler_powers (H : Contract W) (n : ℕ) (p : P) :
    W ((3 : P) ^ n * p) = W (3 : P) ^ n * W p := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        W ((3 : P) ^ (n + 1) * p) = W ((3 : P) * ((3 : P) ^ n * p)) := by
          congr 1
          rw [pow_succ]
          ring
        _ = W (3 : P) * W ((3 : P) ^ n * p) := H.tripler _
        _ = W (3 : P) ^ (n + 1) * W p := by rw [ih, pow_succ]; ring

/-- The base-only coarse bound and natural count order calibrate the tripler. -/
theorem tripler_gain (H : Contract W) : W (3 : P) = 9 := by
  have hG : 1 ≤ W (3 : P) := InitialColumnOrderReadoutCore.annulus_constant_positive H.toBaseContract
  have hGpos : 0 < W (3 : P) := by linarith
  have hthree : E (3 : P) = ((3 : ℝ) : ℂ) := by
    change complexEvaluation (3 : P) = (3 : ℂ)
    exact map_natCast complexEvaluation 3
  have hpower (e : ℕ) : W ((3 : P) ^ e) = W (3 : P) ^ e := by
    simpa only [mul_one, H.normalized] using tripler_powers H e 1
  have hupper : W (3 : P) ≤ 9 := by
    apply InitialColumnOrderReadoutCore.le_of_dyadic_power_bound (W (3 : P)) 9 (W (3 : P)) hGpos.le
      (by norm_num)
    intro j
    have hu := InitialColumnOrderReadoutCore.real_axis_coarse_upper H.toBaseContract
      ((3 : P) ^ (2 ^ j)) ((3 : ℝ) ^ (2 ^ j))
      (E_pow_of_real (3 : P) 3 hthree _) (by positivity)
    rw [hpower, ← nine_pow] at hu
    exact hu
  have hlower : (9 : ℝ) ≤ W (3 : P) := by
    apply InitialColumnOrderReadoutCore.le_of_dyadic_power_bound 9 (W (3 : P)) 4 (by norm_num) hGpos
    intro j
    let e : ℕ := 2 ^ j
    obtain ⟨k, hk, hkhi⟩ := exists_nat_pow_near
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) : 1 ≤ (3 : ℝ) ^ e)
      (by norm_num : (1 : ℝ) < 2)
    have hnat : (2 : ℕ) ^ k ≤ 3 ^ e := by exact_mod_cast hk
    have ho := natural_order H.toBaseContract (2 ^ k) (3 ^ e) hnat 1
    simp only [mul_one, Nat.cast_pow, Nat.cast_ofNat] at ho
    rw [hpower] at ho
    have htwo := doubling_powers_lower H.toBaseContract k 1
    simp only [mul_one, H.normalized] at htwo
    have hstrict : (9 : ℝ) ^ e < 4 * (4 : ℝ) ^ k := by
      rw [nine_pow, InitialColumnOrderReadoutCore.four_pow]
      have hhi : (3 : ℝ) ^ e < (2 : ℝ) ^ k * 2 := by
        simpa only [pow_succ] using hkhi
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k,
        pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) e]
    exact hstrict.le.trans (mul_le_mul_of_nonneg_left (htwo.trans ho) (by norm_num))
  exact le_antisymm hupper hlower

private theorem logarithmic_relation_ne_zero (m n : ℕ) (hm : 0 < m) :
    (n : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2 ≠ 0 := by
  intro heq
  have hpowR : (3 : ℝ) ^ n = (2 : ℝ) ^ m := by
    apply Real.log_injOn_pos (by change 0 < (3 : ℝ) ^ n; positivity)
      (by change 0 < (2 : ℝ) ^ m; positivity)
    simp only [Real.log_pow]
    linarith
  have hpowN : (3 : ℕ) ^ n = (2 : ℕ) ^ m := by exact_mod_cast hpowR
  have hodd : Odd ((3 : ℕ) ^ n) := (by decide : Odd (3 : ℕ)).pow
  have heven : Even ((3 : ℕ) ^ n) := by
    rw [hpowN]
    exact (by decide : Even (2 : ℕ)).pow_of_ne_zero hm.ne'
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Dirichlet approximation with positive finite exponents and a positive error.
For a negative error -d, k=floor(1/d)-1 gives 0 < 1-k*d < 2*d.
This bound also covers the case that 1/d is an integer. -/
private theorem positive_logarithmic_collision (ε : ℝ) (hε : 0 < ε) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      0 < (n : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2 ∧
      (n : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2 < ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let α : ℝ := Real.log 3 / Real.log 2
  have hα : 1 < α := (one_lt_div hlog2).mpr
    (Real.log_lt_log (by norm_num) (by norm_num))
  let δ : ℝ := min (1 / 8) (ε / (4 * Real.log 2))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδsmall : δ ≤ 1 / 8 := min_le_left _ _
  have hδscale : δ * (4 * Real.log 2) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨N, hNbound⟩ := exists_nat_one_div_lt hδ
  have hN : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    rw [hzero] at hNbound
    norm_num at hNbound
    linarith
  obtain ⟨q, hq, _, happ⟩ := Real.exists_nat_abs_mul_sub_round_le α hN
  let z : ℤ := round ((q : ℝ) * α)
  have habs : |(q : ℝ) * α - (z : ℝ)| < δ := happ.trans_lt hNbound
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqα : 1 ≤ (q : ℝ) * α := by nlinarith
  have hzR : 0 < (z : ℝ) := by
    have hh := (abs_lt.mp habs).2
    linarith
  have hz : (0 : ℤ) < z := by exact_mod_cast hzR
  let m : ℕ := z.toNat
  have hmcast : (m : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz.le
  have hmR : 0 < (m : ℝ) := by rw [hmcast]; exact hzR
  have hm : 0 < m := by exact_mod_cast hmR
  let e : ℝ := (q : ℝ) * α - (m : ℝ)
  have heabs : |e| < δ := by simpa only [e, hmcast] using habs
  have heid : e * Real.log 2 =
      (q : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2 := by
    dsimp [e, α]
    field_simp [hlog2.ne']
  have hene : e ≠ 0 := by
    intro he
    apply logarithmic_relation_ne_zero m q hm
    rw [← heid, he, zero_mul]
  rcases lt_or_gt_of_ne hene with heneg | hepos
  · let d : ℝ := -e
    have hd : 0 < d := neg_pos.mpr heneg
    have hdδ : d < δ := by simpa only [d, abs_of_neg heneg] using heabs
    let t : ℕ := ⌊1 / d⌋₊
    have ht : 4 ≤ t := by
      apply (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 1 / d)).mpr
      apply (le_div_iff₀ hd).mpr
      norm_num
      linarith
    let k : ℕ := t - 1
    have hk : 3 ≤ k := by omega
    have hkcast : (k : ℝ) = (t : ℝ) - 1 := by
      dsimp [k]
      rw [Nat.cast_sub (by omega : 1 ≤ t)]
      norm_num
    have htd : (t : ℝ) * d ≤ 1 :=
      (le_div_iff₀ hd).mp (Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / d))
    have htdhi : 1 < ((t : ℝ) + 1) * d :=
      (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (1 / d))
    have hnewpos : 0 < 1 - (k : ℝ) * d := by nlinarith
    have hnewhi : 1 - (k : ℝ) * d < 2 * d := by nlinarith
    have hkm : 3 ≤ k * m := by
      simpa using Nat.mul_le_mul hk (Nat.one_le_iff_ne_zero.mpr hm.ne')
    have hnewm : 0 < k * m - 1 := by omega
    have hnewn : 0 < k * q := Nat.mul_pos (by omega) hq
    have hnewcast : ((k * m - 1 : ℕ) : ℝ) = (k : ℝ) * m - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k * m), Nat.cast_mul, Nat.cast_one]
    have hnewid : ((k * q : ℕ) : ℝ) * Real.log 3 -
        ((k * m - 1 : ℕ) : ℝ) * Real.log 2 =
          (1 - (k : ℝ) * d) * Real.log 2 := by
      calc
        _ = Real.log 2 + (k : ℝ) *
            ((q : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2) := by
          rw [hnewcast, Nat.cast_mul]
          ring
        _ = Real.log 2 + (k : ℝ) * (e * Real.log 2) := by rw [heid]
        _ = (1 - (k : ℝ) * d) * Real.log 2 := by dsimp [d]; ring
    refine ⟨k * m - 1, k * q, hnewm, hnewn, ?_, ?_⟩
    · rw [hnewid]
      exact mul_pos hnewpos hlog2
    · rw [hnewid]
      have hh := mul_lt_mul_of_pos_right (hnewhi.trans (by linarith : 2 * d < 2 * δ)) hlog2
      nlinarith
  · refine ⟨m, q, hm, hq, ?_, ?_⟩
    · rw [← heid]
      exact mul_pos hepos hlog2
    · rw [← heid]
      have heδ : e < δ := (abs_lt.mp heabs).2
      have hh := mul_lt_mul_of_pos_right heδ hlog2
      nlinarith

/-- Positive powers of three approach positive powers of two from above. -/
theorem nearcollision (ε : ℝ) (hε : 0 < ε) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      1 < (3 : ℝ) ^ n / (2 : ℝ) ^ m ∧
      (3 : ℝ) ^ n / (2 : ℝ) ^ m < 1 + ε := by
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  obtain ⟨m, n, hm, hn, hlo, hhi⟩ := positive_logarithmic_collision _ hlog
  have hratio : 0 < (3 : ℝ) ^ n / (2 : ℝ) ^ m := by positivity
  have hid : Real.log ((3 : ℝ) ^ n / (2 : ℝ) ^ m) =
      (n : ℝ) * Real.log 3 - (m : ℝ) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  refine ⟨m, n, hm, hn, ?_, ?_⟩
  · apply (Real.log_lt_log_iff (by norm_num) hratio).mp
    rw [Real.log_one, hid]
    exact hlo
  · apply (Real.log_lt_log_iff hratio (by linarith : 0 < 1 + ε)).mp
    rwa [hid]

private theorem small_square_upper (A B : ℝ) (hB : 0 ≤ B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℝ,
      1 < g ∧ g < 1 + ε ∧ A ≤ g ^ 2 * B) : A ≤ B := by
  by_contra hAB
  have hgap : 0 < A - B := sub_pos.mpr (lt_of_not_ge hAB)
  let ε : ℝ := min 1 ((A - B) / (4 * (B + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεgap : ε * (4 * (B + 1)) ≤ A - B :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨g, hg, hghi, hA⟩ := happrox ε hε
  have hfactor : (g - 1) * (g + 1) ≤ 3 * ε := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + ε - g)
      (by linarith : 0 ≤ 1 + ε + g),
      mul_nonneg hε.le (sub_nonneg.mpr hεone)]
  have hweighted := mul_le_mul_of_nonneg_right hfactor hB
  nlinarith [mul_nonneg hε.le hB]

private theorem doubling_nearcollision_upper (H : Contract W) (m n : ℕ)
    (hm : 0 < m) (hnear : 1 < (3 : ℝ) ^ n / (2 : ℝ) ^ m) (p : P) :
    W ((2 : P) * p) ≤
      ((3 : ℝ) ^ n / (2 : ℝ) ^ m) ^ 2 * (4 * W p) := by
  have hreal : (2 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
    ((one_lt_div (by positivity)).mp hnear).le
  have hnat : (2 : ℕ) ^ m ≤ (3 : ℕ) ^ n := by exact_mod_cast hreal
  have horder := natural_order H.toBaseContract (2 ^ m) (3 ^ n) hnat p
  simp only [Nat.cast_pow, Nat.cast_ofNat] at horder
  rw [tripler_powers H, tripler_gain H] at horder
  have hlower := doubling_powers_lower H.toBaseContract (m - 1) ((2 : P) * p)
  have hid : (2 : P) ^ (m - 1) * ((2 : P) * p) = (2 : P) ^ m * p := by
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
  rw [hid] at hlower
  have hbound := hlower.trans horder
  have hpow : (4 : ℝ) ^ m = (4 : ℝ) ^ (m - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
  have hgain : 4 * ((3 : ℝ) ^ n / (2 : ℝ) ^ m) ^ 2 * (4 : ℝ) ^ (m - 1) =
      (9 : ℝ) ^ n := by
    rw [div_pow, ← nine_pow, ← InitialColumnOrderReadoutCore.four_pow, hpow]
    field_simp
  apply (mul_le_mul_iff_left₀ (pow_pos (by norm_num : (0 : ℝ) < 4) (m - 1))).mp
  calc
    W ((2 : P) * p) * (4 : ℝ) ^ (m - 1) ≤ (9 : ℝ) ^ n * W p := by
      simpa only [mul_comm] using hbound
    _ = (((3 : ℝ) ^ n / (2 : ℝ) ^ m) ^ 2 * (4 * W p)) * (4 : ℝ) ^ (m - 1) := by
      rw [← hgain]
      ring

/-- Exact doubling follows at every preparation, including zero-response inputs. -/
theorem doubling_exact (H : Contract W) (p : P) : W ((2 : P) * p) = 4 * W p := by
  have hW : 0 ≤ W p := InitialColumnOrderReadoutCore.response_nonnegative H.toBaseContract p
  apply le_antisymm
  · apply small_square_upper _ _ (mul_nonneg (by norm_num) hW)
    intro ε hε
    obtain ⟨m, n, hm, _, hlo, hhi⟩ := nearcollision ε hε
    exact ⟨_, hlo, hhi, doubling_nearcollision_upper H m n hm hlo p⟩
  · exact InitialColumnOrderReadoutCore.doubling_lower H.toBaseContract p

/-- The serial cross-return word preserves the response at every preparation. -/
theorem c_equality (H : Contract W) (p : P) : W (c * p) = W p := by
  have hh := InitialColumnOrderReadoutCore.h_response H.toBaseContract ((2 : P) * p)
  have hid : h * ((2 : P) * p) = c * p := by dsimp [h, c]; ring
  rw [hid, doubling_exact H] at hh
  linarith

private theorem twoInv_response (H : Contract W) (p : P) :
    W (twoInv * p) = W p / 4 := by
  have hh := doubling_exact H (twoInv * p)
  rw [← mul_assoc, two_mul_twoInv, one_mul] at hh
  linarith

private theorem twoInv_power_response (H : Contract W) (k : ℕ) (p : P) :
    W (twoInv ^ k * p) = W p / (4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        W (twoInv ^ (k + 1) * p) = W (twoInv * (twoInv ^ k * p)) := by
          congr 1
          rw [pow_succ]
          ring
        _ = W (twoInv ^ k * p) / 4 := twoInv_response H _
        _ = W p / (4 : ℝ) ^ (k + 1) := by
          rw [ih, pow_succ]
          field_simp

private theorem raw_diagonal (d : DyadicCount) : raw d d = scalar d := by
  rw [raw, ← mul_add, transparent, mul_one]

private theorem scalar_order (H : InitialColumnOrderReadoutCore.BaseContract W) (d e : DyadicCount)
    (hde : (d : ℝ) ≤ (e : ℝ)) (p : P) :
    W (scalar d * p) ≤ W (scalar e * p) := by
  have ho := prepared_dyadic_order H.preparedOrder d d e e hde hde p
  simpa only [raw_diagonal] using ho

/-- Only binary denominators and powers-of-three numerators are used here. -/
private theorem binary_ternary_count_gain (H : Contract W) (m n : ℕ) (p : P) :
    W (scalar (dyadicCount m (3 ^ n)) * p) =
      (dyadicCount m (3 ^ n) : ℝ) ^ 2 * W p := by
  rw [scalar_grid, mul_assoc, twoInv_power_response H]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [tripler_powers H, tripler_gain H]
  simp only [dyadicCount_value, Nat.cast_pow, Nat.cast_ofNat, div_pow]
  rw [← nine_pow, ← InitialColumnOrderReadoutCore.four_pow]
  ring

private theorem natural_nearcollision_bounds (H : Contract W) (j : ℕ) (hj : 0 < j)
    (m n : ℕ) (hnear : 1 < (3 : ℝ) ^ n / (2 : ℝ) ^ m) (p : P) :
    W ((j : P) * p) ≤ ((3 : ℝ) ^ n / (2 : ℝ) ^ m) ^ 2 * ((j : ℝ) ^ 2 * W p) ∧
      (j : ℝ) ^ 2 * W p ≤ ((3 : ℝ) ^ n / (2 : ℝ) ^ m) ^ 2 * W ((j : P) * p) := by
  let g : ℝ := (3 : ℝ) ^ n / (2 : ℝ) ^ m
  have hg : 1 < g := hnear
  have hgpos : 0 < g := by linarith
  have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨k, hk, hkhi⟩ := exists_nat_pow_near hjone hg
  have hvalue (t : ℕ) :
      (dyadicCount (m * t) (3 ^ (n * t)) : ℝ) = g ^ t := by
    simp only [dyadicCount_value, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [g]
    rw [div_pow, pow_mul, pow_mul]
  have hmiddle : scalar (dyadicCount 0 j) = (j : P) := by simp [scalar_grid]
  have hlo : (g ^ k) ^ 2 * W p ≤ W ((j : P) * p) := by
    have ho := scalar_order H.toBaseContract
      (dyadicCount (m * k) (3 ^ (n * k))) (dyadicCount 0 j)
      (by simpa only [hvalue, dyadicCount_value, pow_zero, div_one] using hk) p
    rw [binary_ternary_count_gain H, hvalue, hmiddle] at ho
    exact ho
  have hhi : W ((j : P) * p) ≤ (g ^ (k + 1)) ^ 2 * W p := by
    have ho := scalar_order H.toBaseContract
      (dyadicCount 0 j) (dyadicCount (m * (k + 1)) (3 ^ (n * (k + 1))))
      (by simpa only [hvalue, dyadicCount_value, pow_zero, div_one] using hkhi.le) p
    rw [hmiddle, binary_ternary_count_gain H, hvalue] at ho
    exact ho
  have hW : 0 ≤ W p := InitialColumnOrderReadoutCore.response_nonnegative H.toBaseContract p
  have hstepupper : g ^ (k + 1) ≤ g * (j : ℝ) := by rw [pow_succ]; nlinarith
  have hsteplower : (j : ℝ) ≤ g * g ^ k := by
    simpa only [pow_succ, mul_comm] using hkhi.le
  have hsquareupper : (g ^ (k + 1)) ^ 2 ≤ (g * (j : ℝ)) ^ 2 := by
    nlinarith [pow_nonneg hgpos.le (k + 1)]
  have hsquarelower : (j : ℝ) ^ 2 ≤ (g * g ^ k) ^ 2 := by
    nlinarith [pow_nonneg hgpos.le k]
  constructor
  · calc
      W ((j : P) * p) ≤ (g ^ (k + 1)) ^ 2 * W p := hhi
      _ ≤ (g * (j : ℝ)) ^ 2 * W p := mul_le_mul_of_nonneg_right hsquareupper hW
      _ = g ^ 2 * ((j : ℝ) ^ 2 * W p) := by ring
  · calc
      (j : ℝ) ^ 2 * W p ≤ (g * g ^ k) ^ 2 * W p :=
        mul_le_mul_of_nonneg_right hsquarelower hW
      _ = g ^ 2 * ((g ^ k) ^ 2 * W p) := by ring
      _ ≤ g ^ 2 * W ((j : P) * p) := mul_le_mul_of_nonneg_left hlo (sq_nonneg g)

/-- All natural counts have their square gain at every actual preparation. -/
theorem natural_gain (H : Contract W) (j : ℕ) (p : P) :
    W ((j : P) * p) = (j : ℝ) ^ 2 * W p := by
  by_cases hj : j = 0
  · subst j
    simpa only [Nat.cast_zero, zero_mul, zero_pow (by decide : 2 ≠ 0)] using
      InitialColumnOrderReadoutCore.response_zero H.toBaseContract
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj
  have hW : 0 ≤ W p := InitialColumnOrderReadoutCore.response_nonnegative H.toBaseContract p
  have hupper : W ((j : P) * p) ≤ (j : ℝ) ^ 2 * W p := by
    apply small_square_upper _ _ (mul_nonneg (sq_nonneg _) hW)
    intro ε hε
    obtain ⟨m, n, _, _, hlo, hhi⟩ := nearcollision ε hε
    exact ⟨_, hlo, hhi, (natural_nearcollision_bounds H j hjpos m n hlo p).1⟩
  have hlower : (j : ℝ) ^ 2 * W p ≤ W ((j : P) * p) := by
    apply small_square_upper _ _ (InitialColumnOrderReadoutCore.response_nonnegative H.toBaseContract _)
    intro ε hε
    obtain ⟨m, n, _, _, hlo, hhi⟩ := nearcollision ε hε
    exact ⟨_, hlo, hhi, (natural_nearcollision_bounds H j hjpos m n hlo p).2⟩
  exact le_antisymm hupper hlower

/-- Every finite nonnegative binary scalar has its square response gain. -/
theorem scalar_gain (H : Contract W) (d : DyadicCount) (p : P) :
    W (scalar d * p) = (d : ℝ) ^ 2 * W p := by
  obtain ⟨k, n, hd⟩ := nonnegative_dyadic_representation (d : ℝ) d.property.2 d.property.1
  have hgrid : d = dyadicCount k n := Subtype.ext hd
  rw [hgrid, scalar_grid, mul_assoc, twoInv_power_response H, natural_gain H]
  simp only [dyadicCount_value, div_pow]
  rw [← InitialColumnOrderReadoutCore.four_pow]
  ring

/-- A raw diagonal count is the same literal finite scalar word. -/
theorem raw_diagonal_gain (H : Contract W) (d : DyadicCount) (p : P) :
    W (raw d d * p) = (d : ℝ) ^ 2 * W p := by
  rw [raw_diagonal]
  exact scalar_gain H d p

end
end IDT.QMClosure.InitialStationaryTriplerCountCalibration
