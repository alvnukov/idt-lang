import Proofs.QMClosure.TransparentFourthInitialNormalForm

/-!
Shared finite count geometry on the literal initial presentation.
Both coordinates of the checked initial normal form determine every reflected
equality.
-/

namespace IDT.QMClosure.InitialCountGeometry

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm

/-- Natural raw count word in the initial presentation. -/
def bag (n m : ℕ) : P := (n : P) * a + (m : P) * b

/-- Serial cross-return word from the accepted analytic contract. -/
def c : P := (2 : P) * a * b

/-- The explicitly positive inverse word for a. -/
def aInv : P := FourthRejoinIdempotent.geometricInverse a b

/-- The explicitly positive inverse word for scalar two. -/
def twoInv : P := a * b + T ^ 2

theorem aInv_mul_a : aInv * a = 1 :=
  (FourthRejoinIdempotent.geometric_inverse_a transparent fourth_rejoin).1

theorem a_mul_aInv : a * aInv = 1 :=
  (FourthRejoinIdempotent.geometric_inverse_a transparent fourth_rejoin).2

theorem two_mul_twoInv : (2 : P) * twoInv = 1 := by
  exact inverse_contexts.twoRight

theorem twoInv_mul_two : twoInv * (2 : P) = 1 := by
  exact inverse_contexts.twoLeft

theorem two_power_cancel (k : ℕ) :
    (2 : P) ^ k * twoInv ^ k = 1 := by
  rw [← mul_pow, two_mul_twoInv, one_pow]

theorem two_power_cancel_reverse (k : ℕ) :
    twoInv ^ k * (2 : P) ^ k = 1 := by
  rw [← mul_pow, twoInv_mul_two, one_pow]

@[simp] theorem bag_zero_zero : bag 0 0 = 0 := by simp [bag]

theorem bag_diagonal (n : ℕ) : bag n n = (n : P) := by
  rw [bag, ← mul_add, transparent, mul_one]

theorem nat_mul_bag (j n m : ℕ) :
    (j : P) * bag n m = bag (j * n) (j * m) := by
  simp only [bag, Nat.cast_mul]
  ring

/-- Natural-count implementation of alpha(1+i*tau), with shadow alpha(1+tau).
The denominator is a power of two even when tau=m/n has an odd denominator. -/
def plusOverhead (k m n : ℕ) : P := bag m n * (twoInv ^ k * bInv)

/-- The opposite-sign finite word. -/
def minusOverhead (k m n : ℕ) : P := bag n m * (twoInv ^ k * aInv)

/-- Single dyadic positive-imaginary program. -/
def plusWord (k m : ℕ) : P := plusOverhead k m (2 ^ k)

/-- Single dyadic negative-imaginary program. -/
def minusWord (k m : ℕ) : P := minusOverhead k m (2 ^ k)

/-- The analytic packet's paired word, with all exponents natural and finite. -/
def pairedWord (k m n : ℕ) : P := (plusWord k m * minusWord k m) ^ n

/-- Fixed complex-coordinate norm-square used by the target theorem. -/
def normSq (p : P) : ℝ := Complex.normSq (complexEvaluation p)

theorem normSq_nonnegative (p : P) : 0 ≤ normSq p :=
  Complex.normSq_nonneg (complexEvaluation p)

theorem normSq_mul (p q : P) : normSq (p * q) = normSq p * normSq q := by
  simp only [normSq, map_mul]

theorem evaluation_a : complexEvaluation a = complexA := by
  exact congrArg Prod.fst raw_a

theorem evaluation_b : complexEvaluation b = complexB := by
  exact congrArg Prod.fst raw_b

theorem evaluation_twoInv : complexEvaluation twoInv = ((1 / 2 : ℝ) : ℂ) := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  calc
    (2 : ℂ) * complexEvaluation twoInv = 1 := by
      simpa only [map_mul, map_ofNat, map_one] using
        congrArg complexEvaluation two_mul_twoInv
    _ = (2 : ℂ) * ((1 / 2 : ℝ) : ℂ) := by norm_num

theorem shadow_twoInv : realShadow twoInv = (1 / 2 : ℝ) := by
  have hi := congrArg realShadow two_mul_twoInv
  simp only [map_mul, map_ofNat, map_one] at hi
  linarith

theorem evaluation_aInv : complexEvaluation aInv = 1 - Complex.I := by
  have hA : complexA ≠ 0 := by
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [complexA, Complex.div_re, Complex.div_im] at hr
  apply mul_right_cancel₀ hA
  calc
    complexEvaluation aInv * complexA = 1 := by
      simpa only [map_mul, evaluation_a, map_one] using
        congrArg complexEvaluation aInv_mul_a
    _ = (1 - Complex.I) * complexA := by
      apply Complex.ext <;>
        norm_num [complexA, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem evaluation_bInv : complexEvaluation bInv = 1 + Complex.I := by
  have hB : complexB ≠ 0 := by
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [complexB, Complex.div_re, Complex.div_im] at hr
  apply mul_right_cancel₀ hB
  calc
    complexEvaluation bInv * complexB = 1 := by
      simpa only [map_mul, evaluation_b, map_one] using
        congrArg complexEvaluation bInv_mul_b
    _ = (1 + Complex.I) * complexB := by
      apply Complex.ext <;>
        norm_num [complexB, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem shadow_aInv : realShadow aInv = 2 := by
  have hi := congrArg realShadow aInv_mul_a
  simp only [map_mul, realShadow_a, map_one] at hi
  linarith

theorem shadow_bInv : realShadow bInv = 2 := by
  have hi := congrArg realShadow bInv_mul_b
  simp only [map_mul, realShadow_b, map_one] at hi
  linarith

theorem plusOverhead_coordinates (k m n : ℕ) :
    complexEvaluation (plusOverhead k m n) =
      (((n : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) +
        (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I ∧
    realShadow (plusOverhead k m n) = ((n : ℝ) + (m : ℝ)) / (2 : ℝ) ^ k := by
  constructor
  · simp only [plusOverhead, bag, map_mul, map_add, map_natCast, map_pow,
      evaluation_a, evaluation_b, evaluation_twoInv, evaluation_bInv]
    rw [← Complex.ofReal_pow]
    apply Complex.ext <;>
      norm_num only [complexA, complexB, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.normSq_apply, one_div] <;> ring_nf <;> norm_num
  · simp only [plusOverhead, bag, map_mul, map_add, map_natCast, map_pow,
      realShadow_a, realShadow_b, shadow_twoInv, shadow_bInv]
    simp only [one_div_pow]
    ring

theorem minusOverhead_coordinates (k m n : ℕ) :
    complexEvaluation (minusOverhead k m n) =
      (((n : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) -
        (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I ∧
    realShadow (minusOverhead k m n) = ((n : ℝ) + (m : ℝ)) / (2 : ℝ) ^ k := by
  constructor
  · simp only [minusOverhead, bag, map_mul, map_add, map_natCast, map_pow,
      evaluation_a, evaluation_b, evaluation_twoInv, evaluation_aInv]
    rw [← Complex.ofReal_pow]
    apply Complex.ext <;>
      norm_num only [complexA, complexB, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.normSq_apply, one_div] <;> ring_nf <;> norm_num
  · simp only [minusOverhead, bag, map_mul, map_add, map_natCast, map_pow,
      realShadow_a, realShadow_b, shadow_twoInv, shadow_aInv]
    simp only [one_div_pow]
    ring

theorem plusWord_coordinates (k m : ℕ) :
    complexEvaluation (plusWord k m) =
      1 + (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I ∧
    realShadow (plusWord k m) = 1 + (m : ℝ) / (2 : ℝ) ^ k := by
  have hd : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  simpa only [plusWord, Nat.cast_pow, Nat.cast_ofNat, div_self hd,
    Complex.ofReal_one, add_div] using plusOverhead_coordinates k m (2 ^ k)

theorem minusWord_coordinates (k m : ℕ) :
    complexEvaluation (minusWord k m) =
      1 - (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I ∧
    realShadow (minusWord k m) = 1 + (m : ℝ) / (2 : ℝ) ^ k := by
  have hd : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  simpa only [minusWord, Nat.cast_pow, Nat.cast_ofNat, div_self hd,
    Complex.ofReal_one, add_div] using minusOverhead_coordinates k m (2 ^ k)

theorem pairedWord_coordinates (k m n : ℕ) :
    complexEvaluation (pairedWord k m n) =
      (((1 + ((m : ℝ) / (2 : ℝ) ^ k) ^ 2) ^ n : ℝ) : ℂ) ∧
    realShadow (pairedWord k m n) =
      (1 + (m : ℝ) / (2 : ℝ) ^ k) ^ (2 * n) := by
  obtain ⟨hp, hps⟩ := plusWord_coordinates k m
  obtain ⟨hm, hms⟩ := minusWord_coordinates k m
  constructor
  · rw [pairedWord, map_pow, map_mul, hp, hm]
    have hpure :
        (1 + (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I) *
          (1 - (((m : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I) =
          (((1 + ((m : ℝ) / (2 : ℝ) ^ k) ^ 2) : ℝ) : ℂ) := by
      generalize (m : ℝ) / (2 : ℝ) ^ k = t
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] <;> ring
    rw [hpure, Complex.ofReal_pow]
  · rw [pairedWord, map_pow, map_mul, hps, hms]
    rw [show (1 + (m : ℝ) / (2 : ℝ) ^ k) *
      (1 + (m : ℝ) / (2 : ℝ) ^ k) =
      (1 + (m : ℝ) / (2 : ℝ) ^ k) ^ 2 by ring, ← pow_mul]

theorem bag_complex_coordinates (n m : ℕ) :
    (complexEvaluation (bag n m)).re = ((n : ℝ) + (m : ℝ)) / 2 ∧
    (complexEvaluation (bag n m)).im = ((n : ℝ) - (m : ℝ)) / 2 := by
  simp only [bag, map_add, map_mul, map_natCast, evaluation_a, evaluation_b]
  constructor <;>
    simp [complexA, complexB] <;> ring

theorem bag_shadow (n m : ℕ) :
    realShadow (bag n m) = ((n : ℝ) + (m : ℝ)) / 2 := by
  simp only [bag, map_add, map_mul, map_natCast, realShadow_a, realShadow_b]
  ring

theorem normSq_bag (n m : ℕ) :
    normSq (bag n m) = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  obtain ⟨hre, him⟩ := bag_complex_coordinates n m
  rw [normSq, Complex.normSq_apply, hre, him]
  ring

/-- Exactness always uses both coordinates of the checked normal form. -/
theorem eq_of_combined_coordinates {p q : P}
    (hz : complexEvaluation p = complexEvaluation q)
    (hq : realShadow p = realShadow q) : p = q := by
  apply rawSemantics_injective
  exact Prod.ext hz hq

theorem evaluation_real_imag_dyadic (p : P) :
    (complexEvaluation p).re ∈ realDyadic ∧
      (complexEvaluation p).im ∈ realDyadic := by
  have hp := raw_mem_normalSemiring p
  change (complexEvaluation p = 0 ∧ realShadow p = 0) ∨
    (complexEvaluation p ∈ gaussianDyadic ∧ realShadow p ∈ realDyadic ∧
      0 < realShadow p) at hp
  rcases hp with hp | hp
  · rw [hp.1]
    exact ⟨realDyadic.zero_mem, realDyadic.zero_mem⟩
  · obtain ⟨k, m, n, hform⟩ := (mem_gaussianDyadic _).mp hp.1
    have hcast : (((2 : ℝ) ^ k : ℝ) : ℂ) = (2 : ℂ) ^ k := by norm_cast
    constructor
    · apply (mem_realDyadic _).mpr
      refine ⟨k, m, ?_⟩
      rw [hform, ← hcast]
      simp only [Complex.div_ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, sub_zero]
    · apply (mem_realDyadic _).mpr
      refine ⟨k, n, ?_⟩
      rw [hform, ← hcast]
      simp only [Complex.div_ofReal_im, Complex.add_im, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_add]

theorem nonnegative_dyadic_representation (s : ℝ) (hs : 0 ≤ s)
    (hmem : s ∈ realDyadic) :
    ∃ k n : ℕ, s = (n : ℝ) / (2 : ℝ) ^ k := by
  obtain ⟨k, m, hm⟩ := (mem_realDyadic s).mp hmem
  have hden : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hmR : (0 : ℝ) ≤ m := by
    rw [← (eq_div_iff hden).mp hm]
    exact mul_nonneg hs (pow_nonneg (by norm_num) k)
  have hmZ : (0 : ℤ) ≤ m := by exact_mod_cast hmR
  refine ⟨k, m.toNat, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hmZ
  rw [hcast]
  exact hm

/-- Nonnegative dyadic counts share one binary denominator. -/
theorem common_nonnegative_dyadic_counts (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsmem : s ∈ realDyadic) (htmem : t ∈ realDyadic) :
    ∃ k n m : ℕ, s = (n : ℝ) / (2 : ℝ) ^ k ∧
      t = (m : ℝ) / (2 : ℝ) ^ k := by
  obtain ⟨k, n, hn⟩ := nonnegative_dyadic_representation s hs hsmem
  obtain ⟨l, m, hm⟩ := nonnegative_dyadic_representation t ht htmem
  refine ⟨k + l, n * 2 ^ l, m * 2 ^ k, ?_, ?_⟩
  · rw [hn]
    push_cast
    rw [pow_add]
    field_simp
  · rw [hm]
    push_cast
    rw [pow_add]
    field_simp

/-- Every dyadic coordinate point in the raw cone with shadow equal to its
complex real part is exactly a binary-scaled natural raw bag in initial P. -/
theorem exists_dyadic_raw_endpoint (p : P)
    (hshadow : realShadow p = (complexEvaluation p).re)
    (hxmem : (complexEvaluation p).re ∈ realDyadic)
    (hymem : (complexEvaluation p).im ∈ realDyadic)
    (hcone : |(complexEvaluation p).im| ≤ (complexEvaluation p).re) :
    ∃ k n m : ℕ, p = twoInv ^ k * bag n m := by
  let x := (complexEvaluation p).re
  let y := (complexEvaluation p).im
  have hylo : -x ≤ y := (abs_le.mp hcone).1
  have hyhi : y ≤ x := (abs_le.mp hcone).2
  obtain ⟨k, n, m, hn, hm⟩ := common_nonnegative_dyadic_counts (x + y) (x - y)
    (by linarith) (by linarith)
    (realDyadic.add_mem hxmem hymem) (realDyadic.sub_mem hxmem hymem)
  have hd : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hnx : (x + y) * (2 : ℝ) ^ k = (n : ℝ) := (eq_div_iff hd).mp hn
  have hmx : (x - y) * (2 : ℝ) ^ k = (m : ℝ) := (eq_div_iff hd).mp hm
  have hsum : ((n : ℝ) + (m : ℝ)) / 2 = x * (2 : ℝ) ^ k := by
    nlinarith [hnx, hmx]
  have hdiff : ((n : ℝ) - (m : ℝ)) / 2 = y * (2 : ℝ) ^ k := by
    nlinarith [hnx, hmx]
  obtain ⟨hbr, hbi⟩ := bag_complex_coordinates n m
  refine ⟨k, n, m, ?_⟩
  apply eq_of_combined_coordinates
  · apply Complex.ext
    · simp only [map_mul, map_pow, evaluation_twoInv, ← Complex.ofReal_pow,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        hbr, one_div_pow]
      change x = (1 / (2 : ℝ) ^ k) * (((n : ℝ) + (m : ℝ)) / 2)
      rw [hsum]
      field_simp
    · simp only [map_mul, map_pow, evaluation_twoInv, ← Complex.ofReal_pow,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        hbi, one_div_pow]
      change y = (1 / (2 : ℝ) ^ k) * (((n : ℝ) - (m : ℝ)) / 2)
      rw [hdiff]
      field_simp
  · rw [hshadow, map_mul, map_pow, shadow_twoInv, bag_shadow, one_div_pow, hsum]
    change x = (1 / (2 : ℝ) ^ k) * (x * (2 : ℝ) ^ k)
    field_simp

theorem exists_raw_endpoint_of_cone (p : P)
    (hshadow : realShadow p = (complexEvaluation p).re)
    (hcone : |(complexEvaluation p).im| ≤ (complexEvaluation p).re) :
    ∃ k n m : ℕ, p = twoInv ^ k * bag n m := by
  obtain ⟨hx, hy⟩ := evaluation_real_imag_dyadic p
  exact exists_dyadic_raw_endpoint p hshadow hx hy hcone

theorem dyadic_raw_endpoint_count_ratios (p : P) (k n m : ℕ)
    (hp : p = twoInv ^ k * bag n m) :
    (n : ℝ) / (2 : ℝ) ^ k = (complexEvaluation p).re + (complexEvaluation p).im ∧
    (m : ℝ) / (2 : ℝ) ^ k = (complexEvaluation p).re - (complexEvaluation p).im := by
  obtain ⟨hbr, hbi⟩ := bag_complex_coordinates n m
  rw [hp]
  simp only [map_mul, map_pow, evaluation_twoInv, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, hbr, hbi, one_div_pow]
  constructor <;> ring

/-- A finite exact transport displays the raw input and target counts. -/
structure ExactRawTransport (M p : P) where
  rawA : ℕ
  rawB : ℕ
  targetA : ℕ
  targetB : ℕ
  identity : M * bag rawA rawB = bag targetA targetB * p

def ExactRawTransport.height {M p : P} (d : ExactRawTransport M p) : ℕ :=
  max d.targetA d.targetB

/-- Expose the source counts individually for later calibration-independent
envelopes. These are numerical ratios, with no response evaluation. -/
def ExactRawTransport.sourceRatios {M p : P} (d : ExactRawTransport M p) : ℝ × ℝ :=
  ((d.rawA : ℝ) / d.height, (d.rawB : ℝ) / d.height)

theorem repeated_transport {M p : P} (d : ExactRawTransport M p) (j : ℕ) :
    M * ((j : P) * bag d.rawA d.rawB) =
      bag (j * d.targetA) (j * d.targetB) * p := by
  calc
    M * ((j : P) * bag d.rawA d.rawB) =
        (j : P) * (M * bag d.rawA d.rawB) := by ring
    _ = (j : P) * (bag d.targetA d.targetB * p) := by rw [d.identity]
    _ = bag (j * d.targetA) (j * d.targetB) * p := by rw [← mul_assoc, nat_mul_bag]

/-- Combined-coordinate verification for a designed raw transport. All supplied
equations concern finite algebraic endpoints; no response occurs here. -/
theorem exact_transport_of_complex_coordinates
    (M p : P) (u v A B : ℕ) (R S Q x y q x0 v0 X Y : ℝ)
    (hMr : (complexEvaluation M).re = R) (hMi : (complexEvaluation M).im = S)
    (hMq : realShadow M = Q)
    (hpr : (complexEvaluation p).re = x) (hpi : (complexEvaluation p).im = y)
    (hpq : realShadow p = q)
    (hu : (u : ℝ) = x0 * (1 + v0)) (hv : (v : ℝ) = x0 * (1 - v0))
    (hA : (A : ℝ) = X + Y) (hB : (B : ℝ) = X - Y)
    (hreal : X * x - Y * y = x0 * (R - S * v0))
    (himag : X * y + Y * x = x0 * (S + R * v0))
    (hshadow : X * q = Q * x0) :
    M * bag u v = bag A B * p := by
  obtain ⟨hur, hui⟩ := bag_complex_coordinates u v
  obtain ⟨hAr, hAi⟩ := bag_complex_coordinates A B
  apply eq_of_combined_coordinates
  · apply Complex.ext
    · simp only [map_mul, Complex.mul_re, hMr, hMi, hpr, hpi, hur, hui, hAr, hAi]
      rw [hu, hv, hA, hB]
      nlinarith [hreal]
    · simp only [map_mul, Complex.mul_im, hMr, hMi, hpr, hpi, hur, hui, hAr, hAi]
      rw [hu, hv, hA, hB]
      nlinarith [himag]
  · rw [map_mul, map_mul, hMq, hpq, bag_shadow, bag_shadow, hu, hv, hA, hB]
    nlinarith [hshadow]

/-- One rational coefficient has a positive natural denominator and a natural
numerator whenever it is nonnegative. -/
theorem nonnegative_rational_counts (s : ℚ) (hs : 0 ≤ s) :
    ∃ d n : ℕ, 0 < d ∧ (n : ℚ) = (d : ℚ) * s := by
  have hn : 0 ≤ s.num := Rat.num_nonneg.mpr hs
  refine ⟨s.den, s.num.toNat, s.den_pos, ?_⟩
  have hnum : ((s.num.toNat : ℕ) : ℚ) = (s.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hnum]
  have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  calc
    (s.num : ℚ) = (s.den : ℚ) * ((s.num : ℚ) / (s.den : ℚ)) := by field_simp
    _ = (s.den : ℚ) * s := by rw [s.num_div_den]

/-- Clear both raw and both target denominators in one finite natural scale. -/
theorem clear_four_nonnegative_rationals (s t A B : ℚ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ x0 u v a0 b0 : ℕ, 0 < x0 ∧
      (u : ℚ) = (x0 : ℚ) * s ∧ (v : ℚ) = (x0 : ℚ) * t ∧
      (a0 : ℚ) = (x0 : ℚ) * A ∧ (b0 : ℚ) = (x0 : ℚ) * B := by
  obtain ⟨ds, ns, hds, hns⟩ := nonnegative_rational_counts s hs
  obtain ⟨dt, nt, hdt, hnt⟩ := nonnegative_rational_counts t ht
  obtain ⟨dA, nA, hdA, hnA⟩ := nonnegative_rational_counts A hA
  obtain ⟨dB, nB, hdB, hnB⟩ := nonnegative_rational_counts B hB
  refine ⟨ds * dt * dA * dB, ns * dt * dA * dB, ds * nt * dA * dB,
    ds * dt * nA * dB, ds * dt * dA * nB, by positivity, ?_, ?_, ?_, ?_⟩
  · push_cast
    rw [hns]
    ring
  · push_cast
    rw [hnt]
    ring
  · push_cast
    rw [hnA]
    ring
  · push_cast
    rw [hnB]
    ring

/-- The source-count ratios are independent of the denominator-clearing scale.
They retain both counts separately for calibration-independent applications. -/
theorem raw_source_ratios (u v A B x0 : ℕ) (v0 X Y : ℝ)
    (hx0 : 0 < x0)
    (hu : (u : ℝ) = (x0 : ℝ) * (1 + v0))
    (hv : (v : ℝ) = (x0 : ℝ) * (1 - v0))
    (hA : (A : ℝ) = (x0 : ℝ) * (X + Y))
    (hB : (B : ℝ) = (x0 : ℝ) * (X - Y))
    (hXY : 0 < X + |Y|) :
    (u : ℝ) / (max A B : ℕ) = (1 + v0) / (X + |Y|) ∧
    (v : ℝ) / (max A B : ℕ) = (1 - v0) / (X + |Y|) := by
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hm : ((max A B : ℕ) : ℝ) = (x0 : ℝ) * (X + |Y|) := by
    by_cases hY : 0 ≤ Y
    · have hBA : B ≤ A := by
        have hreal : (B : ℝ) ≤ A := by rw [hA, hB]; nlinarith
        exact_mod_cast hreal
      rw [max_eq_left hBA, hA, abs_of_nonneg hY]
    · have hAB : A ≤ B := by
        have hreal : (A : ℝ) ≤ B := by rw [hA, hB]; nlinarith
        exact_mod_cast hreal
      rw [max_eq_right hAB, hB, abs_of_nonpos (lt_of_not_ge hY).le]
      ring
  rw [hm, hu, hv]
  constructor <;> field_simp [ne_of_gt hx0r, ne_of_gt hXY]

/-- Finite upper landing from the exact balance and cone equations. Natural
count order realizes this overhead program, including odd-denominator ratios.
The initial P element is identified using both semantic coordinates. -/
theorem overhead_raw_landing
    (M p : P) (R Q x y q : ℝ) (k m n : ℕ)
    (hMr : (complexEvaluation M).re = R) (hMi : (complexEvaluation M).im = 0)
    (hMq : realShadow M = Q)
    (hpr : (complexEvaluation p).re = x) (hpi : (complexEvaluation p).im = y)
    (hpq : realShadow p = q) (hR : 0 ≤ R)
    (hbalance : (q * Q) * ((n : ℝ) / (2 : ℝ) ^ k + (m : ℝ) / (2 : ℝ) ^ k) =
      R * (((n : ℝ) / (2 : ℝ) ^ k) * x - ((m : ℝ) / (2 : ℝ) ^ k) * y))
    (hcone : |((n : ℝ) / (2 : ℝ) ^ k) * y + ((m : ℝ) / (2 : ℝ) ^ k) * x| ≤
      ((n : ℝ) / (2 : ℝ) ^ k) * x - ((m : ℝ) / (2 : ℝ) ^ k) * y) :
    ∃ j u v : ℕ, (plusOverhead k m n * M) * p = twoInv ^ j * bag u v := by
  obtain ⟨hD, hDq⟩ := plusOverhead_coordinates k m n
  have hDr : (complexEvaluation (plusOverhead k m n)).re = (n : ℝ) / (2 : ℝ) ^ k := by
    rw [hD]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, sub_zero]
  have hDi : (complexEvaluation (plusOverhead k m n)).im = (m : ℝ) / (2 : ℝ) ^ k := by
    rw [hD]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
  have hEre : (complexEvaluation ((plusOverhead k m n * M) * p)).re =
      R * (((n : ℝ) / (2 : ℝ) ^ k) * x - ((m : ℝ) / (2 : ℝ) ^ k) * y) := by
    simp only [map_mul, Complex.mul_re, Complex.mul_im, hDr, hDi, hMr, hMi, hpr, hpi]
    ring
  have hEim : (complexEvaluation ((plusOverhead k m n * M) * p)).im =
      R * (((n : ℝ) / (2 : ℝ) ^ k) * y + ((m : ℝ) / (2 : ℝ) ^ k) * x) := by
    simp only [map_mul, Complex.mul_re, Complex.mul_im, hDr, hDi, hMr, hMi, hpr, hpi]
    ring
  apply exists_raw_endpoint_of_cone
  · rw [map_mul, map_mul, hDq, hMq, hpq, hEre]
    simpa only [add_div, mul_assoc, mul_comm, mul_left_comm] using hbalance
  · rw [hEre, hEim, abs_mul, abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left hcone hR

/-- Denominator-cleared construction of an actual finite raw transport.
Rational divisions are confined to designing these numerical coefficients. -/
theorem exists_transport_from_rational_design
    (M p : P) (x y q R S Q v0 X Y : ℚ)
    (hMr : (complexEvaluation M).re = (R : ℝ))
    (hMi : (complexEvaluation M).im = (S : ℝ)) (hMq : realShadow M = (Q : ℝ))
    (hpr : (complexEvaluation p).re = (x : ℝ))
    (hpi : (complexEvaluation p).im = (y : ℝ))
    (hpq : realShadow p = (q : ℝ))
    (hv : |v0| < 1) (hXY : |Y| < X)
    (hreal : X * x - Y * y = R - S * v0)
    (himag : X * y + Y * x = S + R * v0)
    (hshadow : X * q = Q) :
    ∃ d : ExactRawTransport M p, 0 < d.height ∧
      d.sourceRatios =
        ((1 + (v0 : ℝ)) / ((X : ℝ) + |(Y : ℝ)|),
          (1 - (v0 : ℝ)) / ((X : ℝ) + |(Y : ℝ)|)) := by
  have hvlo := (abs_lt.mp hv).1
  have hvhi := (abs_lt.mp hv).2
  have hYlo : -X < Y := (abs_lt.mp hXY).1
  have hYhi : Y < X := (abs_lt.mp hXY).2
  have hX : 0 < X := (abs_nonneg Y).trans_lt hXY
  obtain ⟨N, u, v, A, B, hN, hu, hvraw, hA, hB⟩ :=
    clear_four_nonnegative_rationals (1 + v0) (1 - v0) (X + Y) (X - Y)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have huR : (u : ℝ) = (N : ℝ) * (1 + (v0 : ℝ)) := by exact_mod_cast hu
  have hvR : (v : ℝ) = (N : ℝ) * (1 - (v0 : ℝ)) := by exact_mod_cast hvraw
  have hAR : (A : ℝ) = (N : ℝ) * ((X : ℝ) + (Y : ℝ)) := by exact_mod_cast hA
  have hBR : (B : ℝ) = (N : ℝ) * ((X : ℝ) - (Y : ℝ)) := by exact_mod_cast hB
  have hAr : (A : ℝ) = (N : ℝ) * (X : ℝ) + (N : ℝ) * (Y : ℝ) := by
    rw [hAR]
    ring
  have hBr : (B : ℝ) = (N : ℝ) * (X : ℝ) - (N : ℝ) * (Y : ℝ) := by
    rw [hBR]
    ring
  have hrealR : (X : ℝ) * (x : ℝ) - (Y : ℝ) * (y : ℝ) =
      (R : ℝ) - (S : ℝ) * (v0 : ℝ) := by
    exact_mod_cast hreal
  have himagR : (X : ℝ) * (y : ℝ) + (Y : ℝ) * (x : ℝ) =
      (S : ℝ) + (R : ℝ) * (v0 : ℝ) := by
    exact_mod_cast himag
  have hshadowR : (X : ℝ) * (q : ℝ) = (Q : ℝ) := by exact_mod_cast hshadow
  have hexact : M * bag u v = bag A B * p := by
    apply exact_transport_of_complex_coordinates M p u v A B
      (R : ℝ) (S : ℝ) (Q : ℝ) (x : ℝ) (y : ℝ) (q : ℝ) (N : ℝ) (v0 : ℝ)
      ((N : ℝ) * (X : ℝ)) ((N : ℝ) * (Y : ℝ))
      hMr hMi hMq hpr hpi hpq huR hvR hAr hBr
    · calc
        (N : ℝ) * (X : ℝ) * (x : ℝ) - (N : ℝ) * (Y : ℝ) * (y : ℝ) =
            (N : ℝ) * ((X : ℝ) * (x : ℝ) - (Y : ℝ) * (y : ℝ)) := by ring
        _ = (N : ℝ) * ((R : ℝ) - (S : ℝ) * (v0 : ℝ)) := by rw [hrealR]
    · calc
        (N : ℝ) * (X : ℝ) * (y : ℝ) + (N : ℝ) * (Y : ℝ) * (x : ℝ) =
            (N : ℝ) * ((X : ℝ) * (y : ℝ) + (Y : ℝ) * (x : ℝ)) := by ring
        _ = (N : ℝ) * ((S : ℝ) + (R : ℝ) * (v0 : ℝ)) := by rw [himagR]
    · calc
        (N : ℝ) * (X : ℝ) * (q : ℝ) = (N : ℝ) * ((X : ℝ) * (q : ℝ)) := by ring
        _ = (Q : ℝ) * (N : ℝ) := by rw [hshadowR]; ring
  let d : ExactRawTransport M p := ⟨u, v, A, B, hexact⟩
  have hsumR : (0 : ℝ) < (A : ℝ) + B := by
    rw [hAR, hBR]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    nlinarith [mul_pos hNR hXR]
  have hsum : 0 < A + B := by exact_mod_cast hsumR
  have hd : 0 < d.height := by
    change 0 < max A B
    have ha := Nat.le_max_left A B
    have hb := Nat.le_max_right A B
    omega
  have hpos : (0 : ℝ) < (X : ℝ) + |(Y : ℝ)| := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    linarith [abs_nonneg (Y : ℝ)]
  have hrat := raw_source_ratios u v A B N (v0 : ℝ) (X : ℝ) (Y : ℝ)
    hN huR hvR hAR hBR hpos
  refine ⟨d, hd, ?_⟩
  exact Prod.ext hrat.1 hrat.2

/-- The unscaled cross-return word. -/
def h : P := a * b

/-- The inverse cross-return is a positive finite preparation. -/
def cInv : P := twoInv * aInv * bInv

theorem c_mul_cInv : c * cInv = 1 := by
  calc
    c * cInv = ((2 : P) * twoInv) * (a * aInv) * (b * bInv) := by
      dsimp [c, cInv]
      ring
    _ = 1 := by rw [two_mul_twoInv, a_mul_aInv, b_mul_bInv]; simp

theorem cInv_mul_c : cInv * c = 1 := by rw [mul_comm, c_mul_cInv]

theorem c_power_cancel (k : ℕ) : c ^ k * cInv ^ k = 1 := by
  rw [← mul_pow, c_mul_cInv, one_pow]

theorem c_power_cancel_reverse (k : ℕ) : cInv ^ k * c ^ k = 1 := by
  rw [← mul_pow, cInv_mul_c, one_pow]

theorem h_eq_c_mul_twoInv : h = c * twoInv := by
  calc
    h = ((2 : P) * twoInv) * (a * b) := by rw [two_mul_twoInv]; simp only [h, one_mul]
    _ = c * twoInv := by dsimp [c]; ring

theorem evaluation_h : complexEvaluation h = ((1 / 2 : ℝ) : ℂ) := by
  rw [h, map_mul, evaluation_a, evaluation_b]
  apply Complex.ext <;>
    norm_num [complexA, complexB, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im]

theorem shadow_h : realShadow h = (1 / 4 : ℝ) := by
  norm_num [h, map_mul, realShadow_a, realShadow_b]

theorem evaluation_c : complexEvaluation c = 1 := by
  have hc : c = (2 : P) * h := by dsimp [c, h]; ring
  rw [hc, map_mul, map_ofNat, evaluation_h]
  norm_num

theorem shadow_c : realShadow c = (1 / 2 : ℝ) := by
  norm_num [c, map_mul, map_ofNat, realShadow_a, realShadow_b]

theorem evaluation_cInv : complexEvaluation cInv = 1 := by
  have hc := congrArg complexEvaluation c_mul_cInv
  simpa only [map_mul, evaluation_c, one_mul, map_one] using hc

theorem shadow_cInv : realShadow cInv = 2 := by
  have hc := congrArg realShadow c_mul_cInv
  rw [map_mul, shadow_c, map_one] at hc
  linarith

/-- The serial/scalar relation is an identity of actual initial elements. -/
theorem serial_scalar_word_grid_identity (j k : ℕ) (hjk : j ≤ k) :
    c ^ k * twoInv ^ j = (2 ^ (k - j) : P) * h ^ k := by
  have hk : k = (k - j) + j := (Nat.sub_add_cancel hjk).symm
  have hh : (2 : P) * h = c := by dsimp [h, c]; ring
  calc
    c ^ k * twoInv ^ j =
        c ^ (k - j) * (c * twoInv) ^ j := by
      conv_lhs => rw [hk]
      rw [pow_add, mul_pow]
      ring
    _ = ((2 : P) * h) ^ (k - j) * h ^ j := by rw [← h_eq_c_mul_twoInv, hh]
    _ = (2 ^ (k - j) : P) * h ^ k := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hjk]

/-- Nonnegative dyadic numerical counts, with no order completion. -/
abbrev DyadicCount := {s : ℝ // s ∈ realDyadic ∧ 0 ≤ s}

/-- Canonical value of a finite binary count. -/
def dyadicCount (k n : ℕ) : DyadicCount :=
  ⟨(n : ℝ) / (2 : ℝ) ^ k,
    (mem_realDyadic _).mpr ⟨k, (n : ℤ), by simp only [Int.cast_natCast]⟩, by positivity⟩

@[simp] theorem dyadicCount_value (k n : ℕ) :
    (dyadicCount k n : ℝ) = (n : ℝ) / (2 : ℝ) ^ k := rfl

/-- The inverse checked normal form constructs the actual scalar element.
At numerical zero its two coordinates are both zero. -/
def scalar (d : DyadicCount) : P :=
  normalFormEquiv.symm ⟨(((d : ℝ) : ℂ), (d : ℝ)), by
    change (((d : ℝ) : ℂ) = 0 ∧ (d : ℝ) = 0) ∨
      (((d : ℝ) : ℂ) ∈ gaussianDyadic ∧ (d : ℝ) ∈ realDyadic ∧ 0 < (d : ℝ))
    by_cases hd : (d : ℝ) = 0
    · exact Or.inl ⟨by simp [hd], hd⟩
    · exact Or.inr ⟨d.property.1, d.property.1,
        lt_of_le_of_ne d.property.2 (Ne.symm hd)⟩⟩

theorem scalar_coordinates (d : DyadicCount) :
    complexEvaluation (scalar d) = ((d : ℝ) : ℂ) ∧ realShadow (scalar d) = (d : ℝ) := by
  have hc := congrArg Subtype.val (normalFormEquiv.apply_symm_apply
    (⟨(((d : ℝ) : ℂ), (d : ℝ)), by
      change (((d : ℝ) : ℂ) = 0 ∧ (d : ℝ) = 0) ∨
        (((d : ℝ) : ℂ) ∈ gaussianDyadic ∧ (d : ℝ) ∈ realDyadic ∧ 0 < (d : ℝ))
      by_cases hd : (d : ℝ) = 0
      · exact Or.inl ⟨by simp [hd], hd⟩
      · exact Or.inr ⟨d.property.1, d.property.1,
          lt_of_le_of_ne d.property.2 (Ne.symm hd)⟩⟩ : normalSemiring))
  exact ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩

theorem evaluation_scalar (d : DyadicCount) :
    complexEvaluation (scalar d) = ((d : ℝ) : ℂ) := (scalar_coordinates d).1

theorem shadow_scalar (d : DyadicCount) :
    realShadow (scalar d) = (d : ℝ) := (scalar_coordinates d).2

/-- Raw coordinates use the same actual scalar construction on both axes. -/
def raw (s t : DyadicCount) : P := scalar s * a + scalar t * b

theorem raw_coordinates (s t : DyadicCount) :
    (complexEvaluation (raw s t)).re = ((s : ℝ) + (t : ℝ)) / 2 ∧
    (complexEvaluation (raw s t)).im = ((s : ℝ) - (t : ℝ)) / 2 ∧
    realShadow (raw s t) = ((s : ℝ) + (t : ℝ)) / 2 := by
  simp only [raw, map_add, map_mul, evaluation_scalar, shadow_scalar,
    evaluation_a, evaluation_b, realShadow_a, realShadow_b]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [complexA, complexB, Complex.mul_re, Complex.mul_im] <;> ring

theorem scalar_grid (k n : ℕ) : scalar (dyadicCount k n) = twoInv ^ k * (n : P) := by
  apply eq_of_combined_coordinates
  · rw [evaluation_scalar, map_mul, map_pow, evaluation_twoInv, map_natCast]
    change (((n : ℝ) / (2 : ℝ) ^ k : ℝ) : ℂ) =
      (((1 / 2 : ℝ) : ℂ) ^ k) * (n : ℂ)
    push_cast
    simp only [one_div_pow]
    ring
  · rw [shadow_scalar, map_mul, map_pow, shadow_twoInv, map_natCast]
    simp only [dyadicCount_value, one_div_pow]
    ring

theorem raw_grid (k n m : ℕ) :
    raw (dyadicCount k n) (dyadicCount k m) = twoInv ^ k * bag n m := by
  rw [raw, scalar_grid, scalar_grid]
  dsimp [bag]
  ring

/-- Four dyadic counts can be compared on one finite binary grid. -/
theorem common_four_nonnegative_dyadic_counts (s t u v : DyadicCount) :
    ∃ k n m n' m' : ℕ,
      (s : ℝ) = (n : ℝ) / (2 : ℝ) ^ k ∧
      (t : ℝ) = (m : ℝ) / (2 : ℝ) ^ k ∧
      (u : ℝ) = (n' : ℝ) / (2 : ℝ) ^ k ∧
      (v : ℝ) = (m' : ℝ) / (2 : ℝ) ^ k := by
  obtain ⟨k, n, m, hn, hm⟩ := common_nonnegative_dyadic_counts s t
    s.property.2 t.property.2 s.property.1 t.property.1
  obtain ⟨l, n', m', hn', hm'⟩ := common_nonnegative_dyadic_counts u v
    u.property.2 v.property.2 u.property.1 v.property.1
  refine ⟨k + l, n * 2 ^ l, m * 2 ^ l, n' * 2 ^ k, m' * 2 ^ k, ?_, ?_, ?_, ?_⟩
  · rw [hn]
    push_cast
    rw [pow_add]
    field_simp
  · rw [hm]
    push_cast
    rw [pow_add]
    field_simp
  · rw [hn']
    push_cast
    rw [pow_add]
    field_simp
  · rw [hm']
    push_cast
    rw [pow_add]
    field_simp

theorem shadow_dyadic (p : P) : realShadow p ∈ realDyadic := by
  have hp := raw_mem_normalSemiring p
  change (complexEvaluation p = 0 ∧ realShadow p = 0) ∨
    (complexEvaluation p ∈ gaussianDyadic ∧ realShadow p ∈ realDyadic ∧
      0 < realShadow p) at hp
  rcases hp with hp | hp
  · rw [hp.2]
    exact realDyadic.zero_mem
  · exact hp.2.1

theorem rational_of_dyadic (s : ℝ) (hs : s ∈ realDyadic) :
    ∃ q : ℚ, s = (q : ℝ) := by
  obtain ⟨k, m, hm⟩ := (mem_realDyadic s).mp hs
  refine ⟨(m : ℚ) / (2 : ℚ) ^ k, ?_⟩
  push_cast
  exact hm

/-- All design arithmetic can be performed in rational coordinates. -/
theorem rational_coordinates (p : P) :
    ∃ x y q : ℚ, (complexEvaluation p).re = (x : ℝ) ∧
      (complexEvaluation p).im = (y : ℝ) ∧ realShadow p = (q : ℝ) := by
  obtain ⟨hx, hy⟩ := evaluation_real_imag_dyadic p
  obtain ⟨x, hx⟩ := rational_of_dyadic _ hx
  obtain ⟨y, hy⟩ := rational_of_dyadic _ hy
  obtain ⟨q, hq⟩ := rational_of_dyadic _ (shadow_dyadic p)
  exact ⟨x, y, q, hx, hy, hq⟩

/-- A repeated transport commutes with every actual scalar shift. -/
theorem scalar_shifted_transport {M p : P} (d : ExactRawTransport M p)
    (s : P) (j : ℕ) :
    M * (s * bag (j * d.rawA) (j * d.rawB)) =
      bag (j * d.targetA) (j * d.targetB) * (s * p) := by
  rw [← nat_mul_bag, ← nat_mul_bag]
  calc
    M * (s * ((j : P) * bag d.rawA d.rawB)) =
        s * (M * ((j : P) * bag d.rawA d.rawB)) := by ring
    _ = s * (bag (j * d.targetA) (j * d.targetB) * p) := by
      rw [repeated_transport]
    _ = (j : P) * bag d.targetA d.targetB * (s * p) := by
      rw [← nat_mul_bag]
      ring

/-- Multiplication by the serial word cancels its inverse on the target. -/
theorem serial_shifted_transport {M p : P} (r : ℕ)
    (d : ExactRawTransport M (cInv ^ r * p)) :
    M * (c ^ r * bag d.rawA d.rawB) = bag d.targetA d.targetB * p := by
  calc
    M * (c ^ r * bag d.rawA d.rawB) = c ^ r * (M * bag d.rawA d.rawB) := by ring
    _ = c ^ r * (bag d.targetA d.targetB * (cInv ^ r * p)) := by rw [d.identity]
    _ = (c ^ r * cInv ^ r) * (bag d.targetA d.targetB * p) := by ring
    _ = bag d.targetA d.targetB * p := by rw [c_power_cancel, one_mul]

/-- Four nonnegative rational count coefficients determine one finite actual
transport whenever their three coordinate equations hold. The output retains
the clearing integer and every cleared count equation. -/
theorem exists_exact_transport_from_rational_counts
    (M p : P) (R S Q x y q s t A B : ℚ)
    (hMr : (complexEvaluation M).re = (R : ℝ))
    (hMi : (complexEvaluation M).im = (S : ℝ))
    (hMq : realShadow M = (Q : ℝ))
    (hpr : (complexEvaluation p).re = (x : ℝ))
    (hpi : (complexEvaluation p).im = (y : ℝ))
    (hpq : realShadow p = (q : ℝ))
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hreal : R * (s + t) - S * (s - t) = (A + B) * x - (A - B) * y)
    (himag : R * (s - t) + S * (s + t) = (A + B) * y + (A - B) * x)
    (hshadow : Q * (s + t) = (A + B) * q) :
    ∃ (N : ℕ) (d : ExactRawTransport M p), 0 < N ∧
      (d.rawA : ℚ) = (N : ℚ) * s ∧ (d.rawB : ℚ) = (N : ℚ) * t ∧
      (d.targetA : ℚ) = (N : ℚ) * A ∧ (d.targetB : ℚ) = (N : ℚ) * B := by
  obtain ⟨N, u, v, a0, b0, hN, hu, hv, ha, hb⟩ :=
    clear_four_nonnegative_rationals s t A B hs ht hA hB
  have huR : (u : ℝ) = (N : ℝ) * (s : ℝ) := by exact_mod_cast hu
  have hvR : (v : ℝ) = (N : ℝ) * (t : ℝ) := by exact_mod_cast hv
  have haR : (a0 : ℝ) = (N : ℝ) * (A : ℝ) := by exact_mod_cast ha
  have hbR : (b0 : ℝ) = (N : ℝ) * (B : ℝ) := by exact_mod_cast hb
  have hrealR : (R : ℝ) * ((s : ℝ) + (t : ℝ)) -
      (S : ℝ) * ((s : ℝ) - (t : ℝ)) =
      ((A : ℝ) + (B : ℝ)) * (x : ℝ) - ((A : ℝ) - (B : ℝ)) * (y : ℝ) := by
    exact_mod_cast hreal
  have himagR : (R : ℝ) * ((s : ℝ) - (t : ℝ)) +
      (S : ℝ) * ((s : ℝ) + (t : ℝ)) =
      ((A : ℝ) + (B : ℝ)) * (y : ℝ) + ((A : ℝ) - (B : ℝ)) * (x : ℝ) := by
    exact_mod_cast himag
  have hshadowR : (Q : ℝ) * ((s : ℝ) + (t : ℝ)) =
      ((A : ℝ) + (B : ℝ)) * (q : ℝ) := by exact_mod_cast hshadow
  have hexact : M * bag u v = bag a0 b0 * p := by
    obtain ⟨hur, hui⟩ := bag_complex_coordinates u v
    obtain ⟨har, hai⟩ := bag_complex_coordinates a0 b0
    apply eq_of_combined_coordinates
    · apply Complex.ext
      · simp only [map_mul, Complex.mul_re, hMr, hMi, hpr, hpi, hur, hui, har, hai]
        rw [huR, hvR, haR, hbR]
        calc
          (R : ℝ) * ((N * (s : ℝ) + N * (t : ℝ)) / 2) -
              (S : ℝ) * ((N * (s : ℝ) - N * (t : ℝ)) / 2) =
              (N : ℝ) / 2 * ((R : ℝ) * ((s : ℝ) + (t : ℝ)) -
                (S : ℝ) * ((s : ℝ) - (t : ℝ))) := by ring
          _ = _ := by rw [hrealR]; ring
      · simp only [map_mul, Complex.mul_im, hMr, hMi, hpr, hpi, hur, hui, har, hai]
        rw [huR, hvR, haR, hbR]
        calc
          (R : ℝ) * ((N * (s : ℝ) - N * (t : ℝ)) / 2) +
              (S : ℝ) * ((N * (s : ℝ) + N * (t : ℝ)) / 2) =
              (N : ℝ) / 2 * ((R : ℝ) * ((s : ℝ) - (t : ℝ)) +
                (S : ℝ) * ((s : ℝ) + (t : ℝ))) := by ring
          _ = _ := by rw [himagR]; ring
    · rw [map_mul, map_mul, hMq, hpq, bag_shadow, bag_shadow, huR, hvR, haR, hbR]
      calc
        (Q : ℝ) * ((N * (s : ℝ) + N * (t : ℝ)) / 2) =
            (N : ℝ) / 2 * ((Q : ℝ) * ((s : ℝ) + (t : ℝ))) := by ring
        _ = _ := by rw [hshadowR]; ring
  exact ⟨N, ⟨u, v, a0, b0, hexact⟩, hN, hu, hv, ha, hb⟩

end
end IDT.QMClosure.InitialCountGeometry
