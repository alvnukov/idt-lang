import Proofs.QMClosure.RationalEchoRegularityControl
import Mathlib.Data.Nat.Log
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rational raw-weight selection from universal count order

The supplied carrier is the rational Gaussian plane. All serial products use
the named `gmul` operation, and the multiplicative unit is `gone`.

Count order is a universal law over unbounded natural counts. The real
codomain's Archimedean structure remains supplied. The raw weight is unbounded
and has no probability interpretation in this contract. The history-to-algebra,
reversal, count-order and actual echo-preparation bridges remain supplied
operational obligations.
-/

namespace IDT.QMClosure.RationalCountOrderReadout

open RationalEchoRegularityControl

noncomputable section

def scalar (q : ℚ) : Carrier := (q, 0)

def natWeight (w : Carrier → ℝ) (n : ℕ) : ℝ := w (scalar n)

structure WeightLaws (w : Carrier → ℝ) : Prop where
  nonnegative : ∀ z, 0 ≤ w z
  zero : w (0, 0) = 0
  one : w gone = 1
  multiplicative : ∀ z t, w (gmul z t) = w z * w t
  conjugation : ∀ z, w (gconj z) = w z
  count_step : ∀ n : ℕ, w (scalar n) ≤ w (scalar (n + 1 : ℕ))

def NondegenerateEcho (w : Carrier → ℝ) : Prop :=
  ∃ a b : Carrier, a ≠ (0, 0) ∧ b ≠ (0, 0) ∧ w a + w b = 1 ∧
    w (gmul a (gconj a) + gmul b (gconj b)) = 1

def BalancedEcho (w : Carrier → ℝ) : Prop :=
  ∃ c : Carrier, w c = 1 / 2 ∧
    w (gmul c (gconj c) + gmul c (gconj c)) = 1

theorem gmul_scalar (q r : ℚ) :
    gmul (scalar q) (scalar r) = scalar (q * r) := by
  simp [gmul, scalar]

theorem scalar_add (q r : ℚ) : scalar q + scalar r = scalar (q + r) := by
  simp [scalar]

theorem gmul_conjugate (z : Carrier) :
    gmul z (gconj z) = scalar (normQ z) := by
  ext <;> dsimp [gmul, gconj, scalar, normQ] <;> ring

theorem echo_eq_scalar (a b : Carrier) :
    gmul a (gconj a) + gmul b (gconj b) =
      scalar (normQ a + normQ b) := by
  rw [gmul_conjugate, gmul_conjugate, scalar_add]

theorem normQ_pos {z : Carrier} (hz : z ≠ (0, 0)) : 0 < normQ z := by
  have hne : normQ z ≠ 0 := by
    intro he
    obtain ⟨hx, hy⟩ := (normQ_eq_zero_iff z).mp he
    exact hz (Prod.ext hx hy)
  exact lt_of_le_of_ne (normQ_nonneg z) (Ne.symm hne)

theorem multiplicative_nat_pow {f : ℕ → ℝ}
    (h1 : f 1 = 1) (hm : ∀ m n, f (m * n) = f m * f n)
    (n k : ℕ) : f (n ^ k) = (f n) ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

/-- One dyadic bracket is reused for the weight and the ordinary count. -/
theorem dyadic_bracket (n k : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 2 ^ m ≤ n ^ k ∧ n ^ k ≤ 2 ^ (m + 1) := by
  have hn0 : n ≠ 0 := by omega
  refine ⟨Nat.log 2 (n ^ k), Nat.pow_log_le_self 2 (pow_ne_zero k hn0), ?_⟩
  exact (Nat.lt_pow_succ_log_self (by norm_num) (n ^ k)).le

/-- Uniform bounds on both ratios' powers force equality in the supplied
Archimedean real codomain. -/
theorem eq_of_mutually_bounded_powers {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : ∀ k : ℕ, x ^ k ≤ 4 * y ^ k)
    (hyx : ∀ k : ℕ, y ^ k ≤ 4 * x ^ k) : x = y := by
  apply le_antisymm
  · by_contra hle
    have hgt : y < x := lt_of_not_ge hle
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 : ℝ) ((one_lt_div₀ hy).mpr hgt)
    have hbound : (x / y) ^ k ≤ 4 := by
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos hy k)).mpr (hxy k)
    exact (not_lt_of_ge hbound) hk
  · by_contra hle
    have hgt : x < y := lt_of_not_ge hle
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 : ℝ) ((one_lt_div₀ hx).mpr hgt)
    have hbound : (y / x) ^ k ≤ 4 := by
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos hx k)).mpr (hyx k)
    exact (not_lt_of_ge hbound) hk

/-- A monotone completely multiplicative natural scalar weight with value
four at two is the square weight. This proof uses dyadic brackets directly. -/
theorem nat_square_character {f : ℕ → ℝ}
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hm : ∀ m n, f (m * n) = f m * f n)
    (hmono : Monotone f) (h2 : f 2 = 4) (n : ℕ) : f n = (n : ℝ) ^ 2 := by
  by_cases hn0 : n = 0
  · simpa [hn0] using h0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hfn : 0 < f n := by
    have h := hmono hn
    rw [h1] at h
    linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hpow := multiplicative_nat_pow h1 hm
  have hfour (m : ℕ) : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hcomm (k : ℕ) : ((n : ℝ) ^ k) ^ 2 = ((n : ℝ) ^ 2) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hbounds (k : ℕ) : ∃ m : ℕ,
      (4 : ℝ) ^ m ≤ (f n) ^ k ∧ (f n) ^ k ≤ 4 ^ (m + 1) ∧
      (4 : ℝ) ^ m ≤ ((n : ℝ) ^ 2) ^ k ∧
      ((n : ℝ) ^ 2) ^ k ≤ 4 ^ (m + 1) := by
    obtain ⟨m, hlo, hhi⟩ := dyadic_bracket n k hn
    have hwlo := hmono hlo
    have hwhi := hmono hhi
    rw [hpow, hpow, h2] at hwlo hwhi
    have hrlo : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlo
    have hrhi : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hhi
    have hslo := pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m) hrlo 2
    have hshi := pow_le_pow_left₀ (pow_nonneg hnR.le k) hrhi 2
    rw [hfour, hcomm] at hslo
    rw [hcomm, hfour] at hshi
    exact ⟨m, hwlo, hwhi, hslo, hshi⟩
  apply eq_of_mutually_bounded_powers hfn (sq_pos_of_pos hnR)
  · intro k
    obtain ⟨m, _, hupper, hlower, _⟩ := hbounds k
    calc
      (f n) ^ k ≤ (4 : ℝ) ^ (m + 1) := hupper
      _ = 4 * 4 ^ m := by rw [pow_succ]; ring
      _ ≤ 4 * ((n : ℝ) ^ 2) ^ k := mul_le_mul_of_nonneg_left hlower (by norm_num)
  · intro k
    obtain ⟨m, hlower, _, _, hupper⟩ := hbounds k
    calc
      ((n : ℝ) ^ 2) ^ k ≤ (4 : ℝ) ^ (m + 1) := hupper
      _ = 4 * 4 ^ m := by rw [pow_succ]; ring
      _ ≤ 4 * (f n) ^ k := mul_le_mul_of_nonneg_left hlower (by norm_num)

/-- The Archimedean real codomain excludes a nonzero slope whose natural
multiples have one fixed two-sided bound. -/
theorem eq_zero_of_bounded_nat_multiples {d C : ℝ}
    (hbound : ∀ k : ℕ, -C ≤ (k : ℝ) * d ∧ (k : ℝ) * d ≤ C) : d = 0 := by
  by_contra hd
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · obtain ⟨k, hk⟩ := exists_lt_nsmul (neg_pos.mpr hneg) C
    have hk' : C < (k : ℝ) * (-d) := by simpa only [nsmul_eq_mul] using hk
    have hb := (hbound k).1
    nlinarith
  · obtain ⟨k, hk⟩ := exists_lt_nsmul hpos C
    have hk' : C < (k : ℝ) * d := by simpa only [nsmul_eq_mul] using hk
    exact (not_lt_of_ge (hbound k).2) hk'

/-- Monotonicity and complete multiplicativity determine a single logarithmic
slope on positive natural scalars, including the zero-slope case. -/
theorem nat_log_character {f : ℕ → ℝ}
    (h1 : f 1 = 1) (hm : ∀ m n, f (m * n) = f m * f n)
    (hmono : Monotone f) :
    ∃ α : ℝ, ∀ n : ℕ, 1 ≤ n →
      f n = Real.exp (α * Real.log (n : ℝ)) := by
  let A : ℝ := Real.log 2
  let B : ℝ := Real.log (f 2)
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hf2one : 1 ≤ f 2 := by
    have he := hmono (by norm_num : (1 : ℕ) ≤ 2)
    rwa [h1] at he
  have hf2pos : 0 < f 2 := lt_of_lt_of_le zero_lt_one hf2one
  have hB : 0 ≤ B := Real.log_nonneg hf2one
  have hpow := multiplicative_nat_pow h1 hm
  refine ⟨B / A, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hfn : 0 < f n := by
    have he := hmono hn
    rw [h1] at he
    linarith
  let d : ℝ := A * Real.log (f n) - B * Real.log (n : ℝ)
  have hbounded (k : ℕ) : - (A * B) ≤ (k : ℝ) * d ∧
      (k : ℝ) * d ≤ A * B := by
    obtain ⟨m, hlo, hhi⟩ := dyadic_bracket n k hn
    have hwlo := hmono hlo
    have hwhi := hmono hhi
    rw [hpow, hpow] at hwlo hwhi
    have hlogwlo := Real.log_le_log (pow_pos hf2pos m) hwlo
    have hlogwhi := Real.log_le_log (pow_pos hfn k) hwhi
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hlogwlo hlogwhi
    change (m : ℝ) * B ≤ (k : ℝ) * Real.log (f n) at hlogwlo
    change (k : ℝ) * Real.log (f n) ≤ ((m : ℝ) + 1) * B at hlogwhi
    have hrlo : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlo
    have hrhi : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hhi
    have hlognlo := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hrlo
    have hlognhi := Real.log_le_log (pow_pos hnR k) hrhi
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hlognlo hlognhi
    change (m : ℝ) * A ≤ (k : ℝ) * Real.log (n : ℝ) at hlognlo
    change (k : ℝ) * Real.log (n : ℝ) ≤ ((m : ℝ) + 1) * A at hlognhi
    have hwlower := mul_le_mul_of_nonneg_left hlogwlo hA.le
    have hwupper := mul_le_mul_of_nonneg_left hlogwhi hA.le
    have hnlower := mul_le_mul_of_nonneg_left hlognlo hB
    have hnupper := mul_le_mul_of_nonneg_left hlognhi hB
    dsimp [d]
    constructor <;> nlinarith
  have hd : d = 0 := eq_zero_of_bounded_nat_multiples hbounded
  have hrelation : A * Real.log (f n) = B * Real.log (n : ℝ) := by
    dsimp [d] at hd
    linarith
  have hlog : Real.log (f n) = (B / A) * Real.log (n : ℝ) := by
    calc
      Real.log (f n) = (B * Real.log (n : ℝ)) / A := by
        apply (eq_div_iff (ne_of_gt hA)).mpr
        nlinarith
      _ = (B / A) * Real.log (n : ℝ) := by ring
  calc
    f n = Real.exp (Real.log (f n)) := (Real.exp_log hfn).symm
    _ = Real.exp ((B / A) * Real.log (n : ℝ)) := congrArg Real.exp hlog

namespace WeightLaws

variable {w : Carrier → ℝ} (h : WeightLaws w)

include h

theorem scalar_zero : w (scalar 0) = 0 := h.zero

theorem scalar_one : w (scalar 1) = 1 := h.one

theorem scalar_mul (q r : ℚ) :
    w (scalar (q * r)) = w (scalar q) * w (scalar r) := by
  rw [← gmul_scalar, h.multiplicative]

theorem natWeight_zero : natWeight w 0 = 0 := by
  simpa [natWeight, scalar] using h.zero

theorem natWeight_one : natWeight w 1 = 1 := by
  simpa [natWeight, scalar, gone] using h.one

theorem natWeight_mul (m n : ℕ) :
    natWeight w (m * n) = natWeight w m * natWeight w n := by
  simpa [natWeight, Nat.cast_mul] using h.scalar_mul (m : ℚ) (n : ℚ)

theorem natWeight_monotone : Monotone (natWeight w) :=
  monotone_nat_of_le_succ h.count_step

theorem natWeight_pow (n k : ℕ) : natWeight w (n ^ k) = (natWeight w n) ^ k :=
  multiplicative_nat_pow h.natWeight_one h.natWeight_mul n k

theorem scalar_neg_one : w (scalar (-1)) = 1 := by
  have he := h.scalar_mul (-1) (-1)
  norm_num only [neg_mul_neg, one_mul] at he
  rw [h.scalar_one] at he
  have hn := h.nonnegative (scalar (-1))
  nlinarith

theorem scalar_neg (q : ℚ) : w (scalar (-q)) = w (scalar q) := by
  have he := h.scalar_mul (-1) q
  rw [neg_one_mul, h.scalar_neg_one, one_mul] at he
  exact he

theorem weight_square (z : Carrier) :
    w z * w z = w (scalar (normQ z)) := by
  rw [← gmul_conjugate, h.multiplicative, h.conjugation]

/-- The supplied balanced echo determines the raw response at scalar two. -/
theorem two_of_balanced_echo {c : Carrier}
    (hc : w c = 1 / 2)
    (he : w (gmul c (gconj c) + gmul c (gconj c)) = 1) :
    w (scalar 2) = 4 := by
  rw [echo_eq_scalar] at he
  have hfactor : normQ c + normQ c = 2 * normQ c := by ring
  rw [hfactor, h.scalar_mul, ← h.weight_square, hc] at he
  nlinarith

theorem scalar_nat_eq_sq (h2 : w (scalar 2) = 4) (n : ℕ) :
    w (scalar n) = (n : ℝ) ^ 2 := by
  exact nat_square_character h.natWeight_zero h.natWeight_one h.natWeight_mul
    h.natWeight_monotone (by simpa [natWeight] using h2) n

theorem scalar_int_eq_sq (h2 : w (scalar 2) = 4) (n : ℤ) :
    w (scalar (n : ℚ)) = (n : ℝ) ^ 2 := by
  cases n with
  | ofNat n => simpa using h.scalar_nat_eq_sq h2 n
  | negSucc n =>
      rw [Int.cast_negSucc, h.scalar_neg]
      simpa only [Int.cast_negSucc, neg_sq] using h.scalar_nat_eq_sq h2 (n + 1)

theorem scalar_rat_eq_sq (h2 : w (scalar 2) = 4) (q : ℚ) :
    w (scalar q) = (q : ℝ) ^ 2 := by
  have hdQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hprod : (q.num : ℚ) = q * (q.den : ℚ) :=
    (div_eq_iff hdQ).mp q.num_div_den
  have he := h.scalar_mul q (q.den : ℚ)
  rw [← hprod, h.scalar_int_eq_sq h2 q.num, h.scalar_nat_eq_sq h2 q.den] at he
  have hdR : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [Rat.cast_def, div_pow]
  exact (eq_div_iff (pow_ne_zero 2 hdR)).mpr he.symm

/-- The direct balanced proof uses count order and the real Archimedean
codomain, with no continuity premise. -/
theorem weight_eq_normQ_of_balanced_echo {c : Carrier}
    (hc : w c = 1 / 2)
    (he : w (gmul c (gconj c) + gmul c (gconj c)) = 1) (z : Carrier) :
    w z = (normQ z : ℝ) := by
  have h2 := h.two_of_balanced_echo hc he
  have hs := h.weight_square z
  rw [h.scalar_rat_eq_sq h2] at hs
  have hn := h.nonnegative z
  have hq : (0 : ℝ) ≤ (normQ z : ℝ) := by exact_mod_cast normQ_nonneg z
  nlinarith

theorem weight_eq_normQ_of_balanced (he : BalancedEcho w) (z : Carrier) :
    w z = (normQ z : ℝ) := by
  obtain ⟨c, hc, he⟩ := he
  exact h.weight_eq_normQ_of_balanced_echo hc he z

/-- Positive rational scalars inherit the one logarithmic slope fixed on the
positive natural scalars. -/
theorem scalar_positive_character :
    ∃ α : ℝ, ∀ q : ℚ, 0 < q →
      w (scalar q) = Real.exp (α * Real.log (q : ℝ)) := by
  obtain ⟨α, hNat⟩ := nat_log_character h.natWeight_one h.natWeight_mul h.natWeight_monotone
  refine ⟨α, fun q hq => ?_⟩
  let n : ℕ := q.num.natAbs
  have hnQ : (n : ℚ) = (q.num : ℚ) := by
    dsimp [n]
    simpa only [Int.cast_natCast] using
      congrArg (fun k : ℤ => (k : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq.le))
  have hdQ : 0 < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hprodQ : (n : ℚ) = q * (q.den : ℚ) :=
    hnQ.trans ((div_eq_iff (ne_of_gt hdQ)).mp q.num_div_den)
  have hnpos : 0 < n := by
    have he : 0 < (n : ℚ) := by rw [hprodQ]; exact mul_pos hq hdQ
    exact_mod_cast he
  have hnform := hNat n (by omega)
  have hdform := hNat q.den (Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)
  change w (scalar (n : ℚ)) = Real.exp (α * Real.log (n : ℝ)) at hnform
  change w (scalar (q.den : ℚ)) = Real.exp (α * Real.log (q.den : ℝ)) at hdform
  have he := h.scalar_mul q (q.den : ℚ)
  rw [← hprodQ, hnform, hdform] at he
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hdR : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hprodR : (n : ℝ) = (q : ℝ) * (q.den : ℝ) := by exact_mod_cast hprodQ
  have hlog : Real.log (n : ℝ) - Real.log (q.den : ℝ) = Real.log (q : ℝ) := by
    rw [hprodR, Real.log_mul (ne_of_gt hqR) (ne_of_gt hdR)]
    ring
  calc
    w (scalar q) = Real.exp (α * Real.log (n : ℝ)) /
        Real.exp (α * Real.log (q.den : ℝ)) :=
      (eq_div_iff (Real.exp_ne_zero _)).mpr he.symm
    _ = Real.exp (α * Real.log (n : ℝ) - α * Real.log (q.den : ℝ)) :=
      (Real.exp_sub _ _).symm
    _ = Real.exp (α * Real.log (q : ℝ)) := by rw [← mul_sub, hlog]

/-- Reversal and nonnegative response transfer the scalar character to the
rational Gaussian norm. The exponent here is half the scalar exponent. -/
theorem radial_character :
    ∃ p : ℝ, ∀ z : Carrier, z ≠ (0, 0) →
      w z = Real.exp (p * Real.log (normQ z : ℝ)) := by
  obtain ⟨α, hα⟩ := h.scalar_positive_character
  refine ⟨α / 2, fun z hz => ?_⟩
  have hN : 0 < normQ z := normQ_pos hz
  have hsq : (w z) ^ 2 = Real.exp (α * Real.log (normQ z : ℝ)) := by
    rw [pow_two, h.weight_square, hα (normQ z) hN]
  have hexpsq : (Real.exp ((α / 2) * Real.log (normQ z : ℝ))) ^ 2 =
      Real.exp (α * Real.log (normQ z : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hn := h.nonnegative z
  have hp := Real.exp_pos ((α / 2) * Real.log (normQ z : ℝ))
  nlinarith

/-- A single supplied nondegenerate normalized echo selects norm square on
the rational Gaussian carrier. Universal count order supplies the scalar
character, with no continuity or additional balanced-witness premise. -/
theorem weight_eq_normQ_of_pair
    {a b : Carrier} (ha : a ≠ (0, 0)) (hb : b ≠ (0, 0))
    (hab : w a + w b = 1)
    (he : w (gmul a (gconj a) + gmul b (gconj b)) = 1) :
    ∀ z : Carrier, w z = (normQ z : ℝ) := by
  obtain ⟨p, hp⟩ := h.radial_character
  have hpa := hp a ha
  have hpb := hp b hb
  have hpne : p ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, Real.exp_zero] at hpa hpb
    linarith
  let S : ℚ := normQ a + normQ b
  have hNa : 0 < normQ a := normQ_pos ha
  have hNb : 0 < normQ b := normQ_pos hb
  have hS : 0 < S := add_pos hNa hNb
  have hSR : 0 < (S : ℝ) := by exact_mod_cast hS
  have hScal : scalar S ≠ (0, 0) := by
    intro hz
    have hf := congrArg Prod.fst hz
    change S = 0 at hf
    linarith
  have heS : w (scalar S) = 1 := by simpa only [echo_eq_scalar] using he
  have hnormS : (normQ (scalar S) : ℝ) = (S : ℝ) ^ 2 := by
    simp [normQ, scalar]
  have hexpS : Real.exp (p * Real.log ((S : ℝ) ^ 2)) = 1 := by
    have hs := hp (scalar S) hScal
    rw [hnormS, heS] at hs
    exact hs.symm
  have hlogS : Real.log ((S : ℝ) ^ 2) = 0 := by
    have hprod : p * Real.log ((S : ℝ) ^ 2) = 0 := by
      apply Real.exp_injective
      simpa only [Real.exp_zero] using hexpS
    exact (mul_eq_zero.mp hprod).resolve_left hpne
  have hSsq : (S : ℝ) ^ 2 = 1 := by
    have hs := congrArg Real.exp hlogS
    simpa only [Real.exp_log (sq_pos_of_pos hSR), Real.exp_zero] using hs
  have hSone : (S : ℝ) = 1 := by nlinarith
  have hsum : (normQ a : ℝ) + (normQ b : ℝ) = 1 := by
    simpa only [S, Rat.cast_add] using hSone
  have hNaR : 0 < (normQ a : ℝ) := by exact_mod_cast hNa
  have hNbR : 0 < (normQ b : ℝ) := by exact_mod_cast hNb
  have hNaLt : (normQ a : ℝ) < 1 := by linarith
  have hNbLt : (normQ b : ℝ) < 1 := by linarith
  have hla : Real.log (normQ a : ℝ) < 0 := Real.log_neg hNaR hNaLt
  have hlb : Real.log (normQ b : ℝ) < 0 := Real.log_neg hNbR hNbLt
  have hpOne : p = 1 := by
    rcases lt_trichotomy p 1 with hlt | heq | hgt
    · have hwa : (normQ a : ℝ) < w a := by
        calc
          (normQ a : ℝ) = Real.exp (Real.log (normQ a : ℝ)) := (Real.exp_log hNaR).symm
          _ < Real.exp (p * Real.log (normQ a : ℝ)) :=
            Real.exp_lt_exp.mpr (by nlinarith)
          _ = w a := hpa.symm
      have hwb : (normQ b : ℝ) < w b := by
        calc
          (normQ b : ℝ) = Real.exp (Real.log (normQ b : ℝ)) := (Real.exp_log hNbR).symm
          _ < Real.exp (p * Real.log (normQ b : ℝ)) :=
            Real.exp_lt_exp.mpr (by nlinarith)
          _ = w b := hpb.symm
      linarith
    · exact heq
    · have hwa : w a < (normQ a : ℝ) := by
        calc
          w a = Real.exp (p * Real.log (normQ a : ℝ)) := hpa
          _ < Real.exp (Real.log (normQ a : ℝ)) :=
            Real.exp_lt_exp.mpr (by nlinarith)
          _ = (normQ a : ℝ) := Real.exp_log hNaR
      have hwb : w b < (normQ b : ℝ) := by
        calc
          w b = Real.exp (p * Real.log (normQ b : ℝ)) := hpb
          _ < Real.exp (Real.log (normQ b : ℝ)) :=
            Real.exp_lt_exp.mpr (by nlinarith)
          _ = (normQ b : ℝ) := Real.exp_log hNbR
      linarith
  intro z
  by_cases hz : z = (0, 0)
  · simpa [hz, normQ] using h.zero
  · have hNz : 0 < (normQ z : ℝ) := by exact_mod_cast normQ_pos hz
    simpa only [hpOne, one_mul, Real.exp_log hNz] using hp z hz

theorem weight_eq_normQ (he : NondegenerateEcho w) (z : Carrier) :
    w z = (normQ z : ℝ) := by
  obtain ⟨a, b, ha, hb, hab, he⟩ := he
  exact h.weight_eq_normQ_of_pair ha hb hab he z

end WeightLaws

end

end IDT.QMClosure.RationalCountOrderReadout
