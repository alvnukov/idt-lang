import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A rational Gaussian-coordinate echo control

The carrier is the rational coordinate plane with its inherited product
topology. Multiplication and the unit are named explicitly. A prime-parameter
counterfamily passes an actual nonzero balanced echo. For each finite set of
readout points, a sufficiently large prime gives agreement with norm square
on those points while differing at another point. The chosen prime depends
on the finite set. The fixed-seven sequence exhibits failure of local
continuity at the unit on this carrier.

The complex-carrier classification retains its separate domain hypotheses.
-/

namespace IDT.QMClosure.RationalEchoRegularityControl

open Filter Topology

noncomputable section

abbrev Carrier := ℚ × ℚ

def gone : Carrier := (1, 0)

def gmul (z t : Carrier) : Carrier :=
  (z.1 * t.1 - z.2 * t.2, z.1 * t.2 + z.2 * t.1)

def gconj (z : Carrier) : Carrier := (z.1, -z.2)

def normQ (z : Carrier) : ℚ := z.1 ^ 2 + z.2 ^ 2

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def qWeightAt (p : ℕ) (z : Carrier) : ℚ :=
  normQ z * (p : ℚ) ^ padicValRat p (normQ z)

def weightAt (p : ℕ) (z : Carrier) : ℝ := (qWeightAt p z : ℝ)

def qWeight (z : Carrier) : ℚ := qWeightAt 7 z

def weight (z : Carrier) : ℝ := (qWeight z : ℝ)

theorem normQ_nonneg (z : Carrier) : 0 ≤ normQ z := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem normQ_eq_zero_iff (z : Carrier) :
    normQ z = 0 ↔ z.1 = 0 ∧ z.2 = 0 := by
  constructor
  · intro h
    dsimp [normQ] at h
    constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  · rintro ⟨h₁, h₂⟩
    simp [normQ, h₁, h₂]

theorem normQ_mul (z t : Carrier) :
    normQ (gmul z t) = normQ z * normQ t := by
  dsimp [normQ, gmul]
  ring

theorem normQ_conjugation (z : Carrier) : normQ (gconj z) = normQ z := by
  simp [normQ, gconj]

theorem qWeightAt_multiplicative (p : ℕ) [Fact (Nat.Prime p)] (z t : Carrier) :
    qWeightAt p (gmul z t) = qWeightAt p z * qWeightAt p t := by
  unfold qWeightAt
  rw [normQ_mul]
  by_cases hz : normQ z = 0
  · simp [hz]
  by_cases ht : normQ t = 0
  · simp [ht]
  have hp : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  rw [padicValRat.mul hz ht, zpow_add₀ hp]
  ring

theorem qWeightAt_zero (p : ℕ) : qWeightAt p (0, 0) = 0 := by
  simp [qWeightAt, normQ]

theorem qWeightAt_one (p : ℕ) : qWeightAt p gone = 1 := by
  simp [qWeightAt, normQ, gone]

theorem qWeightAt_nonnegative (p : ℕ) (z : Carrier) : 0 ≤ qWeightAt p z := by
  exact mul_nonneg (normQ_nonneg z) (zpow_nonneg (Nat.cast_nonneg p) _)

theorem qWeightAt_positive (p : ℕ) [Fact (Nat.Prime p)] (z : Carrier)
    (hz : z ≠ (0, 0)) : 0 < qWeightAt p z := by
  have hnzero : normQ z ≠ 0 := by
    intro hn
    obtain ⟨h₁, h₂⟩ := (normQ_eq_zero_iff z).mp hn
    exact hz (Prod.ext h₁ h₂)
  have hn : 0 < normQ z := lt_of_le_of_ne (normQ_nonneg z) (Ne.symm hnzero)
  have hp : 0 < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  exact mul_pos hn (zpow_pos hp _)

theorem qWeightAt_conjugation (p : ℕ) (z : Carrier) :
    qWeightAt p (gconj z) = qWeightAt p z := by
  simp only [qWeightAt, normQ_conjugation]

theorem weightAt_multiplicative (p : ℕ) [Fact (Nat.Prime p)] (z t : Carrier) :
    weightAt p (gmul z t) = weightAt p z * weightAt p t := by
  unfold weightAt
  exact_mod_cast qWeightAt_multiplicative p z t

theorem weightAt_zero (p : ℕ) : weightAt p (0, 0) = 0 := by
  unfold weightAt
  exact_mod_cast qWeightAt_zero p

theorem weightAt_one (p : ℕ) : weightAt p gone = 1 := by
  unfold weightAt
  exact_mod_cast qWeightAt_one p

theorem weightAt_nonnegative (p : ℕ) (z : Carrier) : 0 ≤ weightAt p z := by
  unfold weightAt
  exact_mod_cast qWeightAt_nonnegative p z

theorem weightAt_positive (p : ℕ) [Fact (Nat.Prime p)] (z : Carrier)
    (hz : z ≠ (0, 0)) : 0 < weightAt p z := by
  unfold weightAt
  exact_mod_cast qWeightAt_positive p z hz

theorem weightAt_conjugation (p : ℕ) (z : Carrier) :
    weightAt p (gconj z) = weightAt p z := by
  unfold weightAt
  exact_mod_cast qWeightAt_conjugation p z

theorem qWeight_multiplicative (z t : Carrier) :
    qWeight (gmul z t) = qWeight z * qWeight t := by
  exact qWeightAt_multiplicative 7 z t

theorem qWeight_zero : qWeight (0, 0) = 0 := by
  exact qWeightAt_zero 7

theorem qWeight_one : qWeight gone = 1 := by
  exact qWeightAt_one 7

theorem qWeight_nonnegative (z : Carrier) : 0 ≤ qWeight z := by
  exact qWeightAt_nonnegative 7 z

theorem qWeight_conjugation (z : Carrier) : qWeight (gconj z) = qWeight z := by
  exact qWeightAt_conjugation 7 z

theorem weight_multiplicative (z t : Carrier) :
    weight (gmul z t) = weight z * weight t := by
  unfold weight
  exact_mod_cast qWeight_multiplicative z t

theorem weight_zero : weight (0, 0) = 0 := by
  unfold weight
  exact_mod_cast qWeight_zero

theorem weight_one : weight gone = 1 := by
  unfold weight
  exact_mod_cast qWeight_one

theorem weight_nonnegative (z : Carrier) : 0 ≤ weight z := by
  unfold weight
  exact_mod_cast qWeight_nonnegative z

theorem weight_conjugation (z : Carrier) : weight (gconj z) = weight z := by
  unfold weight
  exact_mod_cast qWeight_conjugation z

def balanced : Carrier := (1 / 2, 1 / 2)

theorem balanced_ne_zero : balanced ≠ (0, 0) := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num [balanced] at hfst

theorem normQ_balanced : normQ balanced = 1 / 2 := by
  norm_num [normQ, balanced]

theorem valuation_halfAt (p : ℕ) (hp : 2 < p) : padicValRat p (1 / 2 : ℚ) = 0 := by
  have htwo : padicValNat p 2 = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < (2 : ℕ)) hp)
  have hnum : (1 / 2 : ℚ).num = 1 := by
    simpa only [one_div] using Rat.inv_ofNat_num 2
  have hden : (1 / 2 : ℚ).den = 2 := by
    simpa only [one_div] using Rat.inv_ofNat_den 2
  rw [padicValRat_def, padicValInt, hnum, hden]
  norm_num [htwo]

theorem qWeightAt_balanced (p : ℕ) (hp : 2 < p) : qWeightAt p balanced = 1 / 2 := by
  rw [qWeightAt, normQ_balanced, valuation_halfAt p hp]
  norm_num

theorem weightAt_balanced (p : ℕ) (hp : 2 < p) : weightAt p balanced = 1 / 2 := by
  rw [weightAt, qWeightAt_balanced p hp]
  norm_num

theorem valuation_half : padicValRat 7 (1 / 2 : ℚ) = 0 := by
  exact valuation_halfAt 7 (by decide)

theorem qWeight_balanced : qWeight balanced = 1 / 2 := by
  exact qWeightAt_balanced 7 (by decide)

theorem weight_balanced : weight balanced = 1 / 2 := by
  rw [weight, qWeight_balanced]
  norm_num

theorem balanced_echo_unit :
    gmul balanced (gconj balanced) + gmul balanced (gconj balanced) = gone := by
  ext <;> norm_num [gmul, gconj, balanced, gone]

theorem balanced_normalizationAt (p : ℕ) (hp : 2 < p) :
    weightAt p balanced + weightAt p balanced = 1 := by
  rw [weightAt_balanced p hp]
  norm_num

theorem balanced_echoAt (p : ℕ) :
    weightAt p (gmul balanced (gconj balanced) + gmul balanced (gconj balanced)) = 1 := by
  rw [balanced_echo_unit, weightAt_one]

theorem balanced_normalization : weight balanced + weight balanced = 1 := by
  rw [weight_balanced]
  norm_num

theorem balanced_echo :
    weight (gmul balanced (gconj balanced) + gmul balanced (gconj balanced)) = 1 := by
  rw [balanced_echo_unit, weight_one]

theorem valuation_fortynine : padicValRat 7 (49 : ℚ) = 2 := by
  have hself : padicValRat 7 (7 : ℚ) = 1 := by
    convert padicValRat.self (p := 7) (by decide : 1 < (7 : ℕ)) using 1
  have h : (49 : ℚ) = (7 : ℚ) ^ 2 := by norm_num
  rw [h, padicValRat.pow (by norm_num : (7 : ℚ) ≠ 0), hself]
  norm_num

theorem qWeightAt_real_prime (p : ℕ) [Fact (Nat.Prime p)] :
    qWeightAt p ((p : ℚ), 0) = (p : ℚ) ^ 4 := by
  have hp : Nat.Prime p := Fact.out
  have hpzero : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn : normQ ((p : ℚ), 0) = (p : ℚ) ^ 2 := by simp [normQ]
  have hv : padicValRat p ((p : ℚ) ^ 2) = 2 := by
    rw [padicValRat.pow hpzero, padicValRat.self hp.one_lt]
    norm_num
  rw [qWeightAt, hn, hv, zpow_two]
  ring

theorem weightAt_real_prime (p : ℕ) [Fact (Nat.Prime p)] :
    weightAt p ((p : ℚ), 0) = (p : ℝ) ^ 4 := by
  unfold weightAt
  exact_mod_cast qWeightAt_real_prime p

theorem real_prime_fourth_ne_square (p : ℕ) (hp : 2 < p) :
    (p : ℝ) ^ 4 ≠ (p : ℝ) ^ 2 := by
  have hpr : (2 : ℝ) < p := by exact_mod_cast hp
  have hsq : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  intro heq
  nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 1)]

theorem qWeight_real_seven : qWeight (7, 0) = 2401 := by
  change qWeightAt 7 (7, 0) = 2401
  calc
    qWeightAt 7 (7, 0) = (7 : ℚ) ^ 4 := qWeightAt_real_prime 7
    _ = 2401 := by norm_num

theorem weight_real_seven : weight (7, 0) = 2401 := by
  unfold weight
  exact_mod_cast qWeight_real_seven

theorem weight_not_normQ : ¬ ∀ z : Carrier, weight z = (normQ z : ℝ) := by
  intro h
  have hseven := h (7, 0)
  rw [weight_real_seven] at hseven
  norm_num [normQ] at hseven

/-- A prime above the numerator magnitude and denominator has zero valuation.
The zero rational is handled separately. -/
theorem valuation_of_height_lt {p : ℕ} {r : ℚ}
    (hnum : r.num.natAbs < p) (hden : r.den < p) : padicValRat p r = 0 := by
  by_cases hr : r = 0
  · simp [hr]
  have hnumpos : 0 < r.num.natAbs :=
    Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr))
  have hnumdvd : ¬ p ∣ r.num.natAbs := Nat.not_dvd_of_pos_of_lt hnumpos hnum
  have hdendvd : ¬ p ∣ r.den := Nat.not_dvd_of_pos_of_lt r.pos hden
  rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hnumdvd,
    padicValNat.eq_zero_of_not_dvd hdendvd]
  norm_num

/-- For each finite set of rational-coordinate evaluation points, a prime can
be chosen whose weight agrees with norm square at those points and retains a
balanced echo, while differing at its own real-prime coordinate. The selected
prime is allowed to depend on the finite set. -/
theorem finite_readout_wall (S : Finset Carrier) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧
      (∀ z ∈ S, weightAt p z = (normQ z : ℝ)) ∧
      balanced ≠ (0, 0) ∧ weightAt p balanced = 1 / 2 ∧
      weightAt p balanced + weightAt p balanced = 1 ∧
      weightAt p (gmul balanced (gconj balanced) + gmul balanced (gconj balanced)) = 1 ∧
      weightAt p ((p : ℚ), 0) = (p : ℝ) ^ 4 ∧ (p : ℝ) ^ 4 ≠ (p : ℝ) ^ 2 := by
  let B : ℕ := max 2 (S.sup (fun z => max (normQ z).num.natAbs (normQ z).den))
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (B + 1)
  have hBp : B < p := by omega
  have hpgt : 2 < p := lt_of_le_of_lt (le_max_left _ _) hBp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨p, hp, hpgt, ?_, balanced_ne_zero, weightAt_balanced p hpgt,
    balanced_normalizationAt p hpgt, balanced_echoAt p, weightAt_real_prime p,
    real_prime_fourth_ne_square p hpgt⟩
  intro z hz
  have hs : max (normQ z).num.natAbs (normQ z).den ≤
      S.sup (fun t => max (normQ t).num.natAbs (normQ t).den) :=
    Finset.le_sup (f := fun t : Carrier => max (normQ t).num.natAbs (normQ t).den) hz
  have hsB : max (normQ z).num.natAbs (normQ z).den ≤ B :=
    hs.trans (le_max_right _ _)
  have hheight : max (normQ z).num.natAbs (normQ z).den < p :=
    lt_of_le_of_lt hsB hBp
  have hnum : (normQ z).num.natAbs < p :=
    lt_of_le_of_lt (le_max_left _ _) hheight
  have hden : (normQ z).den < p := lt_of_le_of_lt (le_max_right _ _) hheight
  have hv : padicValRat p (normQ z) = 0 := valuation_of_height_lt hnum hden
  simp only [weightAt, qWeightAt, hv, zpow_zero, mul_one]

/-- The exponent starts at one, so every valuation comparison is strict. -/
def smallQ (n : ℕ) : ℚ := (1 / 7 : ℚ) ^ (n + 1)

def nearUnit (n : ℕ) : Carrier := (1 + smallQ n, 0)

theorem smallQ_positive (n : ℕ) : 0 < smallQ n := by
  unfold smallQ
  positivity

theorem valuation_smallQ (n : ℕ) :
    padicValRat 7 (smallQ n) = -((n + 1 : ℕ) : ℤ) := by
  simpa only [smallQ, one_div, inv_pow] using
    padicValRat.self_pow_inv (p := 7) (n + 1)

theorem nearUnit_base_ne_zero (n : ℕ) : (1 : ℚ) + smallQ n ≠ 0 := by
  exact ne_of_gt (add_pos (by norm_num) (smallQ_positive n))

theorem valuation_nearUnit_base (n : ℕ) :
    padicValRat 7 (1 + smallQ n) = -((n + 1 : ℕ) : ℤ) := by
  have hnegative : -((n + 1 : ℕ) : ℤ) < 0 := by omega
  have hval : padicValRat 7 (1 : ℚ) ≠ padicValRat 7 (smallQ n) := by
    rw [padicValRat.one, valuation_smallQ]
    omega
  have h := padicValRat.add_eq_min (p := 7) (nearUnit_base_ne_zero n)
    (by norm_num : (1 : ℚ) ≠ 0) (ne_of_gt (smallQ_positive n)) hval
  rw [padicValRat.one, valuation_smallQ, min_eq_right hnegative.le] at h
  exact h

theorem normQ_nearUnit (n : ℕ) : normQ (nearUnit n) = (1 + smallQ n) ^ 2 := by
  simp [normQ, nearUnit]

theorem valuation_normQ_nearUnit (n : ℕ) :
    padicValRat 7 (normQ (nearUnit n)) = -((2 * (n + 1) : ℕ) : ℤ) := by
  rw [normQ_nearUnit, padicValRat.pow (nearUnit_base_ne_zero n),
    valuation_nearUnit_base]
  push_cast
  ring

theorem qWeight_nearUnit (n : ℕ) :
    qWeight (nearUnit n) = (1 + smallQ n) ^ 2 * (1 / 7 : ℚ) ^ (2 * (n + 1)) := by
  rw [qWeight, qWeightAt, valuation_normQ_nearUnit, normQ_nearUnit]
  rw [zpow_neg, zpow_natCast]
  simp only [one_div, inv_pow, Nat.cast_ofNat]

theorem weight_nearUnit (n : ℕ) :
    weight (nearUnit n) =
      (1 + (1 / 7 : ℝ) ^ (n + 1)) ^ 2 * ((1 / 7 : ℝ) ^ (n + 1)) ^ 2 := by
  change (qWeight (nearUnit n) : ℝ) = _
  rw [qWeight_nearUnit]
  have hcast : ((1 + smallQ n : ℚ) : ℝ) = 1 + (1 / 7 : ℝ) ^ (n + 1) := by
    norm_num [smallQ]
  have hseventh : ((1 / 7 : ℚ) : ℝ) = 1 / 7 := by norm_num
  simp only [Rat.cast_mul, Rat.cast_pow, hcast, hseventh]
  rw [Nat.mul_comm 2 (n + 1), pow_mul]

theorem weight_nearUnit_zero : weight (nearUnit 0) = 64 / 2401 := by
  rw [weight_nearUnit]
  norm_num

theorem smallQ_tendsto_zero : Tendsto smallQ atTop (𝓝 0) := by
  unfold smallQ
  have h : Tendsto (fun n : ℕ => (1 / 7 : ℚ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [pow_succ, zero_mul] using
    h.mul (tendsto_const_nhds (x := (1 / 7 : ℚ)))

theorem nearUnit_tendsto_gone : Tendsto nearUnit atTop (𝓝 gone) := by
  have hbase : Tendsto (fun n : ℕ => (1 : ℚ) + smallQ n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℚ))).add smallQ_tendsto_zero
  simpa only [nearUnit, gone] using
    hbase.prodMk_nhds (tendsto_const_nhds (x := (0 : ℚ)))

theorem weight_nearUnit_tendsto_zero :
    Tendsto (fun n : ℕ => weight (nearUnit n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 / 7 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : Tendsto (fun n : ℕ => (1 / 7 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using
      h.mul (tendsto_const_nhds (x := (1 / 7 : ℝ)))
  have hbase : Tendsto (fun n : ℕ => 1 + (1 / 7 : ℝ) ^ (n + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  have hlimit : Tendsto
      (fun n : ℕ => (1 + (1 / 7 : ℝ) ^ (n + 1)) ^ 2 *
        ((1 / 7 : ℝ) ^ (n + 1)) ^ 2) atTop (𝓝 0) := by
    simpa using (hbase.pow 2).mul (hsmall.pow 2)
  convert hlimit using 1
  ext n
  exact weight_nearUnit n

theorem weight_not_continuousAt_gone : ¬ ContinuousAt weight gone := by
  intro hcontinuous
  have hone : Tendsto (fun n : ℕ => weight (nearUnit n)) atTop (𝓝 1) := by
    simpa only [weight_one] using
      (show Tendsto weight (𝓝 gone) (𝓝 (weight gone)) from hcontinuous).comp
        nearUnit_tendsto_gone
  have hzero_one : (0 : ℝ) = 1 :=
    tendsto_nhds_unique weight_nearUnit_tendsto_zero hone
  norm_num at hzero_one

/-- A universal algebraic counterweight with one actual balanced echo on the
rational Gaussian-coordinate carrier. -/
theorem rational_balanced_echo_control :
    (∀ z, 0 ≤ weight z) ∧
      weight (0, 0) = 0 ∧ weight gone = 1 ∧
      (∀ z t, weight (gmul z t) = weight z * weight t) ∧
      (∀ z, weight (gconj z) = weight z) ∧
      balanced ≠ (0, 0) ∧ weight balanced + weight balanced = 1 ∧
      weight (gmul balanced (gconj balanced) + gmul balanced (gconj balanced)) = 1 ∧
      (¬ ∀ z, weight z = (normQ z : ℝ)) ∧ ¬ ContinuousAt weight gone :=
  ⟨weight_nonnegative, weight_zero, weight_one, weight_multiplicative,
    weight_conjugation, balanced_ne_zero, balanced_normalization, balanced_echo,
    weight_not_normQ, weight_not_continuousAt_gone⟩

end

end IDT.QMClosure.RationalEchoRegularityControl
