import Mathlib.Analysis.SpecificLimits.Basic

/-!
Pure numerical bounds for finite paired count programs.
This module has only real and natural numerical parameters. Each selected index is a natural number
obtained from the first power crossing a fixed ratio. The limit statements are
limits of explicit real coefficients and do not assert continuity of a response.
-/

namespace IDT.QMClosure.InitialPairedCountBounds

noncomputable section

open Filter Topology

/-- The next positive multiple of d after 2^k, using natural arithmetic only. -/
def overheadMultiple (k d : ℕ) : ℕ := d * (2 ^ k / d + 1)

def overheadNumerator (k d h : ℕ) : ℕ := h * (2 ^ k / d + 1)

theorem overheadMultiple_bounds (k d : ℕ) (hd : 0 < d) :
    2 ^ k ≤ overheadMultiple k d ∧ overheadMultiple k d ≤ 2 ^ k + d := by
  have hmod := Nat.mod_lt (2 ^ k) hd
  have hdiv := Nat.mod_add_div (2 ^ k) d
  unfold overheadMultiple
  simp only [Nat.mul_add, Nat.mul_one]
  constructor <;> omega

theorem overheadMultiple_ratio (k d h : ℕ) (hd : 0 < d) :
    (overheadNumerator k d h : ℝ) / (2 : ℝ) ^ k =
      ((overheadMultiple k d : ℝ) / (2 : ℝ) ^ k) * ((h : ℝ) / (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  unfold overheadNumerator overheadMultiple
  push_cast
  field_simp [hd0]

/-- Every fixed rational slope admits arbitrarily small dyadic overhead.
No odd-natural inverse is prepared and no scalar response is evaluated here. -/
theorem exists_small_rational_overhead (d h : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ k m n : ℕ, 2 ^ k ≤ n ∧
      1 ≤ (n : ℝ) / (2 : ℝ) ^ k ∧ (n : ℝ) / (2 : ℝ) ^ k < 1 + ε ∧
      (m : ℝ) / (2 : ℝ) ^ k =
        ((n : ℝ) / (2 : ℝ) ^ k) * ((h : ℝ) / (d : ℝ)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((d : ℝ) / ε) (by norm_num : (1 : ℝ) < 2)
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨hlo, hhi⟩ := overheadMultiple_bounds k d hd
  have hloR : (2 : ℝ) ^ k ≤ (overheadMultiple k d : ℝ) := by exact_mod_cast hlo
  have hhiR : (overheadMultiple k d : ℝ) ≤ (2 : ℝ) ^ k + d := by exact_mod_cast hhi
  have hdsmall : (d : ℝ) / (2 : ℝ) ^ k < ε := by
    apply (div_lt_iff₀ hpow).mpr
    have hdε : (d : ℝ) < (2 : ℝ) ^ k * ε := (div_lt_iff₀ hε).mp hk
    nlinarith [hdε]
  refine ⟨k, overheadNumerator k d h, overheadMultiple k d, hlo, ?_, ?_,
    overheadMultiple_ratio k d h hd⟩
  · exact (le_div_iff₀ hpow).mpr (by simpa using hloR)
  · have hα : (overheadMultiple k d : ℝ) / (2 : ℝ) ^ k ≤ 1 + (d : ℝ) / (2 : ℝ) ^ k := by
      apply (div_le_iff₀ hpow).mpr
      have hclear : (1 + (d : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ k =
          (2 : ℝ) ^ k + d := by field_simp
      rw [hclear]
      exact hhiR
    linarith

def pairedRatio (t : ℝ) : ℝ := (1 + t) ^ 2 / (1 + t ^ 2)

theorem pairedRatio_pos (t : ℝ) (ht : 0 ≤ t) : 0 < pairedRatio t := by
  unfold pairedRatio
  positivity

theorem pairedRatio_gt_one (t : ℝ) (ht : 0 < t) : 1 < pairedRatio t := by
  rw [pairedRatio, lt_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  nlinarith

theorem one_add_le_pairedRatio (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 + t ≤ pairedRatio t := by
  rw [pairedRatio, le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_nonneg ht (sub_nonneg.mpr ht2)
  nlinarith

/-- Select the last strictly sub-target power, including exact crossing cases. -/
theorem exists_last_strict_power (K target : ℝ) (hK : 1 < K) (hTarget : 1 < target) :
    ∃ n : ℕ, K ^ n < target ∧ target ≤ K ^ (n + 1) := by
  have hex : ∃ N : ℕ, target ≤ K ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt target hK
    exact ⟨N, hN.le⟩
  let N := Nat.find hex
  have hN : target ≤ K ^ N := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra hh
    have hn0 : N = 0 := Nat.eq_zero_of_not_pos hh
    rw [hn0, pow_zero] at hN
    linarith
  refine ⟨N - 1, ?_, ?_⟩
  · have hpred : N - 1 < N := by omega
    exact lt_of_not_ge (Nat.find_min hex hpred)
  · have hsucc : N - 1 + 1 = N := by omega
    simpa only [hsucc] using hN

/-- Elementary Bernoulli estimate with a nonnegative increment. -/
theorem bernoulli (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + (n : ℝ) * t ≤ (1 + t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ 1 + t := by linarith
    calc
      1 + ((n + 1 : ℕ) : ℝ) * t ≤ (1 + (n : ℝ) * t) * (1 + t) := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg t)]
      _ ≤ (1 + t) ^ n * (1 + t) := mul_le_mul_of_nonneg_right ih hp
      _ = (1 + t) ^ (n + 1) := (pow_succ _ _).symm

/-- A finite geometric upper estimate, proved without an infinite series. -/
theorem pow_mul_linear_complement_le_one (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) n
    have he : 0 ≤ (1 + u) ^ n * ((n : ℝ) + 1) * u ^ 2 := by positivity
    calc
      (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
          (1 + u) ^ n * (1 - (n : ℝ) * u) := by
        rw [pow_succ]
        push_cast
        nlinarith [he]
      _ ≤ 1 := ih

theorem pow_le_reciprocal (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hnu : (n : ℝ) * u < 1) :
    (1 + u) ^ n ≤ 1 / (1 - (n : ℝ) * u) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - (n : ℝ) * u)).mpr
  exact pow_mul_linear_complement_le_one u hu n

theorem finite_pair_bounds (target t : ℝ) (hTarget : 1 < target) (ht : 0 < t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : (pairedRatio t) ^ n < target)
    (hnnext : target ≤ (pairedRatio t) ^ (n + 1)) :
    target / pairedRatio t ≤ (pairedRatio t) ^ n ∧
    (n : ℝ) * t ^ 2 < (target - 1) * t ∧
    1 ≤ (1 + t ^ 2) ^ n := by
  have hK : 0 < pairedRatio t := pairedRatio_pos t ht.le
  have hB : 1 + (n : ℝ) * t ≤ (pairedRatio t) ^ n := by
    exact (bernoulli t ht.le n).trans
      (pow_le_pow_left₀ (by linarith) (one_add_le_pairedRatio t ht.le ht1) n)
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_iff₀ hK).mpr
    simpa only [pow_succ] using hnnext
  · have hnt : (n : ℝ) * t < target - 1 := by linarith
    have hprod := mul_lt_mul_of_pos_right hnt ht
    nlinarith [hprod]
  · exact one_le_pow₀ (by nlinarith [sq_nonneg t])

theorem finite_pair_R_upper (target t : ℝ) (hTarget : 1 < target) (ht : 0 < t)
    (ht1 : t ≤ 1) (n : ℕ) (hn : (pairedRatio t) ^ n < target)
    (hsmall : (target - 1) * t < 1) :
    (1 + t ^ 2) ^ n ≤ 1 / (1 - (target - 1) * t) := by
  have hB : 1 + (n : ℝ) * t ≤ (pairedRatio t) ^ n := by
    exact (bernoulli t ht.le n).trans
      (pow_le_pow_left₀ (by linarith) (one_add_le_pairedRatio t ht.le ht1) n)
  have hnt : (n : ℝ) * t < target - 1 := by linarith
  have hnt2 : (n : ℝ) * t ^ 2 < (target - 1) * t := by
    nlinarith [mul_lt_mul_of_pos_right hnt ht]
  have hp : 0 ≤ (1 + t ^ 2) ^ n := by positivity
  have hfinite := pow_mul_linear_complement_le_one (t ^ 2) (sq_nonneg t) n
  apply (le_div_iff₀ (by linarith : 0 < 1 - (target - 1) * t)).mpr
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hnt2.le)]

def dyadicStep (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem dyadicStep_pos (k : ℕ) : 0 < dyadicStep k := by
  unfold dyadicStep
  positivity

theorem dyadicStep_le_one (k : ℕ) : dyadicStep k ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem dyadicStep_eq (k : ℕ) : dyadicStep k = 1 / (2 : ℝ) ^ k := by
  simp [dyadicStep]

theorem dyadicStep_tendsto : Tendsto dyadicStep atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A concrete finite index for every dyadic step. -/
def pairedIndex (target : ℝ) (hTarget : 1 < target) (k : ℕ) : ℕ :=
  Classical.choose (exists_last_strict_power (pairedRatio (dyadicStep k)) target
    (pairedRatio_gt_one _ (dyadicStep_pos k)) hTarget)

theorem pairedIndex_spec (target : ℝ) (hTarget : 1 < target) (k : ℕ) :
    (pairedRatio (dyadicStep k)) ^ pairedIndex target hTarget k < target ∧
    target ≤ (pairedRatio (dyadicStep k)) ^ (pairedIndex target hTarget k + 1) :=
  Classical.choose_spec (exists_last_strict_power (pairedRatio (dyadicStep k)) target
    (pairedRatio_gt_one _ (dyadicStep_pos k)) hTarget)

def realAmplification (target : ℝ) (hTarget : 1 < target) (k : ℕ) : ℝ :=
  (1 + dyadicStep k ^ 2) ^ pairedIndex target hTarget k

def ratioAmplification (target : ℝ) (hTarget : 1 < target) (k : ℕ) : ℝ :=
  pairedRatio (dyadicStep k) ^ pairedIndex target hTarget k

def shadowAmplification (target : ℝ) (hTarget : 1 < target) (k : ℕ) : ℝ :=
  (1 + dyadicStep k) ^ (2 * pairedIndex target hTarget k)

theorem pairedRatio_tendsto :
    Tendsto (fun k => pairedRatio (dyadicStep k)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hn := (h1.add dyadicStep_tendsto).pow 2
  have hd := h1.add (dyadicStep_tendsto.pow 2)
  convert hn.div hd (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0) using 1;
    norm_num [pairedRatio]

theorem ratioAmplification_tendsto (target : ℝ) (hTarget : 1 < target) :
    Tendsto (ratioAmplification target hTarget) atTop (𝓝 target) := by
  have hl : Tendsto (fun k => target / pairedRatio (dyadicStep k)) atTop (𝓝 target) := by
    convert (tendsto_const_nhds.div pairedRatio_tendsto (by norm_num : (1 : ℝ) ≠ 0))
      using 1; simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro k
    exact (finite_pair_bounds target (dyadicStep k) hTarget (dyadicStep_pos k)
      (dyadicStep_le_one k) (pairedIndex target hTarget k)
      (pairedIndex_spec target hTarget k).1 (pairedIndex_spec target hTarget k).2).1
  · intro k
    exact (pairedIndex_spec target hTarget k).1.le

theorem realAmplification_tendsto (target : ℝ) (hTarget : 1 < target) :
    Tendsto (realAmplification target hTarget) atTop (𝓝 1) := by
  have hm : Tendsto (fun k => (target - 1) * dyadicStep k) atTop (𝓝 0) := by
    convert dyadicStep_tendsto.const_mul (target - 1) using 1; simp
  have hu : Tendsto (fun k => 1 / (1 - (target - 1) * dyadicStep k)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    convert h1.div (h1.sub hm) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1; norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun k => one_le_pow₀ (by nlinarith [sq_nonneg (dyadicStep k)])
  · have hs : ∀ᶠ k in atTop, (target - 1) * dyadicStep k < 1 :=
      (tendsto_order.1 hm).2 1 (by norm_num)
    filter_upwards [hs] with k hk
    exact finite_pair_R_upper target (dyadicStep k) hTarget (dyadicStep_pos k)
      (dyadicStep_le_one k) (pairedIndex target hTarget k) (pairedIndex_spec target hTarget k).1 hk

theorem shadowAmplification_eq (target : ℝ) (hTarget : 1 < target) (k : ℕ) :
    shadowAmplification target hTarget k =
      realAmplification target hTarget k * ratioAmplification target hTarget k := by
  unfold shadowAmplification realAmplification ratioAmplification pairedRatio
  rw [← mul_pow]
  have hd : 1 + dyadicStep k ^ 2 ≠ 0 := by positivity
  have he : (1 + dyadicStep k ^ 2) *
      ((1 + dyadicStep k) ^ 2 / (1 + dyadicStep k ^ 2)) =
      (1 + dyadicStep k) ^ 2 := by field_simp
  rw [he, pow_mul]

theorem shadowAmplification_tendsto (target : ℝ) (hTarget : 1 < target) :
    Tendsto (shadowAmplification target hTarget) atTop (𝓝 target) := by
  have hm := (realAmplification_tendsto target hTarget).mul (ratioAmplification_tendsto target hTarget)
  have hfun : shadowAmplification target hTarget =
      fun k => realAmplification target hTarget k * ratioAmplification target hTarget k :=
    funext (shadowAmplification_eq target hTarget)
  rw [hfun]
  simpa only [one_mul] using hm

end
end IDT.QMClosure.InitialPairedCountBounds
