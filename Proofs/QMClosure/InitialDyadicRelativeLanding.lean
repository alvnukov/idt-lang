import Proofs.QMClosure.InitialEchoCoordinates
import Proofs.QMClosure.InitialPreparedCountOrder

/-!
Exact finite relative landing. Only universally prepared natural-count order
and one-sided c increase are used. All endpoint coefficients are dyadic.
-/
namespace IDT.QMClosure.InitialDyadicRelativeLanding

noncomputable section

open Filter Topology
open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPairedCountBounds InitialPreparedCountOrder
open InitialEchoCoordinates

/-- Dyadic zero and one are represented by actual scalar preparations. -/
def naturalCount (n : ℕ) : DyadicCount := dyadicCount 0 n

@[simp] theorem naturalCount_value (n : ℕ) : (naturalCount n : ℝ) = n := by
  simp [naturalCount]

@[simp] theorem raw_natural (n m : ℕ) :
    raw (naturalCount n) (naturalCount m) = bag n m := by
  simp only [naturalCount, raw_grid, pow_zero, one_mul]

/-- Every positive shadow can be reduced by an actual c power. -/
theorem exists_shadow_reduction {W : P → ℝ} (hc : ResponseIncreasing W c)
    (r : P) (v : ℝ) (hv : 0 < v) :
    ∃ ell : ℕ, q (c ^ ell * r) < v ∧ W r ≤ W (c ^ ell * r) := by
  by_cases hr0 : r = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [hr0] using hv
    · simp
  have hr : 0 < q r := q_positive r hr0
  obtain ⟨ell, hell⟩ := exists_pow_lt_of_lt_one
    (div_pos hv hr) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨ell, ?_, hc.pow ell r⟩
  rw [map_mul, map_pow, shadow_c]
  exact (lt_div_iff₀ hr).mp hell

/-- A finite coefficient estimate used after the paired word is selected. -/
private theorem endpoint_estimates {d R alpha tau delta : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1 / 2)
    (hR : 1 ≤ R) (hRhi : R < 1 + delta)
    (halpha : 1 ≤ alpha) (halphahi : alpha < 1 + delta)
    (htau : 0 < tau) (htauhi : tau < delta) :
    0 < d * R * (alpha + alpha * tau) ∧
    0 < d * R * (alpha - alpha * tau) ∧
    |d * R * (alpha + alpha * tau) - d| < 8 * d * delta ∧
    |d * R * (alpha - alpha * tau) - d| < 8 * d * delta := by
  have hRpos : 0 < R := by linarith
  have hapos : 0 < alpha := by linarith
  have htau1 : tau < 1 := by linarith
  have hprod : 1 ≤ R * alpha := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ R * alpha := mul_le_mul hR halpha (by norm_num) (by linarith)
  have hprodhi : R * alpha < (1 + delta) ^ 2 := by
    calc
      R * alpha < (1 + delta) * (1 + delta) :=
        (mul_lt_mul_of_pos_right hRhi hapos).trans
          (mul_lt_mul_of_pos_left halphahi (by linarith))
      _ = (1 + delta) ^ 2 := by ring
  have hcube : (1 + delta) ^ 3 ≤ 1 + 7 * delta := by
    nlinarith [mul_nonneg hdelta.le (sub_nonneg.mpr hdelta1),
      mul_nonneg (sq_nonneg delta) (sub_nonneg.mpr hdelta1)]
  have hslo : d ≤ d * R * (alpha + alpha * tau) := by
    have hh : 1 ≤ R * alpha * (1 + tau) := by
      nlinarith [mul_pos (mul_pos hRpos hapos) htau]
    have hm := mul_le_mul_of_nonneg_left hh hd.le
    nlinarith
  have hshi : d * R * (alpha + alpha * tau) < d * (1 + 7 * delta) := by
    have hh : R * alpha * (1 + tau) < (1 + delta) ^ 3 := by
      calc
        R * alpha * (1 + tau) < (1 + delta) ^ 2 * (1 + delta) :=
          mul_lt_mul hprodhi (by linarith) (by linarith) (by positivity)
        _ = (1 + delta) ^ 3 := by ring
    nlinarith [mul_lt_mul_of_pos_left (hh.trans_le hcube) hd]
  have htlo : d * (1 - delta) < d * R * (alpha - alpha * tau) := by
    have hh : 1 - delta < R * alpha * (1 - tau) := by
      calc
        1 - delta < 1 - tau := by linarith
        _ ≤ R * alpha * (1 - tau) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (by linarith : 0 ≤ 1 - tau)
    nlinarith [mul_lt_mul_of_pos_left hh hd]
  have htle : d * R * (alpha - alpha * tau) ≤
      d * R * (alpha + alpha * tau) := by
    nlinarith [mul_pos (mul_pos (mul_pos hd hRpos) hapos) htau]
  refine ⟨by positivity, by nlinarith [mul_pos hd (by linarith : 0 < 1 - delta)], ?_, ?_⟩
  · rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_pos hd hdelta]
  · rw [abs_lt]
    constructor <;> nlinarith [mul_pos hd hdelta]

set_option maxHeartbeats 800000 in
/-- Exact relative landing after the source shadow is already below d*q(p).
The complex source/target relation may have arbitrary phase. -/
theorem relative_landing_of_shadow_lt {W : P → ℝ}
    (hOrd : PreparedCountOrder W) (r p : P) (d : DyadicCount)
    (hd : 0 < (d : ℝ)) (hr : 0 < q r) (hp : 0 < q p)
    (hE : E r = ((d : ℝ) : ℂ) * E p)
    (hq : q r < (d : ℝ) * q p) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ M : P, ∃ s t : DyadicCount,
      ResponseIncreasing W M ∧ M * r = raw s t * p ∧
      0 < (s : ℝ) ∧ 0 < (t : ℝ) ∧
      |(s : ℝ) - (d : ℝ)| < epsilon ∧
      |(t : ℝ) - (d : ℝ)| < epsilon := by
  let target : ℝ := (d : ℝ) * q p / q r
  have hTarget : 1 < target := (lt_div_iff₀ hr).mpr (by simpa using hq)
  let delta : ℝ := min (1 / 2) (epsilon / (16 * (d : ℝ)))
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdelta1 : delta ≤ 1 / 2 := min_le_left _ _
  have hdeltaE : 8 * (d : ℝ) * delta < epsilon := by
    have hh := min_le_right (1 / 2 : ℝ) (epsilon / (16 * (d : ℝ)))
    have hh' := (le_div_iff₀ (by positivity : 0 < 16 * (d : ℝ))).mp hh
    change delta * (16 * (d : ℝ)) ≤ epsilon at hh'
    nlinarith
  let tau : ℕ → ℝ := fun k => target / ratioAmplification target hTarget k - 1
  have htauLim : Tendsto tau atTop (𝓝 0) := by
    have hconstant : Tendsto (fun _ : ℕ => target) atTop (𝓝 target) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := (hconstant.div
      (ratioAmplification_tendsto target hTarget) (ne_of_gt (by linarith : 0 < target))).sub hone
    convert hh using 1 <;> simp [tau, ne_of_gt (by linarith : 0 < target)]
  have hRsmall : ∀ᶠ k in atTop, realAmplification target hTarget k < 1 + delta :=
    (tendsto_order.1 (realAmplification_tendsto target hTarget)).2 _ (by linarith)
  have htausmall : ∀ᶠ k in atTop, tau k < delta :=
    (tendsto_order.1 htauLim).2 _ hdelta
  obtain ⟨k, hRhi, htauhi⟩ := (hRsmall.and htausmall).exists
  let A := selectedPairedWord target hTarget k
  let R := realAmplification target hTarget k
  let Q := shadowAmplification target hTarget k
  let t0 := tau k
  obtain ⟨hEA, hqA⟩ := selectedPairedWord_coordinates target hTarget k
  have hR : 1 ≤ R := one_le_pow₀ (by nlinarith [sq_nonneg (dyadicStep k)])
  have hRpos : 0 < R := by linarith
  have hQpos : 0 < Q := by
    dsimp [Q, shadowAmplification]
    exact pow_pos (by linarith [dyadicStep_pos k]) _
  have hratioPos : 0 < ratioAmplification target hTarget k := by
    dsimp [ratioAmplification]
    exact pow_pos (pairedRatio_pos _ (dyadicStep_pos k).le) _
  have ht0 : 0 < t0 := by
    dsimp [t0, tau]
    exact sub_pos.mpr ((one_lt_div hratioPos).mpr (pairedIndex_spec target hTarget k).1)
  have ht0eq : t0 = target * R / Q - 1 := by
    change target / ratioAmplification target hTarget k - 1 = target * R / Q - 1
    have hQR : Q = R * ratioAmplification target hTarget k :=
      shadowAmplification_eq target hTarget k
    rw [hQR]
    field_simp [ne_of_gt hRpos, ne_of_gt hratioPos]
  have hRmem : R ∈ realDyadic := by
    have hh := (evaluation_real_imag_dyadic A).1
    change E A = (R : ℂ) at hEA
    change (E A).re ∈ realDyadic at hh
    rw [hEA, Complex.ofReal_re] at hh
    exact hh
  obtain ⟨dr, hdr⟩ := rational_of_dyadic _ d.property.1
  obtain ⟨qr, hqr⟩ := rational_of_dyadic _ (shadow_dyadic r)
  obtain ⟨qp, hqp⟩ := rational_of_dyadic _ (shadow_dyadic p)
  obtain ⟨rr, hrr⟩ := rational_of_dyadic R hRmem
  have hQmem : Q ∈ realDyadic := by
    have hh := shadow_dyadic A
    change q A = Q at hqA
    change q A ∈ realDyadic at hh
    rw [hqA] at hh
    exact hh
  obtain ⟨qq, hqq⟩ := rational_of_dyadic Q hQmem
  let tauRat : ℚ := (dr * qp / qr) * rr / qq - 1
  have htauRat : (tauRat : ℝ) = t0 := by
    dsimp [tauRat]
    push_cast
    rw [← hdr, ← hqr, ← hqp, ← hrr, ← hqq]
    exact ht0eq.symm
  have htauRatPos : 0 < tauRat := by exact_mod_cast (htauRat.symm ▸ ht0)
  obtain ⟨den, num, hden, hnum⟩ := nonnegative_rational_counts tauRat htauRatPos.le
  have htauFraction : t0 = (num : ℝ) / (den : ℝ) := by
    have hden0 : (den : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hden
    rw [eq_div_iff hden0]
    have hh : (num : ℝ) = (den : ℝ) * (tauRat : ℝ) := by exact_mod_cast hnum
    rw [htauRat] at hh
    nlinarith
  obtain ⟨ell, m, n, hn, halpha, halphahi, hbeta⟩ :=
    exists_small_rational_overhead den num hden delta hdelta
  let alpha : ℝ := (n : ℝ) / (2 : ℝ) ^ ell
  let beta : ℝ := (m : ℝ) / (2 : ℝ) ^ ell
  have hbetaeq : beta = alpha * t0 := by simpa only [alpha, beta, ← htauFraction] using hbeta
  have hamem : alpha ∈ realDyadic := (dyadicCount ell n).property.1
  have hbmem : beta ∈ realDyadic := (dyadicCount ell m).property.1
  obtain ⟨hspos, htpos, hsclose, htclose⟩ :=
    endpoint_estimates hd hdelta hdelta1 hR hRhi halpha halphahi ht0 htauhi
  let s : DyadicCount := ⟨(d : ℝ) * R * (alpha + beta),
    realDyadic.mul_mem (realDyadic.mul_mem d.property.1 hRmem)
      (realDyadic.add_mem hamem hbmem), by rw [hbetaeq]; exact hspos.le⟩
  let t : DyadicCount := ⟨(d : ℝ) * R * (alpha - beta),
    realDyadic.mul_mem (realDyadic.mul_mem d.property.1 hRmem)
      (realDyadic.sub_mem hamem hbmem), by rw [hbetaeq]; exact htpos.le⟩
  let B := plusOverhead ell m n
  let M := B * A
  refine ⟨M, s, t, (plusOverhead_increasing hOrd ell m n hn).mul
    (selectedPairedWord_increasing hOrd target hTarget k), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hEB, hqB⟩ := plusOverhead_coordinates ell m n
    obtain ⟨hs, ht, hrawq⟩ := raw_coordinates s t
    have hrawE : E (raw s t) =
        (((d : ℝ) * R * alpha : ℝ) : ℂ) +
          (((d : ℝ) * R * beta : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero]
      · rw [hs]; change ((d : ℝ) * R * (alpha + beta) + (d : ℝ) * R * (alpha - beta)) / 2 = _; ring
      · rw [ht]; change ((d : ℝ) * R * (alpha + beta) - (d : ℝ) * R * (alpha - beta)) / 2 = _; ring
    apply eq_of_combined_coordinates
    · change E (B * A * r) = E (raw s t * p)
      rw [map_mul, map_mul, map_mul, hEA, hEB, hE, hrawE]
      change (((alpha : ℂ) + (beta : ℂ) * Complex.I) * (R : ℂ)) *
        ((d : ℂ) * E p) = _
      push_cast
      ring
    · have ht0id : (1 + t0) * Q * q r = (d : ℝ) * q p * R := by
        rw [ht0eq]
        dsimp [target]
        field_simp [ne_of_gt hr, ne_of_gt hQpos]
        <;> ring
      change q (B * A * r) = q (raw s t * p)
      rw [map_mul, map_mul, map_mul, hqA, hqB, hrawq]
      change (((n : ℝ) + (m : ℝ)) / (2 : ℝ) ^ ell * Q) * q r =
        (((d : ℝ) * R * (alpha + beta) + (d : ℝ) * R * (alpha - beta)) / 2) * q p
      rw [add_div]
      change ((alpha + beta) * Q) * q r = _
      rw [hbetaeq]
      nlinarith [congrArg (fun x : ℝ => alpha * x) ht0id]
  · simpa only [s, hbetaeq] using hspos
  · simpa only [t, hbetaeq] using htpos
  · have hh : |(s : ℝ) - (d : ℝ)| < 8 * (d : ℝ) * delta := by
      simpa only [s, hbetaeq] using hsclose
    exact hh.trans hdeltaE
  · have hh : |(t : ℝ) - (d : ℝ)| < 8 * (d : ℝ) * delta := by
      simpa only [t, hbetaeq] using htclose
    exact hh.trans hdeltaE

/-- Generalized landing includes the finite c shift inside the constructed
program. No real-axis premise is present. The coefficient d is dyadic. -/
theorem relative_landing {W : P → ℝ} (hOrd : PreparedCountOrder W)
    (hc : ResponseIncreasing W c) (r p : P) (d : DyadicCount)
    (hd : 0 < (d : ℝ)) (hr : 0 < q r) (hp : 0 < q p)
    (hE : E r = ((d : ℝ) : ℂ) * E p)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ M : P, ∃ s t : DyadicCount,
      ResponseIncreasing W M ∧ M * r = raw s t * p ∧
      0 < (s : ℝ) ∧ 0 < (t : ℝ) ∧
      |(s : ℝ) - (d : ℝ)| < epsilon ∧
      |(t : ℝ) - (d : ℝ)| < epsilon := by
  have hrne : r ≠ 0 := by intro hh; subst r; simpa using hr
  obtain ⟨ell, hsmall, hincrease⟩ := exists_shadow_reduction hc r
    ((d : ℝ) * q p) (mul_pos hd hp)
  have hshift : E (c ^ ell * r) = ((d : ℝ) : ℂ) * E p := by
    rw [map_mul, map_pow, evaluation_c, one_pow, one_mul, hE]
  have hshiftq : 0 < q (c ^ ell * r) := by
    rw [map_mul, map_pow, shadow_c]
    positivity
  obtain ⟨M, s, t, hM, hland, hs, ht, hse, hte⟩ :=
    relative_landing_of_shadow_lt hOrd (c ^ ell * r) p d hd hshiftq hp
      hshift hsmall epsilon hepsilon
  refine ⟨M * c ^ ell, s, t, hM.mul (hc.pow ell), ?_, hs, ht, hse, hte⟩
  simpa only [mul_assoc] using hland

end
end IDT.QMClosure.InitialDyadicRelativeLanding
