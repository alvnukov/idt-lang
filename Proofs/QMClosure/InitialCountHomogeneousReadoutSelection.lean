import Proofs.QMClosure.InitialCountSectorBounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Readout selection from homogeneous natural counts

The response hypotheses are the initial four-law base contract and exact
quadratic gain under natural repetition at every actual preparation. All
regularity statements below are conclusions in the ordinary supplied complex
coordinate model. The module asserts no physical completion or topology
reconstruction.
-/

namespace IDT.QMClosure.InitialCountHomogeneousReadoutSelection

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open Filter Topology
open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPreparedCountOrder
open InitialDyadicRelativeLanding InitialEchoCoordinates
open InitialColumnOrderReadoutCore

private abbrev G := gaussianDyadic
private abbrev D := realDyadic

private def reference (z : G) : P :=
  normalFormEquiv.symm ⟨(z.val, 1), by
    exact Or.inr ⟨z.property, realDyadic.one_mem, zero_lt_one⟩⟩

private theorem reference_evaluation (z : G) : E (reference z) = z.val := by
  have h := congrArg Subtype.val (normalFormEquiv.apply_symm_apply
    (⟨(z.val, 1), Or.inr ⟨z.property, realDyadic.one_mem, zero_lt_one⟩⟩ : normalSemiring))
  exact congrArg Prod.fst h

private theorem evaluation_mem (p : P) : E p ∈ gaussianDyadic := by
  have hp := raw_mem_normalSemiring p
  change (E p = 0 ∧ q p = 0) ∨
    (E p ∈ gaussianDyadic ∧ q p ∈ realDyadic ∧ 0 < q p) at hp
  rcases hp with hp | hp
  · rw [hp.1]
    exact gaussianDyadic.zero_mem
  · exact hp.1

private theorem rational_coordinates_G (z : G) :
    ∃ x y : ℚ, (z : ℂ).re = (x : ℝ) ∧ (z : ℂ).im = (y : ℝ) := by
  obtain ⟨x, y, r, hx, hy, _⟩ := rational_coordinates (reference z)
  rw [reference_evaluation] at hx hy
  exact ⟨x, y, hx, hy⟩

private def response (W : P → ℝ) (z : G) : ℝ := W (reference z)

private theorem scalar_diagonal (d : DyadicCount) : raw d d = scalar d := by
  rw [raw, ← mul_add, transparent, mul_one]

private theorem floor_error (k : ℕ) (x : ℝ) :
    0 ≤ x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k ∧
    x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k < 1 / (2 : ℝ)^k := by
  have hp : 0 < (2 : ℝ)^k := pow_pos (by norm_num) k
  have hlo := Int.floor_le ((2 : ℝ)^k * x)
  have hhi := Int.lt_floor_add_one ((2 : ℝ)^k * x)
  have heq : x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k =
      ((2 : ℝ)^k * x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ)) / (2 : ℝ)^k := by
    field_simp [ne_of_gt hp]
  rw [heq]
  exact ⟨div_nonneg (sub_nonneg.mpr hlo) hp.le,
    div_lt_div_of_pos_right (by linarith) hp⟩

private def approximation (k : ℕ) (z : ℂ) : G :=
  ⟨(((⌊(2 : ℝ)^k * z.re⌋ : ℤ) : ℂ) +
      ((⌊(2 : ℝ)^k * z.im⌋ : ℤ) : ℂ) * Complex.I) / (2 : ℂ)^k,
    (mem_gaussianDyadic _).mpr ⟨k, _, _, rfl⟩⟩

private theorem approximation_re (k : ℕ) (z : ℂ) :
    (approximation k z : ℂ).re =
      ((⌊(2 : ℝ)^k * z.re⌋ : ℤ) : ℝ) / (2 : ℝ)^k := by
  have hd : (2 : ℂ)^k = (((2 : ℝ)^k : ℝ) : ℂ) := by norm_cast
  dsimp [approximation]
  rw [hd, Complex.div_ofReal_re]
  simp

private theorem approximation_im (k : ℕ) (z : ℂ) :
    (approximation k z : ℂ).im =
      ((⌊(2 : ℝ)^k * z.im⌋ : ℤ) : ℝ) / (2 : ℝ)^k := by
  have hd : (2 : ℂ)^k = (((2 : ℝ)^k : ℝ) : ℂ) := by norm_cast
  dsimp [approximation]
  rw [hd, Complex.div_ofReal_im]
  simp

private theorem approximation_error (k : ℕ) (z : ℂ) :
    ‖z - (approximation k z : ℂ)‖ < 2 / (2 : ℝ)^k := by
  have hr := floor_error k z.re
  have hi := floor_error k z.im
  have hr0 : 0 ≤ (z - (approximation k z : ℂ)).re := by
    simpa only [Complex.sub_re, approximation_re] using hr.1
  have hi0 : 0 ≤ (z - (approximation k z : ℂ)).im := by
    simpa only [Complex.sub_im, approximation_im] using hi.1
  have hr1 : (z - (approximation k z : ℂ)).re < 1 / (2 : ℝ)^k := by
    simpa only [Complex.sub_re, approximation_re] using hr.2
  have hi1 : (z - (approximation k z : ℂ)).im < 1 / (2 : ℝ)^k := by
    simpa only [Complex.sub_im, approximation_im] using hi.2
  calc
    ‖z - (approximation k z : ℂ)‖ ≤
        |(z - (approximation k z : ℂ)).re| +
        |(z - (approximation k z : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < 1 / (2 : ℝ)^k + 1 / (2 : ℝ)^k := by
      rw [abs_of_nonneg hr0, abs_of_nonneg hi0]
      exact add_lt_add hr1 hi1
    _ = 2 / (2 : ℝ)^k := by ring

private theorem gaussian_dense : Dense (gaussianDyadic : Set ℂ) := by
  intro z
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / 2 : ℝ)^k < ε / 2 :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  have hk' : 1 / (2 : ℝ)^k < ε / 2 := by
    simpa only [div_pow, one_pow] using hk
  refine ⟨approximation k z, (approximation k z).property, ?_⟩
  rw [dist_eq_norm]
  have hbound : 2 / (2 : ℝ)^k < ε := by
    calc
      2 / (2 : ℝ)^k = 2 * (1 / (2 : ℝ)^k) := by ring
      _ < ε := by linarith
  exact (approximation_error k z).trans hbound

private theorem real_dense : Dense (realDyadic : Set ℝ) := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / 2 : ℝ)^k < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  have hk' : 1 / (2 : ℝ)^k < ε := by
    simpa only [div_pow, one_pow] using hk
  let y : ℝ := ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k
  refine ⟨y, (mem_realDyadic _).mpr ⟨k, _, rfl⟩, ?_⟩
  have he := floor_error k x
  simpa only [Real.dist_eq, y, abs_of_nonneg he.1] using he.2.trans hk'

private def ratioError (u v : G) : ℝ :=
  |((u : ℂ) / (v : ℂ)).re - 1| + |((u : ℂ) / (v : ℂ)).im|

private def complexExtension (W : P → ℝ) : ℂ → ℝ :=
  gaussian_dense.extend (response W)

section Response

variable {W : P → ℝ}
variable (H : BaseContract W)
variable (hNat : ∀ (n : ℕ) (p : P), W ((n : P) * p) = (n : ℝ)^2 * W p)
include H hNat

private theorem inverse_two_gain (p : P) : W (twoInv * p) = W p / 4 := by
  have hn := hNat 2 (twoInv * p)
  have hc : (2 : P) * (twoInv * p) = p := by
    rw [← mul_assoc, two_mul_twoInv, one_mul]
  norm_num only [Nat.cast_ofNat] at hn
  rw [hc] at hn
  norm_num at hn
  linarith

private theorem inverse_two_power_gain (k : ℕ) (p : P) :
    W (twoInv^k * p) = (1 / 4 : ℝ)^k * W p := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hword : twoInv^k * twoInv * p = twoInv * (twoInv^k*p) := by ring
      rw [hword, inverse_two_gain H hNat, ih, pow_succ]
      ring

private theorem scalar_gain (d : DyadicCount) (p : P) :
    W (scalar d * p) = (d : ℝ)^2 * W p := by
  obtain ⟨k, n, hd⟩ := nonnegative_dyadic_representation d d.property.2 d.property.1
  have heq : d = dyadicCount k n := Subtype.ext hd
  rw [heq, scalar_grid, mul_assoc, inverse_two_power_gain H hNat, hNat]
  simp only [dyadicCount_value]
  have hpow : (1 / 4 : ℝ)^k = (1 / (2 : ℝ)^k)^2 := by
    calc
      (1 / 4 : ℝ)^k = ((1 / 2 : ℝ)^2)^k := by norm_num
      _ = ((1 / 2 : ℝ)^k)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (1 / (2 : ℝ)^k)^2 := by rw [div_pow, one_pow]
  rw [hpow]
  ring

private theorem raw_upper (s t d : DyadicCount)
    (hs : (s : ℝ) ≤ d) (ht : (t : ℝ) ≤ d) (p : P) :
    W (raw s t * p) ≤ (d : ℝ)^2 * W p := by
  have ho := prepared_dyadic_order H.preparedOrder s t d d hs ht p
  rw [scalar_diagonal, scalar_gain H hNat] at ho
  exact ho

private theorem extensional_le (r p : P) (he : E r = E p) : W r ≤ W p := by
  by_cases hp : E p = 0
  · simp [null_response H r (he.trans hp), null_response H p hp]
  have hrne : r ≠ 0 := by
    intro hz
    apply hp
    simpa [hz] using he.symm
  have hpne : p ≠ 0 := by
    intro hz
    exact hp (by simp [hz])
  have hbound (k : ℕ) : W r ≤ (1 + (1 / 2 : ℝ)^k)^2 * W p := by
    let d : DyadicCount := dyadicCount k (2^k + 1)
    have hd : (d : ℝ) = 1 + (1 / 2 : ℝ)^k := by
      dsimp [d, dyadicCount]
      push_cast
      rw [add_div, div_self (by positivity : (2 : ℝ)^k ≠ 0)]
      simp only [div_pow, one_pow]
    have hstep : 0 < (1 / 2 : ℝ)^k := pow_pos (by norm_num) _
    obtain ⟨M, s, t, hM, hland, _, _, hs, ht⟩ :=
      relative_landing H.preparedOrder H.cIncreasing r p (dyadicCount 0 1)
        (by norm_num [dyadicCount_value]) (q_positive r hrne) (q_positive p hpne)
        (by simpa using he) ((1 / 2 : ℝ)^k) hstep
    simp only [dyadicCount_value, pow_zero, Nat.cast_one, div_one] at hs ht
    have hs' : (s : ℝ) ≤ d := by rw [hd]; linarith [(abs_lt.mp hs).2]
    have ht' : (t : ℝ) ≤ d := by rw [hd]; linarith [(abs_lt.mp ht).2]
    calc
      W r ≤ W (M * r) := hM r
      _ = W (raw s t * p) := congrArg W hland
      _ ≤ (d : ℝ)^2 * W p := raw_upper H hNat s t d hs' ht' p
      _ = (1 + (1 / 2 : ℝ)^k)^2 * W p := by rw [hd]
  have hzero : Tendsto (fun k : ℕ => (1 / 2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun k : ℕ => (1 + (1 / 2 : ℝ)^k)^2 * W p)
      atTop (𝓝 (W p)) := by
    convert ((tendsto_const_nhds.add hzero).pow 2).mul_const (W p) using 1 <;> simp
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound

/-- Natural count gain and the base contract force equality on each E-fiber. -/
theorem evaluation_extensional (r p : P) (he : E r = E p) : W r = W p :=
  le_antisymm (extensional_le H hNat r p he) (extensional_le H hNat p r he.symm)

private theorem response_evaluation (p : P) :
    response W ⟨E p, evaluation_mem p⟩ = W p := by
  exact evaluation_extensional H hNat _ _ (reference_evaluation _)

private theorem response_nonnegative_G (z : G) : 0 ≤ response W z :=
  response_nonnegative H _

private theorem response_zero_G (z : G) (hz : (z : ℂ) = 0) : response W z = 0 := by
  apply null_response H
  rw [reference_evaluation, hz]

private theorem positive_real_axis (p : P) (x : ℝ)
    (he : E p = (x : ℂ)) (hx : 0 < x) : W p = x^2 := by
  have hmem : x ∈ realDyadic := by
    have hh := (evaluation_real_imag_dyadic p).1
    simpa only [he, Complex.ofReal_re] using hh
  let d : DyadicCount := ⟨x, hmem, hx.le⟩
  have hpd : W p = W (scalar d * 1) := by
    apply evaluation_extensional H hNat
    simpa only [map_mul, map_one, mul_one, evaluation_scalar] using he
  rw [hpd, scalar_gain H hNat, H.normalized, mul_one]

private theorem response_coarse_upper (z : G) : response W z ≤ 256 * ‖(z : ℂ)‖^2 := by
  have h := InitialCountSectorBounds.global_coarse_upper H
    (fun p x he hx => (positive_real_axis H hNat p x he hx).le) (reference z)
  simpa only [response, N, normSq, reference_evaluation,
    Complex.normSq_eq_norm_sq] using h

private theorem ratioError_nonnegative (u v : G) : 0 ≤ ratioError u v := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

private theorem ratio_coordinates (u v : G) :
    ∃ x y : ℚ, ((u : ℂ) / (v : ℂ)).re = (x : ℝ) ∧
      ((u : ℂ) / (v : ℂ)).im = (y : ℝ) := by
  obtain ⟨ux, uy, hux, huy⟩ := rational_coordinates_G u
  obtain ⟨vx, vy, hvx, hvy⟩ := rational_coordinates_G v
  refine ⟨(ux*vx + uy*vy)/(vx^2 + vy^2),
    (uy*vx - ux*vy)/(vx^2 + vy^2), ?_, ?_⟩
  · simp only [Complex.div_re, Complex.normSq_apply, hux, huy, hvx, hvy]
    push_cast
    simp only [sq, add_div]
  · simp only [Complex.div_im, Complex.normSq_apply, hux, huy, hvx, hvy]
    push_cast
    simp only [sq, sub_div]

private theorem ratioError_bound (u v : G) (hv : (v : ℂ) ≠ 0) :
    ratioError u v ≤ 2 * ‖(u : ℂ) - (v : ℂ)‖ / ‖(v : ℂ)‖ := by
  have hdiff : (u : ℂ) / (v : ℂ) - 1 = ((u : ℂ) - (v : ℂ)) / (v : ℂ) := by
    field_simp [hv]
    <;> ring
  calc
    ratioError u v = |((u : ℂ)/(v : ℂ) - 1).re| +
        |((u : ℂ)/(v : ℂ) - 1).im| := by
      simp only [ratioError, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
    _ ≤ 2 * ‖(u : ℂ)/(v : ℂ) - 1‖ := by
      linarith [Complex.abs_re_le_norm ((u : ℂ)/(v : ℂ) - 1),
        Complex.abs_im_le_norm ((u : ℂ)/(v : ℂ) - 1)]
    _ = 2 * ‖(u : ℂ) - (v : ℂ)‖ / ‖(v : ℂ)‖ := by
      rw [hdiff, norm_div]
      ring

private theorem ratio_response_bounds (u v : G) (hv : (v : ℂ) ≠ 0)
    (hη : ratioError u v ≤ 1) :
    (1 - ratioError u v)^2 * response W v ≤ response W u ∧
    response W u ≤ (1 + ratioError u v)^2 * response W v := by
  let r : ℂ := (u : ℂ)/(v : ℂ)
  let η := ratioError u v
  obtain ⟨x, y, hx, hy⟩ := ratio_coordinates H hNat u v
  have hcoeff : 1-η ≤ r.re+r.im ∧ r.re+r.im ≤ 1+η ∧
      1-η ≤ r.re-r.im ∧ r.re-r.im ≤ 1+η := by
    dsimp [η, ratioError, r]
    constructor
    · linarith [neg_le_abs (((u : ℂ)/(v : ℂ)).re - 1),
        neg_le_abs (((u : ℂ)/(v : ℂ)).im)]
    constructor
    · linarith [le_abs_self (((u : ℂ)/(v : ℂ)).re - 1),
        le_abs_self (((u : ℂ)/(v : ℂ)).im)]
    constructor
    · linarith [neg_le_abs (((u : ℂ)/(v : ℂ)).re - 1),
        le_abs_self (((u : ℂ)/(v : ℂ)).im)]
    · linarith [le_abs_self (((u : ℂ)/(v : ℂ)).re - 1),
        neg_le_abs (((u : ℂ)/(v : ℂ)).im)]
  have hs : 0 ≤ x+y := by
    have hh : (0 : ℝ) ≤ (x : ℝ)+(y : ℝ) := by
      rw [← hx, ← hy]
      exact (sub_nonneg.mpr hη).trans hcoeff.1
    exact_mod_cast hh
  have ht : 0 ≤ x-y := by
    have hh : (0 : ℝ) ≤ (x : ℝ)-(y : ℝ) := by
      rw [← hx, ← hy]
      exact (sub_nonneg.mpr hη).trans hcoeff.2.2.1
    exact_mod_cast hh
  obtain ⟨d, s, t, _, _, hd, hsQ, htQ, _, _⟩ :=
    clear_four_nonnegative_rationals (x+y) (x-y) 0 0 hs ht (by norm_num) (by norm_num)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsR : (s : ℝ) = (d : ℝ)*(r.re+r.im) := by
    have hh : (s : ℝ) = (d : ℝ)*((x : ℝ)+(y : ℝ)) := by exact_mod_cast hsQ
    simpa only [r, ← hx, ← hy] using hh
  have htR : (t : ℝ) = (d : ℝ)*(r.re-r.im) := by
    have hh : (t : ℝ) = (d : ℝ)*((x : ℝ)-(y : ℝ)) := by exact_mod_cast htQ
    simpa only [r, ← hx, ← hy] using hh
  have hbag : E (bag s t) = (d : ℂ)*r := by
    apply Complex.ext
    · rw [(bag_complex_coordinates s t).1]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
      rw [hsR, htR]
      ring
    · rw [(bag_complex_coordinates s t).2]
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        zero_mul, add_zero]
      rw [hsR, htR]
      ring
  have hcoord : E ((d : P)*reference u) = E (bag s t * reference v) := by
    rw [map_mul, map_natCast, reference_evaluation, map_mul, hbag, reference_evaluation]
    dsimp [r]
    field_simp [hv] <;> ring
  have hscale : (d : ℝ)^2 * response W u = W (bag s t * reference v) := by
    change (d : ℝ)^2 * W (reference u) = _
    rw [← hNat d (reference u)]
    exact evaluation_extensional H hNat _ _ hcoord
  have hlo := H.preparedOrder (reference v) (min s t) (min s t) s t
    (min_le_left _ _) (min_le_right _ _)
  have hhi := H.preparedOrder (reference v) s t (max s t) (max s t)
    (le_max_left _ _) (le_max_right _ _)
  rw [bag_diagonal, hNat] at hlo
  rw [bag_diagonal, hNat] at hhi
  rw [← hscale] at hlo hhi
  have hlow : (d : ℝ)*(1-η) ≤ (min s t : ℕ) := by
    rcases le_total s t with hst | hts
    · rw [min_eq_left hst, hsR]
      exact mul_le_mul_of_nonneg_left hcoeff.1 hdR.le
    · rw [min_eq_right hts, htR]
      exact mul_le_mul_of_nonneg_left hcoeff.2.2.1 hdR.le
  have hhigh : ((max s t : ℕ) : ℝ) ≤ (d : ℝ)*(1+η) := by
    rcases le_total s t with hst | hts
    · rw [max_eq_right hst, htR]
      exact mul_le_mul_of_nonneg_left hcoeff.2.2.2 hdR.le
    · rw [max_eq_left hts, hsR]
      exact mul_le_mul_of_nonneg_left hcoeff.2.1 hdR.le
  have hη0 := ratioError_nonnegative H hNat u v
  have hmin0 : (0 : ℝ) ≤ (min s t : ℕ) := Nat.cast_nonneg _
  have hmax0 : (0 : ℝ) ≤ (max s t : ℕ) := Nat.cast_nonneg _
  have hlow0 : 0 ≤ (d : ℝ)*(1-η) := mul_nonneg hdR.le (sub_nonneg.mpr hη)
  have hhigh0 : 0 ≤ (d : ℝ)*(1+η) := by positivity
  have hlowSq : ((d : ℝ)*(1-η))^2 ≤ ((min s t : ℕ) : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (add_nonneg hmin0 hlow0)]
  have hhighSq : ((max s t : ℕ) : ℝ)^2 ≤ ((d : ℝ)*(1+η))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhigh) (add_nonneg hmax0 hhigh0)]
  have hwv := response_nonnegative_G H hNat v
  constructor
  · apply (mul_le_mul_iff_right₀ (pow_pos hdR 2)).mp
    calc
      (d : ℝ)^2 * ((1-η)^2 * response W v) =
          ((d : ℝ)*(1-η))^2 * response W v := by ring
      _ ≤ ((min s t : ℕ) : ℝ)^2 * response W v :=
        mul_le_mul_of_nonneg_right hlowSq hwv
      _ ≤ (d : ℝ)^2 * response W u := hlo
  · apply (mul_le_mul_iff_right₀ (pow_pos hdR 2)).mp
    calc
      (d : ℝ)^2 * response W u ≤ ((max s t : ℕ) : ℝ)^2 * response W v := hhi
      _ ≤ ((d : ℝ)*(1+η))^2 * response W v :=
        mul_le_mul_of_nonneg_right hhighSq hwv
      _ = (d : ℝ)^2 * ((1+η)^2 * response W v) := by ring

private theorem response_polynomial_bound (u v : G) :
    |response W u - response W v| ≤
      1536 * (‖(u : ℂ)‖ + ‖(v : ℂ)‖) * ‖(u : ℂ) - (v : ℂ)‖ := by
  have hu0 := response_nonnegative_G H hNat u
  have hv0 := response_nonnegative_G H hNat v
  have huB := response_coarse_upper H hNat u
  have hvB := response_coarse_upper H hNat v
  by_cases hv : (v : ℂ) = 0
  · have hz := response_zero_G H hNat v hv
    rw [hz, sub_zero, abs_of_nonneg hu0, hv, norm_zero, add_zero, sub_zero]
    nlinarith [sq_nonneg ‖(u : ℂ)‖]
  have hvpos : 0 < ‖(v : ℂ)‖ := norm_pos_iff.mpr hv
  let δ := ‖(u : ℂ) - (v : ℂ)‖
  let η := ratioError u v
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hη0 : 0 ≤ η := ratioError_nonnegative H hNat u v
  have hηB : η * ‖(v : ℂ)‖ ≤ 2*δ := by
    apply (le_div_iff₀ hvpos).mp
    exact ratioError_bound H hNat u v hv
  by_cases hclose : 2*δ ≤ ‖(v : ℂ)‖
  · have hη1 : η ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hvpos).mp
      simpa only [one_mul] using hηB.trans hclose
    obtain ⟨hlo, hhi⟩ := ratio_response_bounds H hNat u v hv hη1
    change (1-η)^2 * response W v ≤ response W u at hlo
    change response W u ≤ (1+η)^2 * response W v at hhi
    have hηW : η * response W v ≤ 512 * ‖(v : ℂ)‖ * δ := by
      have hfirst := mul_le_mul_of_nonneg_left hvB hη0
      have hsecond := mul_le_mul_of_nonneg_right hηB (by positivity : 0 ≤ 256 * ‖(v : ℂ)‖)
      nlinarith
    have hηsq : η^2 * response W v ≤ η * response W v := by
      have hprod := mul_nonneg hη0 (sub_nonneg.mpr hη1)
      exact mul_le_mul_of_nonneg_right (by nlinarith : η^2 ≤ η) hv0
    have habs : |response W u - response W v| ≤ 1536 * ‖(v : ℂ)‖ * δ := by
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg (sq_nonneg η) hv0]
    apply habs.trans
    have hprod := mul_nonneg (norm_nonneg (u : ℂ)) hδ0
    nlinarith
  · have hvBδ : ‖(v : ℂ)‖ ≤ 2*δ := le_of_lt (lt_of_not_ge hclose)
    have huBδ : ‖(u : ℂ)‖ ≤ 3*δ := by
      have htri : ‖(u : ℂ)‖ ≤ δ + ‖(v : ℂ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le ((u : ℂ)-(v : ℂ)) (v : ℂ)
      linarith
    have hsq : ‖(u : ℂ)‖^2 + ‖(v : ℂ)‖^2 ≤
        3*(‖(u : ℂ)‖ + ‖(v : ℂ)‖)*δ := by
      have hup := mul_le_mul_of_nonneg_right huBδ (norm_nonneg (u : ℂ))
      have hvp := mul_le_mul_of_nonneg_right hvBδ (norm_nonneg (v : ℂ))
      have hnonneg := mul_nonneg (norm_nonneg (v : ℂ)) hδ0
      nlinarith
    have habs : |response W u-response W v| ≤ response W u+response W v := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hprod : 0 ≤ (‖(u : ℂ)‖ + ‖(v : ℂ)‖)*δ := by positivity
    nlinarith

private theorem response_lipschitz_on (R : ℝ) (hR : 0 ≤ R) :
    LipschitzOnWith ⟨3072*R, by positivity⟩ (response W)
      {u : G | ‖(u : ℂ)‖ ≤ R} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  change dist (response W u) (response W v) ≤
    (3072*R)*dist (u : ℂ) (v : ℂ)
  rw [Real.dist_eq, dist_eq_norm]
  have hp := response_polynomial_bound H hNat u v
  have hsum : ‖(u : ℂ)‖ + ‖(v : ℂ)‖ ≤ 2*R := by
    change ‖(u : ℂ)‖ ≤ R at hu
    change ‖(v : ℂ)‖ ≤ R at hv
    linarith
  have hprod := mul_le_mul_of_nonneg_right hsum
    (by positivity : 0 ≤ 1536*‖(u : ℂ)-(v : ℂ)‖)
  nlinarith

private theorem response_limit_exists (z : ℂ) :
    ∃ y : ℝ, Tendsto (response W)
      (Filter.comap (Subtype.val : G → ℂ) (𝓝 z)) (𝓝 y) := by
  let l := Filter.comap (Subtype.val : G → ℂ) (𝓝 z)
  haveI : l.NeBot := gaussian_dense.comap_val_nhds_neBot z
  have hmap : Cauchy (Filter.map (Subtype.val : G → ℂ) l) :=
    cauchy_nhds.mono Filter.map_comap_le
  have hl : Cauchy l :=
    (isUniformInducing_val (gaussianDyadic : Set ℂ)).cauchy_map_iff.mp hmap
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlocal : l ≤ 𝓟 {u : G | ‖(u : ℂ)‖ ≤ R} := by
    apply Filter.le_principal_iff.mpr
    apply Filter.mem_of_superset
      (Filter.preimage_mem_comap (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ)<1)))
    intro u hu
    change dist (u : ℂ) z < 1 at hu
    rw [dist_eq_norm] at hu
    change ‖(u : ℂ)‖ ≤ ‖z‖+1
    have htri : ‖(u : ℂ)‖ ≤ ‖(u : ℂ)-z‖+‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((u : ℂ)-z) z
    linarith
  have hresponse : Cauchy (Filter.map (response W) l) :=
    hl.map_of_le (response_lipschitz_on H hNat R hR).uniformContinuousOn hlocal
  exact CompleteSpace.complete hresponse

private theorem extension_continuous : Continuous (complexExtension W) := by
  exact gaussian_dense.continuous_extend (response_limit_exists H hNat)

private theorem extension_agrees (z : G) : complexExtension W (z : ℂ) = response W z := by
  exact gaussian_dense.isDenseInducing_val.extend_eq' (response_limit_exists H hNat) z

private theorem extension_evaluation (p : P) : complexExtension W (E p) = W p := by
  calc
    complexExtension W (E p) = response W ⟨E p, evaluation_mem p⟩ :=
      extension_agrees H hNat ⟨E p, evaluation_mem p⟩
    _ = W p := response_evaluation H hNat p

private theorem extension_one : complexExtension W 1 = 1 := by
  have h := extension_evaluation H hNat (1 : P)
  simpa only [map_one, H.normalized] using h

private theorem extension_dyadic_gain (d : DyadicCount) (z : ℂ) :
    complexExtension W (((d : ℝ) : ℂ)*z) = (d : ℝ)^2 * complexExtension W z := by
  have hc := extension_continuous H hNat
  apply isClosed_property gaussian_dense.denseRange_val
    (isClosed_eq (hc.comp (continuous_const.mul continuous_id))
      (continuous_const.mul hc)) ?_ z
  intro u
  calc
    complexExtension W (((d : ℝ) : ℂ)*(u : ℂ)) =
        complexExtension W (E (scalar d * reference u)) := by
      rw [map_mul, evaluation_scalar, reference_evaluation]
    _ = W (scalar d * reference u) := extension_evaluation H hNat _
    _ = (d : ℝ)^2 * W (reference u) := scalar_gain H hNat d _
    _ = (d : ℝ)^2 * complexExtension W (u : ℂ) := by
      rw [extension_agrees H hNat]
      rfl

private theorem extension_real_gain (r : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    complexExtension W ((r : ℂ)*z) = r^2 * complexExtension W z := by
  have hc := extension_continuous H hNat
  have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  have hmax : ∀ t : ℝ, complexExtension W (((max t 0 : ℝ) : ℂ)*z) =
      (max t 0)^2 * complexExtension W z := by
    apply isClosed_property real_dense.denseRange_val
      (isClosed_eq (hc.comp ((Complex.continuous_ofReal.comp hm).mul continuous_const))
        ((hm.pow 2).mul continuous_const))
    intro t
    have hmem : max (t : ℝ) 0 ∈ realDyadic := by
      by_cases ht : 0 ≤ (t : ℝ)
      · simpa only [max_eq_left ht] using t.property
      · rw [max_eq_right (le_of_not_ge ht)]
        exact realDyadic.zero_mem
    exact extension_dyadic_gain H hNat
      ⟨max (t : ℝ) 0, hmem, le_max_right _ _⟩ z
  simpa only [max_eq_left hr] using hmax r

private theorem extension_increasing (M : P) (hM : ResponseIncreasing W M) (z : ℂ) :
    complexExtension W z ≤ complexExtension W (E M*z) := by
  have hc := extension_continuous H hNat
  apply isClosed_property gaussian_dense.denseRange_val
    (isClosed_le hc (hc.comp (continuous_const.mul continuous_id))) ?_ z
  intro u
  calc
    complexExtension W (u : ℂ) = W (reference u) := by
      rw [extension_agrees H hNat]
      rfl
    _ ≤ W (M * reference u) := hM _
    _ = complexExtension W (E M*(u : ℂ)) := by
      rw [← reference_evaluation u, ← map_mul, extension_evaluation H hNat]

private theorem boundary_dyadic (t : D) (z : ℂ) :
    complexExtension W z ≤ complexExtension W ((1 + ((t : ℝ) : ℂ)*Complex.I)*z) := by
  by_cases ht : 0 ≤ (t : ℝ)
  · obtain ⟨k, m, htm⟩ := nonnegative_dyadic_representation (t : ℝ) ht t.property
    have hc : E (plusWord k m) = 1 + ((t : ℝ) : ℂ)*Complex.I := by
      rw [(plusWord_coordinates k m).1, htm]
    rw [← hc]
    exact extension_increasing H hNat _ (plusWord_increasing H.preparedOrder k m) z
  · obtain ⟨k, m, htm⟩ := nonnegative_dyadic_representation (-(t : ℝ))
      (by linarith) (realDyadic.neg_mem t.property)
    have hc : E (minusWord k m) = 1 + ((t : ℝ) : ℂ)*Complex.I := by
      rw [(minusWord_coordinates k m).1, ← htm]
      push_cast
      ring
    rw [← hc]
    exact extension_increasing H hNat _ (minusWord_increasing H.preparedOrder k m) z

private theorem boundary_real (t : ℝ) (z : ℂ) :
    complexExtension W z ≤ complexExtension W ((1 + (t : ℂ)*Complex.I)*z) := by
  have hc := extension_continuous H hNat
  apply isClosed_property real_dense.denseRange_val
    (isClosed_le continuous_const
      (hc.comp ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const))) ?_ t
  intro d
  exact boundary_dyadic H hNat d z

private theorem rotation_le (θ : ℝ) (z : ℂ) :
    complexExtension W z ≤ complexExtension W (Complex.exp ((θ : ℂ)*Complex.I)*z) := by
  have hfinite (n k : ℕ) : complexExtension W z ≤
      complexExtension W ((1 + ((θ : ℂ)*Complex.I)/(n : ℂ))^k*z) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hb := boundary_real H hNat (θ/(n : ℝ))
          ((1 + ((θ : ℂ)*Complex.I)/(n : ℂ))^k*z)
        have he : 1 + ((θ/(n : ℝ) : ℝ) : ℂ)*Complex.I =
            1 + ((θ : ℂ)*Complex.I)/(n : ℂ) := by
          push_cast
          simp only [div_eq_mul_inv]
          ring
        rw [he] at hb
        apply ih.trans
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hb
  have hlim : Tendsto
      (fun n : ℕ => complexExtension W ((1 + ((θ : ℂ)*Complex.I)/(n : ℂ))^n*z))
      atTop (𝓝 (complexExtension W (Complex.exp ((θ : ℂ)*Complex.I)*z))) :=
    (extension_continuous H hNat).continuousAt.tendsto.comp
      ((Complex.tendsto_one_add_div_pow_exp ((θ : ℂ)*Complex.I)).mul_const z)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => hfinite n n)

private theorem rotation_invariant (θ : ℝ) (z : ℂ) :
    complexExtension W (Complex.exp ((θ : ℂ)*Complex.I)*z) = complexExtension W z := by
  have hback := rotation_le H hNat (-θ) (Complex.exp ((θ : ℂ)*Complex.I)*z)
  have hcancel : Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) *
      Complex.exp ((θ : ℂ)*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hzero : (((-θ : ℝ) : ℂ)*Complex.I) + (θ : ℂ)*Complex.I = 0 := by
      push_cast
      ring
    rw [hzero, Complex.exp_zero]
  rw [← mul_assoc, hcancel, one_mul] at hback
  exact le_antisymm hback (rotation_le H hNat θ z)

private theorem extension_norm_square (z : ℂ) : complexExtension W z = ‖z‖^2 := by
  have hradial : complexExtension W ((‖z‖ : ℝ) : ℂ) = ‖z‖^2 := by
    have h := extension_real_gain H hNat ‖z‖ (norm_nonneg _) (1 : ℂ)
    simpa only [mul_one, extension_one H hNat] using h
  calc
    complexExtension W z = complexExtension W
        (Complex.exp (((Complex.arg z : ℝ) : ℂ)*Complex.I)*((‖z‖ : ℝ) : ℂ)) := by
      congr 1
      rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
    _ = complexExtension W ((‖z‖ : ℝ) : ℂ) :=
      rotation_invariant H hNat (Complex.arg z) _
    _ = ‖z‖^2 := hradial

/-- The base contract and quadratic natural-count gain select the norm-square
response on every literal initial preparation. -/
theorem selected (p : P) : W p = N p := by
  calc
    W p = complexExtension W (E p) := (extension_evaluation H hNat p).symm
    _ = ‖E p‖^2 := extension_norm_square H hNat _
    _ = N p := by
      simpa only [N, normSq] using Complex.sq_norm (E p)

end Response
end
end IDT.QMClosure.InitialCountHomogeneousReadoutSelection
