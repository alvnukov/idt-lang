import Proofs.QMClosure.InitialColumnOrderReadoutCore

/-!
Finite-word sector reduction and coarse count bounds on the initial carrier.
The response hypotheses are the four-field base contract. Real-axis response
bounds are supplied separately to the final comparison theorems.
-/

namespace IDT.QMClosure.InitialCountSectorBounds

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPreparedCountOrder InitialDyadicRelativeLanding
open InitialEchoCoordinates InitialColumnOrderReadoutCore

variable {W : P → ℝ}

/-- A finite sector annulus specified by the existing complex coordinate. -/
def NarrowAnnulus (p : P) : Prop :=
  1 ≤ N p ∧ N p ≤ 4 ∧ 0 < (E p).re ∧ 2 * |(E p).im| ≤ (E p).re

private def NarrowSector (p : P) : Prop :=
  0 < (E p).re ∧ 2 * |(E p).im| ≤ (E p).re

private theorem E_rho : E rho = Complex.I :=
  congrArg Prod.fst raw_rho

/-- The quarter turn is the existing finite word a*bInv. Its response law
comes from the two half laws at the actual preparation bInv*p. -/
private theorem rho_response (H : BaseContract W) (p : P) :
    W (rho * p) = W p := by
  have hb := (half_responses H (bInv * p)).2
  rw [← mul_assoc, b_mul_bInv, one_mul] at hb
  have ha := (half_responses H (bInv * p)).1
  rw [rho, mul_assoc, ha]
  linarith

private theorem rho_power_response (H : BaseContract W) (k : ℕ) (p : P) :
    W (rho ^ k * p) = W p := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        W (rho ^ (k + 1) * p) = W (rho * (rho ^ k * p)) := by
          congr 1
          rw [pow_succ]
          ring
        _ = W (rho ^ k * p) := rho_response H _
        _ = W p := ih

private theorem N_power (p : P) (k : ℕ) : N (p ^ k) = N p ^ k := by
  induction k with
  | zero => simp [N, InitialCountGeometry.normSq]
  | succ k ih =>
      calc
        N (p ^ (k + 1)) = N (p ^ k) * N p := by
          simpa only [pow_succ] using InitialCountGeometry.normSq_mul (p ^ k) p
        _ = N p ^ (k + 1) := by rw [ih, pow_succ]

private theorem rho_power_norm (k : ℕ) (p : P) :
    N (rho ^ k * p) = N p := by
  have hrho : N rho = 1 := by
    norm_num [N, InitialCountGeometry.normSq, E_rho]
  calc
    N (rho ^ k * p) = N (rho ^ k) * N p := InitialCountGeometry.normSq_mul _ _
    _ = N p := by rw [N_power, hrho, one_pow, one_mul]

/-- Four literal quarter turns suffice to reach the closed 45-degree sector.
This numerical lemma is used only to choose a finite exponent. -/
private theorem exists_quarter_sector (z : ℂ) (hz : z ≠ 0) :
    ∃ k : ℕ, 0 < (Complex.I ^ k * z).re ∧
      |(Complex.I ^ k * z).im| ≤ (Complex.I ^ k * z).re := by
  have hzero : ¬(z.re = 0 ∧ z.im = 0) := by
    rintro ⟨hr, hi⟩
    apply hz
    apply Complex.ext
    · simpa using hr
    · simpa using hi
  by_cases hdom : |z.im| ≤ |z.re|
  · by_cases hr : 0 < z.re
    · refine ⟨0, ?_, ?_⟩
      · simpa using hr
      · simpa [abs_of_pos hr] using hdom
    · have hrneg : z.re < 0 := by
        have hrle : z.re ≤ 0 := le_of_not_gt hr
        have hrne : z.re ≠ 0 := by
          intro heq
          have hi : z.im = 0 := by
            have habs : |z.im| = 0 :=
              le_antisymm (by simpa [heq] using hdom) (abs_nonneg _)
            exact abs_eq_zero.mp habs
          exact hzero ⟨heq, hi⟩
        exact lt_of_le_of_ne hrle hrne
      refine ⟨2, ?_, ?_⟩
      · simpa [Complex.mul_re, Complex.mul_im] using neg_pos.mpr hrneg
      · simpa [Complex.mul_re, Complex.mul_im, abs_of_neg hrneg] using hdom
  · have hdom' : |z.re| ≤ |z.im| := (lt_of_not_ge hdom).le
    by_cases hi : 0 < z.im
    · refine ⟨3, ?_, ?_⟩
      · simpa [pow_succ, Complex.mul_re, Complex.mul_im] using hi
      · simpa [pow_succ, Complex.mul_re, Complex.mul_im, abs_of_pos hi] using hdom'
    · have hineg : z.im < 0 := by
        have hile : z.im ≤ 0 := le_of_not_gt hi
        have hine : z.im ≠ 0 := by
          intro heq
          have hr : z.re = 0 := by
            have habs : |z.re| = 0 :=
              le_antisymm (by simpa [heq] using hdom') (abs_nonneg _)
            exact abs_eq_zero.mp habs
          exact hzero ⟨hr, heq⟩
        exact lt_of_le_of_ne hile hine
      refine ⟨1, ?_, ?_⟩
      · simpa [Complex.mul_re, Complex.mul_im] using neg_pos.mpr hineg
      · simpa [Complex.mul_re, Complex.mul_im, abs_of_neg hineg] using hdom'

private theorem branch_coordinates (p : P) :
    (E (a * p)).re = ((E p).re - (E p).im) / 2 ∧
    (E (a * p)).im = ((E p).re + (E p).im) / 2 ∧
    (E (b * p)).re = ((E p).re + (E p).im) / 2 ∧
    (E (b * p)).im = ((E p).im - (E p).re) / 2 := by
  simp only [map_mul, evaluation_a, evaluation_b]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [complexA, complexB, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im] <;> ring

private theorem branch_norms (p : P) :
    N (a * p) = (1 / 2 : ℝ) * N p ∧
    N (b * p) = (1 / 2 : ℝ) * N p := by
  have ha : N a = (1 / 2 : ℝ) := by
    norm_num [N, InitialCountGeometry.normSq, evaluation_a, complexA,
      Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hb : N b = (1 / 2 : ℝ) := by
    norm_num [N, InitialCountGeometry.normSq, evaluation_b, complexB,
      Complex.normSq_apply, Complex.div_re, Complex.div_im]
  constructor
  · calc
      N (a * p) = N a * N p := InitialCountGeometry.normSq_mul _ _
      _ = (1 / 2 : ℝ) * N p := by rw [ha]
  · calc
      N (b * p) = N b * N p := InitialCountGeometry.normSq_mul _ _
      _ = (1 / 2 : ℝ) * N p := by rw [hb]

/-- A single actual branch narrows the sector when needed. Its norm and
response have the same positive factor. -/
private theorem narrow_wide_sector (H : BaseContract W) (p : P)
    (hx : 0 < (E p).re) (hy : |(E p).im| ≤ (E p).re) :
    ∃ r : P, ∃ d : ℝ, 0 < d ∧ W r = d * W p ∧
      N r = d * N p ∧ NarrowSector r := by
  by_cases hnarrow : 2 * |(E p).im| ≤ (E p).re
  · exact ⟨p, 1, by norm_num, by ring, by ring, hx, hnarrow⟩
  have hwide : (E p).re < 2 * |(E p).im| := lt_of_not_ge hnarrow
  have hylo := neg_abs_le (E p).im
  have hyhi := le_abs_self (E p).im
  obtain ⟨haRe, haIm, hbRe, hbIm⟩ := branch_coordinates p
  obtain ⟨haN, hbN⟩ := branch_norms p
  by_cases him : 0 ≤ (E p).im
  · have habs : |(E p).im| = (E p).im := abs_of_nonneg him
    have hsign : (E (b * p)).im ≤ 0 := by rw [hbIm]; linarith
    refine ⟨b * p, 1 / 2, by norm_num, ?_, hbN, ?_, ?_⟩
    · rw [(half_responses H p).2]
      ring
    · rw [hbRe]
      linarith
    · rw [abs_of_nonpos hsign, hbRe, hbIm]
      rw [habs] at hwide
      linarith
  · have him' : (E p).im < 0 := lt_of_not_ge him
    have habs : |(E p).im| = -(E p).im := abs_of_neg him'
    have hsign : 0 ≤ (E (a * p)).im := by rw [haIm]; linarith
    refine ⟨a * p, 1 / 2, by norm_num, ?_, haN, ?_, ?_⟩
    · rw [(half_responses H p).1]
      ring
    · rw [haRe]
      linarith
    · rw [abs_of_nonneg hsign, haRe, haIm]
      rw [habs] at hwide
      linarith

private theorem exists_narrow_sector (H : BaseContract W) (p : P)
    (hp : E p ≠ 0) :
    ∃ r : P, ∃ d : ℝ, 0 < d ∧ W r = d * W p ∧
      N r = d * N p ∧ NarrowSector r := by
  obtain ⟨k, hx, hy⟩ := exists_quarter_sector (E p) hp
  have hcoords : E (rho ^ k * p) = Complex.I ^ k * E p := by
    rw [map_mul, map_pow, E_rho]
  rw [← hcoords] at hx hy
  obtain ⟨r, d, hd, hW, hN, hsector⟩ :=
    narrow_wide_sector H (rho ^ k * p) hx hy
  rw [rho_power_response H] at hW
  rw [rho_power_norm] at hN
  exact ⟨r, d, hd, hW, hN, hsector⟩

/-- Positive numerical coordinate scaling preserves the sector. The argument
does not construct a carrier element from the numerical multiplier. -/
private theorem narrow_sector_of_coordinates {p r : P} (u : ℝ) (hu : 0 < u)
    (hcoords : E r = (u : ℂ) * E p) (hsector : NarrowSector p) :
    NarrowSector r := by
  obtain ⟨hx, hy⟩ := hsector
  have hr : (E r).re = u * (E p).re := by
    rw [hcoords]
    simp [Complex.mul_re]
  have hi : (E r).im = u * (E p).im := by
    rw [hcoords]
    simp [Complex.mul_im]
  constructor
  · rw [hr]
    exact mul_pos hu hx
  · rw [hr, hi, abs_mul, abs_of_pos hu]
    nlinarith [mul_le_mul_of_nonneg_left hy hu.le]

private theorem h_power_coordinates (k : ℕ) (p : P) :
    E (h ^ k * p) = (((1 / 2 : ℝ) ^ k : ℝ) : ℂ) * E p := by
  rw [map_mul, map_pow, evaluation_h, Complex.ofReal_pow]

private theorem hInv_power_coordinates (k : ℕ) (p : P) :
    E (hInv ^ k * p) = (((2 : ℝ) ^ k : ℝ) : ℂ) * E p := by
  rw [map_mul, map_pow, E_hInv]
  push_cast
  rfl

private theorem h_power_norm (k : ℕ) (p : P) :
    N (h ^ k * p) = N p / (4 : ℝ) ^ k := by
  have hh : N h = (1 / 4 : ℝ) := by
    rw [N_of_real h (1 / 2) evaluation_h]
    norm_num
  calc
    N (h ^ k * p) = N (h ^ k) * N p := InitialCountGeometry.normSq_mul _ _
    _ = N p / (4 : ℝ) ^ k := by
      rw [N_power, hh]
      simp only [one_div_pow]
      ring

private theorem hInv_power_norm (k : ℕ) (p : P) :
    N (hInv ^ k * p) = (4 : ℝ) ^ k * N p := by
  have hh : N hInv = (4 : ℝ) := by
    rw [N_of_real hInv 2 E_hInv]
    norm_num
  calc
    N (hInv ^ k * p) = N (hInv ^ k) * N p := InitialCountGeometry.normSq_mul _ _
    _ = (4 : ℝ) ^ k * N p := by rw [N_power, hh]

/-- Normalization uses only a quarter-turn power, at most one branch, and
an actual h or hInv power. The common response/norm multiplier is positive. -/
theorem sector_normalize (H : BaseContract W) (p : P) (hp : E p ≠ 0) :
    ∃ r : P, ∃ d : ℝ, 0 < d ∧ W r = d * W p ∧
      N r = d * N p ∧ NarrowAnnulus r := by
  obtain ⟨q, d, hd, hW, hN, hsector⟩ := exists_narrow_sector H p hp
  have hNp : 0 < N p := Complex.normSq_pos.mpr hp
  have hNq : 0 < N q := by rw [hN]; exact mul_pos hd hNp
  by_cases hq1 : 1 ≤ N q
  · obtain ⟨k, hk, hkhi⟩ :=
      exists_nat_pow_near hq1 (by norm_num : (1 : ℝ) < 4)
    have hkpos : (0 : ℝ) < 4 ^ k := by positivity
    have hnlo : 1 ≤ N q / (4 : ℝ) ^ k := (one_le_div hkpos).mpr hk
    have hnhi : N q / (4 : ℝ) ^ k ≤ 4 := by
      apply (div_le_iff₀ hkpos).mpr
      rw [pow_succ] at hkhi
      linarith
    have hnewsector := narrow_sector_of_coordinates
      ((1 / 2 : ℝ) ^ k) (by positivity)
      (h_power_coordinates k q) hsector
    refine ⟨h ^ k * q, d / (4 : ℝ) ^ k, div_pos hd hkpos, ?_, ?_, ?_⟩
    · rw [h_power_response H, hW]
      ring
    · rw [h_power_norm, hN]
      ring
    · exact ⟨by simpa only [h_power_norm] using hnlo,
        by simpa only [h_power_norm] using hnhi, hnewsector⟩
  · have hqinv : 1 ≤ 1 / N q := (one_le_div hNq).mpr (le_of_not_ge hq1)
    obtain ⟨k, hk, hkhi⟩ :=
      exists_nat_pow_near hqinv (by norm_num : (1 : ℝ) < 4)
    let n := k + 1
    have hnpos : (0 : ℝ) < 4 ^ n := by positivity
    have hnlo : 1 ≤ (4 : ℝ) ^ n * N q := by
      have hh := (div_lt_iff₀ hNq).mp hkhi
      dsimp [n]
      linarith
    have hnhi : (4 : ℝ) ^ n * N q ≤ 4 := by
      have hh := (le_div_iff₀ hNq).mp hk
      dsimp [n]
      rw [pow_succ]
      nlinarith
    have hnewsector := narrow_sector_of_coordinates
      ((2 : ℝ) ^ n) (by positivity)
      (hInv_power_coordinates n q) hsector
    refine ⟨hInv ^ n * q, (4 : ℝ) ^ n * d, mul_pos hnpos hd, ?_, ?_, ?_⟩
    · rw [hInv_power_response H, hW]
      ring
    · rw [hInv_power_norm, hN]
      ring
    · exact ⟨by simpa only [hInv_power_norm] using hnlo,
        by simpa only [hInv_power_norm] using hnhi, hnewsector⟩

private theorem sector_coordinate_bounds (p : P) (hp : NarrowAnnulus p) :
    0 ≤ (E p).re - (E p).im ∧ 0 ≤ (E p).re + (E p).im ∧
    (E p).re - (E p).im ≤ 4 ∧ (E p).re + (E p).im ≤ 4 ∧
    1 ≤ 8 * ((E p).re - (E p).im) ∧
    1 ≤ 8 * ((E p).re + (E p).im) := by
  obtain ⟨hnlo, hnhi, hx, hsector⟩ := hp
  have hylo := neg_abs_le (E p).im
  have hyhi := le_abs_self (E p).im
  have habs := abs_nonneg (E p).im
  have hnorm : N p = (E p).re ^ 2 + (E p).im ^ 2 := by
    simp [N, InitialCountGeometry.normSq, Complex.normSq_apply, pow_two]
  have hxhi : (E p).re ≤ 2 := by
    nlinarith [sq_nonneg (E p).im]
  have hySq : (E p).im ^ 2 ≤ (E p).re ^ 2 := by
    nlinarith [mul_nonneg
      (show 0 ≤ (E p).re - (E p).im by linarith)
      (show 0 ≤ (E p).re + (E p).im by linarith)]
  have hxlo : (1 / 2 : ℝ) ≤ (E p).re := by
    by_contra hsmall
    have hsmall' : (E p).re < (1 / 2 : ℝ) := lt_of_not_ge hsmall
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hsmall'.le)]
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- An exact endpoint is computed from two nonnegative dyadic coefficients.
No conjugated preparation is inserted into the initial carrier. -/
private theorem raw_endpoint (p : P) (s t : DyadicCount) (u : ℝ)
    (hs : (s : ℝ) = u * ((E p).re - (E p).im))
    (ht : (t : ℝ) = u * ((E p).re + (E p).im)) :
    E (raw s t * p) = ((u * N p : ℝ) : ℂ) := by
  obtain ⟨hre, him, _⟩ := raw_coordinates s t
  have hnorm : N p = (E p).re ^ 2 + (E p).im ^ 2 := by
    simp [N, InitialCountGeometry.normSq, Complex.normSq_apply, pow_two]
  apply Complex.ext
  · rw [map_mul, Complex.mul_re, hre, him, hs, ht, Complex.ofReal_re, hnorm]
    ring
  · rw [map_mul, Complex.mul_im, hre, him, hs, ht, Complex.ofReal_im]
    ring

/-- A real-axis upper callback controls the whole finite sector annulus. -/
theorem sector_upper (H : BaseContract W)
    (hUpper : ∀ (p : P) (x : ℝ), E p = (x : ℂ) → 0 < x → W p ≤ x ^ 2)
    (p : P) (hp : NarrowAnnulus p) : W p ≤ 256 * N p := by
  obtain ⟨hminus, hplus, _, _, hminus8, hplus8⟩ := sector_coordinate_bounds p hp
  obtain ⟨hxmem, hymem⟩ := evaluation_real_imag_dyadic p
  have h8mem : (8 : ℝ) ∈ realDyadic := by
    simpa only [naturalCount_value] using (naturalCount 8).property.1
  let s : DyadicCount := ⟨8 * ((E p).re - (E p).im),
    realDyadic.mul_mem h8mem (realDyadic.sub_mem hxmem hymem),
    mul_nonneg (by norm_num) hminus⟩
  let t : DyadicCount := ⟨8 * ((E p).re + (E p).im),
    realDyadic.mul_mem h8mem (realDyadic.add_mem hxmem hymem),
    mul_nonneg (by norm_num) hplus⟩
  have hs : (naturalCount 1 : ℝ) ≤ (s : ℝ) := by
    simpa [s, naturalCount, dyadicCount] using hminus8
  have ht : (naturalCount 1 : ℝ) ≤ (t : ℝ) := by
    simpa [t, naturalCount, dyadicCount] using hplus8
  have ho := prepared_dyadic_order H.preparedOrder
    (naturalCount 1) (naturalCount 1) s t hs ht p
  simp only [raw_natural, bag_diagonal, Nat.cast_one, one_mul] at ho
  have he : E (raw s t * p) = ((8 * N p : ℝ) : ℂ) :=
    raw_endpoint p s t 8 rfl rfl
  have hnpos : 0 < N p := lt_of_lt_of_le (by norm_num) hp.1
  have hu := hUpper (raw s t * p) (8 * N p) he (by positivity)
  have hnprod : 0 ≤ N p * (4 - N p) :=
    mul_nonneg hnpos.le (sub_nonneg.mpr hp.2.1)
  nlinarith

/-- Exact positive real-axis calibration gives a positive coarse sector lower
bound using the dyadic coefficients (x-y)/4 and (x+y)/4. -/
theorem sector_lower (H : BaseContract W)
    (hReal : ∀ (p : P) (x : ℝ), E p = (x : ℂ) → 0 < x → W p = x ^ 2)
    (p : P) (hp : NarrowAnnulus p) : N p / 16 ≤ W p := by
  obtain ⟨hminus, hplus, hminus4, hplus4, _, _⟩ := sector_coordinate_bounds p hp
  obtain ⟨hxmem, hymem⟩ := evaluation_real_imag_dyadic p
  have hquarter : (1 / 4 : ℝ) ∈ realDyadic := by
    have hd := (dyadicCount 2 1).property.1
    norm_num only [dyadicCount_value] at hd
    exact hd
  let s : DyadicCount := ⟨(1 / 4 : ℝ) * ((E p).re - (E p).im),
    realDyadic.mul_mem hquarter (realDyadic.sub_mem hxmem hymem),
    mul_nonneg (by norm_num) hminus⟩
  let t : DyadicCount := ⟨(1 / 4 : ℝ) * ((E p).re + (E p).im),
    realDyadic.mul_mem hquarter (realDyadic.add_mem hxmem hymem),
    mul_nonneg (by norm_num) hplus⟩
  have hs : (s : ℝ) ≤ (naturalCount 1 : ℝ) := by
    have hsbound : (1 / 4 : ℝ) * ((E p).re - (E p).im) ≤ 1 := by linarith
    simpa [s, naturalCount, dyadicCount] using hsbound
  have ht : (t : ℝ) ≤ (naturalCount 1 : ℝ) := by
    have htbound : (1 / 4 : ℝ) * ((E p).re + (E p).im) ≤ 1 := by linarith
    simpa [t, naturalCount, dyadicCount] using htbound
  have ho := prepared_dyadic_order H.preparedOrder
    s t (naturalCount 1) (naturalCount 1) hs ht p
  simp only [raw_natural, bag_diagonal, Nat.cast_one, one_mul] at ho
  have he : E (raw s t * p) = (((1 / 4 : ℝ) * N p : ℝ) : ℂ) :=
    raw_endpoint p s t (1 / 4) rfl rfl
  have hnpos : 0 < N p := lt_of_lt_of_le (by norm_num) hp.1
  have hc := hReal (raw s t * p) ((1 / 4 : ℝ) * N p) he (by positivity)
  have hnprod : 0 ≤ N p * (N p - 1) :=
    mul_nonneg hnpos.le (sub_nonneg.mpr hp.1)
  rw [hc] at ho
  nlinarith

/-- Global comparison follows by cancellation of the common positive finite
normalization factor. -/
theorem global_coarse_upper (H : BaseContract W)
    (hUpper : ∀ (p : P) (x : ℝ), E p = (x : ℂ) → 0 < x → W p ≤ x ^ 2)
    (p : P) : W p ≤ 256 * N p := by
  by_cases hp : E p = 0
  · rw [null_response H p hp]
    simp [N, InitialCountGeometry.normSq, hp]
  · obtain ⟨r, d, hd, hW, hN, hAnn⟩ := sector_normalize H p hp
    have hu := sector_upper H hUpper r hAnn
    rw [hW, hN] at hu
    by_contra hgt
    have hpos : 0 < d * (W p - 256 * N p) :=
      mul_pos hd (sub_pos.mpr (lt_of_not_ge hgt))
    nlinarith

/-- Positive real-axis calibration supplies a global coarse lower bound. -/
theorem global_coarse_lower (H : BaseContract W)
    (hReal : ∀ (p : P) (x : ℝ), E p = (x : ℂ) → 0 < x → W p = x ^ 2)
    (p : P) : N p / 16 ≤ W p := by
  by_cases hp : E p = 0
  · rw [null_response H p hp]
    simp [N, InitialCountGeometry.normSq, hp]
  · obtain ⟨r, d, hd, hW, hN, hAnn⟩ := sector_normalize H p hp
    have hl := sector_lower H hReal r hAnn
    rw [hW, hN] at hl
    by_contra hgt
    have hpos : 0 < d * (N p / 16 - W p) :=
      mul_pos hd (sub_pos.mpr (lt_of_not_ge hgt))
    nlinarith

end
end IDT.QMClosure.InitialCountSectorBounds
