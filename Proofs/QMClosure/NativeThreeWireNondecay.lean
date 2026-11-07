import Proofs.QMClosure.NativeThreeWireProbabilityDenominator
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# No asymptotic period for one exact native three-wire weight

The squared norm selected by the existing repeated native word has no positive
asymptotic period. A fourth-order recurrence factors into two second-order
recurrences whose positive definite energies are conserved. This is an exact
mathematical property of the supplied complex circuit semantics. It does not
by itself exclude finite stochastic detectors, supply an actualization law,
or establish physical dynamics or QM closure.
-/

namespace IDT.QMClosure.NativeThreeWireNondecay

noncomputable section

open Filter NativeThreeWireProbabilityDenominator
open scoped Topology

/-- Conserved quadratic form for a real second-order recurrence. -/
def recurrenceEnergy (u : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  u n ^ 2 + u (n + 1) ^ 2 - c * u n * u (n + 1)

theorem recurrenceEnergy_constant (u : ℕ → ℝ) (c : ℝ)
    (hrec : ∀ n, u (n + 2) = c * u (n + 1) - u n) (n : ℕ) :
    recurrenceEnergy u c n = recurrenceEnergy u c 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        recurrenceEnergy u c (n + 1) = recurrenceEnergy u c n := by
          simp only [recurrenceEnergy, Nat.add_assoc]
          rw [hrec n]
          ring
        _ = recurrenceEnergy u c 0 := ih

theorem energy_zero_coordinates (c x y : ℝ) (hlo : -2 < c) (hhi : c < 2)
    (h : x ^ 2 + y ^ 2 - c * x * y = 0) : x = 0 ∧ y = 0 := by
  have hp : 0 < (2 - c) / 4 := by linarith
  have hm : 0 < (2 + c) / 4 := by linarith
  have hA : 0 ≤ ((2 - c) / 4) * (x + y) ^ 2 :=
    mul_nonneg hp.le (sq_nonneg _)
  have hB : 0 ≤ ((2 + c) / 4) * (x - y) ^ 2 :=
    mul_nonneg hm.le (sq_nonneg _)
  have hs : ((2 - c) / 4) * (x + y) ^ 2 +
      ((2 + c) / 4) * (x - y) ^ 2 = 0 := by nlinarith [h]
  have ha : ((2 - c) / 4) * (x + y) ^ 2 = 0 := by linarith
  have hb : ((2 + c) / 4) * (x - y) ^ 2 = 0 := by linarith
  have hplus : x + y = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp ha).resolve_left (ne_of_gt hp))
  have hminus : x - y = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hb).resolve_left (ne_of_gt hm))
  constructor <;> linarith

/-- A stable-energy recurrence can tend to zero only when it is identically zero. -/
theorem recurrence_tendsto_zero (u : ℕ → ℝ) (c : ℝ) (hlo : -2 < c) (hhi : c < 2)
    (hrec : ∀ n, u (n + 2) = c * u (n + 1) - u n)
    (hu : Tendsto u atTop (𝓝 0)) : ∀ n, u n = 0 := by
  have hshift : Tendsto (fun n => u (n + 1)) atTop (𝓝 0) :=
    hu.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun n => recurrenceEnergy u c n) atTop (𝓝 0) := by
    simpa [recurrenceEnergy] using
      ((hu.pow 2).add (hshift.pow 2)).sub (((tendsto_const_nhds (x := c)).mul hu).mul hshift)
  have hec : Tendsto (fun _ : ℕ => recurrenceEnergy u c 0) atTop (𝓝 0) := by
    simpa only [recurrenceEnergy_constant u c hrec] using he
  have hz : recurrenceEnergy u c 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hec
  intro n
  exact (energy_zero_coordinates c (u n) (u (n + 1)) hlo hhi
    ((recurrenceEnergy_constant u c hrec n).trans hz)).1

def centeredAmplitude (n : ℕ) : ℂ := selectedAmplitude n - 1 / 3
def centeredReal (n : ℕ) : ℝ := (centeredAmplitude n).re
def centeredImag (n : ℕ) : ℝ := (centeredAmplitude n).im

theorem centeredAmplitude_recurrence (n : ℕ) :
    centeredAmplitude (n + 2) = centeredAmplitude (n + 1) / 2 - centeredAmplitude n := by
  simp only [centeredAmplitude, selectedAmplitude_recurrence]
  ring

theorem centeredReal_recurrence (n : ℕ) :
    centeredReal (n + 2) = (1 / 2 : ℝ) * centeredReal (n + 1) - centeredReal n := by
  have h := congrArg Complex.re (centeredAmplitude_recurrence n)
  dsimp only [centeredReal]
  norm_num [Complex.div_re] at h
  linarith

theorem centeredImag_recurrence (n : ℕ) :
    centeredImag (n + 2) = (1 / 2 : ℝ) * centeredImag (n + 1) - centeredImag n := by
  have h := congrArg Complex.im (centeredAmplitude_recurrence n)
  dsimp only [centeredImag]
  norm_num [Complex.div_im] at h
  linarith

theorem centered_energy (n : ℕ) :
    recurrenceEnergy centeredReal (1 / 2) n + recurrenceEnergy centeredImag (1 / 2) n =
      2 / 3 := by
  rw [recurrenceEnergy_constant _ _ centeredReal_recurrence,
    recurrenceEnergy_constant _ _ centeredImag_recurrence]
  norm_num [recurrenceEnergy, centeredReal, centeredImag, centeredAmplitude,
    selectedAmplitude_zero, selectedAmplitude_one, Complex.div_re, Complex.div_im]

theorem selectedWeight_centered (n : ℕ) :
    selectedWeight n = centeredReal n ^ 2 + centeredImag n ^ 2 +
      (2 / 3) * centeredReal n + 1 / 9 := by
  norm_num [selectedWeight, centeredReal, centeredImag, centeredAmplitude,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring

theorem half_recurrence_fourth_square (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 2) = (1 / 2 : ℝ) * u (n + 1) - u n) (n : ℕ) :
    8 * u (n + 4) ^ 2 + 10 * u (n + 3) ^ 2 + 9 * u (n + 2) ^ 2 +
      10 * u (n + 1) ^ 2 + 8 * u n ^ 2 = 24 * recurrenceEnergy u (1 / 2) n := by
  have h3 : u (n + 3) = (1 / 2 : ℝ) * u (n + 2) - u (n + 1) := by
    simpa only [Nat.add_assoc] using hu (n + 1)
  have h4 : u (n + 4) = (1 / 2 : ℝ) * u (n + 3) - u (n + 2) := by
    simpa only [Nat.add_assoc] using hu (n + 2)
  rw [h4, h3, hu n]
  simp only [recurrenceEnergy]
  ring

theorem half_recurrence_fourth_linear (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 2) = (1 / 2 : ℝ) * u (n + 1) - u n) (n : ℕ) :
    8 * u (n + 4) + 10 * u (n + 3) + 9 * u (n + 2) +
      10 * u (n + 1) + 8 * u n = 0 := by
  have h3 : u (n + 3) = (1 / 2 : ℝ) * u (n + 2) - u (n + 1) := by
    simpa only [Nat.add_assoc] using hu (n + 1)
  have h4 : u (n + 4) = (1 / 2 : ℝ) * u (n + 3) - u (n + 2) := by
    simpa only [Nat.add_assoc] using hu (n + 2)
  rw [h4, h3, hu n]
  ring

/-- Exact forced fourth-order recurrence of the native selected weight. -/
theorem selectedWeight_recurrence (n : ℕ) :
    8 * selectedWeight (n + 4) + 10 * selectedWeight (n + 3) +
      9 * selectedWeight (n + 2) + 10 * selectedWeight (n + 1) +
      8 * selectedWeight n = 21 := by
  simp only [selectedWeight_centered]
  linarith [half_recurrence_fourth_square centeredReal centeredReal_recurrence n,
    half_recurrence_fourth_square centeredImag centeredImag_recurrence n,
    half_recurrence_fourth_linear centeredReal centeredReal_recurrence n,
    centered_energy n]

/-- The factored fourth-order homogeneous recurrence has no decaying solution. -/
theorem fourth_recurrence_tendsto_zero (d : ℕ → ℝ)
    (hrec : ∀ n, 8 * d (n + 4) + 10 * d (n + 3) + 9 * d (n + 2) +
      10 * d (n + 1) + 8 * d n = 0)
    (hd : Tendsto d atTop (𝓝 0)) : ∀ n, d n = 0 := by
  let f : ℕ → ℝ := fun n => d (n + 2) + (7 / 4) * d (n + 1) + d n
  have hfrec : ∀ n, f (n + 2) = (1 / 2 : ℝ) * f (n + 1) - f n := by
    intro n
    dsimp only [f]
    simp only [Nat.add_assoc]
    linarith [hrec n]
  have hflim : Tendsto f atTop (𝓝 0) := by
    simpa [f] using
      ((hd.comp (tendsto_add_atTop_nat 2)).add
        ((tendsto_const_nhds (x := (7 / 4 : ℝ))).mul
          (hd.comp (tendsto_add_atTop_nat 1)))).add hd
  have hfzero := recurrence_tendsto_zero f (1 / 2) (by norm_num) (by norm_num) hfrec hflim
  have hdrec : ∀ n, d (n + 2) = (-7 / 4 : ℝ) * d (n + 1) - d n := by
    intro n
    have h := hfzero n
    dsimp only [f] at h
    linarith
  exact recurrence_tendsto_zero d (-7 / 4) (by norm_num) (by norm_num) hdrec hd

def periodDifference (q n : ℕ) : ℝ := selectedWeight (n + q) - selectedWeight n

theorem periodDifference_recurrence (q n : ℕ) :
    8 * periodDifference q (n + 4) + 10 * periodDifference q (n + 3) +
      9 * periodDifference q (n + 2) + 10 * periodDifference q (n + 1) +
      8 * periodDifference q n = 0 := by
  have hshift := selectedWeight_recurrence (n + q)
  have hadd (k : ℕ) : n + q + k = n + k + q := by omega
  simp only [hadd] at hshift
  dsimp only [periodDifference]
  linarith [selectedWeight_recurrence n]

/-- No positive shift makes the actual native selected-weight differences decay. -/
theorem selectedWeight_no_asymptotic_period (q : ℕ) (hq : 0 < q) :
    ¬ Tendsto (fun n => selectedWeight (n + q) - selectedWeight n) atTop (𝓝 0) := by
  intro hlim
  have hz := fourth_recurrence_tendsto_zero (periodDifference q)
    (periodDifference_recurrence q) hlim 0
  have hp0 : selectedWeight 0 = 1 := by simp [selectedWeight, selectedAmplitude_zero]
  have hpq : selectedWeight q = 1 := by
    simpa [periodDifference, hp0, sub_eq_zero] using hz
  have hd := denominator_dvd q hq 1 1 (by norm_num) (by simpa using hpq)
  have hexp : 0 < 2 * q - 1 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hexp)
  rw [hm, pow_succ] at hd
  have ht : 2 ∣ (1 : ℕ) := (dvd_mul_left 2 (2 ^ m)).trans hd
  norm_num at ht

end

end IDT.QMClosure.NativeThreeWireNondecay
