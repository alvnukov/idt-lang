import Proofs.QMClosure.PositiveQuadraticPolarization
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic

namespace IDT.QMClosure.NormalizedEchoReadout

open QuadraticRecordRefinement PositiveQuadraticPolarization

noncomputable section

/-- Supplied complex serial algebra and raw real weight laws. The raw weight
is not bounded above by one on the whole complex algebra. -/
structure WeightLaws (w : ℂ → ℝ) : Prop where
  continuous : Continuous w
  nonnegative : ∀ z, 0 ≤ w z
  zero : w 0 = 0
  one : w 1 = 1
  multiplicative : ∀ z t, w (z * t) = w z * w t
  conjugation : ∀ z, w (star z) = w z

/-- Echo normalization is required on every normalized pair of complex inputs. -/
def NormalizedEcho (w : ℂ → ℝ) : Prop :=
  ∀ a b, w a + w b = 1 → w (a * star a + b * star b) = 1

namespace WeightLaws

variable {w : ℂ → ℝ} (h : WeightLaws w)

include h

theorem faithful {z : ℂ} (hz : z ≠ 0) : 0 < w z := by
  have hm := h.multiplicative z z⁻¹
  rw [mul_inv_cancel₀ hz, h.one] at hm
  have hn := h.nonnegative z
  by_contra hp
  have he : w z = 0 := le_antisymm (le_of_not_gt hp) hn
  rw [he, zero_mul] at hm
  norm_num at hm

theorem zero_iff (z : ℂ) : w z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    by_contra hn
    have hp := h.faithful hn
    linarith
  · rintro rfl
    exact h.zero

/-- A balanced reference comes from the supplied global continuity. -/
theorem balanced_reference : ∃ c : ℝ, w (c : ℂ) = 1 / 2 := by
  have hc : Continuous (fun x : ℝ => w (x : ℂ)) := h.continuous.comp Complex.continuous_ofReal
  have hm : (1 / 2 : ℝ) ∈ Set.Icc (w (0 : ℂ)) (w (1 : ℂ)) := by
    rw [h.zero, h.one]
    constructor <;> norm_num
  obtain ⟨c, _, he⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 1)
    (by norm_num) hc.continuousOn hm
  exact ⟨c, he⟩

variable (echo : NormalizedEcho w)

include echo

/-- The normalized balanced test fixes the raw weight of the real scalar two. -/
theorem two : w 2 = 4 := by
  obtain ⟨c, hc⟩ := h.balanced_reference
  have he := echo (c : ℂ) (c : ℂ) (by rw [hc]; norm_num)
  have hf : (c : ℂ) * star (c : ℂ) + (c : ℂ) * star (c : ℂ) =
      2 * ((c : ℂ) * star (c : ℂ)) := by ring
  rw [hf, h.multiplicative, h.multiplicative, h.conjugation, hc] at he
  linarith

theorem powers_two (n : ℕ) : w ((2 : ℂ) ^ n) = (4 : ℝ) ^ n := by
  induction n with
  | zero => simpa using h.one
  | succ n ih => simp only [pow_succ, h.multiplicative, ih, h.two echo]

/-- Every positive response level is attained by an actual nonnegative real
scalar inside the supplied complex algebra. -/
theorem positive_real_level {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 ≤ c ∧ w (c : ℂ) = r := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 4)
  have hc : Continuous (fun x : ℝ => w (x : ℂ)) := h.continuous.comp Complex.continuous_ofReal
  have hp : w (((2 : ℝ) ^ n : ℝ) : ℂ) = (4 : ℝ) ^ n := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_ofNat] using h.powers_two echo n
  have hm : r ∈ Set.Icc (w (0 : ℂ)) (w (((2 : ℝ) ^ n : ℝ) : ℂ)) := by
    rw [h.zero, hp]
    exact ⟨hr.le, hn.le⟩
  obtain ⟨c, hci, he⟩ := intermediate_value_Icc
    (a := (0 : ℝ)) (b := (2 : ℝ)^n) (by positivity) hc.continuousOn hm
  exact ⟨c, hci.1, he⟩

/-- Normalized echoes extend to the exact unnormalized raw-weight identity. -/
theorem universal_echo (a b : ℂ) :
    w (a * star a + b * star b) = (w a + w b)^2 := by
  let S := w a + w b
  have hS : 0 ≤ S := add_nonneg (h.nonnegative a) (h.nonnegative b)
  by_cases hz : S = 0
  · have ha : w a = 0 := by dsimp [S] at hz; linarith [h.nonnegative a, h.nonnegative b]
    have hb : w b = 0 := by dsimp [S] at hz; linarith [h.nonnegative a, h.nonnegative b]
    have haz := (h.zero_iff a).mp ha
    have hbz := (h.zero_iff b).mp hb
    simp [haz, hbz, h.zero]
  · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    obtain ⟨c, _, hc⟩ := h.positive_real_level echo (inv_pos.mpr hSp)
    have hnorm : w ((c : ℂ) * a) + w ((c : ℂ) * b) = 1 := by
      rw [h.multiplicative, h.multiplicative, hc, ← mul_add]
      exact inv_mul_cancel₀ hz
    have he := echo ((c : ℂ) * a) ((c : ℂ) * b) hnorm
    have hf : (c : ℂ) * a * star ((c : ℂ) * a) +
        (c : ℂ) * b * star ((c : ℂ) * b) =
        ((c : ℂ) * star (c : ℂ)) * (a * star a + b * star b) := by
      simp only [star_mul]
      ring
    rw [hf, h.multiplicative, h.multiplicative, h.conjugation] at he
    have hunit : w (c : ℂ) * S = 1 := by rw [hc]; exact inv_mul_cancel₀ hz
    have hsquare : (w (c : ℂ))^2 * S^2 = 1 := by rw [← mul_pow, hunit]; norm_num
    have hcn : (w (c : ℂ))^2 ≠ 0 := by rw [hc]; positivity
    apply mul_left_cancel₀ hcn
    calc
      (w (c : ℂ))^2 * w (a * star a + b * star b) = 1 := by simpa [pow_two] using he
      _ = (w (c : ℂ))^2 * (w a + w b)^2 := hsquare.symm

/-- The complex star identity and positivity turn universal echo into the
real parallelogram law. -/
theorem parallelogram (a b : ℂ) :
    w (a + b) + w (a - b) = 2 * w a + 2 * w b := by
  have hs : (a + b) * star (a + b) + (a - b) * star (a - b) =
      2 * (a * star a + b * star b) := by
    simp only [star_add, star_sub]
    ring
  have he := h.universal_echo echo (a + b) (a - b)
  rw [hs, h.multiplicative, h.two echo, h.universal_echo echo] at he
  nlinarith [h.nonnegative a, h.nonnegative b, h.nonnegative (a + b),
    h.nonnegative (a - b)]

theorem positive_quadratic : PositiveQuadratic w :=
  ⟨h.nonnegative, h.parallelogram echo⟩

/-- Existing polarization supplies continuous real homogeneity after the
parallelogram law has been derived. -/
theorem real_homogeneity (r : ℝ) (z : ℂ) : w (r • z) = r^2 * w z := by
  let q := h.positive_quadratic echo
  have hc (v : ℂ) : Continuous (leftAddHom q v) := by
    change Continuous (fun u => (w (u + v) - w u - w v) / 2)
    exact (((h.continuous.comp (continuous_id.add continuous_const)).sub
      h.continuous).sub continuous_const).div_const 2
  have hl (u v : ℂ) : polarization w (r • u) v = r * polarization w u v := by
    exact map_real_smul (leftAddHom q v) (hc v) r u
  calc
    w (r • z) = polarization w (r • z) (r • z) := (diagonal q _).symm
    _ = r * polarization w z (r • z) := hl _ _
    _ = r * polarization w (r • z) z := by rw [symmetric z (r • z)]
    _ = r * (r * polarization w z z) := by rw [hl]
    _ = r^2 * w z := by rw [diagonal q]; ring

theorem phase_one : w Complex.I = 1 := by
  have hm := h.multiplicative Complex.I Complex.I
  have he := (h.positive_quadratic echo).even (1 : ℂ)
  rw [h.one] at he
  rw [Complex.I_mul_I, he] at hm
  nlinarith [h.nonnegative Complex.I]

/-- Classification is conditional on all supplied weight and normalized echo
laws. Ordinary complex coordinates remain premises of this theorem. -/
theorem weight_eq_normSq (z : ℂ) : w z = Complex.normSq z := by
  have hr (r : ℝ) : w (r : ℂ) = r^2 := by
    simpa [Complex.real_smul, h.one] using h.real_homogeneity echo r (1 : ℂ)
  have hi (r : ℝ) : w ((r : ℂ) * Complex.I) = r^2 := by
    rw [h.multiplicative, hr, h.phase_one echo, mul_one]
  have hp := h.parallelogram echo z (star z)
  rw [h.conjugation, Complex.star_def, Complex.add_conj, Complex.sub_conj, hr, hi] at hp
  rw [Complex.normSq_apply]
  nlinarith

/-- Native two-port conservation follows for the supplied coordinate mixer. -/
theorem native_pair_conservation (a b : ℂ) :
    w (OperationalPhaseMixerReconstruction.selectedMixer Complex.I
      OperationalPhaseMixerWitness.half (a, b)).1 +
    w (OperationalPhaseMixerReconstruction.selectedMixer Complex.I
      OperationalPhaseMixerWitness.half (a, b)).2 = w a + w b := by
  simp only [h.weight_eq_normSq echo]
  exact OperationalPhaseMixerWitness.norm_conservation a b

end WeightLaws

end

end IDT.QMClosure.NormalizedEchoReadout
