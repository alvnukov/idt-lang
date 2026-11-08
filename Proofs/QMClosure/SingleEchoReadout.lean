import Proofs.QMClosure.NormalizedEchoReadout
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace IDT.QMClosure.SingleEchoReadout

noncomputable section

/-- One supplied normalized echo with two nonzero complex branches. -/
def NondegenerateEcho (w : ℂ → ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ w a + w b = 1 ∧
    w (a * star a + b * star b) = 1

theorem echo_eq_real (a b : ℂ) :
    a * star a + b * star b =
      ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_add]

variable {w : ℂ → ℝ}

/-- A normalized pair excludes the zero multiplicative map. -/
theorem one_of_normalized_pair
    (hm : ∀ z t, w (z * t) = w z * w t)
    {a b : ℂ} (hab : w a + w b = 1) : w 1 = 1 := by
  have ha := hm a 1
  have hb := hm b 1
  simp only [mul_one] at ha hb
  nlinarith

/-- Multiplication by zero at both branches forces zero response at zero. -/
theorem zero_of_normalized_pair
    (hm : ∀ z t, w (z * t) = w z * w t)
    {a b : ℂ} (hab : w a + w b = 1) : w 0 = 0 := by
  have ha := hm a 0
  have hb := hm b 0
  simp only [mul_zero] at ha hb
  nlinarith

/-- Exponential inputs have positive response using multiplicativity and
unit response alone. No global positivity premise is supplied. -/
theorem exp_weight_pos
    (hm : ∀ z t, w (z * t) = w z * w t)
    (h1 : w 1 = 1) (z : ℂ) : 0 < w (Complex.exp z) := by
  have hunit : w (Complex.exp z) * w (Complex.exp (-z)) = 1 := by
    rw [← hm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, h1]
  have hne : w (Complex.exp z) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hunit
    norm_num at hunit
  have hhalf : z / 2 + z / 2 = z := by ring
  have hnonneg : 0 ≤ w (Complex.exp z) := by
    calc
      0 ≤ w (Complex.exp (z / 2)) * w (Complex.exp (z / 2)) := mul_self_nonneg _
      _ = w (Complex.exp z) := by rw [← hm, ← Complex.exp_add, hhalf]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Continuity only at the multiplicative unit classifies the response on
complex exponentials. The exponential period removes the phase coefficient. -/
theorem exp_weight_character
    (hm : ∀ z t, w (z * t) = w z * w t)
    (h1 : w 1 = 1) (hc : ContinuousAt w 1) :
    ∃ p : ℝ, ∀ z : ℂ, w (Complex.exp z) = Real.exp (p * z.re) := by
  have hp := exp_weight_pos hm h1
  let L : ℂ →+ ℝ := {
    toFun := fun z => Real.log (w (Complex.exp z))
    map_zero' := by simp [h1]
    map_add' := fun z t => by
      rw [Complex.exp_add, hm, Real.log_mul (ne_of_gt (hp z)) (ne_of_gt (hp t))] }
  have hw0 : ContinuousAt (fun z : ℂ => w (Complex.exp z)) 0 := by
    exact hc.comp_of_eq Complex.continuous_exp.continuousAt Complex.exp_zero
  have hL0 : ContinuousAt L 0 := by
    exact ContinuousAt.comp (f := fun z : ℂ => w (Complex.exp z))
      (Real.continuousAt_log (ne_of_gt (hp 0))) hw0
  have hL : Continuous L := continuous_of_continuousAt_zero L hL0
  have hperiod : L ((2 * Real.pi : ℝ) • Complex.I) = 0 := by
    change Real.log (w (Complex.exp ((2 * Real.pi : ℝ) • Complex.I))) = 0
    simp [Complex.real_smul, Complex.ofReal_mul, h1]
  have hscale (r : ℝ) (z : ℂ) : L ((r : ℂ) * z) = r * L z := by
    have h := map_real_smul L hL r z
    change L ((r : ℂ) * z) = r * L z at h
    exact h
  have hphase : L Complex.I = 0 := by
    change L (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 0 at hperiod
    rw [hscale] at hperiod
    exact (mul_eq_zero.mp hperiod).resolve_left (ne_of_gt Real.two_pi_pos)
  have hreal (r : ℝ) : L (r : ℂ) = r * L 1 := by
    simpa only [mul_one] using hscale r (1 : ℂ)
  have himag (r : ℝ) : L ((r : ℂ) * Complex.I) = r * L Complex.I :=
    hscale r Complex.I
  have hform (z : ℂ) : L z = L 1 * z.re := by
    calc
      L z = L ((z.re : ℂ) + z.im * Complex.I) :=
        congrArg L (Complex.re_add_im z).symm
      _ = L (z.re : ℂ) + L ((z.im : ℂ) * Complex.I) := L.map_add _ _
      _ = L 1 * z.re := by rw [hreal, himag, hphase]; ring
  refine ⟨L 1, fun z => ?_⟩
  have hlog := hform z
  change Real.log (w (Complex.exp z)) = L 1 * z.re at hlog
  calc
    w (Complex.exp z) = Real.exp (Real.log (w (Complex.exp z))) :=
      (Real.exp_log (hp z)).symm
    _ = Real.exp (L 1 * z.re) := congrArg Real.exp hlog

/-- The exponential classification extends to every nonzero complex input. -/
theorem radial_weight_character
    (hm : ∀ z t, w (z * t) = w z * w t)
    (h1 : w 1 = 1) (hc : ContinuousAt w 1) :
    ∃ p : ℝ, ∀ z : ℂ, z ≠ 0 →
      w z = Real.exp (p * Real.log ‖z‖) := by
  obtain ⟨p, hp⟩ := exp_weight_character hm h1 hc
  refine ⟨p, fun z hz => ?_⟩
  calc
    w z = w (Complex.exp (Complex.log z)) :=
      congrArg w (Complex.exp_log hz).symm
    _ = Real.exp (p * Real.log ‖z‖) := by rw [hp, Complex.log_re]

theorem quadratic_exp_log_norm {z : ℂ} (hz : z ≠ 0) :
    Real.exp (2 * Real.log ‖z‖) = Complex.normSq z := by
  calc
    Real.exp (2 * Real.log ‖z‖) =
        Real.exp (Real.log ‖z‖ + Real.log ‖z‖) := by congr 1; ring
    _ = ‖z‖ ^ 2 := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hz)]; ring
    _ = Complex.normSq z := Complex.sq_norm z

/-- On supplied complex serial algebra, global multiplicativity, continuity
at one, and one nondegenerate normalized echo select the quadratic weight.
Zero response, unit response, positivity and conjugation invariance are not
additional premises. -/
theorem weight_eq_normSq_of_pair
    (hm : ∀ z t, w (z * t) = w z * w t)
    (hc : ContinuousAt w 1)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : w a + w b = 1)
    (he : w (a * star a + b * star b) = 1) :
    ∀ z : ℂ, w z = Complex.normSq z := by
  have h1 := one_of_normalized_pair hm hab
  have h0 := zero_of_normalized_pair hm hab
  obtain ⟨p, hp⟩ := radial_weight_character hm h1 hc
  have hpa := hp a ha
  have hpb := hp b hb
  have hpne : p ≠ 0 := by
    intro hpzero
    rw [hpzero, zero_mul, Real.exp_zero] at hpa hpb
    linarith
  let S : ℝ := Complex.normSq a + Complex.normSq b
  have hqa : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hqb : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
  have hS : 0 < S := add_pos hqa hqb
  have heS : w (S : ℂ) = 1 := by
    simpa only [echo_eq_real] using he
  have hScast : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hS)
  have hnS : ‖(S : ℂ)‖ = S := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  have hexpS : Real.exp (p * Real.log S) = 1 := by
    have h := hp (S : ℂ) hScast
    rw [hnS, heS] at h
    exact h.symm
  have hlogS : Real.log S = 0 := by
    have hprod : p * Real.log S = 0 := by
      apply Real.exp_injective
      simpa only [Real.exp_zero] using hexpS
    exact (mul_eq_zero.mp hprod).resolve_left hpne
  have hSone : S = 1 := by
    have h := congrArg Real.exp hlogS
    simpa only [Real.exp_log hS, Real.exp_zero] using h
  have hsum : Complex.normSq a + Complex.normSq b = 1 := hSone
  have hna : ‖a‖ < 1 := by
    have hsq := Complex.normSq_eq_norm_sq a
    nlinarith [norm_nonneg a]
  have hnb : ‖b‖ < 1 := by
    have hsq := Complex.normSq_eq_norm_sq b
    nlinarith [norm_nonneg b]
  have hla : Real.log ‖a‖ < 0 := Real.log_neg (norm_pos_iff.mpr ha) hna
  have hlb : Real.log ‖b‖ < 0 := Real.log_neg (norm_pos_iff.mpr hb) hnb
  have hpTwo : p = 2 := by
    rcases lt_trichotomy p 2 with hlt | heq | hgt
    · have hwa : Complex.normSq a < w a := by
        rw [← quadratic_exp_log_norm ha, hpa]
        exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right hlt hla)
      have hwb : Complex.normSq b < w b := by
        rw [← quadratic_exp_log_norm hb, hpb]
        exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right hlt hlb)
      linarith
    · exact heq
    · have hwa : w a < Complex.normSq a := by
        rw [← quadratic_exp_log_norm ha, hpa]
        exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right hgt hla)
      have hwb : w b < Complex.normSq b := by
        rw [← quadratic_exp_log_norm hb, hpb]
        exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_right hgt hlb)
      linarith
  intro z
  by_cases hz : z = 0
  · simpa [hz] using h0
  · rw [hp z hz, hpTwo, quadratic_exp_log_norm hz]

theorem weight_eq_normSq
    (hm : ∀ z t, w (z * t) = w z * w t)
    (hc : ContinuousAt w 1) (he : NondegenerateEcho w) (z : ℂ) :
    w z = Complex.normSq z := by
  obtain ⟨a, b, ha, hb, hab, he⟩ := he
  exact weight_eq_normSq_of_pair hm hc ha hb hab he z

/-- The equal-branch half-response test is a specialization of the single
nondegenerate echo theorem. Its nonzero branch is derived. -/
theorem weight_eq_normSq_of_balanced_echo
    (hm : ∀ z t, w (z * t) = w z * w t)
    (hc : ContinuousAt w 1)
    {c : ℂ} (hhalf : w c = 1 / 2)
    (he : w (c * star c + c * star c) = 1) (z : ℂ) :
    w z = Complex.normSq z := by
  have hcne : c ≠ 0 := by
    intro hz
    subst c
    have h := hm 0 0
    simp only [mul_zero, hhalf] at h
    norm_num at h
  exact weight_eq_normSq_of_pair hm hc hcne hcne (by rw [hhalf]; norm_num) he z

/-- The existing global weight and echo package supplies the weaker theorem's
single witness through its established balanced-reference lemma. -/
theorem weight_eq_normSq_of_normalized_echo
    (h : NormalizedEchoReadout.WeightLaws w)
    (he : NormalizedEchoReadout.NormalizedEcho w) (z : ℂ) :
    w z = Complex.normSq z := by
  obtain ⟨c, hhalf⟩ := h.balanced_reference
  exact weight_eq_normSq_of_balanced_echo h.multiplicative h.continuous.continuousAt
    hhalf (he (c : ℂ) (c : ℂ) (by rw [hhalf]; norm_num)) z

/-- The supplied native mixer conserves raw response under the reduced
single-echo premises. The mixer and complex coordinates remain supplied. -/
theorem native_pair_conservation
    (hm : ∀ z t, w (z * t) = w z * w t)
    (hc : ContinuousAt w 1) (he : NondegenerateEcho w) (a b : ℂ) :
    w (OperationalPhaseMixerReconstruction.selectedMixer Complex.I
      OperationalPhaseMixerWitness.half (a, b)).1 +
    w (OperationalPhaseMixerReconstruction.selectedMixer Complex.I
      OperationalPhaseMixerWitness.half (a, b)).2 = w a + w b := by
  simp only [weight_eq_normSq hm hc he]
  exact OperationalPhaseMixerWitness.norm_conservation a b

end

end IDT.QMClosure.SingleEchoReadout
