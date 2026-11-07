import Proofs.QMClosure.NativeAllocatedSignatureLaw
import Proofs.QMClosure.NativeGaussianDyadicDensity
import Mathlib.Analysis.Complex.Norm

/-!
# Closed-ball observations of exact allocated scalar values

The complex norm and ideal exact Boolean threshold are supplied mathematical
structure. Positive radius is a mathematical
tolerance, without a physical noise model or a detector-precision guarantee.

Every positive-radius ball separates generated scalar values through finite
contexts with exact finite allocated reference programs. The reference may
depend on the inputs, center and radius; there is no uniform source budget,
efficient search guarantee, or claim of physical reference availability.

Known recipes retain all their wires. A common scalar frame and joint physical
availability remain supplied. No unknown-token cloning, joint-input probability
extension, tensor structure, actualization, or QM closure is established.
-/

namespace IDT.QMClosure.NativeAllocatedBallObservation

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedSourceArithmetic NativeAllocatedSignatureLaw
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b mixer_fst)

def ballSignature (q : ℂ) (r : ℝ) (x : G) : Bool := by
  classical
  exact decide (‖x.val - q‖ ≤ r)

/-- Defined for every ambient center and every real radius. -/
def ballData (q : ℂ) (r : ℝ) : Data G Bool :=
  signatureData (ballSignature q r)

@[simp] theorem ballSignature_eq_true_iff (q : ℂ) (r : ℝ) (x : G) :
    ballSignature q r x = true ↔ ‖x.val - q‖ ≤ r := by
  classical
  simp [ballSignature]

theorem ballSignature_negative (q : ℂ) (r : ℝ) (hr : r < 0) (x : G) :
    ballSignature q r x = false := by
  classical
  have h : ¬ ‖x.val - q‖ ≤ r := by
    have hn := norm_nonneg (x.val - q)
    linarith
  simp [ballSignature, h]

theorem ball_responseEq_negative (q : ℂ) (r : ℝ) (hr : r < 0) (x y : G) :
    ResponseEq operationG (ballSignature q r) x y := by
  intro C
  rw [ballSignature_negative q r hr, ballSignature_negative q r hr]

@[simp] theorem ballSignature_zero (q : ℂ) : ballSignature q 0 = pointSignature q := by
  classical
  funext x
  simp [ballSignature, pointSignature, NativeRecipeObservationBoundary.pointTest,
    norm_le_zero_iff, sub_eq_zero]

theorem ball_responseEq_zero (q : ℂ) (x y : G) :
    ResponseEq operationG (ballSignature q 0) x y ↔ ¬ Reachable q ∨ x = y := by
  rw [ballSignature_zero]
  exact pointGenerated_responseEq_classification q x y

/-- A nonzero translation crosses the boundary with a strictly positive margin. -/
theorem exists_strict_translate_separation (δ : ℂ) (hδ : δ ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ t : ℂ, ∃ ε : ℝ, 0 < ε ∧ ‖t‖ + ε < r ∧ r + ε < ‖t + δ‖ := by
  let d : ℝ := ‖δ‖
  have hd : 0 < d := norm_pos_iff.mpr hδ
  let η : ℝ := min r d / 2
  have hη : 0 < η := div_pos (lt_min hr hd) (by norm_num)
  have hηr : 2 * η ≤ r := by
    have h := min_le_left r d
    dsimp [η]
    linarith
  have hηd : 2 * η ≤ d := by
    have h := min_le_right r d
    dsimp [η]
    linarith
  let k : ℝ := (r - η) / d
  have hk : 0 ≤ k := div_nonneg (by linarith) hd.le
  have hkd : k * d = r - η := div_mul_cancel₀ _ hd.ne'
  let t : ℂ := (k : ℂ) * δ
  have ht : ‖t‖ = r - η := by
    change ‖(k : ℂ) * δ‖ = r - η
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
    exact hkd
  have htδ : ‖t + δ‖ = r - η + d := by
    have he : t + δ = ((k + 1 : ℝ) : ℂ) * δ := by
      dsimp [t]
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ k + 1)]
    change (k + 1) * d = r - η + d
    nlinarith [hkd]
  refine ⟨t, η / 2, by positivity, ?_, ?_⟩
  · rw [ht]
    linarith
  · rw [htδ]
    linarith

/-- The separating reference is an actual finite explicitly allocated program. -/
theorem exists_program_strict_ball_separation (q : ℂ) (r : ℝ) (hr : 0 < r)
    (x y : G) (hxy : x ≠ y) :
    ∃ p : ScalarProgram,
      ‖(mixer (x.val, value p)).1 - q‖ < r ∧
      r < ‖(mixer (y.val, value p)).1 - q‖ := by
  let δ : ℂ := a * (y.val - x.val)
  have hδ : δ ≠ 0 := by
    apply mul_ne_zero ResponseSignatureControls.native_a_ne_zero
    intro hv
    apply hxy
    apply Subtype.ext
    exact (sub_eq_zero.mp hv).symm
  obtain ⟨t, ε, hε, ht, htδ⟩ := exists_strict_translate_separation δ hδ r hr
  have hb : b ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [b, Complex.div_re, Complex.div_im] at hh
  let s : ℂ := (q - a * x.val + t) / b
  have hs : b * s = q - a * x.val + t := by
    dsimp [s]
    field_simp [hb]
  let εref : ℝ := ε / (‖b‖ + 1)
  have hden : 0 < ‖b‖ + 1 := by positivity
  have hεref : 0 < εref := div_pos hε hden
  obtain ⟨p, hp⟩ := NativeGaussianDyadicDensity.exists_program_approx s εref hεref
  let e : ℂ := b * (value p - s)
  have he : ‖e‖ < ε := by
    have hbound := mul_le_mul_of_nonneg_left hp.le (norm_nonneg b)
    have heq : εref * (‖b‖ + 1) = ε := div_mul_cancel₀ _ hden.ne'
    dsimp [e]
    rw [norm_mul]
    nlinarith
  have hfirst : (mixer (x.val, value p)).1 - q = t + e := by
    rw [mixer_fst]
    dsimp [e]
    calc
      a * x.val + b * value p - q =
          t + b * (value p - s) + (b * s - (q - a * x.val + t)) := by ring
      _ = t + b * (value p - s) := by rw [hs]; ring
  have hsecond : (mixer (y.val, value p)).1 - q = t + δ + e := by
    rw [mixer_fst]
    dsimp [δ, e]
    calc
      a * y.val + b * value p - q =
          t + a * (y.val - x.val) + b * (value p - s) +
            (b * s - (q - a * x.val + t)) := by ring
      _ = t + a * (y.val - x.val) + b * (value p - s) := by rw [hs]; ring
  refine ⟨p, ?_, ?_⟩
  · rw [hfirst]
    have hn := norm_add_le t e
    linarith
  · rw [hsecond]
    have hn := norm_add_le (t + δ + e) (-e)
    have hcancel : t + δ + e + -e = t + δ := by ring
    rw [hcancel, norm_neg] at hn
    linarith

/-- Positive radius separates even when the ambient center is not reachable. -/
theorem ball_responseEq_iff_eq_of_positive (q : ℂ) (r : ℝ) (hr : 0 < r)
    (x y : G) : ResponseEq operationG (ballSignature q r) x y ↔ x = y := by
  classical
  constructor
  · intro h
    by_contra hxy
    obtain ⟨p, hx, hy⟩ := exists_program_strict_ball_separation q r hr x y hxy
    have ht := h (.left .first .hole (ofProgram p))
    change decide (‖(mixer (x.val, value p)).1 - q‖ ≤ r) =
      decide (‖(mixer (y.val, value p)).1 - q‖ ≤ r) at ht
    have hx' := hx.le
    have hy' : ¬ ‖(mixer (y.val, value p)).1 - q‖ ≤ r := not_le.mpr hy
    simp [hx', hy'] at ht
  · intro h
    subst y
    intro C
    rfl

theorem ball_separates_iff (q : ℂ) (r : ℝ) :
    Separates (ballSignature q r) ↔ 0 < r ∨ (r = 0 ∧ Reachable q) := by
  classical
  have hunit : unitG ≠ zeroG := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv
  constructor
  · intro hsep
    by_cases hr : 0 < r
    · exact Or.inl hr
    · right
      by_cases hz : r = 0
      · refine ⟨hz, ?_⟩
        by_contra hq
        apply hunit
        apply hsep
        rw [hz, ballSignature_zero]
        exact pointGenerated_responseEq_of_not_reachable q hq unitG zeroG
      · have hn : r < 0 := by
          by_contra hn
          exact hz (le_antisymm (le_of_not_gt hr) (le_of_not_gt hn))
        exact False.elim (hunit (hsep _ _ (ball_responseEq_negative q r hn unitG zeroG)))
  · rintro (hr | ⟨rfl, hq⟩)
    · intro x y h
      exact (ball_responseEq_iff_eq_of_positive q r hr x y).mp h
    · intro x y h
      rw [ballSignature_zero] at h
      exact (pointGenerated_responseEq_iff_eq q hq x y).mp h

theorem ball_law_nonempty_iff (q : ℂ) (r : ℝ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (ballData q r) unitG) ↔
      0 < r ∨ (r = 0 ∧ Reachable q) :=
  (law_nonempty_iff_separates (ballSignature q r)).trans (ball_separates_iff q r)

theorem ball_law_nonempty_iff_gaussian_dyadic (q : ℂ) (r : ℝ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (ballData q r) unitG) ↔
      0 < r ∨ (r = 0 ∧ GaussianDyadic q) := by
  rw [ball_law_nonempty_iff, reachable_iff_gaussian_dyadic]

/-- Preserve the entire probability field of every supplied scalar family. -/
def ballLawOfScalar (q : ℂ) (r : ℝ)
    (hadmissible : 0 < r ∨ (r = 0 ∧ Reachable q))
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (ballData q r) unitG :=
  lawOfScalar (ballSignature q r) ((ball_separates_iff q r).mpr hadmissible) L

theorem ballLawOfScalar_probability (q : ℂ) (r : ℝ)
    (hadmissible : 0 < r ∨ (r = 0 ∧ Reachable q))
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Bool (ballData q r) unitG
      (ballLawOfScalar q r hadmissible L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem ball_no_law_negative (q : ℂ) (r : ℝ) (hr : r < 0) :
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law (ballData q r) unitG) := by
  rw [ball_law_nonempty_iff]
  rintro (h | ⟨h, _⟩) <;> linarith

theorem ball_no_law_zero_unreachable (q : ℂ) (hq : ¬ Reachable q) :
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law (ballData q 0) unitG) := by
  rw [ball_law_nonempty_iff]
  simp [hq]

end
end IDT.QMClosure.NativeAllocatedBallObservation
