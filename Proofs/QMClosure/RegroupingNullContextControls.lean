import Proofs.QMClosure.FourthRejoinPositiveCarrierControl
import Proofs.QMClosure.RegroupingGainSelection
import Proofs.QMClosure.DuplicationGainDestructiveControls

/-!
# A continuous readout with surviving null contexts

The carrier is the previously defined positive-second-coordinate subsemiring.
The readout is a squared complex norm with a bounded log-periodic modulation.
It satisfies both supplied regrouping columns. Its additive null-context
obstruction is witnessed by the generated term 1 + (a² + b²).
-/

noncomputable section

namespace IDT.RegroupingNullContextControls

open IDT.FourthRejoinIdempotent
open IDT.FourthRejoinIdempotent.Controls
open ComplexConjugate
open scoped Topology

/-- The concrete bounded modulation has period one in the base-two logarithm. -/
def modulation (q : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * Real.sin (2 * Real.pi * (Real.log q / Real.log 2))

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma modulation_bounds (q : ℝ) : 1 / 2 ≤ modulation q ∧ modulation q ≤ 3 / 2 := by
  unfold modulation
  constructor <;> nlinarith [Real.neg_one_le_sin (2 * Real.pi * (Real.log q / Real.log 2)),
    Real.sin_le_one (2 * Real.pi * (Real.log q / Real.log 2))]

lemma modulation_pos (q : ℝ) : 0 < modulation q := by
  linarith [(modulation_bounds q).1]

@[simp] lemma modulation_one : modulation 1 = 1 := by
  norm_num [modulation]

/-- The totalized logarithm at zero also respects this exact scale identity. -/
lemma modulation_double (q : ℝ) : modulation (2 * q) = modulation q := by
  by_cases hq : q = 0
  · simp [hq]
  have hlog : Real.log (2 * q) / Real.log 2 = Real.log q / Real.log 2 + 1 := by
    rw [Real.log_mul (by norm_num) hq]
    field_simp [ne_of_gt log_two_pos] <;> ring
  have hangle : 2 * Real.pi * (Real.log (2 * q) / Real.log 2) =
      2 * Real.pi * (Real.log q / Real.log 2) + 2 * Real.pi := by
    rw [hlog]
    ring
  unfold modulation
  rw [hangle, Real.sin_add_two_pi]

lemma modulation_half (q : ℝ) : modulation (q / 2) = modulation q := by
  calc
    modulation (q / 2) = modulation (2 * (q / 2)) := (modulation_double _).symm
    _ = modulation q := by congr 1 <;> ring

lemma modulation_continuousAt {q : ℝ} (hq : q ≠ 0) : ContinuousAt modulation q := by
  unfold modulation
  have hlog := Real.continuousAt_log hq
  exact continuousAt_const.add
    (continuousAt_const.mul
      (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.mul (hlog.div_const (Real.log 2)))))

/-- The real output on the previously defined restricted carrier. -/
def readout (p : positiveSecond) : ℝ :=
  Complex.normSq p.val.1 * modulation p.val.2

@[simp] theorem readout_zero : readout 0 = 0 := by simp [readout]

@[simp] theorem readout_one : readout 1 = 1 := by simp [readout]

theorem readout_nonneg (p : positiveSecond) : 0 ≤ readout p :=
  mul_nonneg (Complex.normSq_nonneg _) (le_of_lt (modulation_pos _))

theorem readout_le_normSq (p : positiveSecond) :
    readout p ≤ Complex.normSq p.val.1 * (3 / 2 : ℝ) :=
  mul_le_mul_of_nonneg_left (modulation_bounds _).2 (Complex.normSq_nonneg _)

/-- Strict positivity detects the complex coordinate alone. -/
theorem readout_pos_iff (p : positiveSecond) : 0 < readout p ↔ p.val.1 ≠ 0 := by
  unfold readout
  rw [mul_pos_iff_of_pos_right (modulation_pos _), Complex.normSq_pos]

/-- The bounded modulation gives continuity at the included origin. -/
theorem readout_continuous : Continuous readout := by
  have hnorm : Continuous (fun p : positiveSecond => Complex.normSq p.val.1) := by
    simp only [Complex.normSq_apply]
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    change Filter.Tendsto readout (𝓝 (0 : positiveSecond)) (𝓝 (readout 0))
    rw [readout_zero]
    have hbound : Filter.Tendsto
        (fun x : positiveSecond => Complex.normSq x.val.1 * (3 / 2 : ℝ))
        (𝓝 (0 : positiveSecond)) (𝓝 0) := by
      have hc : ContinuousAt
          (fun x : positiveSecond => Complex.normSq x.val.1 * (3 / 2 : ℝ)) 0 :=
        (hnorm.mul continuous_const).continuousAt
      simpa using hc.tendsto
    exact squeeze_zero readout_nonneg readout_le_normSq hbound
  · have hq := positive_second_of_ne_zero p hp
    have hsnd : ContinuousAt (fun x : positiveSecond => x.val.2) p :=
      continuous_subtype_val.snd.continuousAt
    have hmod : ContinuousAt (fun x : positiveSecond => modulation x.val.2) p :=
      ContinuousAt.comp (f := fun x : positiveSecond => x.val.2)
        (modulation_continuousAt (ne_of_gt hq)) hsnd
    exact hnorm.continuousAt.mul hmod

lemma normSq_complexA : Complex.normSq complexA = (1 / 2 : ℝ) := by
  norm_num [complexA, Complex.normSq_apply]

lemma normSq_complexB : Complex.normSq complexB = (1 / 2 : ℝ) := by
  norm_num [complexB, Complex.normSq_apply]

theorem readout_halfA (p : positiveSecond) : readout (positiveA * p) = readout p / 2 := by
  change Complex.normSq (complexA * p.val.1) * modulation ((1 / 2 : ℝ) * p.val.2) =
    (Complex.normSq p.val.1 * modulation p.val.2) / 2
  rw [Complex.normSq_mul, normSq_complexA]
  rw [show (1 / 2 : ℝ) * p.val.2 = p.val.2 / 2 by ring, modulation_half]
  ring

theorem readout_halfB (p : positiveSecond) : readout (positiveB * p) = readout p / 2 := by
  change Complex.normSq (complexB * p.val.1) * modulation ((1 / 2 : ℝ) * p.val.2) =
    (Complex.normSq p.val.1 * modulation p.val.2) / 2
  rw [Complex.normSq_mul, normSq_complexB]
  rw [show (1 / 2 : ℝ) * p.val.2 = p.val.2 / 2 by ring, modulation_half]
  ring

theorem readout_column (p : positiveSecond) :
    readout (positiveA * p) + readout (positiveB * p) = readout p := by
  rw [readout_halfA, readout_halfB]
  ring

theorem readout_duplication (p : positiveSecond) :
    readout ((2 : positiveSecond) * p) = 4 * readout p := by
  change Complex.normSq ((2 : ℂ) * p.val.1) * modulation ((2 : ℝ) * p.val.2) =
    4 * (Complex.normSq p.val.1 * modulation p.val.2)
  rw [Complex.normSq_mul, modulation_double]
  norm_num <;> ring

@[simp] theorem readout_two : readout (2 : positiveSecond) = 4 := by
  simpa using readout_duplication 1

/-- The destructive coefficient survives in the semiring and remains readout-null. -/
theorem readout_defect_context (p : positiveSecond) :
    readout ((positiveA ^ 2 + positiveB ^ 2) * p) = 0 := by
  change Complex.normSq ((defect positiveA positiveB).val.1 * p.val.1) *
    modulation ((defect positiveA positiveB).val.2 * p.val.2) = 0
  rw [positive_defect_value]
  simp

/-- The complementary regrouping coefficient has unit complex coordinate. -/
theorem transparency_value :
    (((2 : positiveSecond) * (positiveA * positiveB)).val) = (1, (1 / 2 : ℝ)) := by
  apply Prod.ext
  · change (2 : ℂ) * (complexA * complexB) = 1
    apply Complex.ext <;>
      norm_num [complexA, complexB, Complex.mul_re, Complex.mul_im]
  · change (2 : ℝ) * ((1 / 2) * (1 / 2)) = 1 / 2
    norm_num

theorem readout_transparency (p : positiveSecond) :
    readout (((2 : positiveSecond) * (positiveA * positiveB)) * p) = readout p := by
  change Complex.normSq ((((2 : positiveSecond) * (positiveA * positiveB)).val).1 * p.val.1) *
    modulation ((((2 : positiveSecond) * (positiveA * positiveB)).val).2 * p.val.2) =
      Complex.normSq p.val.1 * modulation p.val.2
  rw [transparency_value]
  simp only [one_mul]
  rw [show (1 / 2 : ℝ) * p.val.2 = p.val.2 / 2 by ring, modulation_half]

theorem readout_regrouping_column (p : positiveSecond) :
    readout ((positiveA ^ 2 + positiveB ^ 2) * p) +
      readout (((2 : positiveSecond) * (positiveA * positiveB)) * p) = readout p := by
  rw [readout_defect_context, readout_transparency, zero_add]

/-- The model instantiates every supplied field of the two-column contract. -/
theorem regrouping_contract :
    IDT.RegroupingGainSelection.Contract positiveA positiveB readout 4 := by
  refine ⟨positive_contract.sum, positive_contract.fourthRejoin, readout_one,
    readout_column, readout_duplication, ?_, readout_regrouping_column⟩
  norm_num

theorem defect_ne_zero : positiveA ^ 2 + positiveB ^ 2 ≠ 0 :=
  positive_defect_ne_zero

theorem transparency_ne_one : (2 : positiveSecond) * (positiveA * positiveB) ≠ 1 := by
  intro h
  have hq := congrArg (fun x : positiveSecond => x.val.2) h
  change (((2 : positiveSecond) * (positiveA * positiveB)).val).2 = 1 at hq
  rw [transparency_value] at hq
  norm_num at hq

/-- Conjugation changes only the complex coordinate. -/
def conjugate (p : positiveSecond) : positiveSecond :=
  ⟨(conj p.val.1, p.val.2), by
    rcases p.property with hz | hp
    · exact Or.inl (by
        have h := congrArg (fun x : ℂ × ℝ => (conj x.1, x.2)) hz
        simpa using h)
    · exact Or.inr hp⟩

theorem readout_conjugate (p : positiveSecond) : readout (conjugate p) = readout p := by
  change Complex.normSq (conj p.val.1) * modulation p.val.2 =
    Complex.normSq p.val.1 * modulation p.val.2
  rw [Complex.normSq_conj]

@[simp] theorem readout_sector : readout (sector positiveA positiveB) = 0 := by
  unfold readout
  rw [positive_sector_value]
  simp

theorem zero_detection_fails : ¬ (∀ p : positiveSecond, readout p = 0 → p = 0) := by
  intro h
  exact positive_nontrivial_idempotent.2.1 (h _ readout_sector)

lemma modulation_three_halves_lt_one : modulation (3 / 2 : ℝ) < 1 := by
  have hlower : Real.log 2 < 2 * Real.log (3 / 2 : ℝ) := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) < (3 / 2 : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hupper : Real.log (3 / 2 : ℝ) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hratio_lower : (1 / 2 : ℝ) < Real.log (3 / 2 : ℝ) / Real.log 2 := by
    apply (lt_div_iff₀ log_two_pos).2
    linarith
  have hratio_upper : Real.log (3 / 2 : ℝ) / Real.log 2 < 1 := by
    apply (div_lt_iff₀ log_two_pos).2
    linarith
  have hangle_lower : Real.pi < 2 * Real.pi * (Real.log (3 / 2 : ℝ) / Real.log 2) := by
    have h := mul_lt_mul_of_pos_left hratio_lower Real.pi_pos
    nlinarith
  have hangle_upper : 2 * Real.pi * (Real.log (3 / 2 : ℝ) / Real.log 2) < 2 * Real.pi := by
    have h := mul_lt_mul_of_pos_left hratio_upper Real.pi_pos
    nlinarith
  have hsine : Real.sin (2 * Real.pi * (Real.log (3 / 2 : ℝ) / Real.log 2)) < 0 := by
    have h := Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith :
        2 * Real.pi * (Real.log (3 / 2 : ℝ) / Real.log 2) - 2 * Real.pi < 0)
      (by linarith :
        -Real.pi < 2 * Real.pi * (Real.log (3 / 2 : ℝ) / Real.log 2) - 2 * Real.pi)
    simpa only [Real.sin_sub_two_pi] using h
  unfold modulation
  linarith

/-- A generated additive context distinguishes the readout-null defect from zero. -/
theorem readout_one_add_defect_lt_one :
    readout (1 + (positiveA ^ 2 + positiveB ^ 2)) < 1 := by
  have hvalue : readout (1 + (positiveA ^ 2 + positiveB ^ 2)) =
      modulation (3 / 2 : ℝ) := by
    change Complex.normSq (1 + (defect positiveA positiveB).val.1) *
      modulation (1 + (defect positiveA positiveB).val.2) = modulation (3 / 2 : ℝ)
    rw [positive_defect_value]
    norm_num
  rw [hvalue]
  exact modulation_three_halves_lt_one

/-- Killing the canonical sector forces any semiring image of its defect to vanish. -/
theorem image_defect_eq_zero {R : Type*} [Semiring R]
    (f : positiveSecond →+* R) (hsector : f (sector positiveA positiveB) = 0) :
    f (positiveA ^ 2 + positiveB ^ 2) = 0 := by
  change f (defect positiveA positiveB) = 0
  calc
    f (defect positiveA positiveB) =
        f (sector positiveA positiveB * defect positiveA positiveB) :=
      congrArg f (sector_mul_defect positive_contract).symm
    _ = f (sector positiveA positiveB) * f (defect positiveA positiveB) := map_mul f _ _
    _ = 0 := by rw [hsector, zero_mul]

/-- The readout cannot factor through any semiring map killing the canonical sector. -/
theorem no_factorization_killing_sector {R : Type*} [Semiring R]
    (f : positiveSecond →+* R) (hsector : f (sector positiveA positiveB) = 0)
    (V : R → ℝ) : ¬ (∀ p, readout p = V (f p)) := by
  intro hfactor
  have hT := image_defect_eq_zero f hsector
  have hsame : f (1 + (positiveA ^ 2 + positiveB ^ 2)) = f 1 := by
    rw [map_add, hT, add_zero]
  have hequal : readout (1 + (positiveA ^ 2 + positiveB ^ 2)) = 1 := by
    calc
      readout (1 + (positiveA ^ 2 + positiveB ^ 2)) =
          V (f (1 + (positiveA ^ 2 + positiveB ^ 2))) := hfactor _
      _ = V (f 1) := congrArg V hsame
      _ = readout 1 := (hfactor _).symm
      _ = 1 := readout_one
  exact (ne_of_lt readout_one_add_defect_lt_one) hequal


/-! ## A multiplicative gain-eight control omitting the second column -/

/-- Total real division assigns zero at the included carrier origin. -/
def gainEightReadout (p : positiveSecond) : ℝ := Complex.normSq p.val.1 ^ 2 / p.val.2

@[simp] theorem gainEightReadout_zero : gainEightReadout 0 = 0 := by
  simp [gainEightReadout]

@[simp] theorem gainEightReadout_one : gainEightReadout 1 = 1 := by
  simp [gainEightReadout]

lemma second_nonneg (p : positiveSecond) : 0 ≤ p.val.2 := by
  rcases p.property with hz | hp
  · have hq := congrArg Prod.snd hz
    change p.val.2 = 0 at hq
    simpa only [hq] using (le_refl (0 : ℝ))
  · exact le_of_lt hp

theorem gainEightReadout_nonneg (p : positiveSecond) : 0 ≤ gainEightReadout p :=
  div_nonneg (sq_nonneg _) (second_nonneg p)

/-- Multiplicativity holds on the entire restricted semiring, including zero. -/
theorem gainEightReadout_mul (p q : positiveSecond) :
    gainEightReadout (p * q) = gainEightReadout p * gainEightReadout q := by
  change Complex.normSq (p.val.1 * q.val.1) ^ 2 / (p.val.2 * q.val.2) =
    (Complex.normSq p.val.1 ^ 2 / p.val.2) * (Complex.normSq q.val.1 ^ 2 / q.val.2)
  rw [Complex.normSq_mul, mul_pow, div_mul_div_comm]

theorem gainEightReadout_halfA (p : positiveSecond) :
    gainEightReadout (positiveA * p) = gainEightReadout p / 2 := by
  by_cases hp : p = 0
  · subst p
    simp
  have hq := ne_of_gt (positive_second_of_ne_zero p hp)
  change Complex.normSq (complexA * p.val.1) ^ 2 / ((1 / 2 : ℝ) * p.val.2) =
    (Complex.normSq p.val.1 ^ 2 / p.val.2) / 2
  rw [Complex.normSq_mul, normSq_complexA]
  field_simp [hq] <;> ring

theorem gainEightReadout_halfB (p : positiveSecond) :
    gainEightReadout (positiveB * p) = gainEightReadout p / 2 := by
  by_cases hp : p = 0
  · subst p
    simp
  have hq := ne_of_gt (positive_second_of_ne_zero p hp)
  change Complex.normSq (complexB * p.val.1) ^ 2 / ((1 / 2 : ℝ) * p.val.2) =
    (Complex.normSq p.val.1 ^ 2 / p.val.2) / 2
  rw [Complex.normSq_mul, normSq_complexB]
  field_simp [hq] <;> ring

theorem gainEightReadout_column (p : positiveSecond) :
    gainEightReadout (positiveA * p) + gainEightReadout (positiveB * p) = gainEightReadout p := by
  rw [gainEightReadout_halfA, gainEightReadout_halfB]
  ring

theorem gainEightReadout_duplication (p : positiveSecond) :
    gainEightReadout ((2 : positiveSecond) * p) = 8 * gainEightReadout p := by
  by_cases hp : p = 0
  · subst p
    simp
  have hq := ne_of_gt (positive_second_of_ne_zero p hp)
  change Complex.normSq ((2 : ℂ) * p.val.1) ^ 2 / ((2 : ℝ) * p.val.2) =
    8 * (Complex.normSq p.val.1 ^ 2 / p.val.2)
  rw [Complex.normSq_mul]
  norm_num only [Complex.normSq_ofNat]
  field_simp [hq] <;> ring

@[simp] theorem gainEightReadout_two : gainEightReadout (2 : positiveSecond) = 8 := by
  simpa using gainEightReadout_duplication 1

theorem gainEightReadout_contrast : gainEightReadout (2 : positiveSecond) ≠ 2 := by
  norm_num

theorem gainEightReadout_defect_context (p : positiveSecond) :
    gainEightReadout ((positiveA ^ 2 + positiveB ^ 2) * p) = 0 := by
  change Complex.normSq ((defect positiveA positiveB).val.1 * p.val.1) ^ 2 /
    ((defect positiveA positiveB).val.2 * p.val.2) = 0
  rw [positive_defect_value]
  simp

/-- At the unit preparation the omitted regrouping coefficient has output two. -/
@[simp] theorem gainEightReadout_transparency_value :
    gainEightReadout ((2 : positiveSecond) * (positiveA * positiveB)) = 2 := by
  unfold gainEightReadout
  rw [transparency_value]
  norm_num

/-- The second regrouping column fails despite the other exact readout laws. -/
theorem gainEightReadout_regrouping_fails :
    ¬ (∀ p, gainEightReadout ((positiveA ^ 2 + positiveB ^ 2) * p) +
      gainEightReadout (((2 : positiveSecond) * (positiveA * positiveB)) * p) =
        gainEightReadout p) := by
  intro h
  have hnull : gainEightReadout (positiveA ^ 2 + positiveB ^ 2) = 0 := by
    simpa only [mul_one] using gainEightReadout_defect_context 1
  have hone := h 1
  norm_num [hnull] at hone


/-! ## The existing mixed-weight control satisfies both regrouping columns -/

namespace MixedGainOmission

open IDT.DuplicationGainDestructive.Controls

/-- The second regrouping coefficient in the product control. -/
theorem product_transparency_value :
    (2 : ℂ × ℝ) * (productA * productB) = (1, (1 / 2 : ℝ)) := by
  apply Prod.ext
  · change (2 : ℂ) * (qa * qb) = 1
    apply Complex.ext <;> norm_num [qa, qb, Complex.mul_re, Complex.mul_im]
  · change (2 : ℝ) * ((1 / 2) * (1 / 2)) = 1 / 2
    norm_num

/-- The defect retains the real half of the mixed readout in every right context. -/
theorem mixed_defect_context (θ : ℝ) (p : ℂ × ℝ) :
    mixedWeight θ (productT * p) = (1 - θ) * |p.2| / 2 := by
  norm_num [mixedWeight, productT_value, Prod.fst_mul, Prod.snd_mul, abs_mul] <;> ring

/-- The other regrouping coefficient retains the complex part and the real half. -/
theorem mixed_transparency_context (θ : ℝ) (p : ℂ × ℝ) :
    mixedWeight θ (((2 : ℂ × ℝ) * (productA * productB)) * p) =
      θ * Complex.normSq p.1 + (1 - θ) * |p.2| / 2 := by
  rw [product_transparency_value]
  norm_num [mixedWeight, Prod.fst_mul, Prod.snd_mul, abs_mul] <;> ring

/-- Both regrouping contributions conserve the same mixed weight for every real parameter. -/
theorem mixed_regrouping_column (θ : ℝ) (p : ℂ × ℝ) :
    mixedWeight θ (productT * p) +
      mixedWeight θ (((2 : ℂ × ℝ) * (productA * productB)) * p) = mixedWeight θ p := by
  rw [mixed_defect_context, mixed_transparency_context]
  unfold mixedWeight
  ring

/-- The faithful mixed-weight control also supplies the second column. -/
theorem mixed_two_column_omission_control {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Commute productA productB ∧ productA + productB = 1 ∧
    productA ^ 4 = productB ^ 4 ∧ mixedWeight θ 1 = 1 ∧
    (∀ p, 0 ≤ mixedWeight θ p) ∧
    (∀ p, mixedWeight θ p = 0 → p = 0) ∧
    (∀ p, mixedWeight θ (productA * p) + mixedWeight θ (productB * p) = mixedWeight θ p) ∧
    (∀ p, mixedWeight θ (productT * p) +
      mixedWeight θ (((2 : ℂ × ℝ) * (productA * productB)) * p) = mixedWeight θ p) ∧
    mixedWeight θ (2 : ℂ × ℝ) ≠ 2 ∧ productT ≠ 0 ∧
    (¬ ∃ k : ℝ, ∀ p, mixedWeight θ ((2 : ℂ × ℝ) * p) = k * mixedWeight θ p) := by
  obtain ⟨hcomm, hsum, hfour, hunit, hnonneg, hzero, hcolumn, hcontrast, hT, hgain⟩ :=
    mixed_omission_control hθ hθ1
  exact ⟨hcomm, hsum, hfour, hunit, hnonneg, hzero, hcolumn,
    mixed_regrouping_column θ, hcontrast, hT, hgain⟩

end MixedGainOmission

end IDT.RegroupingNullContextControls
