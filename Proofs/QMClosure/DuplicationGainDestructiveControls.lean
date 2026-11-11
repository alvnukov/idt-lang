import Proofs.QMClosure.DuplicationGainDestructiveCore

/-!
# Three omitted-hypothesis controls

These elementary mathematical carriers are controls for the supplied contracts. They establish no physical realization.
-/

noncomputable section

namespace IDT.DuplicationGainDestructive.Controls

/-- Omitting the finite unit-duplication contrast admits a real absolute value. -/
def realWeight (x : ℝ) : ℝ := |x|

theorem real_omission_control :
    Commute (1 / 2 : ℝ) (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) + 1 / 2 = 1 ∧
    (1 / 2 : ℝ) ^ 4 = (1 / 2 : ℝ) ^ 4 ∧
    realWeight 1 = 1 ∧
    (∀ x, 0 ≤ realWeight x) ∧
    (∀ x, realWeight x = 0 → x = 0) ∧
    (∀ x, realWeight ((1 / 2 : ℝ) * x) + realWeight ((1 / 2 : ℝ) * x) = realWeight x) ∧
    (∀ x, realWeight ((2 : ℝ) * x) = 2 * realWeight x) ∧
    realWeight (2 : ℝ) = 2 ∧
    (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2 = 1 / 2 ∧
    (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2 ≠ 0 := by
  refine ⟨Commute.refl _, by norm_num, rfl, by norm_num [realWeight],
    ?_, ?_, ?_, ?_, by norm_num [realWeight], by norm_num, by norm_num⟩
  · intro x; exact abs_nonneg x
  · intro x hx; exact abs_eq_zero.mp hx
  · intro x
    norm_num [realWeight, abs_mul] <;> ring
  · intro x; norm_num [realWeight, abs_mul]

def qa : ℂ := ⟨1 / 2, 1 / 2⟩
def qb : ℂ := ⟨1 / 2, -(1 / 2)⟩
def productA : ℂ × ℝ := (qa, 1 / 2)
def productB : ℂ × ℝ := (qb, 1 / 2)
def productT : ℂ × ℝ := productA ^ 2 + productB ^ 2

theorem qa_normSq : Complex.normSq qa = 1 / 2 := by
  norm_num [qa, Complex.normSq_apply]

theorem qb_normSq : Complex.normSq qb = 1 / 2 := by
  norm_num [qb, Complex.normSq_apply]

theorem qa_add_qb : qa + qb = 1 := by
  apply Complex.ext <;> norm_num [qa, qb]

theorem qa_fourth_qb : qa ^ 4 = qb ^ 4 := by
  apply Complex.ext <;>
    norm_num [qa, qb, pow_succ, Complex.mul_re, Complex.mul_im]

/-- A standard complex carrier inhabits the full supplied contract. -/
theorem standard_complex_contract : Contract qa qb Complex.normSq 4 where
  commute := Commute.all _ _
  sum := qa_add_qb
  fourthRejoin := qa_fourth_qb
  unit := by norm_num
  zeroDetection := fun _ hz => Complex.normSq_eq_zero.mp hz
  column := by
    intro z
    rw [Complex.normSq_mul, Complex.normSq_mul, qa_normSq, qb_normSq]
    ring
  duplicationGain := by
    intro z
    norm_num [Complex.normSq_mul]
  unitDuplicationContrast := by norm_num

theorem standard_complex_nonneg (z : ℂ) : 0 ≤ Complex.normSq z :=
  Complex.normSq_nonneg z

theorem standard_complex_generators_distinct : qa ≠ qb := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [qa, qb] at hi

theorem standard_complex_generator_nonzero : qa ≠ 0 := by
  intro h
  have hn := congrArg Complex.normSq h
  rw [qa_normSq] at hn
  norm_num at hn

/-- Nonvacuity also instantiates the entire abstract conclusion record. -/
theorem standard_complex_conclusion : Conclusion qa qb Complex.normSq 4 :=
  derive standard_complex_contract

theorem standard_complex_transparency : (2 : ℂ) * (qa * qb) = 1 :=
  standard_complex_conclusion.transparency

theorem product_sum : productA + productB = 1 := by
  apply Prod.ext
  · exact qa_add_qb
  · norm_num [productA, productB]

theorem product_fourth : productA ^ 4 = productB ^ 4 := by
  apply Prod.ext
  · exact qa_fourth_qb
  · rfl

theorem productT_value : productT = (0, 1 / 2) := by
  apply Prod.ext
  · apply Complex.ext <;>
      norm_num [productT, productA, productB, qa, qb, pow_two,
        Complex.mul_re, Complex.mul_im]
  · norm_num [productT, productA, productB, pow_two]

theorem productT_ne_zero : productT ≠ 0 := by
  intro h
  have hs := congrArg Prod.snd h
  norm_num [productT_value] at hs

/-- Omitting zero detection retains a real ghost coordinate. -/
def blindWeight (p : ℂ × ℝ) : ℝ := Complex.normSq p.1

theorem blind_unit : blindWeight 1 = 1 := by simp [blindWeight]

theorem blind_nonneg (p : ℂ × ℝ) : 0 ≤ blindWeight p :=
  Complex.normSq_nonneg _

theorem blind_column (p : ℂ × ℝ) :
    blindWeight (productA * p) + blindWeight (productB * p) = blindWeight p := by
  simp only [blindWeight, productA, productB, Prod.fst_mul, Complex.normSq_mul]
  rw [qa_normSq, qb_normSq]
  ring

theorem blind_gain (p : ℂ × ℝ) : blindWeight ((2 : ℂ × ℝ) * p) = 4 * blindWeight p := by
  norm_num [blindWeight, Complex.normSq_mul]

theorem blind_contrast : blindWeight (2 : ℂ × ℝ) ≠ 2 := by
  norm_num [blindWeight]

theorem blind_zero_at_nonzero : blindWeight productT = 0 ∧ productT ≠ 0 := by
  constructor
  · simp [productT_value, blindWeight]
  · exact productT_ne_zero

theorem blind_not_zeroDetection :
    ¬ (∀ p : ℂ × ℝ, blindWeight p = 0 → p = 0) := by
  intro hz
  exact productT_ne_zero (hz productT blind_zero_at_nonzero.1)

theorem blind_omission_control :
    Commute productA productB ∧ productA + productB = 1 ∧
    productA ^ 4 = productB ^ 4 ∧ blindWeight 1 = 1 ∧
    (∀ p, 0 ≤ blindWeight p) ∧
    (∀ p, blindWeight (productA * p) + blindWeight (productB * p) = blindWeight p) ∧
    (∀ p, blindWeight ((2 : ℂ × ℝ) * p) = 4 * blindWeight p) ∧
    blindWeight (2 : ℂ × ℝ) ≠ 2 ∧
    blindWeight productT = 0 ∧ productT ≠ 0 ∧
    (¬ (∀ p, blindWeight p = 0 → p = 0)) := by
  exact ⟨Commute.all _ _, product_sum, product_fourth, blind_unit,
    blind_nonneg, blind_column, blind_gain, blind_contrast,
    blind_zero_at_nonzero.1, productT_ne_zero, blind_not_zeroDetection⟩

/-- Mixing the squared complex weight with an absolute real weight preserves
positive faithful columns but prevents one universal duplication gain. -/
def mixedWeight (c : ℝ) (p : ℂ × ℝ) : ℝ :=
  c * Complex.normSq p.1 + (1 - c) * |p.2|

theorem mixed_unit (c : ℝ) : mixedWeight c 1 = 1 := by
  norm_num [mixedWeight] <;> ring

theorem mixed_nonneg {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (p : ℂ × ℝ) :
    0 ≤ mixedWeight c p := by
  dsimp [mixedWeight]
  exact add_nonneg
    (mul_nonneg hc.le (Complex.normSq_nonneg _))
    (mul_nonneg (by linarith) (abs_nonneg _))

theorem mixed_zeroDetection {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (p : ℂ × ℝ) (hz : mixedWeight c p = 0) : p = 0 := by
  have hn := Complex.normSq_nonneg p.1
  have ha := abs_nonneg p.2
  have hcn : 0 ≤ c * Complex.normSq p.1 := mul_nonneg hc.le hn
  have hca : 0 ≤ (1 - c) * |p.2| := mul_nonneg (by linarith) ha
  dsimp [mixedWeight] at hz
  have hnzero : Complex.normSq p.1 = 0 := by nlinarith
  have hazero : |p.2| = 0 := by nlinarith
  apply Prod.ext
  · exact Complex.normSq_eq_zero.mp hnzero
  · exact abs_eq_zero.mp hazero

theorem mixed_column (c : ℝ) (p : ℂ × ℝ) :
    mixedWeight c (productA * p) + mixedWeight c (productB * p) = mixedWeight c p := by
  simp only [mixedWeight, productA, productB, Prod.fst_mul, Prod.snd_mul,
    Complex.normSq_mul, abs_mul]
  rw [qa_normSq, qb_normSq]
  norm_num <;> ring

theorem mixed_two (c : ℝ) : mixedWeight c (2 : ℂ × ℝ) = 2 + 2 * c := by
  norm_num [mixedWeight] <;> ring

theorem mixed_contrast {c : ℝ} (hc : 0 < c) : mixedWeight c (2 : ℂ × ℝ) ≠ 2 := by
  rw [mixed_two]
  linarith

theorem mixed_T (c : ℝ) : mixedWeight c productT = (1 - c) / 2 := by
  norm_num [mixedWeight, productT_value] <;> ring

theorem mixed_double_T (c : ℝ) : mixedWeight c ((2 : ℂ × ℝ) * productT) = 1 - c := by
  norm_num [mixedWeight, productT_value]

theorem mixed_no_fixed_gain {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ¬ ∃ k : ℝ, ∀ p : ℂ × ℝ, mixedWeight c ((2 : ℂ × ℝ) * p) = k * mixedWeight c p := by
  rintro ⟨k, hg⟩
  have hunit := hg 1
  simp only [mul_one, mixed_unit, mul_one] at hunit
  rw [mixed_two] at hunit
  have hT := hg productT
  rw [mixed_double_T, mixed_T] at hT
  have hk2 : k = 2 := by
    have hproduct : (k - 2) * (1 - c) = 0 := by nlinarith [hT]
    rcases mul_eq_zero.mp hproduct with h | h
    · linarith
    · linarith
  linarith

/-- The mixed control fulfills all selected premises except the fixed gain. -/
theorem mixed_omission_control {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Commute productA productB ∧ productA + productB = 1 ∧
    productA ^ 4 = productB ^ 4 ∧ mixedWeight c 1 = 1 ∧
    (∀ p, 0 ≤ mixedWeight c p) ∧
    (∀ p, mixedWeight c p = 0 → p = 0) ∧
    (∀ p, mixedWeight c (productA * p) + mixedWeight c (productB * p) = mixedWeight c p) ∧
    mixedWeight c (2 : ℂ × ℝ) ≠ 2 ∧ productT ≠ 0 ∧
    (¬ ∃ k : ℝ, ∀ p, mixedWeight c ((2 : ℂ × ℝ) * p) = k * mixedWeight c p) := by
  exact ⟨Commute.all _ _, product_sum, product_fourth, mixed_unit c,
    mixed_nonneg hc hc1, mixed_zeroDetection hc hc1, mixed_column c,
    mixed_contrast hc, productT_ne_zero, mixed_no_fixed_gain hc hc1⟩

end IDT.DuplicationGainDestructive.Controls
