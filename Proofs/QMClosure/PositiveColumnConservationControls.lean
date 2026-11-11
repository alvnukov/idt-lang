import Proofs.QMClosure.PositiveColumnConservation

/-!
Separate controls for positive single-column conservation.
The concrete faithful complex evaluation supplies these controls. The principal
theorem in PositiveColumnConservationCore has no complex-evaluation dependency.
The conditional statements in this module are checked by Lean.
-/

noncomputable section

namespace IDT.QMClosure.PositiveColumnConservationControls

open NativeInitialHistoryPresentation NativeGeneratorMixtureReadout

attribute [local instance] presentationCommRing presentationCharZero

private theorem norm_a : Complex.normSq ComplexModel.a = (1 : ℝ) / 2 := by
  norm_num [ComplexModel.a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem norm_b : Complex.normSq ComplexModel.b = (1 : ℝ) / 2 := by
  norm_num [ComplexModel.b, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem complex_column (z : ℂ) :
    Complex.normSq (ComplexModel.a * z) + Complex.normSq (ComplexModel.b * z) =
      Complex.normSq z ∧
    (ComplexModel.a * z).re + (ComplexModel.b * z).re = z.re ∧
    (ComplexModel.a * z).im + (ComplexModel.b * z).im = z.im := by
  have h : ComplexModel.a * z + ComplexModel.b * z = z := by
    rw [← add_mul, ComplexModel.transparent, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.normSq_mul, Complex.normSq_mul, norm_a, norm_b]
    ring
  · simpa only [Complex.add_re] using congrArg Complex.re h
  · simpa only [Complex.add_im] using congrArg Complex.im h

/-- An additive real-valued readout that conserves every native column. -/
def realPart (p : Presentation) : ℝ := (complexEval p).re

theorem realPart_unit : realPart 1 = 1 := by simp [realPart]

theorem realPart_column (p : Presentation) :
    realPart (a * p) + realPart (b * p) = realPart p := by
  simpa only [realPart, map_mul, complexEval_a, complexEval_b] using
    (complex_column (complexEval p)).2.1

/-- Positivity on the original nonnegative additive generator cone is weaker
than positivity on its serial descendants. -/
theorem realPart_nonnegative_bag (m n : ℕ) :
    0 ≤ realPart ((m : Presentation) * a + (n : Presentation) * b) := by
  have heq : realPart ((m : Presentation) * a + (n : Presentation) * b) =
      (m : ℝ) / 2 + (n : ℝ) / 2 := by
    norm_num [realPart, map_add, map_mul, ComplexModel.a, ComplexModel.b,
      Complex.mul_re, Complex.div_re, Complex.div_im]
    <;> ring
  rw [heq]
  positivity

/-- Every mixed increment of this additive control vanishes. -/
theorem realPart_mixed_increment (p x y : Presentation) :
    realPart (p + x + y) - realPart (p + x) - realPart (p + y) + realPart p = 0 := by
  simp only [realPart, map_add, Complex.add_re]
  ring

theorem realPart_phase_branch_failure :
    realPart phase = 0 ∧ realPart (a * phase) = -(1 : ℝ) / 2 ∧
      realPart (b * phase) = (1 : ℝ) / 2 := by
  norm_num [realPart, map_mul, ComplexModel.a, ComplexModel.b, Complex.mul_re,
    Complex.div_re, Complex.div_im]

/-- Positive unit calibration alone permits a quartic norm control. -/
def quartic (p : Presentation) : ℝ := Complex.normSq (complexEval p) ^ 2

theorem quartic_nonnegative (p : Presentation) : 0 ≤ quartic p := sq_nonneg _

theorem quartic_unit : quartic 1 = 1 := by simp [quartic]

theorem quartic_column_half (p : Presentation) :
    quartic (a * p) + quartic (b * p) = quartic p / 2 := by
  simp only [quartic, map_mul, complexEval_a, complexEval_b, Complex.normSq_mul,
    norm_a, norm_b]
  ring

theorem quartic_rejects_column :
    quartic (a * 1) + quartic (b * 1) ≠ quartic 1 := by
  rw [quartic_column_half, quartic_unit]
  norm_num

/-- Nonnegative rescalings exhibit the separate role of unit calibration. -/
def scaledNorm (c : ℝ) (p : Presentation) : ℝ := c * Complex.normSq (complexEval p)

theorem scaledNorm_properties (c : ℝ) (hc : 0 ≤ c) :
    (∀ p, 0 ≤ scaledNorm c p) ∧ scaledNorm c 1 = c ∧
    (∀ p, scaledNorm c (a * p) + scaledNorm c (b * p) = scaledNorm c p) := by
  refine ⟨fun p => mul_nonneg hc (Complex.normSq_nonneg _), ?_, ?_⟩
  · simp [scaledNorm]
  · intro p
    have h := (complex_column (complexEval p)).1
    simp only [Complex.normSq_mul] at h
    simp only [scaledNorm, map_mul, complexEval_a, complexEval_b]
    linear_combination c * h

section FiniteDepth

/-- A nonzero linear perturbation survives any prescribed finite serial depth. -/
def finiteDepth (K : ℕ) (p : Presentation) : ℝ :=
  Complex.normSq (complexEval p) + ((1 : ℝ) / 2) ^ K * (complexEval p).im

theorem finiteDepth_unit (K : ℕ) : finiteDepth K 1 = 1 := by simp [finiteDepth]

theorem finiteDepth_column (K : ℕ) (p : Presentation) :
    finiteDepth K (a * p) + finiteDepth K (b * p) = finiteDepth K p := by
  obtain ⟨hn, _, hi⟩ := complex_column (complexEval p)
  simp only [Complex.normSq_mul] at hn
  simp only [finiteDepth, map_mul, complexEval_a, complexEval_b]
  linear_combination hn + ((1 : ℝ) / 2) ^ K * hi

private theorem half_pow_le_one (n : ℕ) : ((1 : ℝ) / 2) ^ n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hn : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    nlinarith

private theorem half_pow_antitone {n K : ℕ} (h : n ≤ K) :
    ((1 : ℝ) / 2) ^ K ≤ ((1 : ℝ) / 2) ^ n := by
  have hK : K = n + (K - n) := by omega
  rw [hK, pow_add]
  have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
  calc
    ((1 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ (K - n) ≤
        ((1 : ℝ) / 2) ^ n * 1 :=
      mul_le_mul_of_nonneg_left (half_pow_le_one (K - n)) hp
    _ = ((1 : ℝ) / 2) ^ n := mul_one _

/-- Native serial words can be indexed by their two letter counts because the
native coefficients commute. The word-length premise bounds their sum. -/
theorem finiteDepth_nonnegative_word (K m n : ℕ) (hlen : m + n ≤ K) :
    0 ≤ finiteDepth K (a ^ m * b ^ n) := by
  let z := complexEval (a ^ m * b ^ n)
  have hn : Complex.normSq z = ((1 : ℝ) / 2) ^ (m + n) := by
    simp only [z, map_mul, map_pow, complexEval_a, complexEval_b,
      Complex.normSq_mul, norm_a, norm_b, pow_add]
  have hupper : Complex.normSq z ≤ 1 := by rw [hn]; exact half_pow_le_one _
  have him : -1 ≤ z.im := by
    have hsq := Complex.im_sq_le_normSq z
    nlinarith [sq_nonneg (z.im + 1)]
  have hsmall : ((1 : ℝ) / 2) ^ K ≤ Complex.normSq z := by
    rw [hn]
    exact half_pow_antitone hlen
  have heps : 0 ≤ ((1 : ℝ) / 2) ^ K := by positivity
  have hlin := mul_le_mul_of_nonneg_left him heps
  change 0 ≤ Complex.normSq z + ((1 : ℝ) / 2) ^ K * z.im
  nlinarith

theorem finiteDepth_branch_imbalance (K : ℕ) :
    finiteDepth K a - finiteDepth K b = ((1 : ℝ) / 2) ^ K := by
  norm_num [finiteDepth, norm_a, norm_b, ComplexModel.a, ComplexModel.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im] <;> ring

theorem finiteDepth_no_nativeTransfer (K : ℕ) : ¬ NativeTransfer (finiteDepth K) := by
  intro L
  have ha := L.left_a 1
  have hb := L.left_b 1
  simp only [mul_one] at ha hb
  have heps : 0 < ((1 : ℝ) / 2) ^ K := by positivity
  linarith [finiteDepth_branch_imbalance K]

/-- Even a finite cone that includes both first branches leaves a nonzero
imbalance compatible with all tested positivity and exact conservation laws. -/
theorem finiteDepth_control (K : ℕ) (hK : 1 ≤ K) :
    finiteDepth K 1 = 1 ∧
    (∀ p, finiteDepth K (a * p) + finiteDepth K (b * p) = finiteDepth K p) ∧
    (∀ m n, m + n ≤ K → 0 ≤ finiteDepth K (a ^ m * b ^ n)) ∧
    0 ≤ finiteDepth K a ∧ 0 ≤ finiteDepth K b ∧
    ¬ NativeTransfer (finiteDepth K) := by
  refine ⟨finiteDepth_unit K, finiteDepth_column K, finiteDepth_nonnegative_word K,
    ?_, ?_, finiteDepth_no_nativeTransfer K⟩
  · simpa using finiteDepth_nonnegative_word K 1 0 (by omega)
  · simpa using finiteDepth_nonnegative_word K 0 1 (by omega)

end FiniteDepth

section LexicographicBoundary

/-- The codomain is the real additive vector space of pairs with a stated
lexicographic cone. No multiplication or ordered-ring instance is introduced. -/
def LexNonnegative (v : ℝ × ℝ) : Prop := 0 < v.1 ∨ v.1 = 0 ∧ 0 ≤ v.2

def LexLess (u v : ℝ × ℝ) : Prop := u.1 < v.1 ∨ u.1 = v.1 ∧ u.2 < v.2

def lexReadout (p : Presentation) : ℝ × ℝ :=
  (Complex.normSq (complexEval p), (complexEval p).re - Complex.normSq (complexEval p))

theorem lexReadout_unit : lexReadout 1 = (1, 0) := by simp [lexReadout]

theorem lexReadout_nonnegative (p : Presentation) : LexNonnegative (lexReadout p) := by
  by_cases hz : complexEval p = 0
  · right
    simp [lexReadout, hz]
  · left
    exact Complex.normSq_pos.mpr hz

theorem lexReadout_faithful (p : Presentation) : lexReadout p = (0, 0) ↔ p = 0 := by
  constructor
  · intro h
    have hn : Complex.normSq (complexEval p) = 0 := congrArg Prod.fst h
    apply NormalForm.complexEval_injective
    simpa using Complex.normSq_eq_zero.mp hn
  · rintro rfl
    simp [lexReadout]

theorem lexReadout_column (p : Presentation) :
    lexReadout (a * p) + lexReadout (b * p) = lexReadout p := by
  obtain ⟨hn, hr, _⟩ := complex_column (complexEval p)
  apply Prod.ext
  · change Complex.normSq (complexEval (a * p)) +
      Complex.normSq (complexEval (b * p)) = Complex.normSq (complexEval p)
    simpa only [map_mul, complexEval_a, complexEval_b] using hn
  · change
      ((complexEval (a * p)).re - Complex.normSq (complexEval (a * p))) +
      ((complexEval (b * p)).re - Complex.normSq (complexEval (b * p))) =
      (complexEval p).re - Complex.normSq (complexEval p)
    simp only [map_mul, complexEval_a, complexEval_b]
    simp only [Complex.normSq_mul] at hn
    linarith

theorem lexReadout_generators :
    lexReadout a = ((1 : ℝ) / 2, 0) ∧ lexReadout b = ((1 : ℝ) / 2, 0) := by
  norm_num [lexReadout, norm_a, norm_b, ComplexModel.a, ComplexModel.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem lexReadout_phase_branch_failure :
    lexReadout phase = (1, -1) ∧
    lexReadout (a * phase) = ((1 : ℝ) / 2, -1) ∧
    lexReadout (a * phase) ≠
      ((lexReadout phase).1 / 2, (lexReadout phase).2 / 2) := by
  norm_num [lexReadout, map_mul, Complex.normSq_mul, norm_a,
    ComplexModel.a, Complex.mul_re, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem lexReadout_scalar_two_boundary :
    lexReadout (2 : Presentation) = (4, -2) ∧
      lexReadout (2 : Presentation) ≠ (4 : ℝ) • lexReadout 1 := by
  have htwo : complexEval (2 : Presentation) = (2 : ℂ) := by
    rw [show (2 : Presentation) = 1 + 1 from one_add_one_eq_two.symm, map_add, map_one]
    norm_num
  norm_num [lexReadout, htwo, Complex.normSq_apply]

/-- A positive infinitesimal stays below the real unit at every dyadic scale. -/
theorem lex_infinitesimal :
    LexLess (0, 0) (0, 1) ∧
      ∀ n : ℕ, LexLess ((2 : ℝ) ^ n • (0, 1)) (1, 0) := by
  constructor
  · right
    norm_num
  · intro n
    left
    simp

end LexicographicBoundary

end IDT.QMClosure.PositiveColumnConservationControls
