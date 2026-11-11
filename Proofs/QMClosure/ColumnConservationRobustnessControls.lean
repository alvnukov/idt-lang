import Proofs.QMClosure.ColumnConservationRobustness
import Proofs.QMClosure.NativeInitialHistoryPresentation

/-!
Controls in the existing faithful native complex model. Relative
and absolute error have different lower controls. The generic bound module
imports neither this model nor a native transfer or norm selector.
-/

namespace IDT.QMClosure.ColumnConservationRobustnessControls

noncomputable section

open NativeInitialHistoryPresentation

attribute [local instance] presentationCommRing

private theorem norm_a : Complex.normSq ComplexModel.a = (1 : ℝ) / 2 := by
  norm_num [ComplexModel.a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem norm_b : Complex.normSq ComplexModel.b = (1 : ℝ) / 2 := by
  norm_num [ComplexModel.b, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem complex_column (z : ℂ) :
    Complex.normSq (ComplexModel.a * z) + Complex.normSq (ComplexModel.b * z) =
      Complex.normSq z ∧
    (ComplexModel.a * z).im + (ComplexModel.b * z).im = z.im := by
  have h : ComplexModel.a * z + ComplexModel.b * z = z := by
    rw [← add_mul, ComplexModel.transparent, one_mul]
  constructor
  · rw [Complex.normSq_mul, Complex.normSq_mul, norm_a, norm_b]
    ring
  · simpa only [Complex.add_im] using congrArg Complex.im h

private theorem square_im_bound (z : ℂ) : |(z ^ 2).im| ≤ Complex.normSq z := by
  simp only [pow_two, Complex.mul_im, Complex.normSq_apply]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im)]

private theorem square_im_column (z : ℂ) :
    ((ComplexModel.a * z) ^ 2).im + ((ComplexModel.b * z) ^ 2).im = 0 := by
  have h : (ComplexModel.a * z) ^ 2 + (ComplexModel.b * z) ^ 2 = 0 := by
    calc
      _ = (ComplexModel.a ^ 2 + ComplexModel.b ^ 2) * z ^ 2 := by ring
      _ = 0 := by rw [ComplexModel.destructive, zero_mul]
  simpa only [Complex.add_im, Complex.zero_im] using congrArg Complex.im h

def relativeParameter (ε : ℝ) : ℝ := ε / (1 + ε)

def relativeReadout (ε : ℝ) (p : Presentation) : ℝ :=
  Complex.normSq (complexEval p) + relativeParameter ε * ((complexEval p) ^ 2).im

private theorem parameter_bounds {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ relativeParameter ε ∧ relativeParameter ε < 1 ∧
      relativeParameter ε = ε * (1 - relativeParameter ε) := by
  have hden : 0 < 1 + ε := by linarith
  refine ⟨by unfold relativeParameter; positivity, ?_, ?_⟩
  · unfold relativeParameter
    exact (div_lt_one hden).mpr (by linarith)
  · unfold relativeParameter
    field_simp [ne_of_gt hden]
    <;> ring

theorem relativeReadout_nonnegative {ε : ℝ} (hε : 0 ≤ ε) (p : Presentation) :
    0 ≤ relativeReadout ε p := by
  obtain ⟨hτ0, hτ1, hτeq⟩ := parameter_bounds hε
  have hN := Complex.normSq_nonneg (complexEval p)
  have hI := (abs_le.mp (square_im_bound (complexEval p))).1
  have hm := mul_le_mul_of_nonneg_left hI hτ0
  have hp := mul_nonneg (by linarith : 0 ≤ 1 - relativeParameter ε) hN
  dsimp [relativeReadout]
  nlinarith

theorem relativeReadout_faithful {ε : ℝ} (hε : 0 ≤ ε) (p : Presentation) :
    relativeReadout ε p = 0 ↔ p = 0 := by
  constructor
  · intro hw
    obtain ⟨hτ0, hτ1, hτeq⟩ := parameter_bounds hε
    have hN := Complex.normSq_nonneg (complexEval p)
    have hI := (abs_le.mp (square_im_bound (complexEval p))).1
    have hm := mul_le_mul_of_nonneg_left hI hτ0
    have hn : Complex.normSq (complexEval p) = 0 := by
      dsimp [relativeReadout] at hw
      by_contra hn
      have hNpos : 0 < Complex.normSq (complexEval p) :=
        lt_of_le_of_ne hN (Ne.symm hn)
      have hp := mul_pos (by linarith : 0 < 1 - relativeParameter ε) hNpos
      nlinarith
    have hz : complexEval p = 0 := by
      apply Complex.ext
      · have hs := sq_nonneg (complexEval p).im
        rw [Complex.normSq_apply] at hn
        simp only [Complex.zero_re]
        nlinarith [sq_nonneg (complexEval p).re]
      · have hs := sq_nonneg (complexEval p).re
        rw [Complex.normSq_apply] at hn
        simp only [Complex.zero_im]
        nlinarith [sq_nonneg (complexEval p).im]
    apply NormalForm.complexEval_injective
    simpa using hz
  · rintro rfl
    simp [relativeReadout]

theorem relativeReadout_unit (ε : ℝ) : relativeReadout ε 1 = 1 := by
  simp [relativeReadout]

theorem relativeReadout_column {ε : ℝ} (hε : 0 ≤ ε) (p : Presentation) :
    |relativeReadout ε (a * p) + relativeReadout ε (b * p) - relativeReadout ε p| ≤
      ε * relativeReadout ε p := by
  obtain ⟨hτ0, hτ1, hτeq⟩ := parameter_bounds hε
  have hN := (complex_column (complexEval p)).1
  have hI := square_im_column (complexEval p)
  simp only [Complex.normSq_mul] at hN
  have hdef : relativeReadout ε (a * p) + relativeReadout ε (b * p) -
      relativeReadout ε p = -relativeParameter ε * ((complexEval p) ^ 2).im := by
    simp only [relativeReadout, map_mul, complexEval_a, complexEval_b]
    linear_combination hN + relativeParameter ε * hI
  rw [hdef, abs_mul, abs_neg, abs_of_nonneg hτ0]
  have hab := mul_le_mul_of_nonneg_left (square_im_bound (complexEval p)) hτ0
  have hlo := (abs_le.mp (square_im_bound (complexEval p))).1
  have hm := mul_le_mul_of_nonneg_left hlo (mul_nonneg hε hτ0)
  have hweighted := congrArg (fun v : ℝ => v * Complex.normSq (complexEval p)) hτeq
  dsimp [relativeReadout]
  nlinarith

theorem relativeReadout_root_imbalance (ε : ℝ) :
    relativeReadout ε a - relativeReadout ε b = relativeParameter ε := by
  norm_num [relativeReadout, complexEval_a, complexEval_b, ComplexModel.a, ComplexModel.b,
    Complex.normSq_apply, pow_two, Complex.mul_im, Complex.div_re, Complex.div_im]
  <;> ring

/-- A precise linear lower control in the small-relative-error regime. -/
theorem relativeReadout_linear_lower {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε / 2 ≤ |relativeReadout ε a - relativeReadout ε b| := by
  rw [relativeReadout_root_imbalance, abs_of_nonneg (parameter_bounds hε0).1]
  unfold relativeParameter
  apply (le_div_iff₀ (by linarith : 0 < 1 + ε)).mpr
  nlinarith

/-- Positive-part loss from clipping two summands. -/
theorem positive_part_defect (x y : ℝ) :
    0 ≤ max x 0 + max y 0 - max (x + y) 0 ∧
    max x 0 + max y 0 - max (x + y) 0 ≤ max (max (-x) 0) (max (-y) 0) := by
  simp only [max_def]
  split_ifs <;> constructor <;> linarith

private def unclipped (δ : ℝ) (z : ℂ) : ℝ := Complex.normSq z + δ * z.im

private theorem unclipped_lower (δ : ℝ) (z : ℂ) :
    -(δ ^ 2 / 4) ≤ unclipped δ z := by
  dsimp [unclipped]
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im + δ / 2)]

private theorem unclipped_column (δ : ℝ) (z : ℂ) :
    unclipped δ (ComplexModel.a * z) + unclipped δ (ComplexModel.b * z) = unclipped δ z := by
  obtain ⟨hn, hi⟩ := complex_column z
  unfold unclipped
  linear_combination hn + δ * hi

def absoluteReadout (δ : ℝ) (p : Presentation) : ℝ :=
  max (unclipped δ (complexEval p)) 0

theorem absoluteReadout_nonnegative (δ : ℝ) (p : Presentation) :
    0 ≤ absoluteReadout δ p := le_max_right _ _

theorem absoluteReadout_unit (δ : ℝ) : absoluteReadout δ 1 = 1 := by
  norm_num [absoluteReadout, unclipped]

theorem absoluteReadout_column (δ : ℝ) (p : Presentation) :
    0 ≤ absoluteReadout δ (a * p) + absoluteReadout δ (b * p) - absoluteReadout δ p ∧
    absoluteReadout δ (a * p) + absoluteReadout δ (b * p) - absoluteReadout δ p ≤ δ ^ 2 / 4 := by
  let x := unclipped δ (ComplexModel.a * complexEval p)
  let y := unclipped δ (ComplexModel.b * complexEval p)
  have hcolumn : unclipped δ (complexEval p) = x + y :=
    (unclipped_column δ (complexEval p)).symm
  have hpart := positive_part_defect x y
  have hx : max (-x) 0 ≤ δ ^ 2 / 4 := by
    apply max_le
    · have h := unclipped_lower δ (ComplexModel.a * complexEval p)
      dsimp [x]
      linarith
    · positivity
  have hy : max (-y) 0 ≤ δ ^ 2 / 4 := by
    apply max_le
    · have h := unclipped_lower δ (ComplexModel.b * complexEval p)
      dsimp [y]
      linarith
    · positivity
  have hupper : max (max (-x) 0) (max (-y) 0) ≤ δ ^ 2 / 4 := max_le hx hy
  simp only [absoluteReadout, map_mul, complexEval_a, complexEval_b, hcolumn]
  exact ⟨hpart.1, hpart.2.trans hupper⟩

theorem absoluteReadout_absolute_column (δ : ℝ) (p : Presentation) :
    |absoluteReadout δ (a * p) + absoluteReadout δ (b * p) - absoluteReadout δ p| ≤ δ ^ 2 / 4 := by
  rw [abs_of_nonneg (absoluteReadout_column δ p).1]
  exact (absoluteReadout_column δ p).2

theorem absoluteReadout_root_imbalance {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    absoluteReadout δ a - absoluteReadout δ b = δ := by
  have ha : unclipped δ (complexEval a) = (1 + δ) / 2 := by
    norm_num [unclipped, complexEval_a, ComplexModel.a, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    <;> ring
  have hb : unclipped δ (complexEval b) = (1 - δ) / 2 := by
    norm_num [unclipped, complexEval_b, ComplexModel.b, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    <;> ring
  simp only [absoluteReadout, ha, hb,
    max_eq_left (by linarith : 0 ≤ (1 + δ) / 2),
    max_eq_left (by linarith : 0 ≤ (1 - δ) / 2)]
  ring

/-- The squared imbalance is exactly four times the supplied absolute-error
budget. This is the explicit square-root-order lower control. -/
theorem absoluteReadout_square_lower {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < |absoluteReadout δ a - absoluteReadout δ b| ∧
      |absoluteReadout δ a - absoluteReadout δ b| ^ 2 = 4 * (δ ^ 2 / 4) := by
  rw [absoluteReadout_root_imbalance hδ0.le hδ1, abs_of_pos hδ0]
  exact ⟨hδ0, by ring⟩

end

end IDT.QMClosure.ColumnConservationRobustnessControls
