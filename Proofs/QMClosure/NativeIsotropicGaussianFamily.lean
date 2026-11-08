import Proofs.QMClosure.NativeGaussianStatisticalProcess

/-!
# Supplied isotropic Gaussian preparations at arbitrary variance

The sample carrier, Gaussian laws and native channel are supplied mathematical
data. These measure identities include the zero-variance boundary.
-/

namespace IDT.QMClosure.NativeIsotropicGaussianFamily

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open NativeGaussianStatisticalProcess
open scoped ENNReal NNReal

def preparation (v : ℝ≥0) (m : Sample) : Measure Sample :=
  (gaussianReal m.1 v).prod (gaussianReal m.2 v)

instance preparation_isProbabilityMeasure (v : ℝ≥0) (m : Sample) :
    IsProbabilityMeasure (preparation v m) := by
  unfold preparation
  infer_instance

@[simp] theorem map_fst_preparation (v : ℝ≥0) (m : Sample) :
    (preparation v m).map Prod.fst = gaussianReal m.1 v := by
  simp [preparation, Measure.map_fst_prod]

@[simp] theorem map_snd_preparation (v : ℝ≥0) (m : Sample) :
    (preparation v m).map Prod.snd = gaussianReal m.2 v := by
  simp [preparation, Measure.map_snd_prod]

theorem preparation_ext_iff (v w : ℝ≥0) (m n : Sample) :
    preparation v m = preparation w n ↔ v = w ∧ m = n := by
  constructor
  · intro h
    have hx := congrArg (fun μ : Measure Sample => μ.map Prod.fst) h
    have hy := congrArg (fun μ : Measure Sample => μ.map Prod.snd) h
    simp only [map_fst_preparation, map_snd_preparation] at hx hy
    exact ⟨(gaussianReal_ext_iff.mp hx).2,
      Prod.ext (gaussianReal_ext_iff.mp hx).1 (gaussianReal_ext_iff.mp hy).1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem preparation_zero (m : Sample) : preparation 0 m = Measure.dirac m := by
  simp [preparation, gaussianReal_zero_var, Measure.dirac_prod_dirac]

theorem integral_fst_preparation (v : ℝ≥0) (m : Sample) :
    ∫ s, s.1 ∂preparation v m = m.1 := by
  have h := integral_map (μ := preparation v m) measurable_fst.aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  rw [map_fst_preparation, integral_id_gaussianReal] at h
  exact h.symm

theorem integral_snd_preparation (v : ℝ≥0) (m : Sample) :
    ∫ s, s.2 ∂preparation v m = m.2 := by
  have h := integral_map (μ := preparation v m) measurable_snd.aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  rw [map_snd_preparation, integral_id_gaussianReal] at h
  exact h.symm

theorem variance_fst_preparation (v : ℝ≥0) (m : Sample) :
    Var[Prod.fst; preparation v m] = v := by
  have h := variance_map (μ := preparation v m) (Y := Prod.fst)
    measurable_id.aemeasurable measurable_fst.aemeasurable
  simpa only [map_fst_preparation, variance_id_gaussianReal, Function.id_comp] using h.symm

theorem variance_snd_preparation (v : ℝ≥0) (m : Sample) :
    Var[Prod.snd; preparation v m] = v := by
  have h := variance_map (μ := preparation v m) (Y := Prod.snd)
    measurable_id.aemeasurable measurable_snd.aemeasurable
  simpa only [map_snd_preparation, variance_id_gaussianReal, Function.id_comp] using h.symm

private theorem map_unit_gaussian (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) :
    (gaussianReal (a / Real.sqrt v) 1).map (Real.sqrt v * ·) = gaussianReal a v := by
  have hc : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast pos_iff_ne_zero.mpr hv)).ne'
  rw [gaussianReal_map_const_mul, mul_div_cancel₀ _ hc, mul_one]
  congr 1
  apply NNReal.eq
  exact Real.sq_sqrt v.coe_nonneg

/-- Strictly positive supplied variance gives finite directed KL at all means. -/
theorem klDiv_preparation_ne_top (v : ℝ≥0) (hv : v ≠ 0) (mx my : Sample) :
    klDiv (preparation v mx) (preparation v my) ≠ ∞ := by
  have hscalar (a b : ℝ) : klDiv (gaussianReal a v) (gaussianReal b v) ≠ ∞ := by
    rw [← map_unit_gaussian v hv a, ← map_unit_gaussian v hv b]
    exact RelativeEntropyDataProcessing.klDiv_map_ne_top _ _ _ (by fun_prop)
      (GaussianLocationEntropy.gaussianReal_klDiv_ne_top _ _)
  rw [preparation, preparation, RelativeEntropyDataProcessing.klDiv_prod]
  exact ENNReal.add_ne_top.mpr ⟨hscalar _ _, hscalar _ _⟩

theorem G_diagonal (m : Sample) : G (m, m) = (m, m) := by
  rw [G_apply]
  ext <;> dsimp <;> ring

private def f0 : Sample := (1, 0)
private def f1 : Sample := (0, 1)

private theorem sample_linear_form (L : StrongDual ℝ Sample) (m : Sample) :
    L m = m.1 * L f0 + m.2 * L f1 := by
  have hm : m = m.1 • f0 + m.2 • f1 := by ext <;> simp [f0, f1]
  calc
    L m = L (m.1 • f0 + m.2 • f1) := congrArg L hm
    _ = _ := by simp

private theorem charFunDual_gaussianReal (v : ℝ≥0) (m : ℝ) (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal m v) L =
      Complex.exp ((L m : ℂ) * Complex.I - (v : ℂ) * ((L 1) ^ 2 : ℝ) / 2) := by
  rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp [Real.coe_toNNReal _ (sq_nonneg _), mul_comm]

theorem charFunDual_preparation (v : ℝ≥0) (m : Sample) (L : StrongDual ℝ Sample) :
    charFunDual (preparation v m) L =
      Complex.exp ((L m : ℂ) * Complex.I -
        (v : ℂ) * (((L f0) ^ 2 + (L f1) ^ 2 : ℝ) : ℂ) / 2) := by
  simp only [preparation, charFunDual_prod, charFunDual_gaussianReal,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  rw [← Complex.exp_add]
  congr 1
  rw [sample_linear_form L m]
  simp only [f0, f1, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  have h0 : L (m.1, 0) = m.1 * L (1, 0) := by
    simpa using L.map_smul m.1 (1, 0)
  have h1 : L (0, m.2) = m.2 * L (0, 1) := by
    simpa using L.map_smul m.2 (0, 1)
  rw [h0, h1]
  push_cast
  ring

theorem charFunDual_preparation_prod (vx vy : ℝ≥0) (mx my : Sample)
    (L : StrongDual ℝ PairSample) :
    charFunDual ((preparation vx mx).prod (preparation vy my)) L =
      Complex.exp ((L (mx, my) : ℂ) * Complex.I -
        ((vx : ℂ) * (((L e0) ^ 2 + (L e1) ^ 2 : ℝ) : ℂ) +
          (vy : ℂ) * (((L e2) ^ 2 + (L e3) ^ 2 : ℝ) : ℂ)) / 2) := by
  simp only [charFunDual_prod, charFunDual_preparation,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  rw [← Complex.exp_add]
  congr 1
  rw [linear_form L (mx, my)]
  rw [linear_form L (mx, 0), linear_form L (0, my)]
  simp only [f0, f1, e0, e1, e2, e3,
    zero_mul, add_zero, zero_add, show (0 : Sample) = (0, 0) from rfl]
  push_cast
  ring

def first : PairSample →L[ℝ] Sample := (ContinuousLinearMap.fst ℝ Sample Sample).comp G
def second : PairSample →L[ℝ] Sample := (ContinuousLinearMap.snd ℝ Sample Sample).comp G

theorem map_first_preparation_prod (vx vy : ℝ≥0) (mx my : Sample) :
    ((preparation vx mx).prod (preparation vy my)).map first =
      preparation ((vx + vy) / 2) (G (mx, my)).1 := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_preparation_prod, charFunDual_preparation]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, first, ContinuousLinearMap.coe_fst']
  rw [sample_linear_form L (G e0).1, sample_linear_form L (G e1).1,
    sample_linear_form L (G e2).1, sample_linear_form L (G e3).1]
  norm_num [G_apply, e0, e1, e2, e3, f0, f1]
  ring

theorem map_second_preparation_prod (vx vy : ℝ≥0) (mx my : Sample) :
    ((preparation vx mx).prod (preparation vy my)).map second =
      preparation ((vx + vy) / 2) (G (mx, my)).2 := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_preparation_prod, charFunDual_preparation]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, second, ContinuousLinearMap.coe_snd']
  rw [sample_linear_form L (G e0).2, sample_linear_form L (G e1).2,
    sample_linear_form L (G e2).2, sample_linear_form L (G e3).2]
  norm_num [G_apply, e0, e1, e2, e3, f0, f1]
  ring

theorem map_preparation_prod (v : ℝ≥0) (mx my : Sample) :
    ((preparation v mx).prod (preparation v my)).map G =
      (preparation v (G (mx, my)).1).prod (preparation v (G (mx, my)).2) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_preparation_prod, charFunDual_preparation_prod]
  have h := energy_comp_G L
  simp only [energy, ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  have hc := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at hc ⊢
  linear_combination -(v : ℂ) / 2 * hc

end
end IDT.QMClosure.NativeIsotropicGaussianFamily
