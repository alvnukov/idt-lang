import Proofs.QMClosure.GaussianLocationEntropy
import Proofs.QMClosure.ClassicalStatisticalProcessBridge
import Proofs.QMClosure.NativeMixerEventConeExclusion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# A supplied Gaussian realization of the native mixer

Each real coordinate has an explicitly supplied unit-variance Gaussian law.
A single deterministic real-linear channel transforms every independent pair
of preparations into the exact product preparation at the native-mixer output.
The proof compares characteristic functions of the actual measures, including
their output independence. No classification or physical availability follows.
-/

namespace IDT.QMClosure.NativeGaussianStatisticalProcess

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open GaussianLocationEntropy

abbrev Sample := ℝ × ℝ
abbrev PairSample := Sample × Sample

def coordinates (z : ℂ) : Sample := (z.re, z.im)

def e0 : PairSample := ((1, 0), (0, 0))
def e1 : PairSample := ((0, 1), (0, 0))
def e2 : PairSample := ((0, 0), (1, 0))
def e3 : PairSample := ((0, 0), (0, 1))

private def p0 : PairSample →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Sample Sample)
private def p1 : PairSample →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Sample Sample)
private def p2 : PairSample →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Sample Sample)
private def p3 : PairSample →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Sample Sample)

/-- The one common channel map, in the four explicit real coordinates. -/
def G : PairSample →L[ℝ] PairSample :=
  (((1 / 2 : ℝ) • (p0 - p1 + p2 + p3)).prod
    ((1 / 2 : ℝ) • (p0 + p1 - p2 + p3))).prod
  (((1 / 2 : ℝ) • (p0 + p1 + p2 - p3)).prod
    ((1 / 2 : ℝ) • (-p0 + p1 + p2 + p3)))

theorem G_apply (v : PairSample) :
    G v = (((v.1.1 - v.1.2 + v.2.1 + v.2.2) / 2,
      (v.1.1 + v.1.2 - v.2.1 + v.2.2) / 2),
      ((v.1.1 + v.1.2 + v.2.1 - v.2.2) / 2,
      (-v.1.1 + v.1.2 + v.2.1 + v.2.2) / 2)) := by
  ext <;> simp [G, p0, p1, p2, p3] <;> ring

/-- Squared Euclidean length of one outcome's two real coordinates. -/
def coordinateEnergy (u : Sample) : ℝ := u.1 ^ 2 + u.2 ^ 2

/-- The common channel conserves total coordinate energy at every outcome. -/
theorem coordinateEnergy_G (v : PairSample) :
    coordinateEnergy (G v).1 + coordinateEnergy (G v).2 =
      coordinateEnergy v.1 + coordinateEnergy v.2 := by
  rw [G_apply]
  simp only [coordinateEnergy]
  ring

/-- Euclidean coordinate energy of a dual vector, independent of the product norm. -/
def energy (L : StrongDual ℝ PairSample) : ℝ :=
  (L e0) ^ 2 + (L e1) ^ 2 + (L e2) ^ 2 + (L e3) ^ 2

theorem linear_form (L : StrongDual ℝ PairSample) (v : PairSample) :
    L v = v.1.1 * L e0 + v.1.2 * L e1 + v.2.1 * L e2 + v.2.2 * L e3 := by
  have hv : v = v.1.1 • e0 + v.1.2 • e1 + v.2.1 • e2 + v.2.2 • e3 := by
    ext <;> simp [e0, e1, e2, e3]
  calc
    L v = L (v.1.1 • e0 + v.1.2 • e1 + v.2.1 • e2 + v.2.2 • e3) :=
      congrArg L hv
    _ = _ := by simp

theorem energy_comp_G (L : StrongDual ℝ PairSample) :
    energy (L.comp G) = energy L := by
  simp only [energy, ContinuousLinearMap.comp_apply]
  rw [linear_form L (G e0), linear_form L (G e1),
    linear_form L (G e2), linear_form L (G e3)]
  norm_num [G_apply, e0, e1, e2, e3]
  ring

private theorem charFunDual_gaussianReal (μ : ℝ) (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal μ 1) L =
      Complex.exp (((μ * L 1 : ℝ) : ℂ) * Complex.I -
        (((L 1) ^ 2 : ℝ) : ℂ) / 2) := by
  have hmean : L μ = μ * L 1 := by
    simpa using L.map_smul μ (1 : ℝ)
  rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp [hmean, Real.coe_toNNReal _ (sq_nonneg _)]

/-- The four independent real Gaussian factors determine the whole characteristic function. -/
theorem charFunDual_preparation_prod (x y : ℂ) (L : StrongDual ℝ PairSample) :
    charFunDual ((preparation x).prod (preparation y)) L =
      Complex.exp ((L (coordinates x, coordinates y) : ℂ) * Complex.I -
        (energy L : ℂ) / 2) := by
  simp only [preparation, charFunDual_prod, charFunDual_gaussianReal,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [linear_form L (coordinates x, coordinates y)]
  simp only [coordinates, energy, e0, e1, e2, e3,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    show (0 : Sample) = (0, 0) from rfl]
  ring

abbrev nativeF : ℂ × ℂ → ℂ × ℂ := NativeMixerEventConeExclusion.mixer

theorem mean_compatibility (p : ℂ × ℂ) :
    G (coordinates p.1, coordinates p.2) =
      (coordinates (nativeF p).1, coordinates (nativeF p).2) := by
  rw [G_apply]
  apply Prod.ext <;> apply Prod.ext <;>
    simp [coordinates, nativeF, NativeMixerEventConeExclusion.mixer,
      NativeMixerEventConeExclusion.Raw, CompositeProductControls.RawSign.N,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im] <;> ring

/-- Full equality of the pushed-forward probability measure, including output independence. -/
theorem map_preparation_prod (p : ℂ × ℂ) :
    ((preparation p.1).prod (preparation p.2)).map G =
      (preparation (nativeF p).1).prod (preparation (nativeF p).2) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_preparation_prod, charFunDual_preparation_prod,
    energy_comp_G]
  simp only [ContinuousLinearMap.comp_apply, mean_compatibility]

def channel : Kernel PairSample PairSample :=
  Kernel.deterministic G G.continuous.measurable

instance channel_isMarkovKernel : IsMarkovKernel channel := by
  unfold channel
  infer_instance

theorem channel_covariance (p : ℂ × ℂ) :
    channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
      (preparation (nativeF p).1).prod (preparation (nativeF p).2) := by
  rw [channel, Measure.deterministic_comp_eq_map]
  exact map_preparation_prod p

/-- A complete nontrivial consistency witness for the classical statistical bridge. -/
def model : ClassicalStatisticalProcessBridge.Contract ℂ Sample where
  preparation := preparation
  probability := fun _ => inferInstance
  finiteEntropy := klDiv_preparation_ne_top
  chosenZero := 0
  operation := nativeF
  square := NativeMixerEventConeExclusion.mixer_square
  transparent := NativeMixerEventConeExclusion.mixer_transparent
  channel := channel
  markov := inferInstance
  covariance := channel_covariance

theorem model_comparison (x y : ℂ) :
    model.comparison x y = Complex.normSq (x - y) :=
  jeffreys_preparation x y

/-- Distinct complex means give distinct actual probability measures. -/
theorem preparation_injective : Function.Injective preparation := by
  intro x y h
  have hre := congrArg (fun μ : Measure Sample => μ.map Prod.fst) h
  have him := congrArg (fun μ : Measure Sample => μ.map Prod.snd) h
  simp only [preparation, Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul] at hre him
  exact Complex.ext (gaussianReal_ext_iff.mp hre).1 (gaussianReal_ext_iff.mp him).1

theorem feature_one_ne_zero : model.feature 1 ≠ 0 := by
  intro h
  have hnorm := model.norm_feature_sq (1 : ℂ)
  rw [h, norm_zero, zero_pow (by decide), model_comparison] at hnorm
  norm_num [model] at hnorm

end
end IDT.QMClosure.NativeGaussianStatisticalProcess
