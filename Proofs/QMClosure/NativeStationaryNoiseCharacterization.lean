import Proofs.QMClosure.NativeGaussianStatisticalProcess
import Proofs.QMClosure.GaussianSignedSmoothingMoments
import Proofs.QMClosure.GaussianSignedSmoothingCharacterization
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Classification of stationary native noise

For the explicit real two-coordinate sample carrier and supplied native mixer,
two-step stationarity of its first output under independently re-prepared
identical probability inputs forces a product of real Gaussians with a shared variance. Moments
and coordinate independence are consequences. The coordinates and mixer remain
supplied mathematical inputs.
-/

namespace IDT.QMClosure.NativeStationaryNoiseCharacterization

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

abbrev Sample := NativeGaussianStatisticalProcess.Sample

/-- The supplied native mixer's first output. -/
def firstOutput : (Sample × Sample) →L[ℝ] Sample :=
  (ContinuousLinearMap.fst ℝ Sample Sample).comp NativeGaussianStatisticalProcess.G

/-- One smoothing step uses two independent preparations with the same law. -/
def smoothing (μ : Measure Sample) : Measure Sample :=
  (μ.prod μ).map firstOutput

instance isProbabilityMeasure_smoothing (μ : Measure Sample) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (smoothing μ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Stationarity requires only the first output marginal. -/
def FirstMarginalStationary (μ : Measure Sample) : Prop :=
  (μ.prod μ).map firstOutput = μ

/-- Two smoothing steps return the initial law, using independent re-preparation at each step. -/
def TwoStepStationary (μ : Measure Sample) : Prop :=
  smoothing (smoothing μ) = μ

/-- Every first-marginal fixed point is stationary after two smoothing steps. -/
theorem twoStepStationary_of_stationary (μ : Measure Sample)
    (h : FirstMarginalStationary μ) : TwoStepStationary μ := by
  change smoothing (smoothing μ) = μ
  have hfirst : smoothing μ = μ := h
  rw [hfirst, hfirst]

/-- The quarter-turn used in the proof, without any rotation-invariance premise. -/
def J : Sample →L[ℝ] Sample :=
  (-ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

private def A : Sample →L[ℝ] Sample :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Sample + J)

private def B : Sample →L[ℝ] Sample :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Sample - J)

private theorem firstOutput_inl :
    firstOutput.comp (ContinuousLinearMap.inl ℝ Sample Sample) = A := by
  ext x <;> simp [firstOutput, NativeGaussianStatisticalProcess.G_apply, A, J] <;> ring

private theorem firstOutput_inr :
    firstOutput.comp (ContinuousLinearMap.inr ℝ Sample Sample) = B := by
  ext x <;> simp [firstOutput, NativeGaussianStatisticalProcess.G_apply, B, J] <;> ring

private theorem J_comp_J : J.comp J = -ContinuousLinearMap.id ℝ Sample := by
  ext x <;> simp [J]

private theorem dual_neg (μ : Measure Sample) (L : StrongDual ℝ Sample) :
    charFunDual μ (-L) = conj (charFunDual μ L) := by
  have h := charFun_map_eq_charFunDual_smul (μ := μ) L (-1 : ℝ)
  have heq : (-1 : ℝ) • L = -L := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  simpa only [heq, charFun_neg, ← charFunDual_eq_charFun_map_one] using h.symm

private theorem charFunDual_smoothing (μ : Measure Sample) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ Sample) :
    charFunDual (smoothing μ) L =
      charFunDual μ (L.comp A) * charFunDual μ (L.comp B) := by
  rw [smoothing, charFunDual_map, charFunDual_prod]
  congr 1
  · congr 1
    rw [ContinuousLinearMap.comp_assoc, firstOutput_inl]
  · congr 1
    rw [ContinuousLinearMap.comp_assoc, firstOutput_inr]

private def FourFactorIdentity (μ : Measure Sample) : Prop :=
  ∀ L : StrongDual ℝ Sample, charFunDual μ L =
    charFunDual μ ((1 / 2 : ℝ) • L.comp J) *
    charFunDual μ ((1 / 2 : ℝ) • L) ^ 2 *
    conj (charFunDual μ ((1 / 2 : ℝ) • L.comp J))

private theorem fourFactorIdentity_of_twoStepStationary (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : TwoStepStationary μ) : FourFactorIdentity μ := by
  intro L
  have hAA : (L.comp A).comp A = (1 / 2 : ℝ) • L.comp J := by
    apply ContinuousLinearMap.ext
    intro x
    change L (A (A x)) = (1 / 2 : ℝ) * L (J x)
    rw [show A (A x) = (1 / 2 : ℝ) • J x by
      ext <;> simp [A, J] <;> ring]
    simp
  have hAB : (L.comp A).comp B = (1 / 2 : ℝ) • L := by
    apply ContinuousLinearMap.ext
    intro x
    change L (A (B x)) = (1 / 2 : ℝ) * L x
    rw [show A (B x) = (1 / 2 : ℝ) • x by
      ext <;> simp [A, B, J] <;> ring]
    simp
  have hBA : (L.comp B).comp A = (1 / 2 : ℝ) • L := by
    apply ContinuousLinearMap.ext
    intro x
    change L (B (A x)) = (1 / 2 : ℝ) * L x
    rw [show B (A x) = (1 / 2 : ℝ) • x by
      ext <;> simp [A, B, J] <;> ring]
    simp
  have hBB : (L.comp B).comp B = -((1 / 2 : ℝ) • L.comp J) := by
    apply ContinuousLinearMap.ext
    intro x
    change L (B (B x)) = -((1 / 2 : ℝ) * L (J x))
    rw [show B (B x) = -((1 / 2 : ℝ) • J x) by
      ext <;> simp [B, J] <;> ring]
    simp
  have htwo : smoothing (smoothing μ) = μ := h
  calc
    charFunDual μ L = charFunDual (smoothing (smoothing μ)) L := by rw [htwo]
    _ = _ := by
      rw [charFunDual_smoothing, charFunDual_smoothing, charFunDual_smoothing,
        hAA, hAB, hBA, hBB, dual_neg]
      ring

/-- Quarter-turn composition preserves characteristic-function moduli only. -/
private theorem norm_charFunDual_comp_J_of_fourFactorIdentity (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FourFactorIdentity μ) (L : StrongDual ℝ Sample) :
    ‖charFunDual μ (L.comp J)‖ = ‖charFunDual μ L‖ := by
  have hJ : (L.comp J).comp J = -L := by
    rw [ContinuousLinearMap.comp_assoc, J_comp_J]
    apply ContinuousLinearMap.ext
    intro x
    simp
  have hh : (1 / 2 : ℝ) • (-L) = -((1 / 2 : ℝ) • L) := by simp
  rw [h L, h (L.comp J), hJ, hh, dual_neg]
  simp only [norm_mul, norm_pow, Complex.norm_conj]
  ring

/-- Each real projection obeys the scalar signed-smoothing equation. -/
private theorem signed_fixedPoint_of_fourFactorIdentity (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FourFactorIdentity μ) (L : StrongDual ℝ Sample) (t : ℝ) :
    charFun (μ.map L) t =
      (charFun (μ.map L) (t / 2)) ^ 3 * conj (charFun (μ.map L) (t / 2)) := by
  have hnorm := norm_charFunDual_comp_J_of_fourFactorIdentity μ h ((1 / 2 : ℝ) • (t • L))
  have hcomp : ((1 / 2 : ℝ) • (t • L)).comp J =
      (1 / 2 : ℝ) • (t • L).comp J := by rfl
  rw [hcomp] at hnorm
  have hmul : charFunDual μ ((1 / 2 : ℝ) • (t • L).comp J) *
      conj (charFunDual μ ((1 / 2 : ℝ) • (t • L).comp J)) =
      charFunDual μ ((1 / 2 : ℝ) • (t • L)) *
      conj (charFunDual μ ((1 / 2 : ℝ) • (t • L))) := by
    simp only [Complex.mul_conj', hnorm]
  have hhalf : (t / 2) • L = (1 / 2 : ℝ) • (t • L) := by
    rw [smul_smul]
    congr 1
    ring
  simp only [charFun_map_eq_charFunDual_smul, hhalf]
  rw [h (t • L)]
  calc
    _ = (charFunDual μ ((1 / 2 : ℝ) • (t • L))) ^ 2 *
        (charFunDual μ ((1 / 2 : ℝ) • (t • L).comp J) *
        conj (charFunDual μ ((1 / 2 : ℝ) • (t • L).comp J))) := by ring
    _ = _ := by rw [hmul]; ring

/-- The four-factor identity forces every real projection to be Gaussian. -/
private theorem isGaussian_of_fourFactorIdentity (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FourFactorIdentity μ) : IsGaussian μ := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map (by fun_prop)
  have hf := signed_fixedPoint_of_fourFactorIdentity μ h L
  exact ⟨_, _, GaussianSignedSmoothingCharacterization.eq_gaussianReal_of_memLp
    (GaussianSignedSmoothingMoments.memLp_two_of_fixedPoint (μ.map L) hf) hf⟩

/-- The quarter-turn preserves projection variances, while means stay arbitrary. -/
private theorem variance_comp_J_of_fourFactorIdentity (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FourFactorIdentity μ) (L : StrongDual ℝ Sample) :
    variance (L.comp J) μ = variance L μ := by
  letI := isGaussian_of_fourFactorIdentity μ h
  have hn := norm_charFunDual_comp_J_of_fourFactorIdentity μ h L
  simp only [IsGaussian.charFunDual_eq, Complex.norm_exp] at hn
  have hre : ∀ M : StrongDual ℝ Sample,
      ((∫ x, (M x : ℂ) ∂μ) * Complex.I - (variance M μ : ℂ) / 2).re =
        -(variance M μ) / 2 := by
    intro M
    rw [integral_complex_ofReal]
    simp
    ring
  simp only [hre] at hn
  have := Real.exp_injective hn
  linarith

private abbrev fstL : StrongDual ℝ Sample := ContinuousLinearMap.fst ℝ ℝ ℝ
private abbrev sndL : StrongDual ℝ Sample := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The exact stationary law, using its own coordinate means and shared variance. -/
private theorem eq_product_gaussian_of_fourFactorIdentity (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FourFactorIdentity μ) :
    μ = (gaussianReal (∫ x : Sample, x.1 ∂μ) (variance Prod.fst μ).toNNReal).prod
      (gaussianReal (∫ x : Sample, x.2 ∂μ) (variance Prod.fst μ).toNNReal) := by
  letI := isGaussian_of_fourFactorIdentity μ h
  have hfst : MemLp fstL 2 μ := IsGaussian.memLp_dual μ fstL 2 (by simp)
  have hsnd : MemLp sndL 2 μ := IsGaussian.memLp_dual μ sndL 2 (by simp)
  have hvar : variance sndL μ = variance fstL μ := by
    have hj := variance_comp_J_of_fourFactorIdentity μ h fstL
    have heq : fstL.comp J = -sndL := by
      apply ContinuousLinearMap.ext
      intro x
      simp [J]
    rw [heq] at hj
    change variance (fun x => -sndL x) μ = variance fstL μ at hj
    simpa only [variance_fun_neg] using hj
  have hsum : variance (fstL + sndL) μ = variance (fstL - sndL) μ := by
    have hj := variance_comp_J_of_fourFactorIdentity μ h (fstL + sndL)
    have heq : (fstL + sndL).comp J = fstL - sndL := by
      apply ContinuousLinearMap.ext
      intro x
      simp [J]
      ring
    simpa only [heq] using hj.symm
  have hcov : covariance fstL sndL μ = 0 := by
    have ha := variance_add hfst hsnd
    have hs := variance_sub hfst hsnd
    change variance (fun x => fstL x + sndL x) μ = _ at ha
    change variance (fun x => fstL x - sndL x) μ = _ at hs
    change variance (fun x => fstL x + sndL x) μ =
      variance (fun x => fstL x - sndL x) μ at hsum
    linarith
  have hpair : HasGaussianLaw (fun x : Sample => (fstL x, sndL x)) μ := by
    constructor
    change IsGaussian (μ.map id)
    simpa only [Measure.map_id] using (inferInstance : IsGaussian μ)
  have hind := hpair.indepFun_of_covariance_eq_zero hcov
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map
    (by fun_prop : AEMeasurable fstL μ) (by fun_prop : AEMeasurable sndL μ)).mp hind
  have hfstlaw := IsGaussian.map_eq_gaussianReal (μ := μ) fstL
  have hsndlaw := IsGaussian.map_eq_gaussianReal (μ := μ) sndL
  rw [hvar] at hsndlaw
  have hid : (fun x : Sample => (fstL x, sndL x)) = id := by rfl
  rw [hid, Measure.map_id, hfstlaw, hsndlaw] at hprod
  exact hprod

/-- Countable concentration on this explicit native carrier forces a deterministic law. -/
private theorem eq_dirac_of_fourFactorIdentity_countable_concentration (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : FourFactorIdentity μ) (S : Set Sample)
    (hS : S.Countable) (hfull : μ S = 1) :
    μ = Measure.dirac (∫ x : Sample, x.1 ∂μ, ∫ x : Sample, x.2 ∂μ) := by
  have hv : (variance Prod.fst μ).toNNReal = 0 := by
    by_contra hv
    letI : NoAtoms (gaussianReal (∫ x : Sample, x.1 ∂μ)
        (variance Prod.fst μ).toNNReal) := noAtoms_gaussianReal hv
    haveI : NoAtoms μ := by
      rw [eq_product_gaussian_of_fourFactorIdentity μ h]
      infer_instance
    have hz := hS.measure_zero μ
    rw [hfull] at hz
    exact one_ne_zero hz
  conv_lhs => rw [eq_product_gaussian_of_fourFactorIdentity μ h, hv]
  simp only [gaussianReal_zero_var, Measure.dirac_prod_dirac]

/-- Two-step stationarity preserves characteristic-function moduli under the quarter-turn. -/
theorem norm_charFunDual_comp_J_of_twoStepStationary (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : TwoStepStationary μ) (L : StrongDual ℝ Sample) :
    ‖charFunDual μ (L.comp J)‖ = ‖charFunDual μ L‖ :=
  norm_charFunDual_comp_J_of_fourFactorIdentity μ
    (fourFactorIdentity_of_twoStepStationary μ h) L

/-- Each real projection of a two-step stationary law obeys scalar signed smoothing. -/
theorem signed_fixedPoint_of_twoStepStationary (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : TwoStepStationary μ) (L : StrongDual ℝ Sample) (t : ℝ) :
    charFun (μ.map L) t =
      (charFun (μ.map L) (t / 2)) ^ 3 * conj (charFun (μ.map L) (t / 2)) :=
  signed_fixedPoint_of_fourFactorIdentity μ (fourFactorIdentity_of_twoStepStationary μ h) L t

/-- Probability and two-step stationarity force every projection to be Gaussian. -/
theorem isGaussian_of_twoStepStationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : TwoStepStationary μ) : IsGaussian μ :=
  isGaussian_of_fourFactorIdentity μ (fourFactorIdentity_of_twoStepStationary μ h)

/-- Quarter-turn projection variances agree under two-step stationarity. -/
theorem variance_comp_J_of_twoStepStationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : TwoStepStationary μ) (L : StrongDual ℝ Sample) :
    variance (L.comp J) μ = variance L μ :=
  variance_comp_J_of_fourFactorIdentity μ (fourFactorIdentity_of_twoStepStationary μ h) L

/-- The exact two-step stationary law uses its actual coordinate means and one shared variance. -/
theorem eq_product_gaussian_of_twoStepStationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : TwoStepStationary μ) :
    μ = (gaussianReal (∫ x : Sample, x.1 ∂μ) (variance Prod.fst μ).toNNReal).prod
      (gaussianReal (∫ x : Sample, x.2 ∂μ) (variance Prod.fst μ).toNNReal) :=
  eq_product_gaussian_of_fourFactorIdentity μ (fourFactorIdentity_of_twoStepStationary μ h)

/-- Countable concentration of a two-step stationary law on the native carrier is deterministic. -/
theorem eq_dirac_of_twoStepStationary_countable_concentration (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : TwoStepStationary μ) (S : Set Sample)
    (hS : S.Countable) (hfull : μ S = 1) :
    μ = Measure.dirac (∫ x : Sample, x.1 ∂μ, ∫ x : Sample, x.2 ∂μ) :=
  eq_dirac_of_fourFactorIdentity_countable_concentration μ
    (fourFactorIdentity_of_twoStepStationary μ h) S hS hfull

/-- Quarter-turn composition preserves characteristic-function moduli only. -/
theorem norm_charFunDual_comp_J (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FirstMarginalStationary μ) (L : StrongDual ℝ Sample) :
    ‖charFunDual μ (L.comp J)‖ = ‖charFunDual μ L‖ :=
  norm_charFunDual_comp_J_of_twoStepStationary μ (twoStepStationary_of_stationary μ h) L

/-- Each real projection obeys the scalar signed-smoothing equation. -/
theorem signed_fixedPoint_of_stationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FirstMarginalStationary μ) (L : StrongDual ℝ Sample) (t : ℝ) :
    charFun (μ.map L) t =
      (charFun (μ.map L) (t / 2)) ^ 3 * conj (charFun (μ.map L) (t / 2)) :=
  signed_fixedPoint_of_twoStepStationary μ (twoStepStationary_of_stationary μ h) L t

/-- Probability and first-output stationarity force every projection to be Gaussian. -/
theorem isGaussian_of_stationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FirstMarginalStationary μ) : IsGaussian μ :=
  isGaussian_of_twoStepStationary μ (twoStepStationary_of_stationary μ h)

/-- The quarter-turn preserves projection variances, while means stay arbitrary. -/
theorem variance_comp_J_of_stationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FirstMarginalStationary μ) (L : StrongDual ℝ Sample) :
    variance (L.comp J) μ = variance L μ :=
  variance_comp_J_of_twoStepStationary μ (twoStepStationary_of_stationary μ h) L

/-- The exact stationary law, using its own coordinate means and shared variance. -/
theorem eq_product_gaussian_of_stationary (μ : Measure Sample) [IsProbabilityMeasure μ]
    (h : FirstMarginalStationary μ) :
    μ = (gaussianReal (∫ x : Sample, x.1 ∂μ) (variance Prod.fst μ).toNNReal).prod
      (gaussianReal (∫ x : Sample, x.2 ∂μ) (variance Prod.fst μ).toNNReal) :=
  eq_product_gaussian_of_twoStepStationary μ (twoStepStationary_of_stationary μ h)

/-- Countable concentration on this explicit native carrier forces a deterministic law. -/
theorem eq_dirac_of_stationary_countable_concentration (μ : Measure Sample)
    [IsProbabilityMeasure μ] (h : FirstMarginalStationary μ) (S : Set Sample)
    (hS : S.Countable) (hfull : μ S = 1) :
    μ = Measure.dirac (∫ x : Sample, x.1 ∂μ, ∫ x : Sample, x.2 ∂μ) :=
  eq_dirac_of_twoStepStationary_countable_concentration μ
    (twoStepStationary_of_stationary μ h) S hS hfull

end
end IDT.QMClosure.NativeStationaryNoiseCharacterization
