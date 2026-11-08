import Proofs.QMClosure.InvariantEffectReadoutBridge
import Proofs.QMClosure.NativeGaussianStatisticalProcess
import Proofs.QMClosure.NativeAttenuationCircuit
import Proofs.QMClosure.FiniteOutcomeChannelWall

/-!
# A Gaussian soft detector and its finite-event projection boundary

This explicit witness uses independent unit-variance real Gaussian coordinates
and the chosen effect `exp (-(u²+v²)/2)`. Both the noise scale and detector width
are supplied. The response is a genuine binary event probability. Its normalized
negative logarithm is one quarter of the location norm square.

The actual continuous native channel preserves the dual product effect. Its
two selected Bool-record probes have identical input laws and distinct output
laws. Thus that continuous channel cannot descend to a common channel on the
finite records, even for these two probes. No detector classification, physical
origin, Born rule, or full QM closure is asserted.
-/

namespace IDT.QMClosure.GaussianSoftDetectorBoundary

noncomputable section

open MeasureTheory ProbabilityTheory
open GaussianLocationEntropy InvariantEffectReadoutBridge
open scoped ENNReal NNReal BigOperators

abbrev Sample := ℝ × ℝ

/-- Explicit coordinate energy avoids the max norm on a product of real lines. -/
def softValue (ω : Sample) : ℝ := Real.exp (-(ω.1 ^ 2 + ω.2 ^ 2) / 2)

theorem softValue_measurable : Measurable softValue := by
  unfold softValue
  fun_prop

theorem softValue_positive (ω : Sample) : 0 < softValue ω := Real.exp_pos _

theorem softValue_le_one (ω : Sample) : softValue ω ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := add_nonneg (sq_nonneg ω.1) (sq_nonneg ω.2)
  linarith

def softEffect : Effect Sample where
  value := softValue
  measurable := softValue_measurable
  nonnegative ω := (softValue_positive ω).le
  atMostOne := softValue_le_one

/-- The scalar completed-square identity includes the normalization factor. -/
theorem gaussian_soft_density (a t : ℝ) :
    gaussianPDFReal a 1 t * Real.exp (-t ^ 2 / 2) =
      ((Real.sqrt 2)⁻¹ * Real.exp (-a ^ 2 / 4)) *
        gaussianPDFReal (a / 2) (1 / 2 : ℝ≥0) t := by
  have hh : (((1 / 2 : ℝ≥0) : ℝ)) = 1 / 2 := by norm_num
  have hs : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  simp only [gaussianPDFReal, NNReal.coe_one, hh, mul_one]
  rw [show (2 : ℝ) * Real.pi * (1 / 2) = Real.pi by ring,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, hs, mul_inv_rev]
  calc
    (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
          Real.exp (-(t - a) ^ 2 / 2) * Real.exp (-t ^ 2 / 2) =
        ((Real.sqrt 2)⁻¹ * (Real.sqrt Real.pi)⁻¹) *
          Real.exp (-(t - a) ^ 2 / 2 - t ^ 2 / 2) := by
      rw [show -(t - a) ^ 2 / 2 - t ^ 2 / 2 =
        -(t - a) ^ 2 / 2 + (-t ^ 2 / 2) by ring, Real.exp_add]
      ring
    _ = ((Real.sqrt 2)⁻¹ * Real.exp (-a ^ 2 / 4)) *
        ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(t - a / 2) ^ 2)) := by
      rw [show -(t - a) ^ 2 / 2 - t ^ 2 / 2 =
        -a ^ 2 / 4 + -(t - a / 2) ^ 2 by ring, Real.exp_add]
      ring

/-- The scalar expectation is integrated against the actual Gaussian measure. -/
theorem scalar_acceptance (a : ℝ) :
    (∫ t : ℝ, Real.exp (-t ^ 2 / 2) ∂gaussianReal a 1) =
      (Real.sqrt 2)⁻¹ * Real.exp (-a ^ 2 / 4) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  simp_rw [gaussian_soft_density]
  rw [integral_const_mul,
    integral_gaussianPDFReal_eq_one (a / 2) (by norm_num : (1 / 2 : ℝ≥0) ≠ 0), mul_one]

/-- Acceptance is defined as an integral before computing its closed form. -/
def q (z : ℂ) : ℝ := softEffect.acceptance (preparation z)

theorem q_formula (z : ℂ) : q z = (1 / 2 : ℝ) * Real.exp (-Complex.normSq z / 4) := by
  have hf : softValue = fun ω : Sample =>
      Real.exp (-ω.1 ^ 2 / 2) * Real.exp (-ω.2 ^ 2 / 2) := by
    funext ω
    unfold softValue
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ ω, softValue ω ∂(gaussianReal z.re 1).prod (gaussianReal z.im 1)) = _
  rw [hf]
  dsimp only
  rw [integral_prod_mul (fun t : ℝ => Real.exp (-t ^ 2 / 2))
    (fun t : ℝ => Real.exp (-t ^ 2 / 2)), scalar_acceptance, scalar_acceptance]
  rw [mul_mul_mul_comm, ← Real.exp_add, ← pow_two, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [invOf_eq_inv, inv_div, one_div]
  congr 1
  simp only [Complex.normSq_apply]
  ring

theorem q_zero : q 0 = 1 / 2 := by simp [q_formula]

theorem q_positive (z : ℂ) : 0 < q z := by rw [q_formula]; positivity

theorem q_le_reference (z : ℂ) : q z ≤ q 0 := by
  rw [q_formula, q_zero]
  have h : Real.exp (-Complex.normSq z / 4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Complex.normSq_nonneg _))
      (by norm_num)
  nlinarith

/-- Both acceptance and rejection are actual events of one Markov detector. -/
theorem q_actual_event (z : ℂ) :
    (softEffect.binaryKernel ∘ₘ preparation z) {true} = ENNReal.ofReal (q z) :=
  softEffect.binaryKernel_comp_true (preparation z)

theorem rejection_actual_event (z : ℂ) :
    (softEffect.binaryKernel ∘ₘ preparation z) {false} = ENNReal.ofReal (1 - q z) :=
  softEffect.binaryKernel_comp_false (preparation z)

/-- Independent of the integral evaluation, the chosen effect is invariant under
the common latent native channel's deterministic map. -/
theorem soft_product_invariant_map (ω : Sample × Sample) :
    softEffect.productValue (NativeGaussianStatisticalProcess.G ω) =
      softEffect.productValue ω := by
  simp only [Effect.productValue, softEffect, softValue]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [NativeGaussianStatisticalProcess.G_apply]
  dsimp
  ring

theorem soft_product_invariant (ω : Sample × Sample) :
    (∫ ξ, softEffect.productValue ξ ∂NativeGaussianStatisticalProcess.channel ω) =
      softEffect.productValue ω := by
  rw [NativeGaussianStatisticalProcess.channel, Kernel.deterministic_apply]
  rw [integral_dirac]
  exact soft_product_invariant_map ω

/-- The common continuous channel supplies every premise of the event bridge. -/
def detectorModel : InvariantEffectReadoutBridge.Contract ℂ Sample where
  preparation := preparation
  probability := fun _ => inferInstance
  effect := softEffect
  operation := NativeGaussianStatisticalProcess.nativeF
  channel := NativeGaussianStatisticalProcess.channel
  markov := inferInstance
  covariance := NativeGaussianStatisticalProcess.channel_covariance
  invariant := soft_product_invariant

theorem detector_response (z : ℂ) : detectorModel.response z = q z := rfl

/-- The actual channel premises give the product law without assuming it. -/
theorem q_product_conserved (p : ℂ × ℂ) :
    q (NativeGaussianStatisticalProcess.nativeF p).1 *
        q (NativeGaussianStatisticalProcess.nativeF p).2 = q p.1 * q p.2 :=
  detectorModel.response_product p

def W (z : ℂ) : ℝ := detectorModel.weight 0 z

/-- This detector width and noise variance give the explicit coefficient 1/4. -/
theorem W_formula (z : ℂ) : W z = Complex.normSq z / 4 := by
  change -Real.log (q z / q 0) = _
  rw [q_formula, q_zero]
  have h : ((1 / 2 : ℝ) * Real.exp (-Complex.normSq z / 4)) / (1 / 2) =
      Real.exp (-Complex.normSq z / 4) := by ring
  rw [h, Real.log_exp]
  ring

theorem W_nonnegative (z : ℂ) : 0 ≤ W z :=
  detectorModel.weight_nonnegative 0 q_positive q_le_reference z

theorem W_zero : W 0 = 0 := detectorModel.weight_reference 0 (q_positive 0)

theorem W_pair_conserved (p : ℂ × ℂ) :
    W (NativeGaussianStatisticalProcess.nativeF p).1 +
        W (NativeGaussianStatisticalProcess.nativeF p).2 = W p.1 + W p.2 :=
  detectorModel.weight_pair_conserved 0 q_positive p

/-- The finite row is tied to both singleton events of the actual detector. -/
def eventRow (z : ℂ) : Bool → ℝ := softEffect.binaryRow (preparation z)

theorem eventRow_actual (z : ℂ) (b : Bool) :
    (softEffect.binaryKernel ∘ₘ preparation z) {b} = ENNReal.ofReal (eventRow z b) :=
  softEffect.binaryKernel_comp_singleton (preparation z) b

theorem eventRow_nonnegative (z : ℂ) (b : Bool) : 0 ≤ eventRow z b :=
  softEffect.binaryRow_nonnegative (preparation z) b

theorem eventRow_normalized (z : ℂ) : (∑ b : Bool, eventRow z b) = 1 :=
  softEffect.binaryRow_normalized (preparation z)

def jointRow (p : ℂ × ℂ) : Bool × Bool → ℝ :=
  FiniteOutcomeChannelWall.productLaw (eventRow p.1) (eventRow p.2)

theorem jointRow_nonnegative (p : ℂ × ℂ) (b : Bool × Bool) : 0 ≤ jointRow p b :=
  mul_nonneg (eventRow_nonnegative _ _) (eventRow_nonnegative _ _)

theorem jointRow_normalized (p : ℂ × ℂ) : (∑ b : Bool × Bool, jointRow p b) = 1 := by
  simp only [jointRow, FiniteOutcomeChannelWall.productLaw, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, eventRow_normalized, mul_one]
  exact eventRow_normalized _

theorem jointRow_second_true (p : ℂ × ℂ) :
    (∑ b : Bool, jointRow p (b, true)) = q p.2 := by
  change (∑ b : Bool, eventRow p.1 b * q p.2) = q p.2
  rw [← Finset.sum_mul, eventRow_normalized, one_mul]

theorem q_one_eq_q_I : q 1 = q Complex.I := by
  simp [q_formula, Complex.normSq_apply]

theorem q_one_lt_q_zero : q 1 < q 0 := by
  rw [q_formula, q_zero]
  norm_num only [Complex.normSq_one]
  have h : Real.exp (-(1 : ℝ) / 4) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  nlinarith

theorem nativeF_one_one : NativeGaussianStatisticalProcess.nativeF (1, 1) = (1, 1) :=
  NativeMixerEventConeExclusion.mixer_transparent 1

theorem nativeF_one_I :
    NativeGaussianStatisticalProcess.nativeF (1, Complex.I) = (1 + Complex.I, 0) := by
  apply Prod.ext
  · rw [NativeAttenuationCircuit.mixer_fst]
    apply Complex.ext <;> norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  · rw [NativeAttenuationCircuit.mixer_snd]
    apply Complex.ext <;> norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- The two independent input Bool laws coincide in every outcome. -/
theorem input_jointRows_equal : jointRow (1, 1) = jointRow (1, Complex.I) := by
  have hrow : eventRow 1 = eventRow Complex.I := by
    funext b
    change (if b then q 1 else 1 - q 1) =
      (if b then q Complex.I else 1 - q Complex.I)
    rw [q_one_eq_q_I]
  simp only [jointRow, hrow]

/-- The two selected outputs have distinct second-event probabilities. -/
theorem output_jointRows_ne :
    jointRow (NativeGaussianStatisticalProcess.nativeF (1, 1)) ≠
      jointRow (NativeGaussianStatisticalProcess.nativeF (1, Complex.I)) := by
  intro h
  have hm := congrArg (fun f : Bool × Bool → ℝ => ∑ b : Bool, f (b, true)) h
  dsimp only at hm
  rw [jointRow_second_true, jointRow_second_true, nativeF_one_one, nativeF_one_I] at hm
  exact (ne_of_lt q_one_lt_q_zero) hm

/-- Product acceptance is nevertheless conserved on these probes. -/
theorem selected_true_products_equal : q 1 * q 1 = q (1 + Complex.I) * q 0 := by
  have h := q_product_conserved (1, Complex.I)
  rw [nativeF_one_I, ← q_one_eq_q_I] at h
  exact h.symm

/-- No common finite stochastic channel transports even these two actual finite
record probes to their required native outputs. -/
theorem no_single_binary_record_channel :
    ¬ ∃ T : FiniteOutcomeChannelWall.Channel (Bool × Bool) (Bool × Bool),
      T.outputLaw (jointRow (1, 1)) =
        jointRow (NativeGaussianStatisticalProcess.nativeF (1, 1)) ∧
      T.outputLaw (jointRow (1, Complex.I)) =
        jointRow (NativeGaussianStatisticalProcess.nativeF (1, Complex.I)) := by
  rintro ⟨T, h₁, h₂⟩
  apply output_jointRows_ne
  rw [← h₁, ← h₂, input_jointRows_equal]

end
end IDT.QMClosure.GaussianSoftDetectorBoundary
