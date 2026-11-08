import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# An actual binary event from an invariant bounded effect

A measurable effect with values in `[0,1]` defines a genuine binary Markov
kernel. Its acceptance probability is the integral of that effect. Product
covariance of a single latent channel and invariance of the dual product
effect imply conservation of the product of the acceptance probabilities.

The negative-log readout is explicitly defined relative to a chosen maximizer.
Effect invariance and this readout definition are separate premises. No entropy,
Hilbert representation, detector-origin, or physical-scale assertion is used.
-/

namespace IDT.QMClosure.InvariantEffectReadoutBridge

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

/-- A measurable randomized binary detector. -/
structure Effect (Ω : Type v) [MeasurableSpace Ω] where
  value : Ω → ℝ
  measurable : Measurable value
  nonnegative : ∀ ω, 0 ≤ value ω
  atMostOne : ∀ ω, value ω ≤ 1

namespace Effect

variable {Ω : Type v} [MeasurableSpace Ω] (g : Effect Ω)

/-- Actual acceptance and rejection measures at each latent sample. -/
def binaryKernel : Kernel Ω Bool where
  toFun ω := ENNReal.ofReal (g.value ω) • Measure.dirac true +
    ENNReal.ofReal (1 - g.value ω) • Measure.dirac false
  measurable' := by
    exact (g.measurable.ennreal_ofReal.smul_measure (Measure.dirac true)).add
      ((measurable_const.sub g.measurable).ennreal_ofReal.smul_measure (Measure.dirac false))

instance binaryKernel_isMarkovKernel : IsMarkovKernel g.binaryKernel where
  isProbabilityMeasure ω := ⟨by
    simp only [binaryKernel, Kernel.coe_mk, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (g.nonnegative ω) (sub_nonneg.mpr (g.atMostOne ω))]
    simp⟩

theorem binaryKernel_true (ω : Ω) :
    g.binaryKernel ω {true} = ENNReal.ofReal (g.value ω) := by
  simp [binaryKernel]

theorem binaryKernel_false (ω : Ω) :
    g.binaryKernel ω {false} = ENNReal.ofReal (1 - g.value ω) := by
  simp [binaryKernel]

theorem integrable (μ : Measure Ω) [IsFiniteMeasure μ] : Integrable g.value μ := by
  apply Integrable.of_bound g.measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (g.nonnegative ω)]
    exact g.atMostOne ω

def acceptance (μ : Measure Ω) : ℝ := ∫ ω, g.value ω ∂μ

theorem acceptance_nonnegative (μ : Measure Ω) : 0 ≤ g.acceptance μ :=
  integral_nonneg g.nonnegative

theorem acceptance_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] :
    g.acceptance μ ≤ 1 := by
  calc
    g.acceptance μ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_mono (g.integrable μ) (integrable_const 1) g.atMostOne
    _ = 1 := by simp

/-- Acceptance is the probability of an event under the actual detector kernel. -/
theorem binaryKernel_comp_true (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (g.binaryKernel ∘ₘ μ) {true} = ENNReal.ofReal (g.acceptance μ) := by
  rw [Measure.bind_apply (measurableSet_singleton true) g.binaryKernel.aemeasurable]
  simp_rw [g.binaryKernel_true]
  exact (ofReal_integral_eq_lintegral_ofReal (g.integrable μ)
    (Filter.Eventually.of_forall g.nonnegative)).symm

/-- Rejection is the complementary actual binary event. -/
theorem binaryKernel_comp_false (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (g.binaryKernel ∘ₘ μ) {false} = ENNReal.ofReal (1 - g.acceptance μ) := by
  rw [Measure.bind_apply (measurableSet_singleton false) g.binaryKernel.aemeasurable]
  simp_rw [g.binaryKernel_false]
  have hi : Integrable (fun ω => 1 - g.value ω) μ :=
    (integrable_const 1).sub (g.integrable μ)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => sub_nonneg.mpr (g.atMostOne ω))]
  congr 1
  rw [integral_sub (integrable_const 1) (g.integrable μ)]
  simp [acceptance]

/-- The finite row records exactly the probabilities of the two actual events. -/
def binaryRow (μ : Measure Ω) (b : Bool) : ℝ :=
  if b then g.acceptance μ else 1 - g.acceptance μ

theorem binaryKernel_comp_singleton (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool) :
    (g.binaryKernel ∘ₘ μ) {b} = ENNReal.ofReal (g.binaryRow μ b) := by
  cases b
  · exact g.binaryKernel_comp_false μ
  · exact g.binaryKernel_comp_true μ

theorem binaryRow_nonnegative (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool) :
    0 ≤ g.binaryRow μ b := by
  cases b
  · exact sub_nonneg.mpr (g.acceptance_le_one μ)
  · exact g.acceptance_nonnegative μ

theorem binaryRow_normalized (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∑ b : Bool, g.binaryRow μ b) = 1 := by
  simp [binaryRow]

def productValue (ω : Ω × Ω) : ℝ := g.value ω.1 * g.value ω.2

theorem productValue_measurable : Measurable g.productValue :=
  (g.measurable.comp measurable_fst).mul (g.measurable.comp measurable_snd)

theorem productValue_nonnegative (ω : Ω × Ω) : 0 ≤ g.productValue ω :=
  mul_nonneg (g.nonnegative ω.1) (g.nonnegative ω.2)

theorem productValue_le_one (ω : Ω × Ω) : g.productValue ω ≤ 1 := by
  exact mul_le_one₀ (g.atMostOne ω.1) (g.nonnegative ω.2) (g.atMostOne ω.2)

theorem productValue_integrable (μ : Measure (Ω × Ω)) [IsFiniteMeasure μ] :
    Integrable g.productValue μ := by
  apply Integrable.of_bound g.productValue_measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (g.productValue_nonnegative ω)]
    exact g.productValue_le_one ω

end Effect

variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- Product covariance concerns the full latent measures. Effect invariance is
a separate pointwise dual-channel premise. -/
structure Contract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  preparation : V → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  effect : Effect Ω
  operation : V × V → V × V
  channel : Kernel (Ω × Ω) (Ω × Ω)
  markov : IsMarkovKernel channel
  covariance : ∀ p, channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
    (preparation (operation p).1).prod (preparation (operation p).2)
  invariant : ∀ ω, ∫ ξ, effect.productValue ξ ∂channel ω = effect.productValue ω

namespace Contract

variable (D : Contract V Ω)

def response (x : V) : ℝ := D.effect.acceptance (D.preparation x)

theorem response_event (x : V) :
    (D.effect.binaryKernel ∘ₘ D.preparation x) {true} = ENNReal.ofReal (D.response x) := by
  letI := D.probability x
  exact D.effect.binaryKernel_comp_true _

/-- The channel's full product covariance and dual-effect invariance imply this
law. Conservation of the desired response product is not assumed. -/
theorem response_product (p : V × V) :
    D.response (D.operation p).1 * D.response (D.operation p).2 =
      D.response p.1 * D.response p.2 := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsMarkovKernel D.channel := D.markov
  let μ := (D.preparation p.1).prod (D.preparation p.2)
  have hi := D.effect.productValue_integrable (D.channel ∘ₘ μ)
  have hc : (∫ ξ, D.effect.productValue ξ ∂D.channel ∘ₘ μ) =
      ∫ ω, (∫ ξ, D.effect.productValue ξ ∂D.channel ω) ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    simpa only [Kernel.const_apply] using ProbabilityTheory.Kernel.integral_comp hi
  calc
    D.response (D.operation p).1 * D.response (D.operation p).2 =
        ∫ ξ, D.effect.productValue ξ ∂
          (D.preparation (D.operation p).1).prod (D.preparation (D.operation p).2) :=
      (integral_prod_mul D.effect.value D.effect.value).symm
    _ = ∫ ξ, D.effect.productValue ξ ∂D.channel ∘ₘ μ := by rw [D.covariance p]
    _ = ∫ ω, (∫ ξ, D.effect.productValue ξ ∂D.channel ω) ∂μ := hc
    _ = ∫ ω, D.effect.productValue ω ∂μ := by simp_rw [D.invariant]
    _ = D.response p.1 * D.response p.2 := integral_prod_mul _ _

/-- A defined log-response relative to a chosen reference preparation. -/
def weight (reference : V) (x : V) : ℝ :=
  -Real.log (D.response x / D.response reference)

theorem weight_reference (reference : V) (hpositive : 0 < D.response reference) :
    D.weight reference reference = 0 := by
  simp [weight, ne_of_gt hpositive]

theorem weight_nonnegative (reference : V) (hpositive : ∀ x, 0 < D.response x)
    (hmaximal : ∀ x, D.response x ≤ D.response reference) (x : V) :
    0 ≤ D.weight reference x := by
  exact neg_nonneg.mpr (Real.log_nonpos
    (div_pos (hpositive x) (hpositive reference)).le
    ((div_le_one (hpositive reference)).mpr (hmaximal x)))

theorem weight_pair_conserved (reference : V) (hpositive : ∀ x, 0 < D.response x)
    (p : V × V) :
    D.weight reference (D.operation p).1 + D.weight reference (D.operation p).2 =
      D.weight reference p.1 + D.weight reference p.2 := by
  have h := congrArg Real.log (D.response_product p)
  rw [Real.log_mul (ne_of_gt (hpositive _)) (ne_of_gt (hpositive _)),
    Real.log_mul (ne_of_gt (hpositive _)) (ne_of_gt (hpositive _))] at h
  simp only [weight, Real.log_div (ne_of_gt (hpositive _)) (ne_of_gt (hpositive _))]
  linarith

end Contract
end
end IDT.QMClosure.InvariantEffectReadoutBridge
