import Proofs.QMClosure.NativeMarginalProcessControls
import Mathlib.Probability.Distributions.Uniform

/-!
# Sharp controls for reference-entropy factorization

These are actual finite kernels and Gaussian pushforwards. The failed
finiteness control also fails absolute continuity. No separate necessity of
log-density integrability under absolute continuity is asserted.
-/
namespace IDT.QMClosure.ReferenceEntropyFactorizationControls

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open NativeGaussianStatisticalProcess
open scoped ENNReal NNReal

private theorem product_singleton {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [SFinite ν] (a : A) (b : B) :
    μ.prod ν {(a, b)} = μ {a} * ν {b} := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

private theorem finite_comp_singleton {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
    [MeasurableSingletonClass B] (κ : Kernel A B) (μ : Measure A) (b : B) :
    (κ ∘ₘ μ) {b} = ∑ a, μ {a} * κ a {b} := by
  rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul, tsum_fintype]

private theorem bool_integrable (μ : Measure Bool) [IsProbabilityMeasure μ]
    (f : Bool → ℝ) : Integrable f μ := by
  apply Integrable.of_bound (measurable_of_finite f).aestronglyMeasurable
    (max ‖f false‖ ‖f true‖)
  exact Filter.Eventually.of_forall fun b => by
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _

def fair : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance fair_probability : IsProbabilityMeasure fair := by
  unfold fair
  infer_instance

@[simp] theorem fair_singleton (b : Bool) : fair {b} = 1 / 2 := by
  simp [fair, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

def copyFirst (p : Bool × Bool) : Bool × Bool := (p.1, p.1)

def copyChannel : Kernel (Bool × Bool) (Bool × Bool) :=
  Kernel.deterministic copyFirst (measurable_of_finite _)

instance copyChannel_markov : IsMarkovKernel copyChannel := by
  unfold copyChannel
  infer_instance

def unitOperation (p : Unit × Unit) : Unit × Unit := p

theorem unitOperation_square (p : Unit × Unit) :
    unitOperation (unitOperation p) = p.swap := by
  rcases p with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem copy_firstMarginal :
    (copyChannel ∘ₘ fair.prod fair).map Prod.fst = fair := by
  rw [show copyChannel ∘ₘ fair.prod fair = (fair.prod fair).map copyFirst from
    Measure.deterministic_comp_eq_map (measurable_of_finite _)]
  rw [Measure.map_map measurable_fst (measurable_of_finite _)]
  change (fair.prod fair).map Prod.fst = fair
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem copy_secondMarginal :
    (copyChannel ∘ₘ fair.prod fair).map Prod.snd = fair := by
  rw [show copyChannel ∘ₘ fair.prod fair = (fair.prod fair).map copyFirst from
    Measure.deterministic_comp_eq_map (measurable_of_finite _)]
  rw [Measure.map_map measurable_snd (measurable_of_finite _)]
  change (fair.prod fair).map Prod.fst = fair
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem copy_offDiagonal :
    (copyChannel ∘ₘ fair.prod fair) {(false, true)} = 0 := by
  rw [finite_comp_singleton]
  norm_num [copyChannel, copyFirst, Kernel.deterministic_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem copy_not_product : copyChannel ∘ₘ fair.prod fair ≠ fair.prod fair := by
  intro h
  have hh := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, true)}) h
  dsimp only at hh
  rw [copy_offDiagonal, product_singleton, fair_singleton, fair_singleton] at hh
  norm_num at hh

/-- Omitting reference invariance permits dependence despite zero reference KL. -/
theorem no_invariant_reference :
    klDiv fair fair = 0 ∧
      (∀ p, unitOperation (unitOperation p) = p.swap) ∧
      (copyChannel ∘ₘ fair.prod fair).map Prod.fst = fair ∧
      (copyChannel ∘ₘ fair.prod fair).map Prod.snd = fair ∧
      copyChannel ∘ₘ fair.prod fair ≠ fair.prod fair :=
  ⟨klDiv_self fair, unitOperation_square, copy_firstMarginal,
    copy_secondMarginal, copy_not_product⟩

def singularReference : Measure Bool := Measure.dirac false

instance singularReference_probability : IsProbabilityMeasure singularReference := by
  unfold singularReference
  infer_instance

theorem copy_preserves_singular_reference :
    copyChannel ∘ₘ singularReference.prod singularReference =
      singularReference.prod singularReference := by
  simp [singularReference, copyChannel, copyFirst, Measure.dirac_prod_dirac,
    Measure.deterministic_comp_eq_map, Measure.map_dirac]

theorem fair_not_ac_singular_reference : ¬ fair ≪ singularReference := by
  intro h
  have hh := h (show singularReference {true} = 0 by simp [singularReference])
  rw [fair_singleton] at hh
  norm_num at hh

theorem fair_singular_reference_kl_top : klDiv fair singularReference = ∞ :=
  klDiv_of_not_ac fair_not_ac_singular_reference

/-- This omission violates both finite reference KL and absolute continuity. -/
theorem no_finite_reference_entropy :
    copyChannel ∘ₘ singularReference.prod singularReference =
      singularReference.prod singularReference ∧
      klDiv fair singularReference = ∞ ∧
      (copyChannel ∘ₘ fair.prod fair).map Prod.fst = fair ∧
      (copyChannel ∘ₘ fair.prod fair).map Prod.snd = fair ∧
      copyChannel ∘ₘ fair.prod fair ≠ fair.prod fair :=
  ⟨copy_preserves_singular_reference, fair_singular_reference_kl_top,
    copy_firstMarginal, copy_secondMarginal, copy_not_product⟩

/-! A shared fair flip erases marginal bias but preserves correlation. -/

private def quarterEffect : InvariantEffectReadoutBridge.Effect Bool where
  value := fun b => if b then 1 / 2 else 1 / 4
  measurable := measurable_of_finite _
  nonnegative := fun b => by cases b <;> norm_num
  atMostOne := fun b => by cases b <;> norm_num

def biasedPreparation (b : Bool) : Measure Bool := quarterEffect.binaryKernel b

instance biasedPreparation_probability (b : Bool) :
    IsProbabilityMeasure (biasedPreparation b) := by
  unfold biasedPreparation
  infer_instance

@[simp] theorem biasedPreparation_singleton (x b : Bool) :
    biasedPreparation x {b} =
      if x then 1 / 2 else if b then 1 / 4 else 3 / 4 := by
  cases x <;> cases b <;>
    norm_num [biasedPreparation, quarterEffect,
      InvariantEffectReadoutBridge.Effect.binaryKernel, ENNReal.ofReal_div_of_pos]

theorem biasedPreparation_fair : biasedPreparation true = fair := by
  apply Measure.ext_of_singleton
  intro b
  simp

def sharedFlipChannel : Kernel (Bool × Bool) (Bool × Bool) where
  toFun p := (1 / 2 : ℝ≥0∞) • Measure.dirac p +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (!p.1, !p.2)
  measurable' := measurable_of_finite _

instance sharedFlipChannel_markov : IsMarkovKernel sharedFlipChannel where
  isProbabilityMeasure p := ⟨by
    norm_num [sharedFlipChannel, Kernel.coe_mk, Measure.add_apply, Measure.smul_apply,
      ENNReal.inv_two_add_inv_two]⟩

def collapseOperation (_ : Bool × Bool) : Bool × Bool := (true, true)

theorem sharedFlip_singleton (x y a b : Bool) :
    (sharedFlipChannel ∘ₘ (biasedPreparation x).prod (biasedPreparation y)) {(a, b)} =
      (1 / 2 : ℝ≥0∞) *
        (biasedPreparation x {a} * biasedPreparation y {b} +
          biasedPreparation x {!a} * biasedPreparation y {!b}) := by
  rw [finite_comp_singleton]
  cases a <;> cases b <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, product_singleton,
      sharedFlipChannel, Kernel.coe_mk, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff,
      Bool.not_false, Bool.not_true, Prod.mk.injEq, Bool.true_eq_false,
      Bool.false_eq_true, and_true, and_false, false_and, true_and, if_true, if_false,
      mul_zero, mul_one, zero_add, add_zero, Pi.one_apply,
      Prod.fst, Prod.snd] <;> ring

theorem sharedFlip_preserves_reference :
    sharedFlipChannel ∘ₘ fair.prod fair = fair.prod fair := by
  rw [← biasedPreparation_fair]
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [sharedFlip_singleton, product_singleton]
  simp only [biasedPreparation_singleton, if_true]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  (simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_inv]; norm_num)

private theorem finite_map_singleton {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
    [MeasurableSingletonClass B] [DecidableEq B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (b : B) :
    μ.map f {b} = ∑ a, μ {a} * if f a = b then 1 else 0 := by
  rw [← Measure.deterministic_comp_eq_map (μ := μ) (f := f) hf]
  rw [finite_comp_singleton]
  simp [Kernel.deterministic_apply, Measure.dirac_apply', Pi.single_apply, eq_comm]

theorem sharedFlip_firstMarginal (p : Bool × Bool) :
    (sharedFlipChannel ∘ₘ (biasedPreparation p.1).prod (biasedPreparation p.2)).map
      Prod.fst = biasedPreparation (collapseOperation p).1 := by
  apply Measure.ext_of_singleton
  intro b
  rw [finite_map_singleton _ _ measurable_fst]
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> cases b <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, sharedFlip_singleton, collapseOperation] <;>
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    (simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_inv]; norm_num)

theorem sharedFlip_secondMarginal (p : Bool × Bool) :
    (sharedFlipChannel ∘ₘ (biasedPreparation p.1).prod (biasedPreparation p.2)).map
      Prod.snd = biasedPreparation (collapseOperation p).2 := by
  apply Measure.ext_of_singleton
  intro b
  rw [finite_map_singleton _ _ measurable_snd]
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> cases b <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, sharedFlip_singleton, collapseOperation] <;>
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    (simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_inv]; norm_num)

theorem biasedPreparation_absolutelyContinuous (x y : Bool) :
    biasedPreparation x ≪ biasedPreparation y := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    have hp : 0 < biasedPreparation y {b} := by
      cases y <;> cases b <;> norm_num
    exact (not_le_of_gt hp) ((measure_mono (Set.singleton_subset_iff.mpr hb)).trans_eq hs)
  simp [he]

theorem biasedPreparation_finiteKL (x y : Bool) :
    klDiv (biasedPreparation x) (biasedPreparation y) ≠ ∞ :=
  klDiv_ne_top (biasedPreparation_absolutelyContinuous x y) (bool_integrable _ _)

theorem sharedFlip_joint_probabilities :
    (sharedFlipChannel ∘ₘ (biasedPreparation false).prod (biasedPreparation false))
        {(false, false)} = 5 / 16 ∧
    (sharedFlipChannel ∘ₘ (biasedPreparation false).prod (biasedPreparation false))
        {(false, true)} = 3 / 16 ∧
    (sharedFlipChannel ∘ₘ (biasedPreparation false).prod (biasedPreparation false))
        {(true, false)} = 3 / 16 ∧
    (sharedFlipChannel ∘ₘ (biasedPreparation false).prod (biasedPreparation false))
        {(true, true)} = 5 / 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [sharedFlip_singleton] <;>
    simp only [biasedPreparation_singleton, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] <;>
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    (simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_inv]; norm_num)

theorem sharedFlip_not_product :
    sharedFlipChannel ∘ₘ (biasedPreparation false).prod (biasedPreparation false) ≠
      (biasedPreparation (collapseOperation (false, false)).1).prod
        (biasedPreparation (collapseOperation (false, false)).2) := by
  intro h
  have hh := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, false)}) h
  dsimp only at hh
  rw [sharedFlip_joint_probabilities.1, product_singleton] at hh
  have hr := congrArg ENNReal.toReal hh
  norm_num [collapseOperation] at hr

theorem collapseOperation_square_fails :
    collapseOperation (collapseOperation (false, false)) ≠ (false, false).swap := by
  decide

/-! Finite reference KL does not entail pairwise finite KL. -/

open DetectorConservationOmissionControls in
def finiteReference : Measure Label := (PMF.uniformOfFintype Label).toMeasure

instance finiteReference_probability : IsProbabilityMeasure finiteReference := by
  unfold finiteReference
  infer_instance

open DetectorConservationOmissionControls in
@[simp] theorem finiteReference_singleton (x : Label) : finiteReference {x} = 1 / 5 := by
  simp [finiteReference, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

open DetectorConservationOmissionControls in
theorem dirac_finite_referenceKL (x : Label) :
    klDiv (diracPreparation x) finiteReference ≠ ∞ := by
  apply klDiv_ne_top
  · intro s hs
    have hx : x ∉ s := by
      intro hx
      have hh : finiteReference {x} ≤ finiteReference s :=
        measure_mono (Set.singleton_subset_iff.mpr hx)
      rw [finiteReference_singleton, hs] at hh
      norm_num at hh
    simp [diracPreparation, hx]
  · exact integrable_dirac (by simp)

open DetectorConservationOmissionControls in
theorem operation_four (p : Label × Label) :
    operation (operation (operation (operation p))) = p := by
  rw [operation_square, operation_square]
  rfl

open DetectorConservationOmissionControls in
theorem operation_preimage_singleton (q : Label × Label) :
    operation ⁻¹' {q} = {operation (operation (operation q))} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    have hh := congrArg (fun z => operation (operation (operation z))) h
    simpa only [operation_four] using hh
  · rintro rfl
    exact operation_four q

open DetectorConservationOmissionControls in
theorem dirac_channel_preserves_reference :
    deterministicChannel ∘ₘ finiteReference.prod finiteReference =
      finiteReference.prod finiteReference := by
  rw [show deterministicChannel ∘ₘ finiteReference.prod finiteReference =
    (finiteReference.prod finiteReference).map operation from
      Measure.deterministic_comp_eq_map (measurable_of_finite _)]
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    operation_preimage_singleton]
  rw [product_singleton, product_singleton]
  simp

open DetectorConservationOmissionControls in
/-- All reference hypotheses coexist with an infinite pairwise divergence. -/
theorem finite_reference_not_pairwise_finite :
    (∀ x, klDiv (diracPreparation x) finiteReference ≠ ∞) ∧
      deterministicChannel ∘ₘ finiteReference.prod finiteReference =
        finiteReference.prod finiteReference ∧
      klDiv (diracPreparation 0) (diracPreparation 1) = ∞ :=
  ⟨dirac_finite_referenceKL, dirac_channel_preserves_reference,
    diracPreparation_kl_top (by decide)⟩

/-! A negative native Gaussian mixer moves the observed diagonal laws. -/

def negativeMixer : PairSample →L[ℝ] PairSample := -G

def gaussianPreparation (m : Sample) : Measure Sample :=
  NativeIsotropicGaussianFamily.preparation 1 m

instance gaussianPreparation_probability (m : Sample) :
    IsProbabilityMeasure (gaussianPreparation m) := by
  unfold gaussianPreparation
  infer_instance

def negativeChannel : Kernel PairSample PairSample :=
  Kernel.deterministic negativeMixer negativeMixer.continuous.measurable

instance negativeChannel_markov : IsMarkovKernel negativeChannel := by
  unfold negativeChannel
  infer_instance

theorem negativeMixer_square (p : PairSample) :
    negativeMixer (negativeMixer p) = p.swap := by
  simp only [negativeMixer, ContinuousLinearMap.neg_apply, map_neg, neg_neg]
  exact NativeMarginalProcessControls.G_square p

theorem negativeMixer_swap (p : PairSample) :
    negativeMixer p.swap = (negativeMixer p).swap := by
  ext <;> simp [negativeMixer, G_apply] <;> ring

theorem negativeMixer_fullCovariance (p : PairSample) :
    negativeChannel ∘ₘ (gaussianPreparation p.1).prod (gaussianPreparation p.2) =
      (gaussianPreparation (negativeMixer p).1).prod
        (gaussianPreparation (negativeMixer p).2) := by
  rw [show negativeChannel ∘ₘ (gaussianPreparation p.1).prod (gaussianPreparation p.2) =
      ((gaussianPreparation p.1).prod (gaussianPreparation p.2)).map negativeMixer from
    Measure.deterministic_comp_eq_map negativeMixer.continuous.measurable]
  apply Measure.ext_of_charFunDual
  funext L
  unfold gaussianPreparation
  rw [charFunDual_map, NativeIsotropicGaussianFamily.charFunDual_preparation_prod,
    NativeIsotropicGaussianFamily.charFunDual_preparation_prod]
  have h := energy_comp_G L
  simp only [energy, ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.comp_apply, negativeMixer,
    ContinuousLinearMap.neg_apply, map_neg, neg_sq, Prod.mk.eta]
  congr 1
  have hc := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at hc ⊢
  linear_combination -(1 : ℂ) / 2 * hc

theorem negativeMixer_firstMarginal (p : PairSample) :
    (negativeChannel ∘ₘ (gaussianPreparation p.1).prod (gaussianPreparation p.2)).map
      Prod.fst = gaussianPreparation (negativeMixer p).1 := by
  rw [negativeMixer_fullCovariance]
  simp

theorem negativeMixer_secondMarginal (p : PairSample) :
    (negativeChannel ∘ₘ (gaussianPreparation p.1).prod (gaussianPreparation p.2)).map
      Prod.snd = gaussianPreparation (negativeMixer p).2 := by
  rw [negativeMixer_fullCovariance]
  simp

theorem gaussianPreparation_finiteKL (x y : Sample) :
    klDiv (gaussianPreparation x) (gaussianPreparation y) ≠ ∞ :=
  NativeIsotropicGaussianFamily.klDiv_preparation_ne_top 1 (by norm_num) x y

theorem negativeMixer_preserves_reference :
    negativeChannel ∘ₘ (gaussianPreparation 0).prod (gaussianPreparation 0) =
      (gaussianPreparation 0).prod (gaussianPreparation 0) := by
  rw [negativeMixer_fullCovariance (0, 0)]
  simp [negativeMixer, G_apply]
  rfl

theorem negativeMixer_diagonal (x : Sample) :
    negativeMixer (x, x) = (-x, -x) := by
  simp [negativeMixer, NativeIsotropicGaussianFamily.G_diagonal]

/-- Even finite pairwise KL and full covariance leave observed transparency open. -/
theorem negativeMixer_observed_diagonal_moves :
    gaussianPreparation (negativeMixer ((1, 0), (1, 0))).1 ≠
      gaussianPreparation (1, 0) := by
  rw [negativeMixer_diagonal]
  intro h
  have hm := (NativeIsotropicGaussianFamily.preparation_ext_iff 1 1
    (-(1, 0)) (1, 0)).mp h
  norm_num at hm

end
end IDT.QMClosure.ReferenceEntropyFactorizationControls
