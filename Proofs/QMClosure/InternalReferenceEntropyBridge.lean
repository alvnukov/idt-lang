import Proofs.QMClosure.InternalReferenceSupportBridge
import Proofs.QMClosure.LikelihoodTransportSaturation
import Proofs.QMClosure.LogDensityProcessTransport
import Proofs.QMClosure.RelativeEntropyMomentTransfer

/-!
# Finite pairwise entropy from an internal preparation reference

A transparent reference-entropy factorization contract whose reference is a
chosen preparation has finite directed relative entropy between every pair of
preparations. The proof derives likelihood transport from affinity saturation,
then realizes a reciprocal quarter-density moment by an actual preparation.

The chosen reference preparation has log likelihood zero relative to itself.
This is a statistical normalization statement.
-/

namespace IDT.QMClosure.InternalReferenceEntropyBridge

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open LikelihoodTransportSaturation
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

private theorem llr_product (P Q α : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure α]
    (hP : P ≪ α) (hQ : Q ≪ α) (hαP : α ≪ P) (hαQ : α ≪ Q) :
    llr (P.prod Q) (α.prod α) =ᵐ[α.prod α]
      fun s => llr P α s.1 + llr Q α s.2 := by
  have hdensity : (α.prod α).withDensity
      (fun s => P.rnDeriv α s.1 * Q.rnDeriv α s.2) = P.prod Q := by
    rw [← prod_withDensity (Measure.measurable_rnDeriv P α)
      (Measure.measurable_rnDeriv Q α),
      Measure.withDensity_rnDeriv_eq P α hP, Measure.withDensity_rnDeriv_eq Q α hQ]
  have hd : (P.prod Q).rnDeriv (α.prod α) =ᵐ[α.prod α]
      fun s => P.rnDeriv α s.1 * Q.rnDeriv α s.2 := by
    rw [← hdensity]
    exact Measure.rnDeriv_withDensity _ (by fun_prop)
  filter_upwards [hd,
    Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_pos' hαP),
    Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_pos' hαQ),
    Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_ne_top P α),
    Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_ne_top Q α)]
      with s hs hp hq hpfin hqfin
  have hp' : (P.rnDeriv α s.1).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hp.ne' hpfin)
  have hq' : (Q.rnDeriv α s.2).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hq.ne' hqfin)
  simp only [llr, hs, ENNReal.toReal_mul, Real.log_mul hp' hq']

namespace ReferenceContract

variable (D : ReferenceEntropyFactorization.Contract V Ω)

local instance : IsProbabilityMeasure D.reference := D.referenceProbability
local instance (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
local instance : IsMarkovKernel D.channel := D.markov
local instance (p : V × V) : IsProbabilityMeasure (D.input p) := by
  dsimp [ReferenceEntropyFactorization.Contract.input]
  infer_instance

private theorem preparation_ac_reference (x : V) : D.preparation x ≪ D.reference :=
  (klDiv_ne_top_iff.mp (D.finiteReferenceEntropy x)).1

private theorem input_ac_reference (p : V × V) :
    D.input p ≪ D.reference.prod D.reference :=
  (preparation_ac_reference D p.1).prod (preparation_ac_reference D p.2)

private theorem affinity_input_swap (p : V × V) :
    affinity (D.input p.swap) (D.reference.prod D.reference) =
      affinity (D.input p) (D.reference.prod D.reference) := by
  apply le_antisymm
  · have h := affinity_map_le (D.input p.swap) (D.reference.prod D.reference)
      (input_ac_reference D p.swap) Prod.swap measurable_swap
    simpa only [ReferenceEntropyFactorization.Contract.input, Measure.prod_swap,
      Prod.swap] using h
  · have h := affinity_map_le (D.input p) (D.reference.prod D.reference)
      (input_ac_reference D p) Prod.swap measurable_swap
    simpa only [ReferenceEntropyFactorization.Contract.input, Measure.prod_swap,
      Prod.swap] using h

private theorem affinity_input_le (p : V × V) :
    affinity (D.input p) (D.reference.prod D.reference) ≤
      affinity (D.input (D.operation p)) (D.reference.prod D.reference) := by
  have h := affinity_markov_le (D.input p) (D.reference.prod D.reference)
    (input_ac_reference D p) D.channel
  rw [D.referencePreserving] at h
  change affinity (D.input p) (D.reference.prod D.reference) ≤
    affinity (D.output p) (D.reference.prod D.reference) at h
  simpa only [D.covariance p, ReferenceEntropyFactorization.Contract.input] using h

/-- The square-of-swap cycle saturates affinity processing for each input. -/
theorem affinity_saturated (p : V × V) :
    affinity (D.input p) (D.reference.prod D.reference) =
      affinity (D.channel ∘ₘ D.input p)
        (D.channel ∘ₘ (D.reference.prod D.reference)) := by
  rw [D.referencePreserving]
  change affinity (D.input p) (D.reference.prod D.reference) =
    affinity (D.output p) (D.reference.prod D.reference)
  rw [D.covariance p]
  change affinity (D.input p) (D.reference.prod D.reference) =
    affinity (D.input (D.operation p)) (D.reference.prod D.reference)
  apply le_antisymm (affinity_input_le D p)
  have h := affinity_input_le D (D.operation p)
  simpa only [D.square p, affinity_input_swap D p] using h

private theorem input_ae {P : Ω × Ω → Prop}
    (h : ∀ᵐ s ∂D.reference.prod D.reference, P s) :
    ∀ᵐ z ∂((D.reference.prod D.reference) ⊗ₘ D.channel), P z.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  change ∀ᵐ s ∂((D.reference.prod D.reference) ⊗ₘ D.channel).fst, P s
  simpa only [Measure.fst_compProd] using h

private theorem output_ae {P : Ω × Ω → Prop}
    (h : ∀ᵐ s ∂D.reference.prod D.reference, P s) :
    ∀ᵐ z ∂((D.reference.prod D.reference) ⊗ₘ D.channel), P z.2 := by
  apply ae_of_ae_map measurable_snd.aemeasurable
  change ∀ᵐ s ∂((D.reference.prod D.reference) ⊗ₘ D.channel).snd, P s
  simpa only [Measure.snd_compProd, D.referencePreserving] using h

private theorem input_log_product (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) (p : V × V) :
    llr (D.input p) (D.reference.prod D.reference) =ᵐ[D.reference.prod D.reference]
      fun s => llr (D.preparation p.1) D.reference s.1 +
        llr (D.preparation p.2) D.reference s.2 := by
  have hreverse (x : V) : D.reference ≪ D.preparation x := by
    rw [internal]
    exact InternalReferenceSupportBridge.ReferenceContract.mutually_absolutelyContinuous
      D x₀ internal transparent x₀ x
  exact llr_product _ _ _ (preparation_ac_reference D p.1)
    (preparation_ac_reference D p.2) (hreverse p.1) (hreverse p.2)

/-- Actual log likelihood is transported along the common forward channel. -/
theorem log_transport (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) (p : V × V) :
    ∀ᵐ z ∂((D.reference.prod D.reference) ⊗ₘ D.channel),
      llr (D.preparation p.1) D.reference z.1.1 +
        llr (D.preparation p.2) D.reference z.1.2 =
      llr (D.preparation (D.operation p).1) D.reference z.2.1 +
        llr (D.preparation (D.operation p).2) D.reference z.2.2 := by
  have hsat := likelihood_markov_of_affinity_eq (D.input p)
    (D.reference.prod D.reference) (input_ac_reference D p) D.channel
    (affinity_saturated D p)
  change (fun z => ((D.input p).rnDeriv (D.reference.prod D.reference) z.1).toReal)
    =ᵐ[(D.reference.prod D.reference) ⊗ₘ D.channel]
      fun z => ((D.output p).rnDeriv
        (D.channel ∘ₘ (D.reference.prod D.reference)) z.2).toReal at hsat
  rw [D.referencePreserving, D.covariance p] at hsat
  filter_upwards [hsat, input_ae D (input_log_product D x₀ internal transparent p),
    output_ae D (input_log_product D x₀ internal transparent (D.operation p))]
      with z hs hi ho
  calc
    _ = llr (D.input p) (D.reference.prod D.reference) z.1 := hi.symm
    _ = llr (D.input (D.operation p)) (D.reference.prod D.reference) z.2 :=
      congrArg Real.log hs
    _ = _ := ho

/-- The finite log-elimination contract obtained from the statistical contract.
Its chosen origin is precisely the chosen reference preparation. -/
def logDensityProcess (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) :
    LogDensityProcessTransport.Contract V Ω where
  reference := D.reference
  referenceProbability := D.referenceProbability
  coupling := (D.reference.prod D.reference) ⊗ₘ D.channel
  couplingProbability := inferInstance
  inputMarginal := Measure.fst_compProd _ _
  outputMarginal := by
    change ((D.reference.prod D.reference) ⊗ₘ D.channel).snd = _
    rw [Measure.snd_compProd, D.referencePreserving]
  origin := x₀
  operation := D.operation
  square := D.square
  diagonal := transparent
  logDensity x := llr (D.preparation x) D.reference
  measurableLogDensity x := measurable_llr _ _
  originLogDensity := by
    rw [← internal]
    exact llr_self D.reference
  transport := log_transport D x₀ internal transparent

/-- An actual preparation supplies the reciprocal quarter-density moment. -/
theorem reciprocal_quarter_moment (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) (y : V) :
    Integrable (fun s => Real.exp (-llr (D.preparation y) D.reference s / 4))
      D.reference := by
  let L := logDensityProcess D x₀ internal transparent
  let z := L.a (L.a (L.a (L.a y)))
  obtain ⟨c, hc⟩ := L.reciprocal_log_witness y
  have hreverse : D.reference ≪ D.preparation z := by
    rw [internal]
    exact InternalReferenceSupportBridge.ReferenceContract.mutually_absolutelyContinuous
      D x₀ internal transparent x₀ z
  have hdensity : Integrable
      (fun s => ((D.preparation z).rnDeriv D.reference s).toReal) D.reference :=
    Measure.integrable_toReal_rnDeriv
  have hexp : Integrable (fun s => Real.exp (llr (D.preparation z) D.reference s))
      D.reference := hdensity.congr (exp_llr_of_ac' _ _ hreverse).symm
  apply (hexp.const_mul (Real.exp (-c))).congr
  filter_upwards [hc] with s hs
  change llr (D.preparation z) D.reference s =
    -llr (D.preparation y) D.reference s / 4 + c at hs
  rw [← Real.exp_add]
  congr 1
  linarith

/-- Every directed pairwise relative entropy is finite under an internal
preparation reference and a transparent raw diagonal. -/
theorem finite_pairwise_entropy (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) (x y : V) :
    klDiv (D.preparation x) (D.preparation y) ≠ ∞ := by
  have hreverse : D.reference ≪ D.preparation y := by
    rw [internal]
    exact InternalReferenceSupportBridge.ReferenceContract.mutually_absolutelyContinuous
      D x₀ internal transparent x₀ y
  exact RelativeEntropyMomentTransfer.klDiv_ne_top_of_reciprocal_quarter_moment
    _ _ _ (D.finiteReferenceEntropy x) (preparation_ac_reference D y) hreverse
    (reciprocal_quarter_moment D x₀ internal transparent y)

/-- The existing classical-process adapter with its pairwise entropy input
proved from the internal preparation reference. -/
def classicalProcess (x₀ : V)
    (internal : D.reference = D.preparation x₀)
    (transparent : ∀ x, D.operation (x, x) = (x, x)) :
    ClassicalStatisticalProcessBridge.Contract V Ω :=
  D.classicalProcess x₀ transparent (finite_pairwise_entropy D x₀ internal transparent)

end ReferenceContract

/-- A common statistical process with one-way finite entropy to its chosen
reference preparation. Full product covariance is part of this interface. -/
structure PointedContract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  preparation : V → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  chosenReference : V
  finiteReferenceEntropy : ∀ x,
    klDiv (preparation x) (preparation chosenReference) ≠ ∞
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)
  channel : Kernel (Ω × Ω) (Ω × Ω)
  markov : IsMarkovKernel channel
  covariance : ∀ p, channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
    (preparation (operation p).1).prod (preparation (operation p).2)

namespace PointedContract

variable (D : PointedContract V Ω)

/-- The chosen preparation supplies the preserved product reference. -/
def referenceFactorization : ReferenceEntropyFactorization.Contract V Ω where
  preparation := D.preparation
  probability := D.probability
  reference := D.preparation D.chosenReference
  referenceProbability := D.probability D.chosenReference
  finiteReferenceEntropy := D.finiteReferenceEntropy
  operation := D.operation
  square := D.square
  channel := D.channel
  markov := D.markov
  referencePreserving := by
    simpa only [D.transparent D.chosenReference] using
      D.covariance (D.chosenReference, D.chosenReference)
  firstMarginal := by
    intro p
    letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
    rw [D.covariance p]
    exact Measure.fst_prod
  secondMarginal := by
    intro p
    letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
    rw [D.covariance p]
    exact Measure.snd_prod

/-- One-way finite entropy to the chosen reference preparation suffices for
finite directed entropy between every pair. -/
theorem finite_pairwise_entropy (x y : V) :
    klDiv (D.preparation x) (D.preparation y) ≠ ∞ :=
  ReferenceContract.finite_pairwise_entropy D.referenceFactorization
    D.chosenReference rfl D.transparent x y

/-- The legacy process contract with its pairwise finite entropy derived. -/
def classicalProcess : ClassicalStatisticalProcessBridge.Contract V Ω :=
  ReferenceContract.classicalProcess D.referenceFactorization
    D.chosenReference rfl D.transparent

end PointedContract
end
end IDT.QMClosure.InternalReferenceEntropyBridge
