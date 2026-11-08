import Proofs.QMClosure.ProductReferenceEntropyDecomposition
import Proofs.QMClosure.ClassicalStatisticalProcessBridge

/-!
# Reference-preserving processing forces output independence

A common Markov kernel preserves a product reference measure. Its output on each
independent pair has the two preparation marginals prescribed by a raw operation
whose square exchanges the inputs. Finite relative entropy to the reference
forces the output to be independent and conserves summed reference entropy.

The raw carrier has no measurable structure. Pairwise finite relative entropy,
a chosen raw origin, and a fixed raw diagonal are separate adapter inputs.
The common kernel expresses the physical contract. This argument does not prove
that commonality is a mathematically minimal hypothesis.
-/

namespace IDT.QMClosure.ReferenceEntropyFactorization

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open RelativeEntropyDataProcessing ProductReferenceEntropyDecomposition
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- A square root of swap commutes with swap on the raw carrier. -/
theorem operation_commutes_swap (F : V × V → V × V)
    (square : ∀ p, F (F p) = p.swap) (p : V × V) :
    F p.swap = (F p).swap := by
  calc
    F p.swap = F (F (F p)) := congrArg F (square p).symm
    _ = (F p).swap := square (F p)

/-- Pointwise sample-kernel swap symmetry passes to arbitrary input measures. -/
theorem channel_comp_map_swap (κ : Kernel (Ω × Ω) (Ω × Ω))
    (symmetric : ∀ s, κ s.swap = (κ s).map Prod.swap) (μ : Measure (Ω × Ω)) :
    κ ∘ₘ (μ.map Prod.swap) = (κ ∘ₘ μ).map Prod.swap := by
  have hκ : κ.comap Prod.swap measurable_swap = κ.map Prod.swap := by
    ext s t ht
    simpa only [Kernel.comap_apply', Kernel.map_apply' _ measurable_swap _ ht,
      Measure.map_apply measurable_swap ht] using congrArg (fun ν : Measure (Ω × Ω) => ν t)
        (symmetric s)
  calc
    κ ∘ₘ (μ.map Prod.swap) = (κ ∘ₖ Kernel.const Unit (μ.map Prod.swap)) () := rfl
    _ = ((κ.comap Prod.swap measurable_swap) ∘ₖ Kernel.const Unit μ) () := by
      rw [← Kernel.map_const μ measurable_swap, Kernel.comp_map]
    _ = (κ.map Prod.swap) ∘ₘ μ := by rw [hκ]; rfl
    _ = (κ ∘ₘ μ).map Prod.swap := (Measure.map_comp μ κ measurable_swap).symm

/-- Sample-kernel symmetry and first-marginal covariance supply the second marginal. -/
theorem secondMarginal_of_first (K : V → Measure Ω)
    (probability : ∀ x, IsProbabilityMeasure (K x))
    (F : V × V → V × V) (square : ∀ p, F (F p) = p.swap)
    (κ : Kernel (Ω × Ω) (Ω × Ω))
    (symmetric : ∀ s, κ s.swap = (κ s).map Prod.swap)
    (first : ∀ p, (κ ∘ₘ ((K p.1).prod (K p.2))).fst = K (F p).1)
    (p : V × V) :
    (κ ∘ₘ ((K p.1).prod (K p.2))).snd = K (F p).2 := by
  letI (x : V) : IsProbabilityMeasure (K x) := probability x
  have hswap : κ ∘ₘ ((K p.swap.1).prod (K p.swap.2)) =
      (κ ∘ₘ ((K p.1).prod (K p.2))).map Prod.swap := by
    rw [← Measure.prod_swap]
    exact channel_comp_map_swap κ symmetric _
  have h := first p.swap
  rw [hswap, Measure.fst_map_swap, operation_commutes_swap F square p] at h
  exact h

/-- Marginal covariance and reference preservation, before output independence. -/
structure Contract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  preparation : V → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  reference : Measure Ω
  referenceProbability : IsProbabilityMeasure reference
  finiteReferenceEntropy : ∀ x, klDiv (preparation x) reference ≠ ∞
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  channel : Kernel (Ω × Ω) (Ω × Ω)
  markov : IsMarkovKernel channel
  referencePreserving : channel ∘ₘ (reference.prod reference) = reference.prod reference
  firstMarginal : ∀ p,
    (channel ∘ₘ ((preparation p.1).prod (preparation p.2))).fst =
      preparation (operation p).1
  secondMarginal : ∀ p,
    (channel ∘ₘ ((preparation p.1).prod (preparation p.2))).snd =
      preparation (operation p).2

namespace Contract

variable (D : Contract V Ω)

def input (p : V × V) : Measure (Ω × Ω) :=
  (D.preparation p.1).prod (D.preparation p.2)

def output (p : V × V) : Measure (Ω × Ω) := D.channel ∘ₘ D.input p

def referenceEntropy (p : V × V) : ℝ≥0∞ :=
  klDiv (D.preparation p.1) D.reference + klDiv (D.preparation p.2) D.reference

def mutualInformation (p : V × V) : ℝ≥0∞ :=
  klDiv (D.output p) ((D.output p).fst.prod (D.output p).snd)

theorem referenceEntropy_ne_top (p : V × V) : D.referenceEntropy p ≠ ∞ :=
  ENNReal.add_ne_top.mpr ⟨D.finiteReferenceEntropy _, D.finiteReferenceEntropy _⟩

theorem input_reference_entropy (p : V × V) :
    klDiv (D.input p) (D.reference.prod D.reference) = D.referenceEntropy p := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsProbabilityMeasure D.reference := D.referenceProbability
  exact klDiv_prod _ _ _ _

/-- Actual reference-relative data processing, with finite input entropy. -/
theorem output_reference_entropy_le (p : V × V) :
    klDiv (D.output p) (D.reference.prod D.reference) ≤ D.referenceEntropy p := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsProbabilityMeasure D.reference := D.referenceProbability
  letI : IsMarkovKernel D.channel := D.markov
  letI : IsProbabilityMeasure (D.input p) := by
    dsimp [input]
    infer_instance
  have h := klDiv_markov_le (D.input p) (D.reference.prod D.reference) D.channel
  rw [D.referencePreserving, D.input_reference_entropy] at h
  exact h

/-- The output entropy splits into its dependence and its prescribed marginals. -/
theorem output_reference_decomposition (p : V × V) :
    klDiv (D.output p) (D.reference.prod D.reference) =
      D.mutualInformation p + D.referenceEntropy (D.operation p) := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsProbabilityMeasure D.reference := D.referenceProbability
  letI : IsMarkovKernel D.channel := D.markov
  letI : IsProbabilityMeasure (D.input p) := by
    dsimp [input]
    infer_instance
  letI : IsProbabilityMeasure (D.output p) := by
    dsimp [output]
    infer_instance
  have h := product_reference_decomposition (D.output p) D.reference D.reference
  simpa only [mutualInformation, referenceEntropy, output, input,
    D.firstMarginal p, D.secondMarginal p, add_assoc] using h

/-- Dependence and output marginal entropy share the finite input budget. -/
theorem entropy_budget (p : V × V) :
    D.mutualInformation p + D.referenceEntropy (D.operation p) ≤
      D.referenceEntropy p := by
  rw [← D.output_reference_decomposition]
  exact D.output_reference_entropy_le p

theorem referenceEntropy_nonincreasing (p : V × V) :
    D.referenceEntropy (D.operation p) ≤ D.referenceEntropy p := by
  calc
    D.referenceEntropy (D.operation p) = 0 + D.referenceEntropy (D.operation p) :=
      (zero_add _).symm
    _ ≤ D.mutualInformation p + D.referenceEntropy (D.operation p) :=
      add_le_add (zero_le _) le_rfl
    _ ≤ D.referenceEntropy p := D.entropy_budget p

/-- Square-swap closes the entropy cycle without an inverse-channel premise. -/
theorem referenceEntropy_conserved (p : V × V) :
    D.referenceEntropy (D.operation p) = D.referenceEntropy p := by
  apply le_antisymm (D.referenceEntropy_nonincreasing p)
  have h := D.referenceEntropy_nonincreasing (D.operation p)
  simpa only [D.square p, referenceEntropy, Prod.fst_swap, Prod.snd_swap, add_comm]
    using h

/-- Finite ENNReal cancellation forces the output dependence to vanish. -/
theorem mutualInformation_eq_zero (p : V × V) : D.mutualInformation p = 0 := by
  have h := D.entropy_budget p
  rw [D.referenceEntropy_conserved p] at h
  have hc : D.mutualInformation p + D.referenceEntropy p ≤
      0 + D.referenceEntropy p := by simpa only [zero_add] using h
  exact le_antisymm
    ((ENNReal.add_le_add_iff_right (D.referenceEntropy_ne_top p)).mp hc) (zero_le _)

/-- Both prescribed marginals are jointly realized as their independent product. -/
theorem covariance (p : V × V) :
    D.output p = (D.preparation (D.operation p).1).prod
      (D.preparation (D.operation p).2) := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsMarkovKernel D.channel := D.markov
  letI : IsProbabilityMeasure (D.input p) := by
    dsimp [input]
    infer_instance
  letI : IsProbabilityMeasure (D.output p) := by
    dsimp [output]
    infer_instance
  have h : D.output p = (D.output p).fst.prod (D.output p).snd :=
    klDiv_eq_zero_iff.mp (D.mutualInformation_eq_zero p)
  simpa only [output, input, D.firstMarginal p, D.secondMarginal p] using h

/-- Reference-relative data processing is saturated by every input pair. -/
theorem reference_dpi_equality (p : V × V) :
    klDiv (D.output p) (D.channel ∘ₘ (D.reference.prod D.reference)) =
      klDiv (D.input p) (D.reference.prod D.reference) := by
  rw [D.referencePreserving, D.output_reference_decomposition,
    D.mutualInformation_eq_zero, zero_add, D.referenceEntropy_conserved,
    D.input_reference_entropy]

/-- Reconstruction additionally requires a chosen raw origin, fixed diagonal,
and finite directed pairwise KL. None is inferred from reference finiteness. -/
def classicalProcess (x0 : V)
    (transparent : ∀ x, D.operation (x, x) = (x, x))
    (finiteEntropy : ∀ x y, klDiv (D.preparation x) (D.preparation y) ≠ ∞) :
    ClassicalStatisticalProcessBridge.Contract V Ω where
  preparation := D.preparation
  probability := D.probability
  finiteEntropy := finiteEntropy
  chosenZero := x0
  operation := D.operation
  square := D.square
  transparent := transparent
  channel := D.channel
  markov := D.markov
  covariance := D.covariance

end Contract
end
end IDT.QMClosure.ReferenceEntropyFactorization
