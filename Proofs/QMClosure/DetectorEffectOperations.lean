import Proofs.QMClosure.InvariantEffectReadoutBridge

/-! Bounded measurable detector operations and separation of probability measures. -/
namespace IDT.QMClosure.DetectorEffectOperations

noncomputable section
open MeasureTheory
open InvariantEffectReadoutBridge

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The detector which accepts every sample. -/
def sure : Effect Ω where
  value := fun _ => 1
  measurable := measurable_const
  nonnegative := fun _ => by norm_num
  atMostOne := fun _ => le_refl _

/-- Rejection viewed as a detector effect. -/
def complement (g : Effect Ω) : Effect Ω where
  value := fun ω => 1 - g.value ω
  measurable := measurable_const.sub g.measurable
  nonnegative := fun ω => sub_nonneg.mpr (g.atMostOne ω)
  atMostOne := fun ω => by linarith [g.nonnegative ω]

/-- An equally weighted randomized choice of two detectors. -/
def average (g h : Effect Ω) : Effect Ω where
  value := fun ω => (g.value ω + h.value ω) / 2
  measurable := (g.measurable.add h.measurable).div_const 2
  nonnegative := fun ω => by linarith [g.nonnegative ω, h.nonnegative ω]
  atMostOne := fun ω => by linarith [g.atMostOne ω, h.atMostOne ω]

/-- The sharp detector of a measurable latent event. -/
def indicator (s : Set Ω) (hs : MeasurableSet s) : Effect Ω where
  value := s.indicator (fun _ => (1 : ℝ))
  measurable := measurable_const.indicator hs
  nonnegative := fun ω => by by_cases hw : ω ∈ s <;> simp [hw]
  atMostOne := fun ω => by by_cases hw : ω ∈ s <;> simp [hw]

@[simp] theorem acceptance_sure (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (sure : Effect Ω).acceptance μ = 1 := by
  simp [Effect.acceptance, sure]

@[simp] theorem acceptance_complement (g : Effect Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (complement g).acceptance μ = 1 - g.acceptance μ := by
  unfold Effect.acceptance complement
  rw [integral_sub (integrable_const 1) (g.integrable μ)]
  simp

@[simp] theorem acceptance_average (g h : Effect Ω) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    (average g h).acceptance μ = (g.acceptance μ + h.acceptance μ) / 2 := by
  unfold Effect.acceptance average
  rw [integral_div, integral_add (g.integrable μ) (h.integrable μ)]

@[simp] theorem acceptance_indicator (s : Set Ω) (hs : MeasurableSet s)
    (μ : Measure Ω) :
    (indicator s hs).acceptance μ = (μ s).toReal := by
  exact integral_indicator_one hs

/-- All bounded measurable binary detectors separate finite measures. -/
theorem measure_ext_of_acceptance_eq {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : Effect Ω, g.acceptance μ = g.acceptance ν) : μ = ν := by
  apply Measure.ext
  intro s hs
  have hi := h (indicator s hs)
  rw [acceptance_indicator, acceptance_indicator] at hi
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp hi

end
end IDT.QMClosure.DetectorEffectOperations
