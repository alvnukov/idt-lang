import Proofs.QMClosure.ReadoutScaffoldsDraft

namespace IDT
namespace QMClosure

/-!
V7 probability decomposition recovery.

The v7 research pass split "probability" into layers. This module preserves
that split in Lean so v8 does not collapse the old result back into one opaque
Born/probability obligation.

Nothing here proves the Born rule. The point is narrower: normalization is a
downstream readout layer over an already supplied measure/weight law and an
admissible context.
-/

structure V7ProbabilityLayerStack where
  actualizationWeights : Prop
  positiveMeasure : Prop
  admissibleReadoutContext : Prop
  contextNormalization : Prop
  exclusivityAdditivity : Prop
  coarseGrainingConsistency : Prop
  operationalEquivalence : Prop
  frequencyInterpretation : Prop
  noBornImport : Prop

def V7AdmissibleProbabilityReadout
    (stack : V7ProbabilityLayerStack) : Prop :=
  stack.actualizationWeights
    ∧ stack.positiveMeasure
    ∧ stack.admissibleReadoutContext
    ∧ stack.contextNormalization
    ∧ stack.exclusivityAdditivity
    ∧ stack.coarseGrainingConsistency
    ∧ stack.operationalEquivalence
    ∧ stack.frequencyInterpretation
    ∧ stack.noBornImport

theorem v7_probability_readout_requires_actualization_weights
    (stack : V7ProbabilityLayerStack) :
    V7AdmissibleProbabilityReadout stack →
      stack.actualizationWeights :=
  fun closed => closed.left

theorem v7_probability_readout_requires_positive_measure
    (stack : V7ProbabilityLayerStack) :
    V7AdmissibleProbabilityReadout stack →
      stack.positiveMeasure :=
  fun closed => closed.right.left

theorem v7_probability_readout_requires_admissible_context
    (stack : V7ProbabilityLayerStack) :
    V7AdmissibleProbabilityReadout stack →
      stack.admissibleReadoutContext :=
  fun closed => closed.right.right.left

theorem v7_probability_readout_requires_operational_equivalence
    (stack : V7ProbabilityLayerStack) :
    V7AdmissibleProbabilityReadout stack →
      stack.operationalEquivalence :=
  fun closed => closed.right.right.right.right.right.right.left

def v7NormalizationOnlyStack : V7ProbabilityLayerStack :=
  {
    actualizationWeights := False,
    positiveMeasure := False,
    admissibleReadoutContext := False,
    contextNormalization := True,
    exclusivityAdditivity := False,
    coarseGrainingConsistency := False,
    operationalEquivalence := False,
    frequencyInterpretation := False,
    noBornImport := True
  }

theorem v7_normalization_only_does_not_supply_probability_readout :
    ¬ V7AdmissibleProbabilityReadout v7NormalizationOnlyStack := by
  intro closed
  exact closed.left

structure V7FiniteNormalizationBridge where
  readout : StableFiniteReadout
  normalized : List NormalizedWeight
  lengthMatches : normalized.length = readout.weights.length
  commonDenominator :
    ∀ weight : NormalizedWeight,
      weight ∈ normalized →
        weight.denominator = normalizationDenominator readout

def v7FiniteNormalizationBridge
    (readout : StableFiniteReadout) :
    V7FiniteNormalizationBridge :=
  {
    readout := readout,
    normalized := normalizedReadout readout,
    lengthMatches := normalized_readout_length_matches readout,
    commonDenominator :=
      normalized_readout_common_denominator readout
  }

theorem v7_finite_normalization_bridge_preserves_denominator
    (readout : StableFiniteReadout) :
    ∀ weight : NormalizedWeight,
      weight ∈ (v7FiniteNormalizationBridge readout).normalized →
        weight.denominator = normalizationDenominator readout :=
  (v7FiniteNormalizationBridge readout).commonDenominator

structure V7CoarseGrainingBridge where
  blocks : List FiniteReadout
  totalPreserved :
    contextTotal (flattenReadoutBlocks blocks) =
      contextTotal (coarseGrainBlocks blocks)

def v7CoarseGrainingBridge
    (blocks : List FiniteReadout) :
    V7CoarseGrainingBridge :=
  {
    blocks := blocks,
    totalPreserved := coarse_grain_blocks_preserve_total blocks
  }

structure V7OperationalEquivalenceBridge (event : Type) where
  equivalent : event → event → Prop
  weight : EventWeight event
  respects : RespectsOperationalEquivalence equivalent weight

theorem v7_operational_equivalence_bridge_preserves_weight
    {event : Type}
    (bridge : V7OperationalEquivalenceBridge event)
    (left right : event)
    (equivalentEvents : bridge.equivalent left right) :
    bridge.weight left = bridge.weight right :=
  operational_equivalence_respecting_weight_function_preserves_weight
    bridge.equivalent
    bridge.weight
    bridge.respects
    left
    right
    equivalentEvents

end QMClosure
end IDT
