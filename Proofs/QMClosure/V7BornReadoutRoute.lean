import Proofs.QMClosure.PrimitiveBoundaryQMChain
import Proofs.QMClosure.V7ProbabilityDecomposition

namespace IDT
namespace QMClosure

/-!
V7 Born/readout route recovery.

The v7 result was not "Born is proved". It was a decomposition of the Born wall:
positive quadratic measure is upstream of probability, and four readout
obligations are needed to turn that measure into an admissible probability
readout.
-/

structure V7BornReadoutRouteInputs where
  positiveQuadraticMeasure : Prop
  contextNormalization : Prop
  exclusivityAdditivity : Prop
  coarseGrainingConsistency : Prop
  operationalEquivalenceProbability : Prop
  admissibleReadoutContext : Prop
  frequencyInterpretation : Prop
  noBornImport : Prop

def V7BornReadoutRouteClosed
    (inputs : V7BornReadoutRouteInputs) : Prop :=
  inputs.positiveQuadraticMeasure
    ∧ inputs.contextNormalization
    ∧ inputs.exclusivityAdditivity
    ∧ inputs.coarseGrainingConsistency
    ∧ inputs.operationalEquivalenceProbability
    ∧ inputs.admissibleReadoutContext
    ∧ inputs.frequencyInterpretation
    ∧ inputs.noBornImport

def v7BornRouteToProbabilityStack
    (inputs : V7BornReadoutRouteInputs) :
    V7ProbabilityLayerStack :=
  {
    actualizationWeights := inputs.positiveQuadraticMeasure,
    positiveMeasure := inputs.positiveQuadraticMeasure,
    admissibleReadoutContext := inputs.admissibleReadoutContext,
    contextNormalization := inputs.contextNormalization,
    exclusivityAdditivity := inputs.exclusivityAdditivity,
    coarseGrainingConsistency := inputs.coarseGrainingConsistency,
    operationalEquivalence := inputs.operationalEquivalenceProbability,
    frequencyInterpretation := inputs.frequencyInterpretation,
    noBornImport := inputs.noBornImport
  }

theorem v7_born_route_supplies_admissible_probability_readout
    (inputs : V7BornReadoutRouteInputs) :
    V7BornReadoutRouteClosed inputs →
      V7AdmissibleProbabilityReadout
        (v7BornRouteToProbabilityStack inputs) := by
  intro closed
  rcases closed with
    ⟨quadratic, normalization, exclusivity, coarseGraining,
      equivalence, context, frequency, noBorn⟩
  exact And.intro quadratic
    (And.intro quadratic
      (And.intro context
        (And.intro normalization
          (And.intro exclusivity
            (And.intro coarseGraining
              (And.intro equivalence
                (And.intro frequency noBorn)))))))

theorem v7_born_route_requires_positive_quadratic_measure
    (inputs : V7BornReadoutRouteInputs) :
    V7BornReadoutRouteClosed inputs →
      inputs.positiveQuadraticMeasure :=
  fun closed => closed.left

theorem v7_born_route_requires_operational_equivalence_probability
    (inputs : V7BornReadoutRouteInputs) :
    V7BornReadoutRouteClosed inputs →
      inputs.operationalEquivalenceProbability :=
  fun closed => closed.right.right.right.right.left

def v7BornRouteFromSignedOverlap
    (signed : AffineOverlapBornInputs)
    (contextNormalization : Prop)
    (exclusivityAdditivity : Prop)
    (coarseGrainingConsistency : Prop)
    (operationalEquivalenceProbability : Prop)
    (admissibleReadoutContext : Prop)
    (frequencyInterpretation : Prop) :
    V7BornReadoutRouteInputs :=
  {
    positiveQuadraticMeasure :=
      PositiveQuadraticActualizationFromSignedOverlap signed,
    contextNormalization := contextNormalization,
    exclusivityAdditivity := exclusivityAdditivity,
    coarseGrainingConsistency := coarseGrainingConsistency,
    operationalEquivalenceProbability :=
      operationalEquivalenceProbability,
    admissibleReadoutContext := admissibleReadoutContext,
    frequencyInterpretation := frequencyInterpretation,
    noBornImport := signed.noBornImport
  }

theorem signed_overlap_plus_v7_readout_obligations_closes_born_route
    (signed : AffineOverlapBornInputs)
    (quadratic :
      PositiveQuadraticActualizationFromSignedOverlap signed)
    (contextNormalization : Prop)
    (normalization : contextNormalization)
    (exclusivityAdditivity : Prop)
    (exclusivity : exclusivityAdditivity)
    (coarseGrainingConsistency : Prop)
    (coarseGraining : coarseGrainingConsistency)
    (operationalEquivalenceProbability : Prop)
    (equivalence : operationalEquivalenceProbability)
    (admissibleReadoutContext : Prop)
    (context : admissibleReadoutContext)
    (frequencyInterpretation : Prop)
    (frequency : frequencyInterpretation)
    (noBorn : signed.noBornImport) :
    V7BornReadoutRouteClosed
      (v7BornRouteFromSignedOverlap
        signed
        contextNormalization
        exclusivityAdditivity
        coarseGrainingConsistency
        operationalEquivalenceProbability
        admissibleReadoutContext
        frequencyInterpretation) :=
  And.intro quadratic
    (And.intro normalization
      (And.intro exclusivity
        (And.intro coarseGraining
          (And.intro equivalence
            (And.intro context
              (And.intro frequency noBorn))))))

def v7BornNormalizationOnlyInputs : V7BornReadoutRouteInputs :=
  {
    positiveQuadraticMeasure := False,
    contextNormalization := True,
    exclusivityAdditivity := False,
    coarseGrainingConsistency := False,
    operationalEquivalenceProbability := False,
    admissibleReadoutContext := False,
    frequencyInterpretation := False,
    noBornImport := True
  }

theorem v7_born_normalization_only_route_is_blocked :
    ¬ V7BornReadoutRouteClosed v7BornNormalizationOnlyInputs := by
  intro closed
  exact closed.left

end QMClosure
end IDT
