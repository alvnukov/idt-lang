import Proofs.QMClosure.BornWallSeparation

namespace IDT
namespace QMClosure

/-!
S2/Born proof-search separator.

This file does not prove Born. It machine-checks the current obstruction:
finite closure, finite facticity, orientation accounting, and loss accounting
can all hold in a toy finite core that still admits a primitive third-order
facticization witness. Therefore the present B2-like accounting package does
not force second-order facticization by itself.
-/

structure S2CandidateCore where
  dclClosed : Prop
  finiteFacticity : Prop
  orientedComparisons : Prop
  lossAccounting : Prop
  singletonWitness : Prop
  pairwiseWitness : Prop
  ternaryWitness : Prop
  nonnegativeCompositeWeights : Prop
  stableI3Nonzero : Prop

def B2LikeAccounting (core : S2CandidateCore) : Prop :=
  core.dclClosed
    ∧ core.finiteFacticity
    ∧ core.orientedComparisons
    ∧ core.lossAccounting
    ∧ core.singletonWitness
    ∧ core.pairwiseWitness
    ∧ core.nonnegativeCompositeWeights

def SecondOrderFacticization (core : S2CandidateCore) : Prop :=
  ¬ core.ternaryWitness ∧ ¬ core.stableI3Nonzero

def PairwiseWitnessExhaustive (core : S2CandidateCore) : Prop :=
  core.ternaryWitness → False

def HiddenContextOnlyFact (core : S2CandidateCore) : Prop :=
  core.ternaryWitness
    ∧ core.stableI3Nonzero
    ∧ ¬ PairwiseWitnessExhaustive core

def NoHiddenContextOnlyFact (core : S2CandidateCore) : Prop :=
  ¬ HiddenContextOnlyFact core

def thirdOrderStableCore : S2CandidateCore :=
  {
    dclClosed := True,
    finiteFacticity := True,
    orientedComparisons := True,
    lossAccounting := True,
    singletonWitness := True,
    pairwiseWitness := True,
    ternaryWitness := True,
    nonnegativeCompositeWeights := True,
    stableI3Nonzero := True
  }

theorem third_order_core_satisfies_b2_like_accounting :
    B2LikeAccounting thirdOrderStableCore :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro True.intro)))))

theorem third_order_core_refutes_second_order_facticization :
    ¬ SecondOrderFacticization thirdOrderStableCore := by
  intro s2
  exact s2.left True.intro

theorem b2_like_accounting_does_not_force_s2 :
    ∃ core : S2CandidateCore,
      B2LikeAccounting core ∧ ¬ SecondOrderFacticization core :=
  Exists.intro thirdOrderStableCore
    (And.intro
      third_order_core_satisfies_b2_like_accounting
      third_order_core_refutes_second_order_facticization)

theorem third_order_core_has_hidden_context_only_fact :
    HiddenContextOnlyFact thirdOrderStableCore :=
  And.intro True.intro
    (And.intro True.intro
      (fun pairwiseExhaustive => pairwiseExhaustive True.intro))

theorem third_order_core_refutes_no_hidden_context_only_fact :
    ¬ NoHiddenContextOnlyFact thirdOrderStableCore := by
  intro noHidden
  exact noHidden third_order_core_has_hidden_context_only_fact

theorem b2_like_accounting_does_not_force_no_hidden_context_only_fact :
    ∃ core : S2CandidateCore,
      B2LikeAccounting core ∧ ¬ NoHiddenContextOnlyFact core :=
  Exists.intro thirdOrderStableCore
    (And.intro
      third_order_core_satisfies_b2_like_accounting
      third_order_core_refutes_no_hidden_context_only_fact)

theorem stable_i3_with_ternary_witness_is_context_only_fact
    (core : S2CandidateCore)
    (ternary : core.ternaryWitness)
    (i3 : core.stableI3Nonzero) :
    HiddenContextOnlyFact core :=
  And.intro ternary
    (And.intro i3
      (fun pairwiseExhaustive => pairwiseExhaustive ternary))

theorem no_hidden_context_only_fact_blocks_stable_i3
    (core : S2CandidateCore)
    (noHidden : NoHiddenContextOnlyFact core) :
    ¬ (core.ternaryWitness ∧ core.stableI3Nonzero) := by
  intro witness
  exact noHidden
    (stable_i3_with_ternary_witness_is_context_only_fact
      core witness.left witness.right)

theorem no_hidden_context_only_fact_supplies_s2_when_ternary_is_i3_source
    (core : S2CandidateCore)
    (noHidden : NoHiddenContextOnlyFact core)
    (ternaryIffI3 : core.ternaryWitness ↔ core.stableI3Nonzero) :
    SecondOrderFacticization core := by
  constructor
  · intro ternary
    exact (no_hidden_context_only_fact_blocks_stable_i3 core noHidden)
      (And.intro ternary (ternaryIffI3.mp ternary))
  · intro i3
    exact (no_hidden_context_only_fact_blocks_stable_i3 core noHidden)
      (And.intro (ternaryIffI3.mpr i3) i3)

structure BornConditionalInputs where
  positiveQuadraticActualization : Prop
  contextNormalization : Prop
  exclusivityAdditivity : Prop
  coarseGrainingConsistency : Prop
  operationalEquivalenceProbability : Prop

def BornLikeFiniteContextProbability (inputs : BornConditionalInputs) : Prop :=
  inputs.positiveQuadraticActualization
    ∧ inputs.contextNormalization
    ∧ inputs.exclusivityAdditivity
    ∧ inputs.coarseGrainingConsistency
    ∧ inputs.operationalEquivalenceProbability

theorem born_like_context_probability_requires_quadratic_input
    (inputs : BornConditionalInputs) :
    BornLikeFiniteContextProbability inputs →
      inputs.positiveQuadraticActualization :=
  fun proof => proof.left

theorem supplied_quadratic_inputs_give_born_like_context_probability
    (inputs : BornConditionalInputs)
    (quadratic : inputs.positiveQuadraticActualization)
    (normalization : inputs.contextNormalization)
    (exclusivity : inputs.exclusivityAdditivity)
    (coarseGraining : inputs.coarseGrainingConsistency)
    (equivalence : inputs.operationalEquivalenceProbability) :
    BornLikeFiniteContextProbability inputs :=
  And.intro quadratic
    (And.intro normalization
      (And.intro exclusivity
        (And.intro coarseGraining equivalence)))

/-!
Bracketing/coarse-graining associativity audit.

The witness below is deliberately small. It checks a possible false shortcut:
"if finite fact formation is grouping-independent, then primitive I3 is
impossible." Bracketing equality alone is too weak. A whole-context residue can
be carried through both groupings without contradiction.
-/

structure TernaryGroupingWitness where
  leftGroupingTotal : Nat
  rightGroupingTotal : Nat
  ternaryResidue : Nat

def GroupingCoherent (witness : TernaryGroupingWitness) : Prop :=
  witness.leftGroupingTotal = witness.rightGroupingTotal

def StablePrimitiveTernaryResidue (witness : TernaryGroupingWitness) : Prop :=
  witness.ternaryResidue > 0

def associativeTernaryResidueWitness : TernaryGroupingWitness :=
  {
    leftGroupingTotal := 4,
    rightGroupingTotal := 4,
    ternaryResidue := 1
  }

theorem associative_grouping_can_carry_primitive_ternary_residue :
    GroupingCoherent associativeTernaryResidueWitness
      ∧ StablePrimitiveTernaryResidue associativeTernaryResidueWitness :=
  And.intro
    (by
      unfold GroupingCoherent associativeTernaryResidueWitness
      rfl)
    (by
      unfold StablePrimitiveTernaryResidue associativeTernaryResidueWitness
      decide)

theorem grouping_coherence_alone_does_not_force_no_i3 :
    ∃ witness : TernaryGroupingWitness,
      GroupingCoherent witness ∧ StablePrimitiveTernaryResidue witness :=
  Exists.intro associativeTernaryResidueWitness
    associative_grouping_can_carry_primitive_ternary_residue

def ProperSubcontextExhaustive (witness : TernaryGroupingWitness) : Prop :=
  witness.ternaryResidue = 0

theorem proper_subcontext_exhaustion_blocks_ternary_residue
    (witness : TernaryGroupingWitness)
    (exhaustive : ProperSubcontextExhaustive witness) :
    ¬ StablePrimitiveTernaryResidue witness := by
  intro residue
  unfold StablePrimitiveTernaryResidue at residue
  unfold ProperSubcontextExhaustive at exhaustive
  rw [exhaustive] at residue
  exact Nat.lt_irrefl 0 residue

/-!
Witness-exhaustion audit.

Pointwise witnessability, NUSD-like accounting, or finite-route coverage do not
by themselves reject I3 if the ternary fact has its own admissible route. What
is needed is not "every stable fact has some witness", but "whole-context facts
are exhausted by proper-subcontext witnesses" for the sector being claimed.
-/

structure ThreeAlternativeWitnessRoutes where
  singletonRoutes : Prop
  pairwiseRoutes : Prop
  ternaryRoute : Prop
  stableI3Nonzero : Prop

def PointwiseWitnessed (routes : ThreeAlternativeWitnessRoutes) : Prop :=
  routes.singletonRoutes ∧ routes.pairwiseRoutes ∧ routes.ternaryRoute

def ProperSubcontextWitnessExhausted
    (routes : ThreeAlternativeWitnessRoutes) : Prop :=
  routes.singletonRoutes ∧ routes.pairwiseRoutes ∧ ¬ routes.ternaryRoute

def pointwiseTernaryWitnessRoutes : ThreeAlternativeWitnessRoutes :=
  {
    singletonRoutes := True,
    pairwiseRoutes := True,
    ternaryRoute := True,
    stableI3Nonzero := True
  }

theorem pointwise_witnessability_can_include_stable_i3 :
    PointwiseWitnessed pointwiseTernaryWitnessRoutes
      ∧ pointwiseTernaryWitnessRoutes.stableI3Nonzero :=
  And.intro
    (And.intro True.intro (And.intro True.intro True.intro))
    True.intro

theorem pointwise_witnessability_does_not_force_s2 :
    ∃ routes : ThreeAlternativeWitnessRoutes,
      PointwiseWitnessed routes ∧ routes.stableI3Nonzero :=
  Exists.intro pointwiseTernaryWitnessRoutes
    pointwise_witnessability_can_include_stable_i3

theorem proper_subcontext_witness_exhaustion_blocks_ternary_route
    (routes : ThreeAlternativeWitnessRoutes)
    (exhausted : ProperSubcontextWitnessExhausted routes) :
    ¬ routes.ternaryRoute :=
  exhausted.right.right

/-!
Metric/pairwise-generation audit.

Metric comparison readout is represented here only by its formal consequence:
the whole three-alternative readout has no primitive ternary coordinate beyond
singleton and pairwise comparison data. This is a useful conditional route, but
it is not a derivation of metricity from the primitive base.
-/

structure ThreeAlternativeComparisonReadout where
  singletonData : Nat
  pairwiseData : Nat
  primitiveTernaryData : Nat

def PairwiseGeneratedReadout (readout : ThreeAlternativeComparisonReadout) :
    Prop :=
  readout.primitiveTernaryData = 0

def PrimitiveTernaryReadoutResidue
    (readout : ThreeAlternativeComparisonReadout) : Prop :=
  readout.primitiveTernaryData > 0

def pairwiseMetricToyReadout : ThreeAlternativeComparisonReadout :=
  {
    singletonData := 3,
    pairwiseData := 3,
    primitiveTernaryData := 0
  }

def higherOrderToyReadout : ThreeAlternativeComparisonReadout :=
  {
    singletonData := 3,
    pairwiseData := 3,
    primitiveTernaryData := 1
  }

theorem pairwise_generated_readout_blocks_primitive_ternary_residue
    (readout : ThreeAlternativeComparisonReadout)
    (pairwise : PairwiseGeneratedReadout readout) :
    ¬ PrimitiveTernaryReadoutResidue readout := by
  intro residue
  unfold PrimitiveTernaryReadoutResidue at residue
  unfold PairwiseGeneratedReadout at pairwise
  rw [pairwise] at residue
  exact Nat.lt_irrefl 0 residue

theorem higher_order_readout_is_not_pairwise_generated :
    ¬ PairwiseGeneratedReadout higherOrderToyReadout := by
  intro pairwise
  unfold PairwiseGeneratedReadout higherOrderToyReadout at pairwise
  contradiction

/-!
Primitive-base audit.

This checks whether the current context-first/B1-style discipline already
contains the missing pairwise basis. It does not. A local ternary witness can be
constructor-generated, non-global, accounted, and stable unless the base also
contains a proper-subcontext or pairwise-basis rule.
-/

structure PrimitiveBaseWitnessDiscipline where
  constructorGenerated : Prop
  noPrimitiveGlobalFactTable : Prop
  localReadoutWitness : Prop
  lossAccountingRoute : Prop
  properSubcontextBasis : Prop
  ternaryWitness : Prop
  stableI3Nonzero : Prop

def CurrentPrimitiveBaseDiscipline
    (discipline : PrimitiveBaseWitnessDiscipline) : Prop :=
  discipline.constructorGenerated
    ∧ discipline.noPrimitiveGlobalFactTable
    ∧ discipline.localReadoutWitness
    ∧ discipline.lossAccountingRoute

def PairwiseWitnessBasis
    (discipline : PrimitiveBaseWitnessDiscipline) : Prop :=
  discipline.properSubcontextBasis ∧ ¬ discipline.ternaryWitness

def localTernaryPrimitiveDiscipline : PrimitiveBaseWitnessDiscipline :=
  {
    constructorGenerated := True,
    noPrimitiveGlobalFactTable := True,
    localReadoutWitness := True,
    lossAccountingRoute := True,
    properSubcontextBasis := False,
    ternaryWitness := True,
    stableI3Nonzero := True
  }

theorem local_ternary_witness_satisfies_current_primitive_discipline :
    CurrentPrimitiveBaseDiscipline localTernaryPrimitiveDiscipline :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro True.intro))

theorem local_ternary_witness_refutes_pairwise_basis :
    ¬ PairwiseWitnessBasis localTernaryPrimitiveDiscipline := by
  intro basis
  exact basis.left

theorem current_primitive_discipline_does_not_force_pairwise_basis :
    ∃ discipline : PrimitiveBaseWitnessDiscipline,
      CurrentPrimitiveBaseDiscipline discipline ∧ ¬ PairwiseWitnessBasis discipline :=
  Exists.intro localTernaryPrimitiveDiscipline
    (And.intro
      local_ternary_witness_satisfies_current_primitive_discipline
      local_ternary_witness_refutes_pairwise_basis)

theorem proper_subcontext_basis_blocks_local_ternary_witness
    (discipline : PrimitiveBaseWitnessDiscipline)
    (basis : PairwiseWitnessBasis discipline) :
    ¬ discipline.ternaryWitness :=
  basis.right

/-!
Probability concept audit.

Normalized context probability is a readout layer over supplied weights. It is
not a selector for the weight law. Linear, quadratic, and cubic positive
weights all normalize into well-formed finite context probabilities. Therefore
probability normalization cannot prove Born; the lower obligation is to select
the facticization-weight law.
-/

def linearProbabilityAuditReadout : StableFiniteReadout :=
  {
    weights := [2, 3],
    positive_total := by decide
  }

def quadraticProbabilityAuditReadout : StableFiniteReadout :=
  {
    weights := [4, 9],
    positive_total := by decide
  }

def cubicProbabilityAuditReadout : StableFiniteReadout :=
  {
    weights := [8, 27],
    positive_total := by decide
  }

theorem linear_probability_audit_readout_normalizes :
    ReadoutAccountingAdmits linearProbabilityAuditReadout :=
  stable_readout_is_admitted_by_accounting linearProbabilityAuditReadout

theorem quadratic_probability_audit_readout_normalizes :
    ReadoutAccountingAdmits quadraticProbabilityAuditReadout :=
  stable_readout_is_admitted_by_accounting quadraticProbabilityAuditReadout

theorem cubic_probability_audit_readout_normalizes :
    ReadoutAccountingAdmits cubicProbabilityAuditReadout :=
  stable_readout_is_admitted_by_accounting cubicProbabilityAuditReadout

theorem probability_normalization_does_not_select_quadratic_weight_law :
    ReadoutAccountingAdmits linearProbabilityAuditReadout
      ∧ ReadoutAccountingAdmits quadraticProbabilityAuditReadout
      ∧ ReadoutAccountingAdmits cubicProbabilityAuditReadout
      ∧ normalizationDenominator linearProbabilityAuditReadout
          ≠ normalizationDenominator quadraticProbabilityAuditReadout
      ∧ normalizationDenominator quadraticProbabilityAuditReadout
          ≠ normalizationDenominator cubicProbabilityAuditReadout :=
  And.intro
    linear_probability_audit_readout_normalizes
    (And.intro
      quadratic_probability_audit_readout_normalizes
      (And.intro
        cubic_probability_audit_readout_normalizes
        (And.intro (by decide) (by decide))))

structure ProbabilityLayerInputs where
  suppliedWeights : Prop
  positiveTotal : Prop
  normalizationRule : Prop
  stableFrequencies : Prop

def ProbabilityLayerWellFormed (inputs : ProbabilityLayerInputs) : Prop :=
  inputs.suppliedWeights
    ∧ inputs.positiveTotal
    ∧ inputs.normalizationRule
    ∧ inputs.stableFrequencies

structure FacticizationWeightSelector where
  pairwiseBasis : Prop
  positiveComparisonGeometry : Prop
  quadraticWeightLaw : Prop

def BornReadyWeightSelector (selector : FacticizationWeightSelector) : Prop :=
  selector.pairwiseBasis
    ∧ selector.positiveComparisonGeometry
    ∧ selector.quadraticWeightLaw

theorem probability_layer_does_not_supply_weight_selector
    (inputs : ProbabilityLayerInputs)
    (_wellFormed : ProbabilityLayerWellFormed inputs)
    (selector : FacticizationWeightSelector)
    (missingQuadratic : ¬ selector.quadraticWeightLaw) :
    ¬ BornReadyWeightSelector selector := by
  intro ready
  exact missingQuadratic ready.right.right

theorem born_ready_weight_selector_supplies_quadratic_law
    (selector : FacticizationWeightSelector) :
    BornReadyWeightSelector selector → selector.quadraticWeightLaw :=
  fun ready => ready.right.right

/-!
Normalized-overlap selector audit.

This is the local formal shape of the stronger finite result checked by
`scripts/evaluate_overlap_primitive_route.py`: if a sector supplies reversible
orientation transport and exposes only normalized bilinear overlap, then its
readout selector is pairwise. This is not yet a derivation from primitives and
not a universal S2 theorem for all readout contexts.
-/

structure NormalizedOverlapSelector where
  reversibleOrientationTransport : Prop
  normalizedBilinearOverlap : Prop
  noDirectBornTable : Prop
  noOpenParameters : Prop

def PairwiseOverlapWeightSelector
    (selector : NormalizedOverlapSelector) : Prop :=
  selector.reversibleOrientationTransport
    ∧ selector.normalizedBilinearOverlap
    ∧ selector.noDirectBornTable
    ∧ selector.noOpenParameters

def finiteOrientationOverlapSelector : NormalizedOverlapSelector :=
  {
    reversibleOrientationTransport := True,
    normalizedBilinearOverlap := True,
    noDirectBornTable := True,
    noOpenParameters := True
  }

theorem finite_orientation_overlap_selector_is_pairwise :
    PairwiseOverlapWeightSelector finiteOrientationOverlapSelector :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro True.intro))

theorem pairwise_overlap_selector_has_no_primitive_ternary_coordinate :
    PairwiseGeneratedReadout pairwiseMetricToyReadout :=
  rfl

/-!
Finite dependency-chain audit.

The executable finite route now has more structure than a single selector hit:
compatible-kernel additivity feeds normalized-overlap uniqueness; normalized
orientation overlap feeds the canonical quadrature/phase-bundle screen; that
screen feeds the finite complex-sector carrier check. This Lean block records
only that conditional dependency shape. It deliberately preserves the
universal Born/S2 gap.
-/

structure OverlapUniquenessInputs where
  compatibleKernelAdditivity : Prop
  transportInvariance : Prop
  scaleGauge : Prop
  normalization : Prop
  invariantKernelUniqueness : Prop
  noDirectAngleBornImport : Prop

def NormalizedOverlapUniquenessHit
    (inputs : OverlapUniquenessInputs) : Prop :=
  inputs.compatibleKernelAdditivity
    ∧ inputs.transportInvariance
    ∧ inputs.scaleGauge
    ∧ inputs.normalization
    ∧ inputs.invariantKernelUniqueness
    ∧ inputs.noDirectAngleBornImport

def finiteOverlapUniquenessInputs : OverlapUniquenessInputs :=
  {
    compatibleKernelAdditivity := True,
    transportInvariance := True,
    scaleGauge := True,
    normalization := True,
    invariantKernelUniqueness := True,
    noDirectAngleBornImport := True
  }

theorem finite_overlap_uniqueness_screen_is_hit :
    NormalizedOverlapUniquenessHit finiteOverlapUniquenessInputs :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro True.intro))))

structure FiniteBornChainEvidence where
  compatibleKernelAdditivity : Prop
  normalizedOverlapUnique : Prop
  normalizedOrientationOverlapSelector : Prop
  canonicalQuadratureJ : Prop
  phaseBundleCarrierScreen : Prop
  finiteComplexSectorScreen : Prop
  negativeControlsRejected : Prop
  universalBornTheorem : Prop
  universalS2Theorem : Prop

def FiniteBornChainHit (evidence : FiniteBornChainEvidence) : Prop :=
  evidence.compatibleKernelAdditivity
    ∧ evidence.normalizedOverlapUnique
    ∧ evidence.normalizedOrientationOverlapSelector
    ∧ evidence.canonicalQuadratureJ
    ∧ evidence.phaseBundleCarrierScreen
    ∧ evidence.finiteComplexSectorScreen
    ∧ evidence.negativeControlsRejected

def UniversalBornS2Closed (evidence : FiniteBornChainEvidence) : Prop :=
  evidence.universalBornTheorem ∧ evidence.universalS2Theorem

def finiteBornChainEvidence : FiniteBornChainEvidence :=
  {
    compatibleKernelAdditivity := True,
    normalizedOverlapUnique := True,
    normalizedOrientationOverlapSelector := True,
    canonicalQuadratureJ := True,
    phaseBundleCarrierScreen := True,
    finiteComplexSectorScreen := True,
    negativeControlsRejected := True,
    universalBornTheorem := False,
    universalS2Theorem := False
  }

theorem finite_born_chain_evidence_is_hit :
    FiniteBornChainHit finiteBornChainEvidence :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro True.intro)))))

theorem finite_born_chain_hit_does_not_close_universal_born_or_s2 :
    FiniteBornChainHit finiteBornChainEvidence
      ∧ ¬ UniversalBornS2Closed finiteBornChainEvidence :=
  And.intro
    finite_born_chain_evidence_is_hit
    (by
      intro closed
      exact closed.left)

end QMClosure
end IDT
