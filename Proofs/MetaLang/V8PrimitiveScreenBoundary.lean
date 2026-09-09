namespace IDT.MetaLang.V8.PrimitiveScreen

/-!
Research ledger for the fast, pre-proof candidate screen.

Python performs bounded exploratory computations, not Lean-certified experiment
execution. This ledger neither verifies the Python implementation nor promotes
its results to physical derivations. The existing experiment/proof authorities
are unchanged. The known controls are regression cases, not new discoveries.
-/

inductive ScreenOutcome where
  | counterexampleUnderStatedAssumptions
  | noCounterexampleWithinBounds
  | inconclusive
  | unsupported
deriving DecidableEq, Repr

inductive EvidenceKind where
  | boundedComputation
  | kernelCheckedMathematicalProof
  | empiricalComparison
deriving DecidableEq, Repr

def currentEvidenceKind : EvidenceKind := .boundedComputation

def currentCheckIds : List String := [
  "unit_weight", "event_nonnegative", "coefficient_third_difference",
  "self_composition", "signed_reference_composition"
]

inductive ImportedStructure where
  | rationalCoefficientCarrier
  | coefficientAddition
  | candidateWeightRule
  | indicatorEvents
  | pairKernelRepresentation
  | tensorMultiplication
  | normalizedSignedRankOneReferencesWithNonzeroSum
deriving DecidableEq, Repr

def kernelReferenceScreenImports : List ImportedStructure := [
  .rationalCoefficientCarrier, .candidateWeightRule, .indicatorEvents,
  .pairKernelRepresentation, .tensorMultiplication,
  .normalizedSignedRankOneReferencesWithNonzeroSum
]

inductive OpenObligation where
  | deriveOperationalSemanticsFromLowerPrimitives
  | deriveDetectorRecordAndProbabilityBridge
  | addIndependentExperimentalDataWithUncertainties
  | addBellAndCompositeDynamicsWithoutUnstatedImports
  | proveSelectedSurvivingStatementsInLean
  | establishContinuumAndComplexCarrierScope
  | reconstructStandardModelAndGravity
deriving DecidableEq, Repr

def nextObligations : List OpenObligation := [
  .deriveOperationalSemanticsFromLowerPrimitives,
  .deriveDetectorRecordAndProbabilityBridge,
  .addIndependentExperimentalDataWithUncertainties,
  .addBellAndCompositeDynamicsWithoutUnstatedImports,
  .proveSelectedSurvivingStatementsInLean,
  .establishContinuumAndComplexCarrierScope,
  .reconstructStandardModelAndGravity
]

-- No mathematical proof or empirical result is inferred from an outcome tag.
def outcomeEvidence (_ : ScreenOutcome) : EvidenceKind := .boundedComputation

/-! The optional physics adapters import QM/QFT structure; they do not close
any of nextObligations. Cache entries and short cards have the same bounded
computational evidence category as fresh execution. -/
def physicsBenchmarkIds : List String := [
  "qm_born_reference", "qm_phase_interference", "qm_projective_repeatability",
  "qm_local_no_signalling", "qm_singlet_correlations", "qm_tsirelson_bound",
  "sm_su3_cubic", "sm_su3_squared_y", "sm_su2_squared_y", "sm_y_cubic",
  "sm_mixed_gravitational_y", "sm_witten_doublets",
  "sm_minimal_multiplet_content", "sm_neutral_higgs_lower_component"
]

def physicsAdapterImports : List String := [
  "complex_amplitudes_linear_context_maps_projective_measurements_tensor_products",
  "Born_QM_reference_targets",
  "su3_su2_u1_Lie_algebra_left_handed_Weyl_fundamentals",
  "Q_equals_T3_plus_Y_scalar_Higgs_doublet_QFT_anomaly_formulas",
  "minimal_three_generation_content_target"
]

def pipelineResearchObligations : List String := [
  "derive_a_shared_lower_primitive_specification_and_bridges_to_both_sectors",
  "add_independent_experimental_targets_with_uncertainties_and_validity_domains",
  "derive_mass_interaction_and_neutrino_sectors_before_full_SM_claims",
  "formally_check_selected_statements_not_just_replay_Python",
  "no_status_upgrade_from_cache_hit_or_short_card"
]

end IDT.MetaLang.V8.PrimitiveScreen
