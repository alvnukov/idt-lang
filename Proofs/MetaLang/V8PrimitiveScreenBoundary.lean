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

/-! Checker quality is the current engineering/research priority. These are
work-ledger entries, not proofs of Python execution or of physical claims. -/
def currentDevelopmentPriority : String :=
  "improve_checker_coverage_and_independent_quality_checks_while_advancing_research"

def exactAlgebraicCheckIds : List String := ["exact_kernel_positivity"]

def kernelCertificateEvidence : String :=
  "Python_checked_weighted_square_identity_or_negative_reference_not_Lean_proof"

def checkerQualityControls : List String := [
  "independent_principal_minor_comparison_on_729_three_by_three_matrices",
  "169_normalized_kernel_regressions_including_12_previous_grid_misses",
  "permutation_positive_scaling_and_invertible_congruence_checks",
  "certificate_mutations_and_generator_failure_are_not_candidate_results",
  "cache_hits_reverify_certificates_without_repeating_search",
  "CI_runs_primitive_QM_SM_pipeline_and_certificate_tests"
]

/-! Candidate history protects both directions of checker drift. These are
engineering contracts, not a proof that a physically correct candidate exists
in the inventory or that the checker can never reject one. -/
def candidateHistoryDiscipline : List String := [
  "retain_submitted_candidates_including_rejected_unsupported_and_checker_errors",
  "archive_complete_observations_without_overwriting_prior_generations",
  "recompute_all_history_with_original_bounds_and_current_checker_without_disk_cache",
  "review_survival_to_counterexample_and_counterexample_to_survival_changes",
  "review_changed_assumptions_requirements_coverage_witnesses_and_claim_scope",
  "checker_failure_is_not_candidate_rejection_and_does_not_skip_neighbors",
  "historical_baseline_is_an_observation_not_physical_ground_truth",
  "CI_replays_initial_275_candidate_inventory_and_new_archived_submissions",
  "no_automatic_baseline_refresh_or_proof_status_upgrade"
]

def checkerQualityOpenObligations : List String := [
  "prove_certificate_validator_soundness_in_Lean_and_connect_runtime_evidence",
  "add_source_code_mutation_testing_beyond_certificate_mutations",
  "expand_QM_states_settings_and_independent_implementation_comparisons",
  "add_SM_interaction_process_and_neutrino_sector_benchmarks",
  "add_versioned_empirical_data_uncertainties_and_independent_holdouts",
  "audit_all_adapter_imports_before_any_joint_primitive_claim",
  "measure_speedups_only_under_preserved_coverage_and_evidence_contracts"
]

end IDT.MetaLang.V8.PrimitiveScreen
