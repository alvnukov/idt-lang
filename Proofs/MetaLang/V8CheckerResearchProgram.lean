import Proofs.MetaLang.V8PrimitiveEmpiricalConstraintLedger
import Proofs.MetaLang.V8PrimitiveScreenBoundary

namespace IDT.MetaLang.V8

/-! A typed two-track work ledger. These declarations describe engineering and
research obligations, not completed physical derivations or an exhaustive world. -/
inductive CheckerResearchTrack where
  | checker
  | primitiveResearch
deriving DecidableEq, Repr

inductive CheckerResearchWorkState where
  | active
  | blocked
  | planned
deriving DecidableEq, Repr

structure CheckerResearchWorkItem where
  id : String
  track : CheckerResearchTrack
  state : CheckerResearchWorkState
  inputs : List String
  requiredOutputs : List String
  acceptance : List String
  blockers : List String
deriving Repr

def currentCheckerResearchProgram : List CheckerResearchWorkItem := [
  { id := "retain_existing_primitive_candidates"
    track := .checker
    state := .active
    inputs := ["data/existing_primitive_inventory.json"]
    requiredOutputs := ["data/candidate_history", "immutable_source_snapshots"]
    acceptance := ["preserve_distinct_historical_bases_and_scoped_failures",
      "missing_prediction_adapter_is_unsupported_not_rejection",
      "all_candidates_remain_in_cross_version_regression"]
    blockers := [] },
  { id := "connect_versioned_world_constraints_to_checked_evidence"
    track := .checker
    state := .blocked
    inputs := ["primitiveEmpiricalConstraints", "currentPrimitiveSearchCoverage"]
    requiredOutputs := ["versioned_data_prediction_and_uncertainty_contracts",
      "evidence_linked_requirement_statuses"]
    acceptance := ["complete_unique_canonical_inventory",
      "separate_formal_artifacts_imported_benchmarks_and_actual_data",
      "source_version_hash_units_uncertainties_correlations_and_validity_domain",
      "prediction_map_approximation_error_and_preregistered_comparison_rule"]
    blockers := ["status_labels_are_not_independently_checked_evidence",
      "versioned_numerical_data_and_many_sector_engines_are_missing"] },
  { id := "derive_prediction_adapters_from_archived_primitive_bases"
    track := .primitiveResearch
    state := .active
    inputs := ["data/existing_primitive_inventory.json", "data/candidate_history"]
    requiredOutputs := ["candidate_specific_prediction_map_or_exact_bridge_wall",
      "archived_probe_evidence_and_checker_gap_feedback"]
    acceptance := ["no_silent_merging_of_incompatible_primitive_vocabularies",
      "no_import_of_the_target_as_a_derivation",
      "finite_probe_is_not_universal_proof",
      "negative_result_is_scoped_to_imports_and_selected_requirements"]
    blockers := ["quantitative_readout_and_composite_bridges_remain_open"] },
  { id := "exercise_false_rejection_scope_controls"
    track := .primitiveResearch
    state := .active
    inputs := ["sm_minimal_multiplet_content", "sm_gauge_anomaly_checks"]
    requiredOutputs := ["sm_neutral_singlet_scope_probe_in_candidate_history"]
    acceptance := ["minimal_content_mismatch_is_not_global_rejection_of_extensions",
      "do_not_infer_neutrino_masses_from_neutral_singlet_content",
      "independent_controls_and_history_regression_before_checker_changes"]
    blockers := [] },
  { id := "native_pair_history_adapter_and_composition_wall"
    track := .primitiveResearch
    state := .active
    inputs := ["pair_history_signed_scalar_realization",
      "pair_history_gaussian_realization", "pair_history_lower_law"]
    requiredOutputs := ["theory_experiments/amplitude_algebra.py",
      "Proofs/QMClosure/PairHistoryAdapterSafety.lean",
      "data/amplitude_algebra_controls.json", "PAIR_HISTORY_ADAPTER_RESULT.md"]
    acceptance := ["bind_exact_source_specification_to_its_original_integer_operations",
      "retain_old_unsupported_observations_and_review_only_two_changed_baselines",
      "real_projection_composition_counterexample_rejects_bridge_not_candidate",
      "scalar_and_gaussian_and_degenerate_dual_survival_does_not_select_physics",
      "phase_samples_are_diagnostics_not_rejection_requirements",
      "finite_missing_existence_witness_is_inconclusive"]
    blockers := ["generic_lower_law_does_not_supply_a_carrier_or_weight",
      "native_multiplication_does_not_derive_physical_composite_closure",
      "operational_preparation_readout_and_empirical_bridge_are_missing"] },
  { id := "native_observable_quotient_and_parameter_classification"
    track := .primitiveResearch
    state := .active
    inputs := ["native_dual_blindspot_control", "pair_history_signed_scalar_realization",
      "pair_history_gaussian_realization", "native_composition_activation_probe",
      "native_weighted_plane_probe"]
    requiredOutputs := ["Proofs/QMClosure/NativeAmplitudeObservability.lean",
      "theory_experiments/native_observability.py", "data/native_observability_review.json",
      "NATIVE_OBSERVABILITY_RESULT.md"]
    acceptance := ["all_integer_parameter_classification_is_scoped_to_supplied_quadratic_algebra",
      "dual_to_scalar_quotient_preserves_only_declared_polynomial_grammar",
      "projection_failure_is_not_candidate_rejection",
      "null_weight_alone_does_not_justify_quotient_under_composition",
      "retain_equivalent_descriptions_in_history_without_merging_or_deleting",
      "new_diagnostics_do_not_change_old_candidate_baselines"]
    blockers := ["physical_preparability_and_allowed_operations_are_not_derived",
      "additional_operations_can_break_the_restricted_quotient",
      "nonnegative_multiplicative_weights_do_not_select_gaussian_integers_or_QM"] },
  { id := "native_operation_bridge_and_false_rejection_controls"
    track := .primitiveResearch
    state := .active
    inputs := ["native_dual_blindspot_control", "pair_history_signed_scalar_realization",
      "pair_history_gaussian_realization", "data/native_operation_probes.json"]
    requiredOutputs := ["Proofs/QMClosure/NativeOperationBridge.lean",
      "theory_experiments/native_operations.py", "tests/test_native_operations.py",
      "NATIVE_OPERATION_BRIDGE_RESULT.md"]
    acceptance := ["reversible_individual_weight_preservation_does_not_imply_reference_equivalence",
      "additivity_plus_weight_preservation_is_a_conditional_pair_sum_bridge",
      "matrix_weight_identity_uses_exact_coefficients_not_finite_absence_of_counterexamples",
      "all_operation_contracts_are_diagnostics_not_primitive_rejection_requirements",
      "actual_scalar_carrier_not_ambient_determinant_controls_reversibility",
      "gaussian_quarter_turn_must_not_be_rejected_for_nonmultiplicativity",
      "new_operations_may_refine_old_equivalence_without_refuting_the_base",
      "preserve_all_candidate_history_and_existing_baselines"]
    blockers := ["joint_physical_realizability_of_preparations_operation_and_coherent_reference_readout",
      "coherent_amplitude_additivity_is_not_derived_from_probabilistic_mixture_affinity",
      "distinguishability_noncollapse_is_not_indistinguishability_congruence",
      "signed_unnormalized_pair_weight_is_not_the_existing_Nat_normalized_overlap",
      "no_full_QM_SM_gravity_or_empirical_closure_is_established"] },
  { id := "supplied_identical_pair_benchmark_and_native_bridge_wall"
    track := .checker
    state := .active
    inputs := ["data/identical_particle_controls.json", "retained_candidate_history"]
    requiredOutputs := ["theory_experiments/identical_particles.py",
      "scripts/check_identical_particles.py", "tests/test_identical_particles.py",
      "PAULI_CHECKER_RESULT.md"]
    acceptance := ["independent_exact_diagonal_and_transpose_exchange_residuals",
      "complete_mode_includes_internal_labels_but_labels_do_not_certify_completeness",
      "boson_pauli_is_not_applicable_not_success",
      "zero_tensor_is_inconclusive_prepared_state_not_vacuum_rejection",
      "sparse_unnormalized_nonzero_states_are_allowed_for_homogeneous_identities",
      "missing_native_pair_adapter_is_unsupported_not_candidate_rejection",
      "preserve_all_old_baselines_and_append_only_new_fixture_observations"]
    blockers := ["native_primitive_to_two_particle_amplitudes_bridge_is_missing",
      "statistics_selection_and_physical_mode_completeness_are_external_inputs",
      "empirical_preparation_probability_and_occupation_readout_bridge_is_missing",
      "finite_benchmark_does_not_derive_CAR_spin_statistics_or_full_QM"] }
]

def scopedSearchReadinessRequirements : List String := [
  "published_versioned_requirement_inventory_not_all_timeless_physics",
  "retained_candidates_including_unsupported_and_rejected",
  "checked_adapters_with_explicit_imports_domains_and_failure_meaning",
  "independent_positive_and_negative_controls",
  "bidirectional_history_regression_and_no_automatic_baseline_refresh",
  "explicit_unimplemented_data_engine_and_proof_obligations",
  "empirical_comparisons_require_versioned_data_and_uncertainty_models",
  "engineering_readiness_never_confirms_a_primitive_base"
]

def currentCheckerProgramPhase : String := "joint_checker_and_primitive_research_development"

def checkerWorldDescriptionComplete : Bool := false

end IDT.MetaLang.V8
