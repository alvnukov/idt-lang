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
    blockers := [] }
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
