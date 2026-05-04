from __future__ import annotations

import json
import hashlib
import math
import zipfile
from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


BASE_UNITS = ("M", "L", "T", "Q")

STATUS_VALUES = {
    "primitive",
    "definition",
    "derived",
    "derived_conditional",
    "bridge_assumption",
    "experimental_gate",
    "open",
    "blocked",
    "gate",
    "target",
    "formula",
}

QM_EXPERIMENT_STATUS_VALUES = {
    "executable_gate",
    "idt_language_description",
    "gate_candidate",
    "not_claimed",
}

QM_EXPERIMENT_REQUIRED_PRIMITIVES = (
    "event",
    "distinguishability",
    "inheritance",
    "readout_context",
    "facticity",
    "stable_invariant",
)

QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS = (
    "event_packet",
    "distinguishability_partition",
    "inheritance_update",
    "readout_context",
    "facticity_rule",
    "stable_invariant",
)

QM_CORE_PROOF_STATUS_VALUES = {
    "open",
    "target",
    "regression_supported",
    "blocked",
    "derived_conditional",
    "derived",
}

QM_CORE_PROOF_REQUIRED_OBLIGATIONS = (
    "finite_operational_core",
    "probability_measure_layer",
    "distinguishability_geometry",
    "hilbert_carrier_derivation",
    "born_rule_derivation",
    "reversible_inheritance_symmetry",
    "measurement_facticity_mechanism",
    "tensor_composition_law",
    "recompile_35_from_core",
    "continuum_action_scale_extension",
)

DISTINGUISHABILITY_GEOMETRY_REQUIREMENTS = (
    "contextual_probability_readout",
    "interference_i3_zero",
    "reversible_inheritance_maps",
    "contextual_correlation_obstruction",
    "noncopyability",
    "tensor_like_composition",
)

DISTINGUISHABILITY_GEOMETRY_CAPABILITIES = {
    "supported",
    "unsupported",
    "underdetermined",
}

DISTINGUISHABILITY_GEOMETRY_STATUSES = {
    "rejected",
    "survives",
    "underdetermined",
}

GPT_SEPARATOR_PRINCIPLES = (
    "local_tomography",
    "homogeneous_self_dual_cone",
    "continuous_reversible_bit_symmetry",
    "no_third_order_interference",
    "purification_or_filtering",
    "bounded_nonclassical_correlations",
)

IDT_LOCAL_TOMOGRAPHY_CONDITIONS = (
    "product_readout_context_closure",
    "joint_facticity_exhaustion",
    "no_hidden_joint_invariant",
    "stable_invariant_separability",
)

CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_THEOREM_ASSUMPTIONS = (
    "finite_context_family",
    "product_context_closure",
    "stable_invariant_witness_completeness",
    "product_effect_separation",
    "no_hidden_joint_only_facticizable_invariant",
)

CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_THEOREM_CONCLUSIONS = (
    "local_tomography",
    "minimal_parameter_product_basis",
)

CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_prove_Born_rule",
    "does_not_select_complex_Hilbert_from_IDT_primitives_alone",
)

CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES = (
    "event_packet",
    "distinguishability_partition",
    "readout_context",
    "facticity_rule",
    "stable_invariant",
)

IDT_PURIFICATION_FILTERING_CONDITIONS = (
    "recoverable_extension_context",
    "marginal_readout_consistency",
    "facticized_filter_context",
    "posterior_support_renormalization",
)

PURIFICATION_FILTERING_THEOREM_ASSUMPTIONS = (
    "finite_context_family",
    "recoverable_extension_context",
    "marginal_readout_consistency",
    "facticized_filter_context",
    "posterior_support_renormalization",
)

PURIFICATION_FILTERING_THEOREM_CONCLUSIONS = (
    "recoverable_marginal_extension",
    "support_restricted_filter_update",
    "zero_support_filter_rejection",
)

PURIFICATION_FILTERING_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_prove_Born_rule",
    "does_not_select_complex_Hilbert_from_IDT_primitives_alone",
)

REVERSIBLE_FILTER_CLOSURE_THEOREM_ASSUMPTIONS = (
    "finite_context_family",
    "recoverable_extension_context",
    "support_restricted_filter_update",
    "nonzero_filter_support",
    "bijective_support_witness",
)

REVERSIBLE_FILTER_CLOSURE_THEOREM_CONCLUSIONS = (
    "reversible_filter_closure",
    "zero_support_filter_rejection",
    "nonbijective_filter_witness_rejection",
)

REVERSIBLE_FILTER_CLOSURE_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_close_broader_generic_gpt_cone",
)

IDT_BOUNDED_CORRELATION_CONDITIONS = (
    "single_joint_context_facticity",
    "normalized_context_amplitudes",
    "no_global_counterfactual_table",
    "stable_correlation_invariant",
)

BOUNDED_CORRELATION_THEOREM_ASSUMPTIONS = (
    "finite_context_family",
    "single_joint_context_facticity",
    "normalized_context_amplitudes",
    "no_global_counterfactual_table",
    "stable_correlation_invariant",
    "declared_gpt_separator_principles",
)

BOUNDED_CORRELATION_THEOREM_CONCLUSIONS = (
    "tsirelson_bounded_correlation_screen",
    "pr_box_like_resource_rejection",
    "boxworld_like_gpt_rejection",
)

BOUNDED_CORRELATION_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_prove_Born_rule",
    "does_not_select_complex_Hilbert_from_IDT_primitives_alone",
)

NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS = (
    "complex_phase_orientation",
    "local_tomographic_composition",
    "associative_tensor_composition",
    "purification_filtering_route",
    "bounded_correlation_route",
)

NONCOMPLEX_JORDAN_THEOREM_ASSUMPTIONS = (
    "finite_candidate_family",
    "complex_phase_orientation",
    "local_tomographic_composition",
    "associative_tensor_composition",
    "purification_filtering_route",
    "bounded_correlation_route",
)

NONCOMPLEX_JORDAN_THEOREM_CONCLUSIONS = (
    "real_hilbert_like_rejection",
    "quaternionic_hilbert_like_rejection",
    "exceptional_jordan_like_rejection",
)

NONCOMPLEX_JORDAN_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_prove_Born_rule",
    "does_not_select_complex_Hilbert_from_IDT_primitives_alone",
)

GENERIC_GPT_CLOSURE_CONDITIONS = (
    "finite_route_witness_completeness",
    "no_unwitnessed_effect_cone_degrees",
    "tomographic_state_effect_duality",
    "reversible_filter_closure",
    "bounded_composite_correlations",
)

GENERIC_GPT_THEOREM_ASSUMPTIONS = (
    "finite_candidate_family",
    "finite_route_witness_completeness",
    "no_unwitnessed_effect_cone_degrees",
    "tomographic_state_effect_duality",
    "reversible_filter_closure",
    "bounded_composite_correlations",
)

GENERIC_GPT_THEOREM_CONCLUSIONS = (
    "unconstrained_generic_gpt_cone_rejection",
    "route_closed_gpt_subtheory_delegated_to_subfrontier",
    "generic_gpt_cone_remains_underdetermined",
)

GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_prove_Born_rule",
    "does_not_select_complex_Hilbert_from_IDT_primitives_alone",
)

BROADER_GENERIC_GPT_FRONTIER_SLICES = (
    "finite_route_incomplete_slice",
    "finite_route_closed_slice",
    "nonfinite_unwitnessed_residual",
)

BROADER_GENERIC_GPT_FRONTIER_STATUSES = (
    "rejected",
    "collapses_to_complex_hilbert_like",
    "underdetermined",
)

BROADER_GENERIC_GPT_THEOREM_ASSUMPTIONS = (
    "finite_candidate_family",
    "declared_route_witness_screen",
    "route_closed_subfrontier",
    "nonfinite_residual_boundary",
)

BROADER_GENERIC_GPT_THEOREM_CONCLUSIONS = (
    "finite_route_incomplete_slice_rejected",
    "finite_route_closed_slice_collapses_to_complex_hilbert_like",
    "nonfinite_unwitnessed_residual_remains_underdetermined",
)

BROADER_GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_close_nonfinite_generic_gpt_residual",
)

NONFINITE_GPT_RESIDUAL_FRONTIER_OBLIGATIONS = (
    "uniform_route_witness_compactness",
    "idt_derivation_of_uniform_witness_bound",
    "idt_derivation_of_no_emergent_joint_only_invariants",
)

NONFINITE_GPT_RESIDUAL_FRONTIER_STATUSES = (
    "open",
    "conditional_proof",
    "formal_proof",
)

NONFINITE_GPT_RESIDUAL_COMPACTNESS_ASSUMPTIONS = (
    "uniform_finite_route_witness_bound",
    "limit_preserves_facticized_readout_separation",
    "no_emergent_unwitnessed_composite_invariant",
)

NONFINITE_GPT_RESIDUAL_COMPACTNESS_CONCLUSIONS = (
    "nonfinite_limit_residual_reduces_to_finite_route_screen",
    "unwitnessed_residual_rejected_by_effect_separation",
)

NONFINITE_GPT_RESIDUAL_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_close_nonfinite_generic_gpt_residual_without_IDT_derivations",
)

NO_EMERGENT_JOINT_ONLY_INVARIANT_ASSUMPTIONS = (
    "context_product_exhaustion",
    "product_effect_separation",
    "stable_invariant_witness_completeness",
    "facticized_readout_closure",
)

NO_EMERGENT_JOINT_ONLY_INVARIANT_CONCLUSIONS = (
    "joint_only_invariant_requires_product_witness",
    "unwitnessed_joint_only_invariant_rejected",
)

NO_EMERGENT_JOINT_ONLY_INVARIANT_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_close_uniform_witness_bound",
)

TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_ASSUMPTIONS = (
    "finite_route_witness_completeness",
    "no_unwitnessed_effect_cone_degrees",
    "local_tomographic_state_basis",
    "full_rank_effect_separation_matrix",
)

TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_CONCLUSIONS = (
    "tomographic_state_effect_duality",
    "no_hidden_effect_kernel",
)

TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_carrier_selection",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_close_reversible_filter_closure",
)

BORN_READOUT_ROUTE_CONDITIONS = (
    "normalized_amplitude_packet",
    "phase_invariant_readout",
    "orthogonal_event_additivity",
    "facticized_context_probability",
)

BORN_READOUT_THEOREM_ASSUMPTIONS = (
    "finite_amplitude_packet_family",
    "normalized_amplitude_packet",
    "phase_invariant_readout",
    "orthogonal_event_additivity",
    "facticized_context_probability",
)

BORN_READOUT_THEOREM_CONCLUSIONS = (
    "quadratic_modulus_readout_survives",
    "linear_modulus_readout_rejected_on_registered_packets",
)

BORN_READOUT_THEOREM_FORBIDDEN_UPGRADES = (
    "does_not_prove_universal_Born_rule",
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_carrier",
    "does_not_replace_measurement_facticity_theorem",
)

TENSOR_COMPOSITION_ROUTE_CONDITIONS = (
    "product_context_basis",
    "local_tomographic_dimension_product",
    "schmidt_factorization_rank",
    "entangled_nonproduct_states",
)

QM_CORE_RECOMPILE_REQUIRED_ROUTES = (
    "born_quadratic_readout_route_demo",
    "measurement_facticity_route_demo",
    "tensor_composition_route_demo",
    "context_product_exhaustion_demo",
    "idt_local_tomography_derivation_demo",
    "idt_purification_filtering_demo",
    "idt_bounded_correlation_demo",
    "noncomplex_jordan_separator_demo",
    "generic_gpt_closure_separator_demo",
    "carrier_selection_frontier_demo",
)

MEASUREMENT_FACTICITY_ROUTE_CONDITIONS = (
    "context_readout_gain",
    "disturbance_bound",
    "recoverability_loss_threshold",
    "stable_record_facticity",
)

CONTINUUM_ACTION_FRONTIER_REQUIREMENTS = (
    "finite_generator_reconstruction",
    "finite_translation_relation",
    "finite_weyl_relation",
    "strong_continuity_modulus",
    "generator_difference_convergence",
    "calibrated_action_holdout",
    "first_principles_hbar_lock",
    "field_mode_limit",
)

FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS = (
    "universal_carrier_selection_theorem",
    "hilbert_carrier_derivation",
    "universal_born_rule_theorem",
    "wigner_reversible_inheritance_theorem",
    "apparatus_facticity_theorem",
    "monoidal_tensor_composition_theorem",
    "first_principles_hbar_lock",
    "field_mode_continuum_limit",
)

FULL_QM_OBSTRUCTION_KINDS = (
    "carrier_selection",
    "imported_carrier",
    "born_rule_derivation",
    "symmetry_inheritance",
    "apparatus_facticity",
    "composition_law",
    "calibration_not_derivation",
    "continuum_limit",
)

CARRIER_SELECTION_OPEN_OBSTRUCTIONS = (
    "extend_context_product_exhaustion_to_carrier_theorem",
    "extend_purification_filtering_to_carrier_theorem",
    "extend_bounded_correlation_to_carrier_theorem",
    "extend_noncomplex_jordan_exclusion_to_classification_theorem",
    "extend_generic_gpt_exclusion_to_classification_theorem",
)

CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES = (
    "finite_witnessed",
    "conditional_proof",
    "open",
    "blocked",
    "formal_proof",
)

CONTEXT_PRODUCT_CARRIER_LEMMA_TARGET = "extend_context_product_exhaustion_to_carrier_theorem"
PURIFICATION_FILTERING_CARRIER_LEMMA_TARGET = "extend_purification_filtering_to_carrier_theorem"
BOUNDED_CORRELATION_CARRIER_LEMMA_TARGET = "extend_bounded_correlation_to_carrier_theorem"
NONCOMPLEX_JORDAN_CLASSIFICATION_LEMMA_TARGET = "extend_noncomplex_jordan_exclusion_to_classification_theorem"
GENERIC_GPT_CLASSIFICATION_LEMMA_TARGET = "extend_generic_gpt_exclusion_to_classification_theorem"

CARRIER_SELECTION_LEMMA_ROUTE_REFS = {
    CONTEXT_PRODUCT_CARRIER_LEMMA_TARGET: "context_product_carrier_lemma_route_demo",
    PURIFICATION_FILTERING_CARRIER_LEMMA_TARGET: "purification_filtering_carrier_lemma_route_demo",
    BOUNDED_CORRELATION_CARRIER_LEMMA_TARGET: "bounded_correlation_carrier_lemma_route_demo",
    NONCOMPLEX_JORDAN_CLASSIFICATION_LEMMA_TARGET: "noncomplex_jordan_classification_lemma_route_demo",
    GENERIC_GPT_CLASSIFICATION_LEMMA_TARGET: "generic_gpt_classification_lemma_route_demo",
}

CARRIER_SELECTION_FRONTIER_STATUSES = {
    "not_derived",
    "selected_by_current_gates",
}

CARRIER_QUANTIFIER_FRONTIER_CLASSES = (
    "complex_hilbert_like",
    "noncomplex_jordan_family",
    "unconstrained_generic_gpt_cone",
    "route_closed_gpt_subtheory",
    "broader_generic_gpt_cone",
)

CARRIER_QUANTIFIER_STATUSES = {
    "survives",
    "rejected",
    "collapses_to_complex_hilbert_like",
    "underdetermined",
    "out_of_scope",
}

CARRIER_QUANTIFIER_FRONTIER_STATUSES = {
    "open",
    "closed",
}

ROUTE_CLOSED_GPT_FRONTIER_REQUIREMENTS = (
    "tomographic_state_effect_duality",
    "reversible_filter_closure",
)

ROUTE_CLOSED_GPT_FRONTIER_INHERITED_SUPPORT = (
    "finite_route_witness_completeness",
    "no_unwitnessed_effect_cone_degrees",
    "bounded_composite_correlations",
)

ROUTE_CLOSED_GPT_FRONTIER_STATUSES = {
    "underdetermined",
    "collapses_to_complex_hilbert_like",
    "rejected",
}

NON_DERIVED_DEPENDENCY_STATUSES = {
    "open",
    "blocked",
    "bridge_assumption",
    "experimental_gate",
    "target",
}

ACTION_STANDARD_TARGET = "action_standard_work_time_closure_I"

ELL0_CLOSURE_TARGET = "ell0_closure_I"

CLOCK_VACUUM_POLE_TARGET = "clock_vacuum_pole_closure_I"

SPECTRAL_PRIMITIVE_REDUCTION_TARGET = "spectral_primitive_reduction_I"

CLOCK_VACUUM_POLE_REQUIRED_SYMBOLS = (
    "clock_vacuum_spectral_law_I",
    "omega_ell_I",
    SPECTRAL_PRIMITIVE_REDUCTION_TARGET,
)

CLOCK_VACUUM_POLE_REQUIRED_GATES = (
    "clock_vacuum_pole_candidate_demo",
    "clock_vacuum_pole_universality_demo",
    "clock_vacuum_pole_no_calibrated_input_demo",
    "clock_vacuum_pole_no_postfit_demo",
)

SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS = (
    "clock_vacuum_spectral_law_I",
    "omega_ell_I",
    "cross_update_contraction_selection_I",
    "primitive_transition_phase_readout_I",
    "non_exact_holonomy_source_I",
    "fixed_point_step_invariant_I",
)

SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_GATES = (
    "spectral_law_free_parameter_audit_demo",
    "spectral_law_no_calibrated_input_demo",
    "fixed_point_component_status_demo",
    "non_exact_holonomy_source_demo",
)

CROSS_UPDATE_CONTRACTION_SELECTION_TARGET = "cross_update_contraction_selection_I"

CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_SYMBOLS = (
    "cross_update_support_relation_I",
    "cross_update_block_kernel_I",
    "support_respecting_isometry_I",
    "contraction_phase_selection_rule_I",
    "non_exact_holonomy_source_I",
)

CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_GATES = (
    "contraction_phase_degeneracy_demo",
    "support_matching_phase_freedom_demo",
    "contraction_selection_no_calibrated_input_demo",
)

FIXED_POINT_STEP_INVARIANT_TARGET = "fixed_point_step_invariant_I"

FIXED_POINT_STEP_INVARIANT_REQUIRED_SYMBOLS = (
    "fixed_point_rotation_map_I",
    "cycle_rotation_number_I",
    "step_clock_readout_rule_I",
    "radar_response_pole_relation_I",
)

FIXED_POINT_STEP_INVARIANT_REQUIRED_GATES = (
    "fixed_point_step_integer_obstruction_demo",
    "fixed_point_step_free_parameter_audit_demo",
    "fixed_point_step_no_gravity_input_demo",
)

PRIMITIVE_TRANSITION_PHASE_TARGET = "primitive_transition_phase_readout_I"

PRIMITIVE_TRANSITION_PHASE_REQUIRED_SYMBOLS = (
    "cross_update_block_kernel_I",
    "transfer_phase_normalization_I",
    "cycle_holonomy_composition_I",
    "phase_branch_reconstruction_I",
)

PRIMITIVE_TRANSITION_PHASE_REQUIRED_GATES = (
    "transition_phase_unit_readout_demo",
    "cycle_holonomy_composition_demo",
    "primitive_transition_phase_no_calibrated_input_demo",
)

HOLONOMY_SOURCE_CLASSES = (
    "discrete_curvature",
    "topological_winding",
    "action_cost_obstruction",
    "source_coupled_phase_response",
)

HOLONOMY_SOURCE_CLASSES_WITH_NONE = HOLONOMY_SOURCE_CLASSES + ("none",)

PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET = "primitive_holonomy_source_selector_I"

PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_SYMBOLS = (
    "primitive_source_class_registry_I",
    "pre_observation_selection_rule_I",
    "selector_holdout_policy_I",
)

PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_GATES = (
    "holonomy_selector_class_registry_demo",
    "holonomy_selector_status_demo",
    "holonomy_selector_no_calibrated_input_demo",
)

PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET = "primitive_topology_winding_selector_I"

PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_SYMBOLS = (
    "cycle_word_grammar_I",
    "cycle_homotopy_class_I",
    "orientation_reversal_rule_I",
    "winding_additivity_rule_I",
)

PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_GATES = (
    "winding_selector_homotopy_consistency_demo",
    "winding_selector_orientation_reversal_demo",
    "winding_selector_additivity_demo",
    "winding_selector_no_calibrated_input_demo",
)

SECTOR_ROLE_VALUES = (
    "structural_selector",
    "dimensional_anchor",
    "dimensionless_coupling",
    "bridge_assumption",
    "derived_readout",
    "experimental_gate",
    "blocked_claim",
)

RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES = (
    "claim_role_type_system",
    "dependency_dag",
    "proof_status_axis",
    "prediction_protocol",
    "failure_ledger",
    "minimal_core_kernel",
    "theorem_cards",
)

RESEARCH_GRAPH_CONTRACT_SCHEMA_REFS = (
    "symbols.status",
    "derivations.status",
    "derivations.depends_on",
    "qm_core_proof_obligations",
    "qm_core_proof_obligations.status",
    "theorem_cards",
    "theorem_cards.proof_status",
)

RESEARCH_GRAPH_CONTRACT_CHECK_REFS = (
    "derivation graph cycles",
    "forbidden input paths",
)

THEOREM_CARD_ROLE_VALUES = (
    "primitive",
    "definition",
    "axiom",
    "bridge",
    "calibration",
    "readout",
    "gate",
    "prediction",
    "failure",
    "theorem",
)

THEOREM_CARD_PROOF_STATUS_VALUES = (
    "formal_proof",
    "conditional_proof",
    "finite_verifier_pass",
    "numerical_evidence",
    "calibrated_match",
    "open",
    "blocked",
)

SECTOR_ROLE_TAXONOMY_TARGET = "sector_role_taxonomy_I"

SECTOR_ROLE_TAXONOMY_REQUIRED_SYMBOLS = (
    "structural_selector_registry_I",
    "dimensional_anchor_registry_I",
    "dimensionless_coupling_registry_I",
    "bridge_assumption_registry_I",
    "derived_readout_registry_I",
    "cross_sector_holdout_policy_I",
)

SECTOR_ROLE_TAXONOMY_REQUIRED_GATES = (
    "sector_role_registry_demo",
    "sector_role_assignment_partition_demo",
    "dimensionful_anchor_policy_demo",
    "dimensionless_coupling_policy_demo",
    "bridge_assumption_boundary_demo",
)

NON_EXACT_HOLONOMY_SOURCE_TARGET = "non_exact_holonomy_source_I"

NON_EXACT_HOLONOMY_SOURCE_REQUIRED_SYMBOLS = (
    PRIMITIVE_TRANSITION_PHASE_TARGET,
    "phase_branch_reconstruction_I",
    PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET,
    "holonomy_source_classification_I",
    "phase_cost_independence_I",
)

NON_EXACT_HOLONOMY_SOURCE_REQUIRED_GATES = (
    "holonomy_source_classification_demo",
    "phase_branch_additivity_demo",
    "phase_branch_no_postfit_demo",
    "phase_cost_independence_demo",
)

ELL0_EMERGENCE_CLEARANCE_TARGET = "ell0_emergence_clearance_I"

ELL0_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS = (
    "c_I",
    "omega_ell_I",
    CLOCK_VACUUM_POLE_TARGET,
)

ELL0_EMERGENCE_CLEARANCE_REQUIRED_GATES = (
    "ell0_candidate_from_clock_pole_demo",
    "ell0_candidate_no_gravity_input_demo",
    "ell0_bound_not_value_demo",
)

ELL0_PHYSICAL_CANDIDATE_TARGET = "ell0_physical_candidate_I"

ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS = (
    ELL0_EMERGENCE_CLEARANCE_TARGET,
)

ELL0_CLOSURE_REQUIRED_SYMBOLS = ("ell0", "c_I", "omega_ell_I", ELL0_PHYSICAL_CANDIDATE_TARGET)

ELL0_CLOSURE_REQUIRED_GATES = (
    "ell0_radar_consistency_demo",
    "ell0_link_frequency_consistency_demo",
    "ell0_no_gravity_input_demo",
    "tick_scale_lock_status_demo",
)

PRIMITIVE_TICK_TARGET = "primitive_tick_closure_I"

PRIMITIVE_TICK_REQUIRED_SYMBOLS = (
    "primitive_tick_I",
    "ell0",
    ELL0_CLOSURE_TARGET,
    "c_I",
    "tick_scale_lock_I",
)

PRIMITIVE_TICK_REQUIRED_GATES = (
    "primitive_tick_clock_count_demo",
    "primitive_tick_radar_consistency_demo",
    "primitive_tick_reparam_invariance_demo",
    "primitive_tick_clock_universality_demo",
    "tick_scale_lock_status_demo",
)

PRIMITIVE_WORK_TARGET = "primitive_work_unit_closure_I"

PRIMITIVE_MASS_ANCHOR_TARGET = "primitive_mass_anchor_closure_I"

PRIMITIVE_MASS_ANCHOR_REQUIRED_SYMBOLS = ("primitive_mass_anchor_I", "work_scale_lock_I")

PRIMITIVE_MASS_ANCHOR_REQUIRED_GATES = (
    "primitive_mass_anchor_inertia_response_demo",
    "primitive_mass_anchor_no_quantum_gravity_input_demo",
    "work_scale_lock_status_demo",
)

RHO_CHI_PROTOCOL_TARGET = "rho_chi_protocol_closure_I"

RHO_CHI_PROTOCOL_REQUIRED_SYMBOLS = (
    "rho_chi_I",
    "C_chi_I",
    "tau_chi_star",
    "ell0",
    ELL0_CLOSURE_TARGET,
)

RHO_CHI_PROTOCOL_REQUIRED_GATES = (
    "rho_chi_protocol_invariance_demo",
    "rho_chi_no_gravity_input_demo",
)

KAPPA_OMEGA_CONSISTENCY_TARGET = "kappa_omega_consistency_closure_I"

KAPPA_OMEGA_CONSISTENCY_REQUIRED_SYMBOLS = (
    "kappa_chi_I",
    "hbar_I",
    "omega_ell_I",
    "rho_chi_I",
    RHO_CHI_PROTOCOL_TARGET,
    CLOCK_VACUUM_POLE_TARGET,
)

KAPPA_OMEGA_CONSISTENCY_REQUIRED_GATES = (
    "kappa_omega_consistency_demo",
    "kappa_omega_no_gravity_input_demo",
)

NON_GRAVITY_LINK_BOUND_TARGET = "omega_ell_lower_bound_I"

NON_GRAVITY_LINK_BOUND_REQUIRED_SYMBOLS = (
    "minimal_link_dispersion_residual_I",
    "photon_dispersion_omega_bound_obs",
    "matter_wave_omega_bound_proxy",
    "omega_ell_lower_bound_I",
    "ell0_upper_bound_I",
    "primitive_tick_upper_bound_I",
    "c_I",
)

NON_GRAVITY_LINK_BOUND_REQUIRED_DEPENDENCIES = (
    "minimal_link_dispersion_residual_I",
    "photon_dispersion_omega_bound_obs",
    "matter_wave_omega_bound_proxy",
)

NON_GRAVITY_LINK_BOUND_REQUIRED_GATES = (
    "photon_dispersion_bound_demo",
    "matter_wave_bound_demo",
    "composite_omega_bound_demo",
    "ell0_tick_bound_demo",
)

WEAK_FIELD_CLOCK_TARGET = "weak_field_clock_calculator_I"

WEAK_FIELD_CLOCK_REQUIRED_SYMBOLS = (
    "c_I",
    "G_N",
    "G_I",
    "Phi_I",
    "gamma_ppn_I",
    WEAK_FIELD_CLOCK_TARGET,
)

WEAK_FIELD_CLOCK_REQUIRED_DEPENDENCIES = (
    "c_I",
    "G_N",
    "Phi_I",
    "gamma_ppn_I",
)

WEAK_FIELD_CLOCK_REQUIRED_GATES = (
    "clock_redshift_1m_demo",
    "combined_clock_rate_demo",
    "point_mass_clock_field_demo",
    "source_flux_gauss_demo",
    "ppn_light_bending_solar_limb_demo",
)

SOURCE_LAW_VARIATIONAL_TARGET = "clock_strain_source_law_I"

SOURCE_LAW_VARIATIONAL_REQUIRED_SYMBOLS = (
    "Phi_I",
    "rho_source_I",
    "alpha_chi_I",
    "beta_source_I",
    SOURCE_LAW_VARIATIONAL_TARGET,
)

SOURCE_LAW_VARIATIONAL_REQUIRED_DEPENDENCIES = (
    "Phi_I",
    "rho_source_I",
    "alpha_chi_I",
    "beta_source_I",
)

SOURCE_LAW_VARIATIONAL_REQUIRED_GATES = (
    "clock_strain_variational_poisson_demo",
    "source_law_coefficient_demo",
)

PPN_NO_SLIP_TARGET = "ppn_no_slip_validation_I"

PPN_NO_SLIP_REQUIRED_SYMBOLS = (
    "Phi_I",
    "Psi_I",
    "gamma_ppn_I",
    "beta_ppn_I",
    PPN_NO_SLIP_TARGET,
)

PPN_NO_SLIP_REQUIRED_DEPENDENCIES = (
    "Phi_I",
    "Psi_I",
    "gamma_ppn_I",
    "beta_ppn_I",
)

PPN_NO_SLIP_REQUIRED_GATES = (
    "ppn_gamma_no_slip_demo",
    "ppn_light_bending_solar_limb_demo",
    "shapiro_delay_solar_limb_demo",
    "ppn_perihelion_mercury_demo",
)

NO_SLIP_STRESS_TARGET = "no_slip_stress_closure_I"

NO_SLIP_STRESS_REQUIRED_SYMBOLS = (
    "Psi_I",
    "Phi_I",
    "anisotropic_stress_I",
    "non_gravity_slip_residual_I",
    NO_SLIP_STRESS_TARGET,
)

NO_SLIP_STRESS_REQUIRED_DEPENDENCIES = (
    "Psi_I",
    "Phi_I",
    "anisotropic_stress_I",
    "non_gravity_slip_residual_I",
)

NO_SLIP_STRESS_REQUIRED_GATES = (
    "slip_source_poisson_demo",
    "zero_stress_boundary_no_slip_demo",
    "source_continuity_demo",
)

SOURCE_STRESS_PACKET_TARGET = "source_stress_packet_closure_I"

SOURCE_STRESS_PACKET_REQUIRED_SYMBOLS = (
    "source_stress_tensor_I",
    "isotropic_pressure_I",
    "anisotropic_stress_I",
    "stress_coarse_grain_I",
    SOURCE_STRESS_PACKET_TARGET,
)

SOURCE_STRESS_PACKET_REQUIRED_DEPENDENCIES = (
    "source_stress_tensor_I",
    "isotropic_pressure_I",
    "anisotropic_stress_I",
    "stress_coarse_grain_I",
)

SOURCE_STRESS_PACKET_REQUIRED_GATES = (
    "stress_tensor_decomposition_demo",
    "isotropic_stress_zero_anisotropy_demo",
    "coarse_grained_anisotropy_cancellation_demo",
    "slip_source_bound_from_anisotropy_demo",
)

SCALE_RESIDUAL_POLICY_TARGET = "scale_separated_residual_policy_I"

SCALE_RESIDUAL_POLICY_REQUIRED_SYMBOLS = (
    "validated_weak_field_domain_I",
    "transition_scale_I",
    "non_gravity_slip_residual_I",
    "dark_sector_residual_candidate_I",
    SCALE_RESIDUAL_POLICY_TARGET,
)

SCALE_RESIDUAL_POLICY_REQUIRED_DEPENDENCIES = (
    "validated_weak_field_domain_I",
    "transition_scale_I",
    "non_gravity_slip_residual_I",
    "dark_sector_residual_candidate_I",
)

SCALE_RESIDUAL_POLICY_REQUIRED_GATES = (
    "solar_system_residual_bound_demo",
    "scale_residual_activation_profile_demo",
    "validated_domain_no_refit_demo",
)

SCREENED_SLIP_RESIDUAL_TARGET = "screened_slip_residual_candidate_I"

SCREENED_SLIP_RESIDUAL_REQUIRED_SYMBOLS = (
    "residual_amplitude_I",
    "residual_transition_length_I",
    "non_gravity_slip_residual_I",
    "dark_sector_residual_candidate_I",
    SCREENED_SLIP_RESIDUAL_TARGET,
)

SCREENED_SLIP_RESIDUAL_REQUIRED_DEPENDENCIES = (
    "residual_amplitude_I",
    "residual_transition_length_I",
    "non_gravity_slip_residual_I",
    "dark_sector_residual_candidate_I",
)

SCREENED_SLIP_RESIDUAL_REQUIRED_GATES = (
    "screened_transition_bound_demo",
    "screened_profile_prediction_demo",
    "screened_acceleration_output_demo",
    "screened_light_bending_output_demo",
)

SCREENED_OBSERVATIONAL_GATE_TARGET = "screened_slip_observational_gate_I"

SCREENED_OBSERVATIONAL_GATE_REQUIRED_SYMBOLS = (
    SCREENED_SLIP_RESIDUAL_TARGET,
    "validated_weak_field_domain_I",
    "galactic_residual_test_I",
    "sparc_rotation_curve_data_I",
    "observed_centripetal_acceleration_I",
    "baryonic_rotation_acceleration_I",
    "sparc_galaxy_residual_packet_I",
    "screened_sparc_capacity_test_I",
    "sparc_amplitude_lower_bound_I",
    "galaxy_residual_no_postfit_policy_I",
    "sparc_solar_transition_bound_I",
    "old_screened_profile_rejection_I",
    "sparc_corridor_feasibility_I",
    "sparc_no_fit_claim_policy_I",
    "sparc_radius_scale_map_candidate_I",
    "sparc_simple_map_rejection_I",
    "sparc_baryonic_acceleration_map_candidate_I",
    "sparc_acceleration_map_rejection_I",
    "sparc_inverse_residual_map_forbidden_I",
    "sparc_baryonic_exponent_family_I",
    "sparc_q_selection_postfit_policy_I",
    "sparc_q25_heldout_transfer_I",
    "sparc_heldout_selection_policy_I",
    SCREENED_OBSERVATIONAL_GATE_TARGET,
)

SCREENED_OBSERVATIONAL_GATE_REQUIRED_DEPENDENCIES = (
    SCREENED_SLIP_RESIDUAL_TARGET,
    "validated_weak_field_domain_I",
    "galactic_residual_test_I",
    "sparc_rotation_curve_data_I",
    "observed_centripetal_acceleration_I",
    "baryonic_rotation_acceleration_I",
    "sparc_galaxy_residual_packet_I",
    "screened_sparc_capacity_test_I",
    "sparc_amplitude_lower_bound_I",
    "galaxy_residual_no_postfit_policy_I",
    "sparc_solar_transition_bound_I",
    "old_screened_profile_rejection_I",
    "sparc_corridor_feasibility_I",
    "sparc_no_fit_claim_policy_I",
    "sparc_radius_scale_map_candidate_I",
    "sparc_simple_map_rejection_I",
    "sparc_baryonic_acceleration_map_candidate_I",
    "sparc_acceleration_map_rejection_I",
    "sparc_inverse_residual_map_forbidden_I",
    "sparc_baryonic_exponent_family_I",
    "sparc_q_selection_postfit_policy_I",
    "sparc_q25_heldout_transfer_I",
    "sparc_heldout_selection_policy_I",
)

SCREENED_OBSERVATIONAL_GATE_REQUIRED_GATES = (
    "screened_solar_galactic_observation_demo",
    "sparc_ddo154_outer_baryonic_residual_demo",
    "sparc_ddo154_residual_packet_demo",
    "screened_sparc_capacity_bound_demo",
    "sparc_ddo154_amplitude_lower_bound_demo",
    "galaxy_residual_no_postfit_demo",
    "sparc_amplitude_solar_transition_bound_demo",
    "old_screened_profile_solar_rejection_demo",
    "sparc_solar_galactic_corridor_demo",
    "sparc_no_fit_claim_status_demo",
    "sparc_proportional_radius_map_rejection_demo",
    "sparc_baryonic_acceleration_power_map_demo",
    "sparc_inverse_residual_map_forbidden_demo",
    "sparc_baryonic_exponent_family_scan_demo",
    "sparc_q_selection_postfit_demo",
    "sparc_q25_heldout_transfer_demo",
    "sparc_heldout_selection_no_postfit_demo",
)

PRIMITIVE_WORK_REQUIRED_SYMBOLS = (
    "primitive_work_unit_I",
    "primitive_mass_anchor_I",
    PRIMITIVE_MASS_ANCHOR_TARGET,
    "work_scale_lock_I",
)

PRIMITIVE_WORK_REQUIRED_GATES = (
    "primitive_work_balance_demo",
    "primitive_work_no_quantum_energy_demo",
    "primitive_work_coarse_grain_balance_demo",
    "primitive_work_sector_universality_demo",
    "primitive_work_dimensional_obstruction_demo",
    "work_scale_lock_status_demo",
)

SOURCE_RESPONSE_CHARGE_TARGET = "source_response_charge_closure_I"

SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS = (
    "primitive_mass_anchor_I",
    PRIMITIVE_MASS_ANCHOR_TARGET,
    "source_response_charge_I",
    "active_passive_inertial_equality_I",
    SOURCE_STRESS_PACKET_TARGET,
    SOURCE_LAW_VARIATIONAL_TARGET,
)

SOURCE_RESPONSE_CHARGE_REQUIRED_GATES = (
    "source_response_charge_normalization_demo",
    "source_response_no_calibrated_input_demo",
    "active_passive_inertial_equality_demo",
    "source_response_packet_universality_demo",
    "source_response_no_postfit_demo",
)

GEOMETRY_RESPONSE_FACTOR_TARGET = "geometry_response_factor_closure_I"

GEOMETRY_RESPONSE_FACTOR_REQUIRED_SYMBOLS = (
    "D_S",
    "z_I",
    "q_V_I",
    "ell0",
    ELL0_CLOSURE_TARGET,
)

GEOMETRY_RESPONSE_FACTOR_REQUIRED_GATES = (
    "geometry_response_factor_freeze_demo",
    "geometry_response_no_gravity_anchor_demo",
)

CLOCK_VACUUM_STIFFNESS_TARGET = "clock_vacuum_stiffness_from_source_charge_I"

CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS = (
    SOURCE_RESPONSE_CHARGE_TARGET,
    "source_response_charge_I",
    SOURCE_LAW_VARIATIONAL_TARGET,
    "clock_vacuum_spectral_law_I",
    "kappa_chi_I",
    GEOMETRY_RESPONSE_FACTOR_TARGET,
)

CLOCK_VACUUM_STIFFNESS_REQUIRED_GATES = (
    "clock_vacuum_stiffness_from_source_response_demo",
    "clock_vacuum_stiffness_universality_demo",
    "clock_vacuum_stiffness_no_calibrated_input_demo",
    "clock_vacuum_stiffness_no_postfit_demo",
)

G_EMERGENCE_CLEARANCE_TARGET = "G_emergence_clearance_I"

G_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS = (
    "c_I",
    "ell0",
    ELL0_CLOSURE_TARGET,
    "D_S",
    "z_I",
    "q_V_I",
    GEOMETRY_RESPONSE_FACTOR_TARGET,
    "kappa_chi_I",
    CLOCK_VACUUM_STIFFNESS_TARGET,
    SOURCE_RESPONSE_CHARGE_TARGET,
    SOURCE_LAW_VARIATIONAL_TARGET,
)

G_EMERGENCE_CLEARANCE_REQUIRED_GATES = (
    "G_symbolic_clock_strain_candidate_demo",
    "G_candidate_no_calibrated_input_demo",
    "G_candidate_no_postfit_holdout_demo",
)

FIRST_PRINCIPLES_G_CANDIDATE_TARGET = "first_principles_G_candidate_I"

FIRST_PRINCIPLES_G_CANDIDATE_REQUIRED_SYMBOLS = (
    G_EMERGENCE_CLEARANCE_TARGET,
)

ACTION_STANDARD_REQUIRED_SYMBOLS = (
    "primitive_work_unit_I",
    "primitive_tick_I",
    PRIMITIVE_WORK_TARGET,
    PRIMITIVE_TICK_TARGET,
    "action_scale_gauge_obstruction_I",
    "tick_scale_lock_I",
    "work_scale_lock_I",
    "action_anchor_lock_I",
    "A0_I",
)

ACTION_STANDARD_REQUIRED_GATES = (
    "action_standard_work_time_provenance_demo",
    "action_scale_gauge_obstruction_demo",
    "action_anchor_lock_status_demo",
)

QM_FOUNDATION_REQUIRED_SYMBOLS = (
    "complex_amplitude_packet_I",
    "born_readout_I",
    "unitary_evolution_I",
    "continuum_limit_I",
    "qm_continuum_limit_closure_I",
    "schrodinger_generator_I",
    "hbar_action_standard_closure_I",
    "hbar_I",
    "hamiltonian_energy_operator_I",
    "translation_generator_I",
    "momentum_operator_I",
    "de_broglie_relation_I",
    "canonical_commutator_I",
    "observable_context_I",
    "apparatus_context_dynamics_I",
    "measurement_facticity_I",
    "qm_generator_translation_closure_I",
    "qm_apparatus_facticity_closure_I",
    "qm_dynamics_action_facticity_closure_I",
)

QM_FOUNDATION_CLOSED_STATUSES = {"derived", "definition", "primitive"}

QM_SINGLE_PASS_TARGET = "qm_dynamics_action_facticity_closure_I"

QM_SINGLE_PASS_REQUIRED_SYMBOLS = (
    "continuum_limit_I",
    "qm_continuum_limit_closure_I",
    "schrodinger_generator_I",
    "A0_I",
    "bar_C_gamma",
    "theta_gamma",
    "hbar_action_standard_closure_I",
    "hbar_I",
    "hamiltonian_energy_operator_I",
    "translation_generator_I",
    "momentum_operator_I",
    "de_broglie_relation_I",
    "canonical_commutator_I",
    "qm_generator_translation_closure_I",
    "observable_context_I",
    "apparatus_context_dynamics_I",
    "measurement_facticity_I",
    "qm_apparatus_facticity_closure_I",
)

HBAR_ACTION_ROUTE_REQUIRED_DEPENDENCIES = ("A0_I", "bar_C_gamma", "theta_gamma")

HBAR_ACTION_STANDARD_TARGET = "hbar_action_standard_closure_I"

HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS = (
    "action_standard_work_time_closure_I",
    "A0_I",
    "bar_C_gamma",
    "theta_gamma",
    "action_scale_gauge_obstruction_I",
    "action_anchor_lock_I",
    "hbar_I",
)

HBAR_ACTION_STANDARD_REQUIRED_GATES = (
    "action_standard_work_time_provenance_demo",
    "action_standard_provenance_demo",
    "action_scale_gauge_obstruction_demo",
    "action_anchor_lock_status_demo",
    "phase_action_scale_universality_demo",
    "action_standard_independence_demo",
    "hbar_known_gate_holdout_demo",
)

JOINT_ACTION_GRAVITY_ANCHOR_TARGET = "joint_action_gravity_anchor_I"

JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS = (
    "primitive_tick_I",
    PRIMITIVE_TICK_TARGET,
    "primitive_work_unit_I",
    PRIMITIVE_WORK_TARGET,
    "primitive_mass_anchor_I",
    PRIMITIVE_MASS_ANCHOR_TARGET,
    SOURCE_RESPONSE_CHARGE_TARGET,
    ACTION_STANDARD_TARGET,
    HBAR_ACTION_STANDARD_TARGET,
    "hbar_I",
    "clock_strain_source_law_I",
    "source_stress_packet_closure_I",
    CLOCK_VACUUM_STIFFNESS_TARGET,
    "G_I",
)

QM_GENERATOR_TRANSLATION_TARGET = "qm_generator_translation_closure_I"

QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS = (
    "unitary_evolution_I",
    "continuum_limit_I",
    "qm_continuum_limit_closure_I",
    "schrodinger_generator_I",
    "hbar_I",
    "hamiltonian_energy_operator_I",
    "translation_generator_I",
    "momentum_operator_I",
    "de_broglie_relation_I",
    "canonical_commutator_I",
)

QM_GENERATOR_TRANSLATION_REQUIRED_GATES = (
    "unitary_generator_reconstruction_demo",
    "translation_de_broglie_scale_demo",
    "finite_weyl_relation_demo",
)

QM_APPARATUS_FACTICITY_TARGET = "qm_apparatus_facticity_closure_I"

QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS = (
    "born_readout_I",
    "observable_context_I",
    "apparatus_context_dynamics_I",
    "measurement_facticity_I",
)

QM_APPARATUS_FACTICITY_REQUIRED_GATES = (
    "pointer_sector_stability_demo",
    "premeasurement_decoherence_demo",
    "recoverability_loss_demo",
)

QM_CONTINUUM_LIMIT_TARGET = "qm_continuum_limit_closure_I"

QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS = (
    "unitary_evolution_I",
    "continuum_limit_I",
)

QM_CONTINUUM_LIMIT_REQUIRED_GATES = (
    "one_parameter_unitary_flow_demo",
    "strong_continuity_modulus_demo",
    "generator_difference_convergence_demo",
)

CALIBRATED_QM_TARGET = "calibrated_QM_reconstruction_I"

CALIBRATED_QM_REQUIRED_SYMBOLS = (
    "complex_amplitude_packet_I",
    "born_readout_I",
    "unitary_evolution_I",
    "continuum_limit_I",
    "calibrated_qm_continuum_closure_I",
    "schrodinger_generator_I",
    "calibrated_hbar_I",
    "calibrated_hamiltonian_energy_operator_I",
    "translation_generator_I",
    "calibrated_momentum_operator_I",
    "calibrated_de_broglie_relation_I",
    "calibrated_canonical_commutator_I",
    "observable_context_I",
    "apparatus_context_dynamics_I",
    "measurement_facticity_I",
    "calibrated_qm_generator_translation_closure_I",
    "calibrated_qm_apparatus_facticity_closure_I",
    "calibrated_qm_dynamics_action_facticity_closure_I",
)

CALIBRATED_QM_CLOSED_STATUSES = QM_FOUNDATION_CLOSED_STATUSES | {
    "derived_conditional",
    "bridge_assumption",
}


class ManifestError(ValueError):
    """Raised when a verifier manifest has invalid structure."""


@dataclass(frozen=True)
class Dimension:
    exponents: tuple[int, int, int, int]

    @classmethod
    def dimensionless(cls) -> Dimension:
        return cls((0, 0, 0, 0))

    @classmethod
    def from_mapping(cls, value: object, field: str) -> Dimension:
        mapping = require_mapping(value, field)
        exponents: list[int] = []
        for unit in BASE_UNITS:
            raw_exponent = mapping.get(unit, 0)
            if not isinstance(raw_exponent, int):
                raise ManifestError(f"{field}.{unit} must be an integer")
            exponents.append(raw_exponent)
        return cls((exponents[0], exponents[1], exponents[2], exponents[3]))

    def __mul__(self, other: Dimension) -> Dimension:
        return Dimension(tuple_add(self.exponents, other.exponents))

    def __truediv__(self, other: Dimension) -> Dimension:
        return Dimension(tuple_sub(self.exponents, other.exponents))

    def __pow__(self, exponent: int) -> Dimension:
        return Dimension(
            (
                self.exponents[0] * exponent,
                self.exponents[1] * exponent,
                self.exponents[2] * exponent,
                self.exponents[3] * exponent,
            )
        )

    def to_jsonable(self) -> dict[str, int]:
        return {
            unit: exponent
            for unit, exponent in zip(BASE_UNITS, self.exponents, strict=True)
            if exponent != 0
        }


@dataclass(frozen=True)
class Symbol:
    name: str
    status: str
    dimension: Dimension


@dataclass(frozen=True)
class Equation:
    identifier: str
    lhs: str
    rhs: object


@dataclass(frozen=True)
class Derivation:
    identifier: str
    target: str
    depends_on: tuple[str, ...]
    status: str


@dataclass(frozen=True)
class ForbiddenPath:
    target: str
    sources: tuple[str, ...]


@dataclass(frozen=True)
class FiniteGate:
    identifier: str
    gate_type: str
    payload: dict[str, object]


@dataclass(frozen=True)
class QMExperimentCoverage:
    identifier: str
    title: str
    status: str
    standard_result: str
    idt_primitives: dict[str, str]
    stable_invariant: str
    finite_gates: tuple[str, ...]
    proposed_gates: tuple[str, ...]
    claim_boundary: str


@dataclass(frozen=True)
class QMUniversalPattern:
    identifier: str
    title: str
    mechanism: str
    experiments: tuple[str, ...]
    finite_gates: tuple[str, ...]
    operations: dict[str, str]
    compiler_target: str
    claim_boundary: str


@dataclass(frozen=True)
class QMCoreProofObligation:
    identifier: str
    title: str
    status: str
    scope: str
    depends_on: tuple[str, ...]
    evidence_refs: tuple[str, ...]
    open_gap: str
    claim_boundary: str


@dataclass(frozen=True)
class TheoremCard:
    identifier: str
    statement: str
    role: str
    assumptions: tuple[str, ...]
    dependencies: tuple[str, ...]
    proof_status: str
    verifier: str
    known_failures: tuple[str, ...]
    physical_scope: str
    forbidden_claims: tuple[str, ...]


@dataclass(frozen=True)
class PhaseActionScaleCycle:
    identifier: str
    role: str
    cost: float
    phase: float


@dataclass(frozen=True)
class SparcRotmodRow:
    radius_kpc: float
    observed_velocity_km_s: float
    gas_velocity_km_s: float
    disk_velocity_km_s: float
    bulge_velocity_km_s: float


@dataclass(frozen=True)
class Manifest:
    symbols: dict[str, Symbol]
    equations: tuple[Equation, ...]
    derivations: tuple[Derivation, ...]
    forbidden_paths: tuple[ForbiddenPath, ...]
    finite_gates: tuple[FiniteGate, ...]
    qm_experiments: tuple[QMExperimentCoverage, ...]
    qm_universal_patterns: tuple[QMUniversalPattern, ...]
    qm_core_proof_obligations: tuple[QMCoreProofObligation, ...]
    theorem_cards: tuple[TheoremCard, ...]


@dataclass(frozen=True)
class Issue:
    code: str
    message: str

    def to_jsonable(self) -> dict[str, str]:
        return {"code": self.code, "message": self.message}


FiniteGateChecker = Callable[[FiniteGate], list[Issue]]


@dataclass(frozen=True)
class VerificationReport:
    checks: tuple[str, ...]
    issues: tuple[Issue, ...]

    @property
    def ok(self) -> bool:
        return not self.issues

    def to_jsonable(self) -> dict[str, object]:
        return {
            "ok": self.ok,
            "checks": list(self.checks),
            "issues": [issue.to_jsonable() for issue in self.issues],
        }


def tuple_add(
    left: tuple[int, int, int, int], right: tuple[int, int, int, int]
) -> tuple[int, int, int, int]:
    return (left[0] + right[0], left[1] + right[1], left[2] + right[2], left[3] + right[3])


def tuple_sub(
    left: tuple[int, int, int, int], right: tuple[int, int, int, int]
) -> tuple[int, int, int, int]:
    return (left[0] - right[0], left[1] - right[1], left[2] - right[2], left[3] - right[3])


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ManifestError(f"{field} must be an object")
    output: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise ManifestError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ManifestError(f"{field} must be a list")
    return list(value)


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise ManifestError(f"{field} must be a string")
    return value


def require_string_tuple(value: object, field: str) -> tuple[str, ...]:
    items = require_list(value, field)
    strings: list[str] = []
    for index, item in enumerate(items):
        strings.append(require_string(item, f"{field}[{index}]"))
    return tuple(strings)


def load_manifest(path: Path) -> Manifest:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return parse_manifest(raw)


def parse_manifest(raw: object) -> Manifest:
    root = require_mapping(raw, "manifest")
    symbols = parse_symbols(root.get("symbols", {}))
    equations = parse_equations(root.get("equations", []))
    derivations = parse_derivations(root.get("derivations", []))
    forbidden_paths = parse_forbidden_paths(root.get("forbidden_paths", []))
    finite_gates = parse_finite_gates(root.get("finite_gates", []))
    qm_experiments = parse_qm_experiments(root.get("qm_experiments", []))
    qm_universal_patterns = parse_qm_universal_patterns(root.get("qm_universal_patterns", []))
    qm_core_proof_obligations = parse_qm_core_proof_obligations(root.get("qm_core_proof_obligations", []))
    theorem_cards = parse_theorem_cards(root.get("theorem_cards", []))
    return Manifest(
        symbols=symbols,
        equations=equations,
        derivations=derivations,
        forbidden_paths=forbidden_paths,
        finite_gates=finite_gates,
        qm_experiments=qm_experiments,
        qm_universal_patterns=qm_universal_patterns,
        qm_core_proof_obligations=qm_core_proof_obligations,
        theorem_cards=theorem_cards,
    )


def parse_symbols(raw: object) -> dict[str, Symbol]:
    mapping = require_mapping(raw, "symbols")
    symbols: dict[str, Symbol] = {}
    for name, symbol_raw in mapping.items():
        symbol_map = require_mapping(symbol_raw, f"symbols.{name}")
        status = require_string(symbol_map.get("status"), f"symbols.{name}.status")
        if status not in STATUS_VALUES:
            raise ManifestError(f"symbols.{name}.status has unknown value {status!r}")
        dimension = Dimension.from_mapping(symbol_map.get("dimension", {}), f"symbols.{name}.dimension")
        symbols[name] = Symbol(name=name, status=status, dimension=dimension)
    return symbols


def parse_equations(raw: object) -> tuple[Equation, ...]:
    items = require_list(raw, "equations")
    equations: list[Equation] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"equations[{index}]")
        equations.append(
            Equation(
                identifier=require_string(item_map.get("id"), f"equations[{index}].id"),
                lhs=require_string(item_map.get("lhs"), f"equations[{index}].lhs"),
                rhs=item_map.get("rhs"),
            )
        )
    return tuple(equations)


def parse_derivations(raw: object) -> tuple[Derivation, ...]:
    items = require_list(raw, "derivations")
    derivations: list[Derivation] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"derivations[{index}]")
        status = require_string(item_map.get("status"), f"derivations[{index}].status")
        if status not in STATUS_VALUES:
            raise ManifestError(f"derivations[{index}].status has unknown value {status!r}")
        derivations.append(
            Derivation(
                identifier=require_string(item_map.get("id"), f"derivations[{index}].id"),
                target=require_string(item_map.get("target"), f"derivations[{index}].target"),
                depends_on=require_string_tuple(
                    item_map.get("depends_on", []), f"derivations[{index}].depends_on"
                ),
                status=status,
            )
        )
    return tuple(derivations)


def parse_forbidden_paths(raw: object) -> tuple[ForbiddenPath, ...]:
    items = require_list(raw, "forbidden_paths")
    paths: list[ForbiddenPath] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"forbidden_paths[{index}]")
        paths.append(
            ForbiddenPath(
                target=require_string(item_map.get("target"), f"forbidden_paths[{index}].target"),
                sources=require_string_tuple(
                    item_map.get("sources", []), f"forbidden_paths[{index}].sources"
                ),
            )
        )
    return tuple(paths)


def parse_finite_gates(raw: object) -> tuple[FiniteGate, ...]:
    items = require_list(raw, "finite_gates")
    gates: list[FiniteGate] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"finite_gates[{index}]")
        gates.append(
            FiniteGate(
                identifier=require_string(item_map.get("id"), f"finite_gates[{index}].id"),
                gate_type=require_string(item_map.get("type"), f"finite_gates[{index}].type"),
                payload=item_map,
            )
        )
    return tuple(gates)


def parse_qm_experiments(raw: object) -> tuple[QMExperimentCoverage, ...]:
    items = require_list(raw, "qm_experiments")
    experiments: list[QMExperimentCoverage] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"qm_experiments[{index}]")
        primitive_map = require_mapping(
            item_map.get("idt_primitives", {}),
            f"qm_experiments[{index}].idt_primitives",
        )
        idt_primitives: dict[str, str] = {}
        for key, value in primitive_map.items():
            idt_primitives[key] = require_string(
                value,
                f"qm_experiments[{index}].idt_primitives.{key}",
            )
        experiments.append(
            QMExperimentCoverage(
                identifier=require_string(item_map.get("id"), f"qm_experiments[{index}].id"),
                title=require_string(item_map.get("title"), f"qm_experiments[{index}].title"),
                status=require_string(item_map.get("status"), f"qm_experiments[{index}].status"),
                standard_result=require_string(
                    item_map.get("standard_result"),
                    f"qm_experiments[{index}].standard_result",
                ),
                idt_primitives=idt_primitives,
                stable_invariant=require_string(
                    item_map.get("stable_invariant"),
                    f"qm_experiments[{index}].stable_invariant",
                ),
                finite_gates=require_string_tuple(
                    item_map.get("finite_gates", []),
                    f"qm_experiments[{index}].finite_gates",
                ),
                proposed_gates=require_string_tuple(
                    item_map.get("proposed_gates", []),
                    f"qm_experiments[{index}].proposed_gates",
                ),
                claim_boundary=require_string(
                    item_map.get("claim_boundary"),
                    f"qm_experiments[{index}].claim_boundary",
                ),
            )
        )
    return tuple(experiments)


def parse_qm_universal_patterns(raw: object) -> tuple[QMUniversalPattern, ...]:
    items = require_list(raw, "qm_universal_patterns")
    patterns: list[QMUniversalPattern] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"qm_universal_patterns[{index}]")
        operation_map = require_mapping(
            item_map.get("operations", {}),
            f"qm_universal_patterns[{index}].operations",
        )
        operations: dict[str, str] = {}
        for key, value in operation_map.items():
            operations[key] = require_string(
                value,
                f"qm_universal_patterns[{index}].operations.{key}",
            )
        patterns.append(
            QMUniversalPattern(
                identifier=require_string(item_map.get("id"), f"qm_universal_patterns[{index}].id"),
                title=require_string(item_map.get("title"), f"qm_universal_patterns[{index}].title"),
                mechanism=require_string(item_map.get("mechanism"), f"qm_universal_patterns[{index}].mechanism"),
                experiments=require_string_tuple(
                    item_map.get("experiments", []),
                    f"qm_universal_patterns[{index}].experiments",
                ),
                finite_gates=require_string_tuple(
                    item_map.get("finite_gates", []),
                    f"qm_universal_patterns[{index}].finite_gates",
                ),
                operations=operations,
                compiler_target=require_string(
                    item_map.get("compiler_target"),
                    f"qm_universal_patterns[{index}].compiler_target",
                ),
                claim_boundary=require_string(
                    item_map.get("claim_boundary"),
                    f"qm_universal_patterns[{index}].claim_boundary",
                ),
            )
        )
    return tuple(patterns)


def parse_qm_core_proof_obligations(raw: object) -> tuple[QMCoreProofObligation, ...]:
    items = require_list(raw, "qm_core_proof_obligations")
    obligations: list[QMCoreProofObligation] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"qm_core_proof_obligations[{index}]")
        obligations.append(
            QMCoreProofObligation(
                identifier=require_string(item_map.get("id"), f"qm_core_proof_obligations[{index}].id"),
                title=require_string(item_map.get("title"), f"qm_core_proof_obligations[{index}].title"),
                status=require_string(item_map.get("status"), f"qm_core_proof_obligations[{index}].status"),
                scope=require_string(item_map.get("scope"), f"qm_core_proof_obligations[{index}].scope"),
                depends_on=require_string_tuple(
                    item_map.get("depends_on", []),
                    f"qm_core_proof_obligations[{index}].depends_on",
                ),
                evidence_refs=require_string_tuple(
                    item_map.get("evidence_refs", []),
                    f"qm_core_proof_obligations[{index}].evidence_refs",
                ),
                open_gap=require_string(
                    item_map.get("open_gap"),
                    f"qm_core_proof_obligations[{index}].open_gap",
                ),
                claim_boundary=require_string(
                    item_map.get("claim_boundary"),
                    f"qm_core_proof_obligations[{index}].claim_boundary",
                ),
            )
        )
    return tuple(obligations)


def parse_theorem_cards(raw: object) -> tuple[TheoremCard, ...]:
    items = require_list(raw, "theorem_cards")
    cards: list[TheoremCard] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"theorem_cards[{index}]")
        cards.append(
            TheoremCard(
                identifier=require_string(item_map.get("id"), f"theorem_cards[{index}].id"),
                statement=require_string(item_map.get("statement"), f"theorem_cards[{index}].statement"),
                role=require_string(item_map.get("role"), f"theorem_cards[{index}].role"),
                assumptions=require_string_tuple(
                    item_map.get("assumptions", []),
                    f"theorem_cards[{index}].assumptions",
                ),
                dependencies=require_string_tuple(
                    item_map.get("dependencies", []),
                    f"theorem_cards[{index}].dependencies",
                ),
                proof_status=require_string(
                    item_map.get("proof_status"),
                    f"theorem_cards[{index}].proof_status",
                ),
                verifier=require_string(item_map.get("verifier"), f"theorem_cards[{index}].verifier"),
                known_failures=require_string_tuple(
                    item_map.get("known_failures", []),
                    f"theorem_cards[{index}].known_failures",
                ),
                physical_scope=require_string(
                    item_map.get("physical_scope"),
                    f"theorem_cards[{index}].physical_scope",
                ),
                forbidden_claims=require_string_tuple(
                    item_map.get("forbidden_claims", []),
                    f"theorem_cards[{index}].forbidden_claims",
                ),
            )
        )
    return tuple(cards)


def verify_manifest(manifest: Manifest) -> VerificationReport:
    checks: list[str] = []
    issues: list[Issue] = []

    issues.extend(check_symbol_references(manifest))
    checks.append("symbol references")

    issues.extend(check_dimensions(manifest))
    checks.append("equation dimensions")

    issues.extend(check_derived_dependencies(manifest))
    checks.append("derived dependency statuses")

    issues.extend(check_qm_foundation_spine(manifest))
    checks.append("QM foundation spine")

    issues.extend(check_calibrated_qm_reconstruction(manifest))
    checks.append("calibrated QM reconstruction")

    issues.extend(check_qm_single_pass_closure(manifest))
    checks.append("QM single-pass closure")

    issues.extend(check_qm_experiment_coverage(manifest))
    checks.append("QM experiment coverage")

    issues.extend(check_qm_universal_patterns(manifest))
    checks.append("QM universal pattern audit")

    issues.extend(check_qm_core_proof_obligations(manifest))
    checks.append("QM core proof obligations")

    issues.extend(check_theorem_cards(manifest))
    checks.append("theorem cards")

    issues.extend(check_carrier_selection_theorem_grounding(manifest))
    checks.append("carrier-selection theorem grounding")

    issues.extend(check_context_product_local_tomography_theorem_grounding(manifest))
    checks.append("context-product local tomography theorem grounding")

    issues.extend(check_purification_filtering_theorem_grounding(manifest))
    checks.append("purification-filtering theorem grounding")

    issues.extend(check_reversible_filter_closure_theorem_grounding(manifest))
    checks.append("reversible filter closure theorem grounding")

    issues.extend(check_bounded_correlation_theorem_grounding(manifest))
    checks.append("bounded-correlation theorem grounding")

    issues.extend(check_noncomplex_jordan_theorem_grounding(manifest))
    checks.append("noncomplex-Jordan theorem grounding")

    issues.extend(check_generic_gpt_theorem_grounding(manifest))
    checks.append("generic-GPT theorem grounding")

    issues.extend(check_broader_generic_gpt_theorem_grounding(manifest))
    checks.append("broader generic-GPT theorem grounding")

    issues.extend(check_nonfinite_gpt_residual_theorem_grounding(manifest))
    checks.append("nonfinite GPT residual theorem grounding")

    issues.extend(check_no_emergent_joint_only_invariant_theorem_grounding(manifest))
    checks.append("no-emergent joint-only invariant theorem grounding")

    issues.extend(check_born_readout_theorem_grounding(manifest))
    checks.append("Born readout theorem grounding")

    issues.extend(check_tomographic_state_effect_duality_theorem_grounding(manifest))
    checks.append("tomographic state-effect duality theorem grounding")

    issues.extend(check_clock_vacuum_pole_closure(manifest))
    checks.append("clock-vacuum pole closure")

    issues.extend(check_cross_update_contraction_selection(manifest))
    checks.append("cross-update contraction selection")

    issues.extend(check_fixed_point_step_invariant(manifest))
    checks.append("fixed-point step invariant")

    issues.extend(check_primitive_transition_phase_readout(manifest))
    checks.append("primitive transition phase readout")

    issues.extend(check_primitive_holonomy_source_selector(manifest))
    checks.append("primitive holonomy source selector")

    issues.extend(check_primitive_topology_winding_selector(manifest))
    checks.append("primitive topology winding selector")

    issues.extend(check_sector_role_taxonomy(manifest))
    checks.append("sector role taxonomy")

    issues.extend(check_non_exact_holonomy_source_closure(manifest))
    checks.append("non-exact holonomy source closure")

    issues.extend(check_spectral_primitive_reduction(manifest))
    checks.append("spectral primitive reduction")

    issues.extend(check_ell0_emergence_clearance(manifest))
    checks.append("ell0 emergence clearance")

    issues.extend(check_ell0_physical_candidate(manifest))
    checks.append("ell0 physical candidate")

    issues.extend(check_ell0_closure(manifest))
    checks.append("ell0 closure")

    issues.extend(check_primitive_mass_anchor_closure(manifest))
    checks.append("primitive mass anchor closure")

    issues.extend(check_non_gravity_link_scale_bound(manifest))
    checks.append("non-gravity link-scale bound")

    issues.extend(check_weak_field_clock_calculator(manifest))
    checks.append("weak-field clock calculator")

    issues.extend(check_source_law_variational_closure(manifest))
    checks.append("source-law variational closure")

    issues.extend(check_ppn_no_slip_validation(manifest))
    checks.append("PPN no-slip validation")

    issues.extend(check_no_slip_stress_closure(manifest))
    checks.append("no-slip stress closure")

    issues.extend(check_source_stress_packet_closure(manifest))
    checks.append("source-stress packet closure")

    issues.extend(check_scale_residual_policy(manifest))
    checks.append("scale-separated residual policy")

    issues.extend(check_screened_slip_residual_candidate(manifest))
    checks.append("screened slip residual candidate")

    issues.extend(check_screened_observational_gate(manifest))
    checks.append("screened slip observational gate")

    issues.extend(check_primitive_tick_closure(manifest))
    checks.append("primitive tick closure")

    issues.extend(check_primitive_work_unit_closure(manifest))
    checks.append("primitive work unit closure")

    issues.extend(check_rho_chi_protocol_closure(manifest))
    checks.append("rho chi protocol closure")

    issues.extend(check_kappa_omega_consistency_closure(manifest))
    checks.append("kappa-omega consistency closure")

    issues.extend(check_source_response_charge_closure(manifest))
    checks.append("source-response charge closure")

    issues.extend(check_geometry_response_factor_closure(manifest))
    checks.append("geometry response factor closure")

    issues.extend(check_clock_vacuum_stiffness_closure(manifest))
    checks.append("clock-vacuum stiffness closure")

    issues.extend(check_G_emergence_clearance(manifest))
    checks.append("G emergence clearance")

    issues.extend(check_first_principles_G_candidate(manifest))
    checks.append("first-principles G candidate")

    issues.extend(check_action_standard_work_time_closure(manifest))
    checks.append("action standard work-time closure")

    issues.extend(check_qm_generator_translation_closure(manifest))
    checks.append("QM generator translation closure")

    issues.extend(check_qm_apparatus_facticity_closure(manifest))
    checks.append("QM apparatus facticity closure")

    issues.extend(check_qm_continuum_limit_closure(manifest))
    checks.append("QM continuum limit closure")

    issues.extend(check_hbar_action_standard_closure(manifest))
    checks.append("hbar action standard closure")

    issues.extend(check_joint_action_gravity_anchor(manifest))
    checks.append("joint action-gravity anchor")

    issues.extend(check_cycles(manifest))
    checks.append("derivation graph cycles")

    issues.extend(check_forbidden_paths(manifest))
    checks.append("forbidden input paths")

    issues.extend(check_finite_gates(manifest))
    checks.append("finite kernel and holonomy gates")

    issues.extend(check_research_graph_contract_grounding(manifest))
    checks.append("research graph contract grounding")

    return VerificationReport(checks=tuple(checks), issues=tuple(issues))


def check_symbol_references(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known = set(manifest.symbols)
    for equation in manifest.equations:
        if equation.lhs not in known:
            issues.append(Issue("unknown_lhs", f"{equation.identifier}: unknown lhs symbol {equation.lhs}"))
        for symbol_name in expression_symbols(equation.rhs):
            if symbol_name not in known:
                issues.append(
                    Issue("unknown_rhs_symbol", f"{equation.identifier}: unknown rhs symbol {symbol_name}")
                )
    for derivation in manifest.derivations:
        if derivation.target not in known:
            issues.append(
                Issue("unknown_derivation_target", f"{derivation.identifier}: unknown target {derivation.target}")
            )
        for dependency in derivation.depends_on:
            if dependency not in known:
                issues.append(
                    Issue("unknown_dependency", f"{derivation.identifier}: unknown dependency {dependency}")
                )
    for path in manifest.forbidden_paths:
        if path.target not in known:
            issues.append(Issue("unknown_forbidden_target", f"unknown forbidden target {path.target}"))
        for source in path.sources:
            if source not in known:
                issues.append(Issue("unknown_forbidden_source", f"unknown forbidden source {source}"))
    return issues


def check_dimensions(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    for equation in manifest.equations:
        lhs_symbol = manifest.symbols.get(equation.lhs)
        if lhs_symbol is None:
            continue
        try:
            rhs_dimension = evaluate_dimension(equation.rhs, manifest.symbols)
        except ManifestError as error:
            issues.append(Issue("invalid_expression", f"{equation.identifier}: {error}"))
            continue
        if lhs_symbol.dimension != rhs_dimension:
            issues.append(
                Issue(
                    "dimension_mismatch",
                    (
                        f"{equation.identifier}: {equation.lhs} has "
                        f"{lhs_symbol.dimension.to_jsonable()} but rhs has {rhs_dimension.to_jsonable()}"
                    ),
                )
            )
    return issues


def check_derived_dependencies(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    for derivation in manifest.derivations:
        if derivation.status != "derived":
            continue
        for dependency in derivation.depends_on:
            symbol = manifest.symbols.get(dependency)
            if symbol is None:
                continue
            if symbol.status in NON_DERIVED_DEPENDENCY_STATUSES:
                issues.append(
                    Issue(
                        "underived_dependency",
                        (
                            f"{derivation.identifier}: derived target {derivation.target} "
                            f"depends on {dependency} with status {symbol.status}"
                        ),
                    )
                )
    return issues


def check_qm_foundation_spine(manifest: Manifest) -> list[Issue]:
    if "full_QM_I" not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in QM_FOUNDATION_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "qm_foundation_spine_incomplete",
                f"full_QM_I foundation spine missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols["full_QM_I"].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in QM_FOUNDATION_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "qm_full_claim_premature",
                    f"full_QM_I cannot be derived while unclosed nodes remain: {', '.join(blocked)}",
                )
            )
    derivation = next((item for item in manifest.derivations if item.target == "full_QM_I"), None)
    if derivation is None:
        issues.append(Issue("qm_foundation_spine_missing_derivation", "full_QM_I needs an explicit derivation"))
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in QM_FOUNDATION_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "qm_foundation_spine_incomplete",
                    f"full_QM_I derivation omits: {', '.join(omitted)}",
                )
            )
    return issues


def check_calibrated_qm_reconstruction(manifest: Manifest) -> list[Issue]:
    if CALIBRATED_QM_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in CALIBRATED_QM_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "calibrated_qm_reconstruction_incomplete",
                f"{CALIBRATED_QM_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[CALIBRATED_QM_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in CALIBRATED_QM_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in CALIBRATED_QM_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "calibrated_qm_reconstruction_premature",
                    f"{CALIBRATED_QM_TARGET} cannot be derived while unclosed nodes remain: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == CALIBRATED_QM_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "calibrated_qm_reconstruction_missing_derivation",
                f"{CALIBRATED_QM_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in CALIBRATED_QM_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "calibrated_qm_reconstruction_incomplete",
                    f"{CALIBRATED_QM_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )
    return issues


def check_qm_single_pass_closure(manifest: Manifest) -> list[Issue]:
    if QM_SINGLE_PASS_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in QM_SINGLE_PASS_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "qm_single_pass_closure_incomplete",
                f"{QM_SINGLE_PASS_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[QM_SINGLE_PASS_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in QM_SINGLE_PASS_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "qm_single_pass_closure_premature",
                    f"{QM_SINGLE_PASS_TARGET} cannot be derived while unclosed nodes remain: {', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == QM_SINGLE_PASS_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "qm_single_pass_closure_missing_derivation",
                f"{QM_SINGLE_PASS_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in QM_SINGLE_PASS_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "qm_single_pass_closure_incomplete",
                    f"{QM_SINGLE_PASS_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    hbar_derivation = next((item for item in manifest.derivations if item.target == "hbar_I"), None)
    if hbar_derivation is None:
        issues.append(Issue("hbar_action_route_missing", "hbar_I needs an explicit action-scale derivation route"))
        return issues
    hbar_dependencies = set(hbar_derivation.depends_on)
    omitted_hbar_deps = [
        symbol for symbol in HBAR_ACTION_ROUTE_REQUIRED_DEPENDENCIES if symbol not in hbar_dependencies
    ]
    if omitted_hbar_deps:
        issues.append(
            Issue(
                "hbar_action_route_incomplete",
                f"hbar_I action route omits: {', '.join(omitted_hbar_deps)}",
            )
        )
    if manifest.symbols["hbar_I"].status in {"derived", "derived_conditional"}:
        blocked_hbar_deps = [
            symbol
            for symbol in HBAR_ACTION_ROUTE_REQUIRED_DEPENDENCIES
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked_hbar_deps:
            issues.append(
                Issue(
                    "hbar_action_scale_premature",
                    f"hbar_I cannot be derived while action-scale inputs remain unclosed: {', '.join(blocked_hbar_deps)}",
                )
            )
    return issues


def check_qm_experiment_coverage(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    seen: set[str] = set()
    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}

    for experiment in manifest.qm_experiments:
        if experiment.identifier in seen:
            issues.append(
                Issue(
                    "qm_experiment_duplicate",
                    f"{experiment.identifier}: duplicate QM experiment coverage entry",
                )
            )
        seen.add(experiment.identifier)

        if experiment.status not in QM_EXPERIMENT_STATUS_VALUES:
            issues.append(
                Issue(
                    "qm_experiment_status_unknown",
                    f"{experiment.identifier}: unknown status {experiment.status!r}",
                )
            )

        missing_primitives = [
            primitive
            for primitive in QM_EXPERIMENT_REQUIRED_PRIMITIVES
            if primitive not in experiment.idt_primitives
        ]
        if missing_primitives:
            issues.append(
                Issue(
                    "qm_experiment_primitives_incomplete",
                    f"{experiment.identifier}: missing IDT primitives: {', '.join(missing_primitives)}",
                )
            )

        empty_primitives = [
            primitive
            for primitive in QM_EXPERIMENT_REQUIRED_PRIMITIVES
            if not experiment.idt_primitives.get(primitive, "").strip()
        ]
        if empty_primitives:
            issues.append(
                Issue(
                    "qm_experiment_primitives_empty",
                    f"{experiment.identifier}: empty IDT primitive descriptions: {', '.join(empty_primitives)}",
                )
            )

        missing_gates = [gate_id for gate_id in experiment.finite_gates if gate_id not in finite_gate_ids]
        if missing_gates:
            issues.append(
                Issue(
                    "qm_experiment_gate_missing",
                    f"{experiment.identifier}: references missing finite gates: {', '.join(missing_gates)}",
                )
            )

        if experiment.status == "executable_gate" and not experiment.finite_gates:
            issues.append(
                Issue(
                    "qm_experiment_executable_without_gate",
                    f"{experiment.identifier}: executable QM experiment needs at least one finite gate",
                )
            )

        if experiment.status == "gate_candidate" and not experiment.proposed_gates:
            issues.append(
                Issue(
                    "qm_experiment_candidate_without_proposed_gate",
                    f"{experiment.identifier}: gate candidate needs a proposed gate id",
                )
            )

        if not experiment.standard_result.strip():
            issues.append(
                Issue(
                    "qm_experiment_standard_result_missing",
                    f"{experiment.identifier}: standard result must be declared",
                )
            )

        if not experiment.stable_invariant.strip():
            issues.append(
                Issue(
                    "qm_experiment_stable_invariant_missing",
                    f"{experiment.identifier}: stable invariant must be declared",
                )
            )

        if not experiment.claim_boundary.strip():
            issues.append(
                Issue(
                    "qm_experiment_claim_boundary_missing",
                    f"{experiment.identifier}: claim boundary must be declared",
                )
            )

    return issues


def check_qm_universal_patterns(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    if not manifest.qm_universal_patterns:
        if len(manifest.qm_experiments) >= 10:
            return [
                Issue(
                    "qm_universal_patterns_missing",
                    "large QM experiment ledgers must declare universal pattern coverage",
                )
            ]
        return issues

    experiment_ids = {experiment.identifier for experiment in manifest.qm_experiments}
    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    executable_gate_ids = {
        gate_id
        for experiment in manifest.qm_experiments
        if experiment.status == "executable_gate"
        for gate_id in experiment.finite_gates
    }
    seen_pattern_ids: set[str] = set()
    experiment_to_pattern: dict[str, str] = {}
    covered_gate_ids: set[str] = set()

    for pattern in manifest.qm_universal_patterns:
        if pattern.identifier in seen_pattern_ids:
            issues.append(
                Issue(
                    "qm_universal_pattern_duplicate",
                    f"{pattern.identifier}: duplicate QM universal pattern entry",
                )
            )
        seen_pattern_ids.add(pattern.identifier)

        if not pattern.title.strip():
            issues.append(
                Issue(
                    "qm_universal_pattern_title_missing",
                    f"{pattern.identifier}: title must be declared",
                )
            )
        if not pattern.mechanism.strip():
            issues.append(
                Issue(
                    "qm_universal_pattern_mechanism_missing",
                    f"{pattern.identifier}: mechanism must be declared",
                )
            )
        if not pattern.compiler_target.strip():
            issues.append(
                Issue(
                    "qm_universal_pattern_compiler_target_missing",
                    f"{pattern.identifier}: compiler target must be declared",
                )
            )
        if not pattern.claim_boundary.strip():
            issues.append(
                Issue(
                    "qm_universal_pattern_claim_boundary_missing",
                    f"{pattern.identifier}: claim boundary must be declared",
                )
            )

        missing_operations = [
            operation
            for operation in QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS
            if operation not in pattern.operations
        ]
        if missing_operations:
            issues.append(
                Issue(
                    "qm_universal_pattern_operations_incomplete",
                    f"{pattern.identifier}: missing operations: {', '.join(missing_operations)}",
                )
            )
        empty_operations = [
            operation
            for operation in QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS
            if not pattern.operations.get(operation, "").strip()
        ]
        if empty_operations:
            issues.append(
                Issue(
                    "qm_universal_pattern_operations_empty",
                    f"{pattern.identifier}: empty operations: {', '.join(empty_operations)}",
                )
            )

        for experiment_id in pattern.experiments:
            if experiment_id not in experiment_ids:
                issues.append(
                    Issue(
                        "qm_universal_pattern_experiment_missing",
                        f"{pattern.identifier}: references missing experiment {experiment_id}",
                    )
                )
                continue
            if experiment_id in experiment_to_pattern:
                issues.append(
                    Issue(
                        "qm_universal_pattern_experiment_duplicate",
                        (
                            f"{experiment_id}: assigned to both {experiment_to_pattern[experiment_id]} "
                            f"and {pattern.identifier}"
                        ),
                    )
                )
            experiment_to_pattern[experiment_id] = pattern.identifier

        missing_gates = [gate_id for gate_id in pattern.finite_gates if gate_id not in finite_gate_ids]
        if missing_gates:
            issues.append(
                Issue(
                    "qm_universal_pattern_gate_missing",
                    f"{pattern.identifier}: references missing finite gates: {', '.join(missing_gates)}",
                )
            )
        covered_gate_ids.update(gate_id for gate_id in pattern.finite_gates if gate_id in finite_gate_ids)

    uncovered_experiments = sorted(experiment_ids - set(experiment_to_pattern))
    if uncovered_experiments:
        issues.append(
            Issue(
                "qm_universal_pattern_experiment_uncovered",
                f"QM experiments without universal pattern coverage: {', '.join(uncovered_experiments)}",
            )
        )

    uncovered_gates = sorted(executable_gate_ids - covered_gate_ids)
    if uncovered_gates:
        issues.append(
            Issue(
                "qm_universal_pattern_gate_uncovered",
                f"QM finite gates without universal pattern coverage: {', '.join(uncovered_gates)}",
            )
        )

    return issues


def check_qm_core_proof_obligations(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    if not manifest.qm_core_proof_obligations:
        if len(manifest.qm_experiments) >= 10:
            return [
                Issue(
                    "qm_core_proof_obligations_missing",
                    "large QM experiment ledgers must declare finite/full QM proof obligations",
                )
            ]
        return issues

    obligation_ids = {obligation.identifier for obligation in manifest.qm_core_proof_obligations}
    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    pattern_ids = {pattern.identifier for pattern in manifest.qm_universal_patterns}
    symbol_ids = set(manifest.symbols)
    theorem_card_ids = {card.identifier for card in manifest.theorem_cards}
    evidence_ids = finite_gate_ids | pattern_ids | symbol_ids | theorem_card_ids
    seen: set[str] = set()

    missing_required = sorted(set(QM_CORE_PROOF_REQUIRED_OBLIGATIONS) - obligation_ids)
    if missing_required:
        issues.append(
            Issue(
                "qm_core_proof_obligations_incomplete",
                f"missing QM core proof obligations: {', '.join(missing_required)}",
            )
        )

    for obligation in manifest.qm_core_proof_obligations:
        if obligation.identifier in seen:
            issues.append(
                Issue(
                    "qm_core_proof_obligation_duplicate",
                    f"{obligation.identifier}: duplicate QM core proof obligation",
                )
            )
        seen.add(obligation.identifier)

        if obligation.status not in QM_CORE_PROOF_STATUS_VALUES:
            issues.append(
                Issue(
                    "qm_core_proof_status_unknown",
                    f"{obligation.identifier}: unknown proof status {obligation.status!r}",
                )
            )
        if not obligation.title.strip():
            issues.append(
                Issue(
                    "qm_core_proof_title_missing",
                    f"{obligation.identifier}: title must be declared",
                )
            )
        if obligation.scope not in {"finite_core", "full_qm_extension"}:
            issues.append(
                Issue(
                    "qm_core_proof_scope_unknown",
                    f"{obligation.identifier}: unknown scope {obligation.scope!r}",
                )
            )
        missing_deps = [dependency for dependency in obligation.depends_on if dependency not in obligation_ids]
        if missing_deps:
            issues.append(
                Issue(
                    "qm_core_proof_dependency_missing",
                    f"{obligation.identifier}: references missing obligations: {', '.join(missing_deps)}",
                )
            )
        missing_evidence = [evidence for evidence in obligation.evidence_refs if evidence not in evidence_ids]
        if missing_evidence:
            issues.append(
                Issue(
                    "qm_core_proof_evidence_missing",
                    f"{obligation.identifier}: references missing evidence: {', '.join(missing_evidence)}",
                )
            )
        if obligation.status in {"open", "target", "regression_supported", "blocked"} and not obligation.open_gap.strip():
            issues.append(
                Issue(
                    "qm_core_proof_open_gap_missing",
                    f"{obligation.identifier}: non-derived obligations must declare the remaining open gap",
                )
            )
        if not obligation.claim_boundary.strip():
            issues.append(
                Issue(
                    "qm_core_proof_claim_boundary_missing",
                    f"{obligation.identifier}: claim boundary must be declared",
                )
            )

    full_qm = manifest.symbols.get("full_QM_I")
    if full_qm is not None and full_qm.status == "derived":
        underived = sorted(
            obligation.identifier
            for obligation in manifest.qm_core_proof_obligations
            if obligation.status != "derived"
        )
        if underived:
            issues.append(
                Issue(
                    "full_qm_core_proof_incomplete",
                    f"full_QM_I cannot be derived before QM proof obligations close: {', '.join(underived)}",
                )
            )

    return issues


def check_theorem_cards(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    theorem_ids = {card.identifier for card in manifest.theorem_cards}
    known_refs = research_graph_known_evidence_refs(manifest)
    seen: set[str] = set()

    for card in manifest.theorem_cards:
        if card.identifier in seen:
            issues.append(Issue("theorem_card_duplicate", f"{card.identifier}: duplicate theorem card"))
        seen.add(card.identifier)
        if not card.statement.strip():
            issues.append(Issue("theorem_card_statement_missing", f"{card.identifier}: statement is missing"))
        if card.role not in THEOREM_CARD_ROLE_VALUES:
            issues.append(Issue("theorem_card_role_unknown", f"{card.identifier}: unknown role {card.role!r}"))
        if card.proof_status not in THEOREM_CARD_PROOF_STATUS_VALUES:
            issues.append(
                Issue(
                    "theorem_card_proof_status_unknown",
                    f"{card.identifier}: unknown proof status {card.proof_status!r}",
                )
            )
        if not card.physical_scope.strip():
            issues.append(
                Issue(
                    "theorem_card_physical_scope_missing",
                    f"{card.identifier}: physical scope is missing",
                )
            )
        if card.verifier and card.verifier not in known_refs:
            issues.append(
                Issue(
                    "theorem_card_verifier_missing",
                    f"{card.identifier}: verifier ref {card.verifier!r} is not grounded",
                )
            )
        missing_dependencies = [dependency for dependency in card.dependencies if dependency not in known_refs]
        if missing_dependencies:
            issues.append(
                Issue(
                    "theorem_card_dependency_missing",
                    f"{card.identifier}: dependencies are not grounded: {', '.join(missing_dependencies)}",
                )
            )

    full_qm_frontiers = [gate for gate in manifest.finite_gates if gate.gate_type == "full_qm_closure_frontier"]
    if full_qm_frontiers:
        cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
        missing_cards = sorted(set(FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS) - theorem_ids)
        if missing_cards:
            issues.append(
                Issue(
                    "full_qm_frontier_theorem_card_missing",
                    f"full-QM frontier requirements without theorem cards: {', '.join(missing_cards)}",
                )
            )
        for gate in full_qm_frontiers:
            components = require_list(gate.payload.get("components"), f"{gate.identifier}.components")
            for index, item in enumerate(components):
                component = require_mapping(item, f"{gate.identifier}.components[{index}]")
                requirement = require_string(
                    component.get("requirement"),
                    f"{gate.identifier}.components[{index}].requirement",
                )
                declared_status = require_string(
                    component.get("status"),
                    f"{gate.identifier}.components[{index}].status",
                )
                frontier_card = cards_by_id.get(requirement)
                if frontier_card is None:
                    continue
                card_status = full_qm_frontier_status_from_proof(frontier_card.proof_status)
                if declared_status != card_status:
                    issues.append(
                        Issue(
                            "full_qm_frontier_theorem_card_status_mismatch",
                            (
                                f"{gate.identifier}: component {requirement} declares {declared_status}, "
                                f"but theorem card proof_status {frontier_card.proof_status!r} maps to {card_status}"
                            ),
                        )
                    )
    return issues


def full_qm_frontier_status_from_proof(proof_status: str) -> str:
    if proof_status == "blocked":
        return "blocked"
    if proof_status == "formal_proof":
        return "supported"
    return "open"


def check_carrier_selection_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    gates_by_id = {gate.identifier: gate for gate in manifest.finite_gates}
    theorem_card = cards_by_id.get("universal_carrier_selection_theorem")
    proof_route = gates_by_id.get("carrier_selection_proof_route_demo")
    if theorem_card is None or proof_route is None:
        return issues
    if proof_route.gate_type != "carrier_selection_proof_route":
        issues.append(
            Issue(
                "carrier_selection_theorem_route_type_mismatch",
                "carrier_selection_proof_route_demo must be a carrier_selection_proof_route gate",
            )
        )
        return issues

    try:
        lemmas = require_list(proof_route.payload.get("lemmas"), f"{proof_route.identifier}.lemmas")
        expected_proof_status = require_string(
            proof_route.payload.get("expected_proof_status"),
            f"{proof_route.identifier}.expected_proof_status",
        )
    except ManifestError as error:
        issues.append(Issue("carrier_selection_theorem_grounding_invalid", f"{proof_route.identifier}: {error}"))
        return issues

    if theorem_card.proof_status != expected_proof_status:
        issues.append(
            Issue(
                "carrier_selection_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    f"does not match route status {expected_proof_status!r}"
                ),
            )
        )

    required_theorem_dependencies = {
        "carrier_universal_quantifier_frontier_demo",
        "carrier_selection_proof_route_demo",
        "carrier_selection_frontier_demo",
    }
    if not required_theorem_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_theorem_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "carrier_selection_theorem_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )

    for index, item in enumerate(lemmas):
        try:
            lemma = require_mapping(item, f"{proof_route.identifier}.lemmas[{index}]")
            lemma_id = require_string(lemma.get("id"), f"{proof_route.identifier}.lemmas[{index}].id")
            evidence_refs = require_string_tuple(
                lemma.get("evidence_refs", []),
                f"{proof_route.identifier}.lemmas[{index}].evidence_refs",
            )
        except ManifestError as error:
            issues.append(Issue("carrier_selection_theorem_grounding_invalid", f"{proof_route.identifier}: {error}"))
            continue

        expected_route_ref = CARRIER_SELECTION_LEMMA_ROUTE_REFS.get(lemma_id)
        if expected_route_ref is not None and expected_route_ref not in evidence_refs:
            issues.append(
                Issue(
                    "carrier_selection_theorem_lemma_route_missing",
                    f"{proof_route.identifier}: lemma {lemma_id} must cite {expected_route_ref}",
                )
            )
        missing_refs = [evidence_ref for evidence_ref in evidence_refs if evidence_ref not in known_refs]
        if missing_refs:
            issues.append(
                Issue(
                    "carrier_selection_theorem_evidence_unresolved",
                    f"{proof_route.identifier}: lemma {lemma_id} has unresolved evidence refs: {', '.join(missing_refs)}",
                )
            )
    return issues


def check_context_product_local_tomography_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("context_product_exhaustion_implies_local_tomography")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "context_product_local_tomography_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "context_product_local_tomography_theorem_demo",
        "real_hilbert_composite_hidden_joint_invariant_demo",
        "context_product_exhaustion_demo",
        "idt_local_tomography_derivation_demo",
        "local_tomography_separator_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "context_product_local_tomography_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "context_product_local_tomography_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "context_product_local_tomography_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_purification_filtering_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("purification_filtering_implies_recoverable_support_update")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "purification_filtering_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "purification_filtering_recoverable_support_theorem_demo",
        "idt_purification_filtering_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "purification_filtering_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "purification_filtering_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(PURIFICATION_FILTERING_THEOREM_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "purification_filtering_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_reversible_filter_closure_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("recoverable_support_update_implies_reversible_filter_closure")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "reversible_filter_closure_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "reversible_filter_closure_theorem_demo",
        "purification_filtering_implies_recoverable_support_update",
        "purification_filtering_recoverable_support_theorem_demo",
        "idt_purification_filtering_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "reversible_filter_closure_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "reversible_filter_closure_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(REVERSIBLE_FILTER_CLOSURE_THEOREM_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "reversible_filter_closure_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing assumptions from reversible filter closure boundary",
            )
        )
    if not set(REVERSIBLE_FILTER_CLOSURE_THEOREM_FORBIDDEN_UPGRADES).issubset(set(theorem_card.forbidden_claims)):
        issues.append(
            Issue(
                "reversible_filter_closure_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_bounded_correlation_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("bounded_correlation_screen_rejects_superquantum_boxes")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "bounded_correlation_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "bounded_correlation_screen_theorem_demo",
        "idt_bounded_correlation_demo",
        "gpt_principle_separator_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "bounded_correlation_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "bounded_correlation_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(BOUNDED_CORRELATION_THEOREM_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "bounded_correlation_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_noncomplex_jordan_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("noncomplex_jordan_separator_rejects_noncomplex_samples")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "noncomplex_jordan_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "noncomplex_jordan_separator_theorem_demo",
        "noncomplex_jordan_separator_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "noncomplex_jordan_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "noncomplex_jordan_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(NONCOMPLEX_JORDAN_THEOREM_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "noncomplex_jordan_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_generic_gpt_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("generic_gpt_closure_rejects_unconstrained_cone")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "generic_gpt_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "generic_gpt_closure_theorem_demo",
        "generic_gpt_closure_separator_demo",
        "carrier_selection_frontier_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "generic_gpt_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "generic_gpt_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "generic_gpt_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_broader_generic_gpt_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("finite_route_coverage_reduces_broader_generic_gpt_cone")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "broader_generic_gpt_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "broader_generic_gpt_cone_frontier_demo",
        "generic_gpt_closure_rejects_unconstrained_cone",
        "route_closed_gpt_subtheory_frontier_demo",
        "carrier_universal_quantifier_frontier_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "broader_generic_gpt_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "broader_generic_gpt_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(BROADER_GENERIC_GPT_THEOREM_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "broader_generic_gpt_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing assumptions from broader generic-GPT boundary",
            )
        )
    if not set(BROADER_GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES).issubset(set(theorem_card.forbidden_claims)):
        issues.append(
            Issue(
                "broader_generic_gpt_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_nonfinite_gpt_residual_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("uniform_route_witness_compactness_closes_nonfinite_gpt_residual")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "nonfinite_gpt_residual_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "nonfinite_gpt_residual_compactness_demo",
        "broader_generic_gpt_cone_frontier_demo",
        "finite_route_coverage_reduces_broader_generic_gpt_cone",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "nonfinite_gpt_residual_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "nonfinite_gpt_residual_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(NONFINITE_GPT_RESIDUAL_COMPACTNESS_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "nonfinite_gpt_residual_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing residual compactness assumptions",
            )
        )
    if not set(NONFINITE_GPT_RESIDUAL_FORBIDDEN_UPGRADES).issubset(set(theorem_card.forbidden_claims)):
        issues.append(
            Issue(
                "nonfinite_gpt_residual_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing residual forbidden upgrades",
            )
        )
    return issues


def check_no_emergent_joint_only_invariant_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("no_emergent_joint_only_invariants_under_context_product_exhaustion")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "no_emergent_joint_only_invariant_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "no_emergent_joint_only_invariant_route_demo",
        "context_product_exhaustion_implies_local_tomography",
        "real_hilbert_composite_hidden_joint_invariant",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "no_emergent_joint_only_invariant_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "no_emergent_joint_only_invariant_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(NO_EMERGENT_JOINT_ONLY_INVARIANT_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "no_emergent_joint_only_invariant_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing no-emergence assumptions",
            )
        )
    if not set(NO_EMERGENT_JOINT_ONLY_INVARIANT_FORBIDDEN_UPGRADES).issubset(set(theorem_card.forbidden_claims)):
        issues.append(
            Issue(
                "no_emergent_joint_only_invariant_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing no-emergence forbidden upgrades",
            )
        )
    return issues


def check_born_readout_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("finite_born_quadratic_readout_survivor")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "born_readout_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "born_quadratic_readout_route_demo",
        "born_context_probability_table_demo",
        "measurement_facticity_route_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "born_readout_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "born_readout_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(BORN_READOUT_THEOREM_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "born_readout_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing assumptions from finite Born route boundary",
            )
        )
    forbidden_upgrades = set(theorem_card.forbidden_claims)
    if not set(BORN_READOUT_THEOREM_FORBIDDEN_UPGRADES).issubset(forbidden_upgrades):
        issues.append(
            Issue(
                "born_readout_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_tomographic_state_effect_duality_theorem_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    cards_by_id = {card.identifier: card for card in manifest.theorem_cards}
    theorem_card = cards_by_id.get("route_witness_completeness_implies_tomographic_state_effect_duality")
    if theorem_card is None:
        return issues

    if theorem_card.proof_status != "conditional_proof":
        issues.append(
            Issue(
                "tomographic_state_effect_duality_theorem_card_status_mismatch",
                (
                    f"{theorem_card.identifier}: proof_status {theorem_card.proof_status!r} "
                    "must remain conditional_proof"
                ),
            )
        )
    required_dependencies = {
        "tomographic_state_effect_duality_theorem_demo",
        "context_product_exhaustion_implies_local_tomography",
        "context_product_local_tomography_theorem_demo",
        "generic_gpt_closure_separator_demo",
    }
    if not required_dependencies.issubset(set(theorem_card.dependencies)):
        missing = sorted(required_dependencies - set(theorem_card.dependencies))
        issues.append(
            Issue(
                "tomographic_state_effect_duality_theorem_card_dependency_missing",
                f"{theorem_card.identifier}: missing dependencies: {', '.join(missing)}",
            )
        )
    missing_refs = [dependency for dependency in theorem_card.dependencies if dependency not in known_refs]
    if missing_refs:
        issues.append(
            Issue(
                "tomographic_state_effect_duality_theorem_card_dependency_unresolved",
                f"{theorem_card.identifier}: unresolved dependencies: {', '.join(missing_refs)}",
            )
        )
    if not set(TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_ASSUMPTIONS).issubset(set(theorem_card.assumptions)):
        issues.append(
            Issue(
                "tomographic_state_effect_duality_theorem_card_assumption_missing",
                f"{theorem_card.identifier}: missing assumptions from state-effect duality boundary",
            )
        )
    if not set(TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_FORBIDDEN_UPGRADES).issubset(
        set(theorem_card.forbidden_claims)
    ):
        issues.append(
            Issue(
                "tomographic_state_effect_duality_theorem_card_forbidden_claim_missing",
                f"{theorem_card.identifier}: missing forbidden upgrades from conditional theorem boundary",
            )
        )
    return issues


def check_clock_vacuum_pole_closure(manifest: Manifest) -> list[Issue]:
    if CLOCK_VACUUM_POLE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=CLOCK_VACUUM_POLE_TARGET,
        required_symbols=CLOCK_VACUUM_POLE_REQUIRED_SYMBOLS,
        required_gates=CLOCK_VACUUM_POLE_REQUIRED_GATES,
        issue_prefix="clock_vacuum_pole_closure",
        premature_message=(
            f"{CLOCK_VACUUM_POLE_TARGET} cannot close while pole inputs remain unclosed"
        ),
    )


def check_spectral_primitive_reduction(manifest: Manifest) -> list[Issue]:
    if SPECTRAL_PRIMITIVE_REDUCTION_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=SPECTRAL_PRIMITIVE_REDUCTION_TARGET,
        required_symbols=SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS,
        required_gates=SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_GATES,
        issue_prefix="spectral_primitive_reduction",
        premature_message=(
            f"{SPECTRAL_PRIMITIVE_REDUCTION_TARGET} cannot close while spectral route inputs remain unclosed"
        ),
    )


def check_cross_update_contraction_selection(manifest: Manifest) -> list[Issue]:
    if CROSS_UPDATE_CONTRACTION_SELECTION_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=CROSS_UPDATE_CONTRACTION_SELECTION_TARGET,
        required_symbols=CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_SYMBOLS,
        required_gates=CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_GATES,
        issue_prefix="cross_update_contraction_selection",
        premature_message=(
            f"{CROSS_UPDATE_CONTRACTION_SELECTION_TARGET} cannot close while contraction inputs remain unclosed"
        ),
    )


def check_fixed_point_step_invariant(manifest: Manifest) -> list[Issue]:
    if FIXED_POINT_STEP_INVARIANT_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=FIXED_POINT_STEP_INVARIANT_TARGET,
        required_symbols=FIXED_POINT_STEP_INVARIANT_REQUIRED_SYMBOLS,
        required_gates=FIXED_POINT_STEP_INVARIANT_REQUIRED_GATES,
        issue_prefix="fixed_point_step_invariant",
        premature_message=(
            f"{FIXED_POINT_STEP_INVARIANT_TARGET} cannot close while step inputs remain unclosed"
        ),
    )


def check_primitive_transition_phase_readout(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_TRANSITION_PHASE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=PRIMITIVE_TRANSITION_PHASE_TARGET,
        required_symbols=PRIMITIVE_TRANSITION_PHASE_REQUIRED_SYMBOLS,
        required_gates=PRIMITIVE_TRANSITION_PHASE_REQUIRED_GATES,
        issue_prefix="primitive_transition_phase_readout",
        premature_message=(
            f"{PRIMITIVE_TRANSITION_PHASE_TARGET} cannot close while transition phase inputs remain unclosed"
        ),
    )


def check_primitive_holonomy_source_selector(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET,
        required_symbols=PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_SYMBOLS,
        required_gates=PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_GATES,
        issue_prefix="primitive_holonomy_source_selector",
        premature_message=(
            f"{PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET} cannot close while selector inputs remain unclosed"
        ),
    )


def check_primitive_topology_winding_selector(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET,
        required_symbols=PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_SYMBOLS,
        required_gates=PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_GATES,
        issue_prefix="primitive_topology_winding_selector",
        premature_message=(
            f"{PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET} cannot close while winding inputs remain unclosed"
        ),
    )


def check_sector_role_taxonomy(manifest: Manifest) -> list[Issue]:
    if SECTOR_ROLE_TAXONOMY_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=SECTOR_ROLE_TAXONOMY_TARGET,
        required_symbols=SECTOR_ROLE_TAXONOMY_REQUIRED_SYMBOLS,
        required_gates=SECTOR_ROLE_TAXONOMY_REQUIRED_GATES,
        issue_prefix="sector_role_taxonomy",
        premature_message=(
            f"{SECTOR_ROLE_TAXONOMY_TARGET} cannot close while role registries remain unclosed"
        ),
    )


def check_non_exact_holonomy_source_closure(manifest: Manifest) -> list[Issue]:
    if NON_EXACT_HOLONOMY_SOURCE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=NON_EXACT_HOLONOMY_SOURCE_TARGET,
        required_symbols=NON_EXACT_HOLONOMY_SOURCE_REQUIRED_SYMBOLS,
        required_gates=NON_EXACT_HOLONOMY_SOURCE_REQUIRED_GATES,
        issue_prefix="non_exact_holonomy_source_closure",
        premature_message=(
            f"{NON_EXACT_HOLONOMY_SOURCE_TARGET} cannot close while holonomy inputs remain unclosed"
        ),
    )


def check_ell0_emergence_clearance(manifest: Manifest) -> list[Issue]:
    if ELL0_EMERGENCE_CLEARANCE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=ELL0_EMERGENCE_CLEARANCE_TARGET,
        required_symbols=ELL0_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS,
        required_gates=ELL0_EMERGENCE_CLEARANCE_REQUIRED_GATES,
        issue_prefix="ell0_emergence_clearance",
        premature_message=(
            f"{ELL0_EMERGENCE_CLEARANCE_TARGET} cannot close while length-pole inputs remain unclosed"
        ),
    )


def check_ell0_physical_candidate(manifest: Manifest) -> list[Issue]:
    if ELL0_PHYSICAL_CANDIDATE_TARGET not in manifest.symbols:
        return []
    issues = check_closure_target(
        manifest,
        target=ELL0_PHYSICAL_CANDIDATE_TARGET,
        required_symbols=ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS,
        required_gates=(),
        issue_prefix="ell0_physical_candidate",
        premature_message=(
            f"{ELL0_PHYSICAL_CANDIDATE_TARGET} cannot close before ell0 emergence clearance"
        ),
    )
    ell0 = manifest.symbols.get("ell0")
    if ell0 is not None and ell0.status in {"derived", "derived_conditional"}:
        clearance = manifest.symbols.get(ELL0_EMERGENCE_CLEARANCE_TARGET)
        candidate = manifest.symbols.get(ELL0_PHYSICAL_CANDIDATE_TARGET)
        if clearance is None or candidate is None or clearance.status != "derived" or candidate.status != "derived":
            issues.append(
                Issue(
                    "ell0_derived_without_clearance",
                    "ell0 cannot be derived before ell0_emergence_clearance_I and "
                    "ell0_physical_candidate_I are derived",
                )
            )
    return issues


def check_ell0_closure(manifest: Manifest) -> list[Issue]:
    if ELL0_CLOSURE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=ELL0_CLOSURE_TARGET,
        required_symbols=ELL0_CLOSURE_REQUIRED_SYMBOLS,
        required_gates=ELL0_CLOSURE_REQUIRED_GATES,
        issue_prefix="ell0_closure",
        premature_message="ell0_closure_I cannot be derived while length inputs remain unclosed",
    )


def check_primitive_mass_anchor_closure(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_MASS_ANCHOR_TARGET not in manifest.symbols:
        return []
    return check_target_closure(
        manifest,
        target=PRIMITIVE_MASS_ANCHOR_TARGET,
        required_symbols=PRIMITIVE_MASS_ANCHOR_REQUIRED_SYMBOLS,
        required_gates=PRIMITIVE_MASS_ANCHOR_REQUIRED_GATES,
        issue_prefix="primitive_mass_anchor_closure",
        premature_message="primitive_mass_anchor_closure_I cannot be derived while mass inputs remain unclosed",
    )


def check_non_gravity_link_scale_bound(manifest: Manifest) -> list[Issue]:
    if NON_GRAVITY_LINK_BOUND_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in NON_GRAVITY_LINK_BOUND_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "non_gravity_link_bound_incomplete",
                f"{NON_GRAVITY_LINK_BOUND_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]
    omega_derivation = next(
        (item for item in manifest.derivations if item.target == NON_GRAVITY_LINK_BOUND_TARGET),
        None,
    )
    if omega_derivation is None:
        issues.append(
            Issue(
                "non_gravity_link_bound_missing_derivation",
                f"{NON_GRAVITY_LINK_BOUND_TARGET} needs a derivation",
            )
        )
    else:
        dependencies = set(omega_derivation.depends_on)
        omitted = [
            symbol for symbol in NON_GRAVITY_LINK_BOUND_REQUIRED_DEPENDENCIES if symbol not in dependencies
        ]
        if omitted:
            issues.append(
                Issue(
                    "non_gravity_link_bound_incomplete",
                    f"{NON_GRAVITY_LINK_BOUND_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )
    derivation_targets = {
        "ell0_upper_bound_I": ("c_I", "omega_ell_lower_bound_I"),
        "primitive_tick_upper_bound_I": ("ell0_upper_bound_I", "c_I"),
    }
    for target, required_dependencies in derivation_targets.items():
        derivation = next((item for item in manifest.derivations if item.target == target), None)
        if derivation is None:
            issues.append(Issue("non_gravity_link_bound_missing_derivation", f"{target} needs a derivation"))
            continue
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in required_dependencies if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "non_gravity_link_bound_incomplete",
                    f"{target} derivation omits: {', '.join(omitted)}",
                )
            )
    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [
        gate_id for gate_id in NON_GRAVITY_LINK_BOUND_REQUIRED_GATES if gate_id not in finite_gate_ids
    ]
    if missing_gates:
        issues.append(
            Issue(
                "non_gravity_link_bound_gate_missing",
                f"{NON_GRAVITY_LINK_BOUND_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_target_closure(
    manifest: Manifest,
    *,
    target: str,
    required_symbols: tuple[str, ...],
    required_gates: tuple[str, ...],
    issue_prefix: str,
    premature_message: str,
) -> list[Issue]:
    issues: list[Issue] = []
    missing = [symbol for symbol in required_symbols if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                f"{issue_prefix}_incomplete",
                f"{target} missing symbols: {', '.join(missing)}",
            )
        ]
    if manifest.symbols[target].status == "derived":
        blocked = [
            symbol
            for symbol in required_symbols
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    f"{issue_prefix}_premature",
                    f"{premature_message}: {', '.join(blocked)}",
                )
            )
    derivation = next((item for item in manifest.derivations if item.target == target), None)
    if derivation is None:
        issues.append(Issue(f"{issue_prefix}_missing_derivation", f"{target} needs an explicit derivation"))
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in required_symbols if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    f"{issue_prefix}_incomplete",
                    f"{target} derivation omits: {', '.join(omitted)}",
                )
            )
    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in required_gates if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                f"{issue_prefix}_gate_missing",
                f"{target} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_weak_field_clock_calculator(manifest: Manifest) -> list[Issue]:
    if WEAK_FIELD_CLOCK_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in WEAK_FIELD_CLOCK_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "weak_field_clock_calculator_incomplete",
                f"{WEAK_FIELD_CLOCK_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == WEAK_FIELD_CLOCK_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "weak_field_clock_calculator_missing_derivation",
                f"{WEAK_FIELD_CLOCK_TARGET} needs a derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in WEAK_FIELD_CLOCK_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "weak_field_clock_calculator_incomplete",
                    f"{WEAK_FIELD_CLOCK_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in WEAK_FIELD_CLOCK_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "weak_field_clock_gate_missing",
                f"{WEAK_FIELD_CLOCK_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_source_law_variational_closure(manifest: Manifest) -> list[Issue]:
    if SOURCE_LAW_VARIATIONAL_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SOURCE_LAW_VARIATIONAL_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "source_law_variational_incomplete",
                f"{SOURCE_LAW_VARIATIONAL_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == SOURCE_LAW_VARIATIONAL_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "source_law_variational_missing_derivation",
                f"{SOURCE_LAW_VARIATIONAL_TARGET} needs a derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SOURCE_LAW_VARIATIONAL_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "source_law_variational_incomplete",
                    f"{SOURCE_LAW_VARIATIONAL_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SOURCE_LAW_VARIATIONAL_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "source_law_variational_gate_missing",
                f"{SOURCE_LAW_VARIATIONAL_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_ppn_no_slip_validation(manifest: Manifest) -> list[Issue]:
    if PPN_NO_SLIP_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in PPN_NO_SLIP_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "ppn_no_slip_validation_incomplete",
                f"{PPN_NO_SLIP_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == PPN_NO_SLIP_TARGET), None)
    if derivation is None:
        issues.append(Issue("ppn_no_slip_validation_missing_derivation", f"{PPN_NO_SLIP_TARGET} needs a derivation"))
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in PPN_NO_SLIP_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "ppn_no_slip_validation_incomplete",
                    f"{PPN_NO_SLIP_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in PPN_NO_SLIP_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "ppn_no_slip_gate_missing",
                f"{PPN_NO_SLIP_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_no_slip_stress_closure(manifest: Manifest) -> list[Issue]:
    if NO_SLIP_STRESS_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in NO_SLIP_STRESS_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "no_slip_stress_closure_incomplete",
                f"{NO_SLIP_STRESS_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == NO_SLIP_STRESS_TARGET), None)
    if derivation is None:
        issues.append(Issue("no_slip_stress_closure_missing_derivation", f"{NO_SLIP_STRESS_TARGET} needs a derivation"))
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in NO_SLIP_STRESS_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "no_slip_stress_closure_incomplete",
                    f"{NO_SLIP_STRESS_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in NO_SLIP_STRESS_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "no_slip_stress_gate_missing",
                f"{NO_SLIP_STRESS_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_source_stress_packet_closure(manifest: Manifest) -> list[Issue]:
    if SOURCE_STRESS_PACKET_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SOURCE_STRESS_PACKET_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "source_stress_packet_closure_incomplete",
                f"{SOURCE_STRESS_PACKET_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == SOURCE_STRESS_PACKET_TARGET), None)
    if derivation is None:
        issues.append(
            Issue("source_stress_packet_closure_missing_derivation", f"{SOURCE_STRESS_PACKET_TARGET} needs a derivation")
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SOURCE_STRESS_PACKET_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "source_stress_packet_closure_incomplete",
                    f"{SOURCE_STRESS_PACKET_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SOURCE_STRESS_PACKET_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "source_stress_packet_gate_missing",
                f"{SOURCE_STRESS_PACKET_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_scale_residual_policy(manifest: Manifest) -> list[Issue]:
    if SCALE_RESIDUAL_POLICY_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SCALE_RESIDUAL_POLICY_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "scale_residual_policy_incomplete",
                f"{SCALE_RESIDUAL_POLICY_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == SCALE_RESIDUAL_POLICY_TARGET), None)
    if derivation is None:
        issues.append(
            Issue("scale_residual_policy_missing_derivation", f"{SCALE_RESIDUAL_POLICY_TARGET} needs a derivation")
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SCALE_RESIDUAL_POLICY_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "scale_residual_policy_incomplete",
                    f"{SCALE_RESIDUAL_POLICY_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SCALE_RESIDUAL_POLICY_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "scale_residual_policy_gate_missing",
                f"{SCALE_RESIDUAL_POLICY_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_screened_slip_residual_candidate(manifest: Manifest) -> list[Issue]:
    if SCREENED_SLIP_RESIDUAL_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SCREENED_SLIP_RESIDUAL_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "screened_slip_residual_incomplete",
                f"{SCREENED_SLIP_RESIDUAL_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == SCREENED_SLIP_RESIDUAL_TARGET), None)
    if derivation is None:
        issues.append(
            Issue("screened_slip_residual_missing_derivation", f"{SCREENED_SLIP_RESIDUAL_TARGET} needs a derivation")
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SCREENED_SLIP_RESIDUAL_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "screened_slip_residual_incomplete",
                    f"{SCREENED_SLIP_RESIDUAL_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SCREENED_SLIP_RESIDUAL_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "screened_slip_residual_gate_missing",
                f"{SCREENED_SLIP_RESIDUAL_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_screened_observational_gate(manifest: Manifest) -> list[Issue]:
    if SCREENED_OBSERVATIONAL_GATE_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SCREENED_OBSERVATIONAL_GATE_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "screened_observational_gate_incomplete",
                f"{SCREENED_OBSERVATIONAL_GATE_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    derivation = next((item for item in manifest.derivations if item.target == SCREENED_OBSERVATIONAL_GATE_TARGET), None)
    if derivation is None:
        issues.append(
            Issue("screened_observational_gate_missing_derivation", f"{SCREENED_OBSERVATIONAL_GATE_TARGET} needs a derivation")
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SCREENED_OBSERVATIONAL_GATE_REQUIRED_DEPENDENCIES if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "screened_observational_gate_incomplete",
                    f"{SCREENED_OBSERVATIONAL_GATE_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SCREENED_OBSERVATIONAL_GATE_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "screened_observational_gate_missing",
                f"{SCREENED_OBSERVATIONAL_GATE_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_primitive_tick_closure(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_TICK_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in PRIMITIVE_TICK_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "primitive_tick_closure_incomplete",
                f"{PRIMITIVE_TICK_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[PRIMITIVE_TICK_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in PRIMITIVE_TICK_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "primitive_tick_closure_premature",
                    f"{PRIMITIVE_TICK_TARGET} cannot be derived while tick inputs remain unclosed: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == PRIMITIVE_TICK_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "primitive_tick_closure_missing_derivation",
                f"{PRIMITIVE_TICK_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in PRIMITIVE_TICK_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "primitive_tick_closure_incomplete",
                    f"{PRIMITIVE_TICK_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in PRIMITIVE_TICK_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "primitive_tick_gate_missing",
                f"{PRIMITIVE_TICK_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_primitive_work_unit_closure(manifest: Manifest) -> list[Issue]:
    if PRIMITIVE_WORK_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in PRIMITIVE_WORK_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "primitive_work_closure_incomplete",
                f"{PRIMITIVE_WORK_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[PRIMITIVE_WORK_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in PRIMITIVE_WORK_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "primitive_work_closure_premature",
                    f"{PRIMITIVE_WORK_TARGET} cannot be derived while work inputs remain unclosed: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == PRIMITIVE_WORK_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "primitive_work_closure_missing_derivation",
                f"{PRIMITIVE_WORK_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in PRIMITIVE_WORK_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "primitive_work_closure_incomplete",
                    f"{PRIMITIVE_WORK_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in PRIMITIVE_WORK_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "primitive_work_gate_missing",
                f"{PRIMITIVE_WORK_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_rho_chi_protocol_closure(manifest: Manifest) -> list[Issue]:
    if RHO_CHI_PROTOCOL_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=RHO_CHI_PROTOCOL_TARGET,
        required_symbols=RHO_CHI_PROTOCOL_REQUIRED_SYMBOLS,
        required_gates=RHO_CHI_PROTOCOL_REQUIRED_GATES,
        issue_prefix="rho_chi_protocol_closure",
        premature_message=(
            f"{RHO_CHI_PROTOCOL_TARGET} cannot close while sampling/action inputs remain unclosed"
        ),
    )


def check_kappa_omega_consistency_closure(manifest: Manifest) -> list[Issue]:
    if KAPPA_OMEGA_CONSISTENCY_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=KAPPA_OMEGA_CONSISTENCY_TARGET,
        required_symbols=KAPPA_OMEGA_CONSISTENCY_REQUIRED_SYMBOLS,
        required_gates=KAPPA_OMEGA_CONSISTENCY_REQUIRED_GATES,
        issue_prefix="kappa_omega_consistency_closure",
        premature_message=(
            f"{KAPPA_OMEGA_CONSISTENCY_TARGET} cannot close while kappa/omega inputs remain unclosed"
        ),
    )


def check_source_response_charge_closure(manifest: Manifest) -> list[Issue]:
    if SOURCE_RESPONSE_CHARGE_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "source_response_charge_closure_incomplete",
                f"{SOURCE_RESPONSE_CHARGE_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[SOURCE_RESPONSE_CHARGE_TARGET].status
    if target_status in {"derived", "derived_conditional"}:
        blocked = [
            symbol
            for symbol in SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "source_response_charge_closure_premature",
                    f"{SOURCE_RESPONSE_CHARGE_TARGET} cannot be closed while source-charge inputs remain unclosed: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == SOURCE_RESPONSE_CHARGE_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "source_response_charge_closure_missing_derivation",
                f"{SOURCE_RESPONSE_CHARGE_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "source_response_charge_closure_incomplete",
                    f"{SOURCE_RESPONSE_CHARGE_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in SOURCE_RESPONSE_CHARGE_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "source_response_charge_gate_missing",
                f"{SOURCE_RESPONSE_CHARGE_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_geometry_response_factor_closure(manifest: Manifest) -> list[Issue]:
    if GEOMETRY_RESPONSE_FACTOR_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=GEOMETRY_RESPONSE_FACTOR_TARGET,
        required_symbols=GEOMETRY_RESPONSE_FACTOR_REQUIRED_SYMBOLS,
        required_gates=GEOMETRY_RESPONSE_FACTOR_REQUIRED_GATES,
        issue_prefix="geometry_response_factor_closure",
        premature_message=(
            f"{GEOMETRY_RESPONSE_FACTOR_TARGET} cannot be closed while geometry/readout inputs remain unclosed"
        ),
    )


def check_clock_vacuum_stiffness_closure(manifest: Manifest) -> list[Issue]:
    if CLOCK_VACUUM_STIFFNESS_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=CLOCK_VACUUM_STIFFNESS_TARGET,
        required_symbols=CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS,
        required_gates=CLOCK_VACUUM_STIFFNESS_REQUIRED_GATES,
        issue_prefix="clock_vacuum_stiffness_closure",
        premature_message=(
            f"{CLOCK_VACUUM_STIFFNESS_TARGET} cannot be closed while stiffness inputs remain unclosed"
        ),
    )


def check_G_emergence_clearance(manifest: Manifest) -> list[Issue]:
    if G_EMERGENCE_CLEARANCE_TARGET not in manifest.symbols:
        return []
    return check_closure_target(
        manifest,
        target=G_EMERGENCE_CLEARANCE_TARGET,
        required_symbols=G_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS,
        required_gates=G_EMERGENCE_CLEARANCE_REQUIRED_GATES,
        issue_prefix="G_emergence_clearance",
        premature_message=f"{G_EMERGENCE_CLEARANCE_TARGET} cannot close while G inputs remain unclosed",
    )


def check_first_principles_G_candidate(manifest: Manifest) -> list[Issue]:
    if FIRST_PRINCIPLES_G_CANDIDATE_TARGET not in manifest.symbols:
        return []
    issues = check_closure_target(
        manifest,
        target=FIRST_PRINCIPLES_G_CANDIDATE_TARGET,
        required_symbols=FIRST_PRINCIPLES_G_CANDIDATE_REQUIRED_SYMBOLS,
        required_gates=(),
        issue_prefix="first_principles_G_candidate",
        premature_message=(
            f"{FIRST_PRINCIPLES_G_CANDIDATE_TARGET} cannot close before G emergence clearance"
        ),
    )
    if "G_I" in manifest.symbols and manifest.symbols["G_I"].status == "derived":
        clearance_status = manifest.symbols[G_EMERGENCE_CLEARANCE_TARGET].status
        candidate_status = manifest.symbols[FIRST_PRINCIPLES_G_CANDIDATE_TARGET].status
        if clearance_status != "derived" or candidate_status != "derived":
            issues.append(
                Issue(
                    "G_derived_without_clearance",
                    "G_I cannot be derived before G_emergence_clearance_I and "
                    "first_principles_G_candidate_I are derived",
                )
            )
    return issues


def check_closure_target(
    manifest: Manifest,
    *,
    target: str,
    required_symbols: tuple[str, ...],
    required_gates: tuple[str, ...],
    issue_prefix: str,
    premature_message: str,
) -> list[Issue]:
    issues: list[Issue] = []
    missing = [symbol for symbol in required_symbols if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                f"{issue_prefix}_incomplete",
                f"{target} missing symbols: {', '.join(missing)}",
            )
        ]

    if manifest.symbols[target].status in {"derived", "derived_conditional"}:
        blocked = [
            symbol
            for symbol in required_symbols
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    f"{issue_prefix}_premature",
                    f"{premature_message}: {', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == target), None)
    if derivation is None:
        issues.append(Issue(f"{issue_prefix}_missing_derivation", f"{target} needs an explicit derivation"))
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in required_symbols if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    f"{issue_prefix}_incomplete",
                    f"{target} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in required_gates if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                f"{issue_prefix}_gate_missing",
                f"{target} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_action_standard_work_time_closure(manifest: Manifest) -> list[Issue]:
    if ACTION_STANDARD_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in ACTION_STANDARD_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "action_standard_work_time_closure_incomplete",
                f"{ACTION_STANDARD_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    if manifest.symbols["A0_I"].status in {"derived", "derived_conditional"}:
        blocked = [
            symbol
            for symbol in ACTION_STANDARD_REQUIRED_SYMBOLS[:-1]
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "action_standard_work_time_premature",
                    f"A0_I cannot be derived while action inputs remain unclosed: {', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == ACTION_STANDARD_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "action_standard_work_time_missing_derivation",
                f"{ACTION_STANDARD_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in ACTION_STANDARD_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "action_standard_work_time_closure_incomplete",
                    f"{ACTION_STANDARD_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in ACTION_STANDARD_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "action_standard_work_time_gate_missing",
                f"{ACTION_STANDARD_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_hbar_action_standard_closure(manifest: Manifest) -> list[Issue]:
    if HBAR_ACTION_STANDARD_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "hbar_action_standard_closure_incomplete",
                f"{HBAR_ACTION_STANDARD_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[HBAR_ACTION_STANDARD_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "hbar_action_standard_closure_premature",
                    f"{HBAR_ACTION_STANDARD_TARGET} cannot be derived while unclosed nodes remain: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == HBAR_ACTION_STANDARD_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "hbar_action_standard_closure_missing_derivation",
                f"{HBAR_ACTION_STANDARD_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "hbar_action_standard_closure_incomplete",
                    f"{HBAR_ACTION_STANDARD_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in HBAR_ACTION_STANDARD_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "hbar_action_standard_gate_missing",
                f"{HBAR_ACTION_STANDARD_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_joint_action_gravity_anchor(manifest: Manifest) -> list[Issue]:
    if JOINT_ACTION_GRAVITY_ANCHOR_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [
        symbol for symbol in JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS if symbol not in manifest.symbols
    ]
    if missing:
        return [
            Issue(
                "joint_action_gravity_anchor_incomplete",
                f"{JOINT_ACTION_GRAVITY_ANCHOR_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[JOINT_ACTION_GRAVITY_ANCHOR_TARGET].status
    if target_status in {"derived", "derived_conditional"}:
        blocked = [
            symbol
            for symbol in JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "joint_action_gravity_anchor_premature",
                    f"{JOINT_ACTION_GRAVITY_ANCHOR_TARGET} cannot be closed while joint inputs remain unclosed: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next(
        (item for item in manifest.derivations if item.target == JOINT_ACTION_GRAVITY_ANCHOR_TARGET),
        None,
    )
    if derivation is None:
        issues.append(
            Issue(
                "joint_action_gravity_anchor_missing_derivation",
                f"{JOINT_ACTION_GRAVITY_ANCHOR_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [
            symbol for symbol in JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS if symbol not in dependencies
        ]
        if omitted:
            issues.append(
                Issue(
                    "joint_action_gravity_anchor_incomplete",
                    f"{JOINT_ACTION_GRAVITY_ANCHOR_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )
    return issues


def check_qm_generator_translation_closure(manifest: Manifest) -> list[Issue]:
    if QM_GENERATOR_TRANSLATION_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [
        symbol for symbol in QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS if symbol not in manifest.symbols
    ]
    if missing:
        return [
            Issue(
                "qm_generator_translation_closure_incomplete",
                f"{QM_GENERATOR_TRANSLATION_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[QM_GENERATOR_TRANSLATION_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "qm_generator_translation_closure_premature",
                    f"{QM_GENERATOR_TRANSLATION_TARGET} cannot be derived while unclosed nodes remain: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next(
        (item for item in manifest.derivations if item.target == QM_GENERATOR_TRANSLATION_TARGET), None
    )
    if derivation is None:
        issues.append(
            Issue(
                "qm_generator_translation_closure_missing_derivation",
                f"{QM_GENERATOR_TRANSLATION_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [
            symbol for symbol in QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS if symbol not in dependencies
        ]
        if omitted:
            issues.append(
                Issue(
                    "qm_generator_translation_closure_incomplete",
                    f"{QM_GENERATOR_TRANSLATION_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [
        gate_id for gate_id in QM_GENERATOR_TRANSLATION_REQUIRED_GATES if gate_id not in finite_gate_ids
    ]
    if missing_gates:
        issues.append(
            Issue(
                "qm_generator_translation_gate_missing",
                f"{QM_GENERATOR_TRANSLATION_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_qm_apparatus_facticity_closure(manifest: Manifest) -> list[Issue]:
    if QM_APPARATUS_FACTICITY_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [
        symbol for symbol in QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS if symbol not in manifest.symbols
    ]
    if missing:
        return [
            Issue(
                "qm_apparatus_facticity_closure_incomplete",
                f"{QM_APPARATUS_FACTICITY_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[QM_APPARATUS_FACTICITY_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "qm_apparatus_facticity_closure_premature",
                    f"{QM_APPARATUS_FACTICITY_TARGET} cannot be derived while unclosed nodes remain: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next(
        (item for item in manifest.derivations if item.target == QM_APPARATUS_FACTICITY_TARGET), None
    )
    if derivation is None:
        issues.append(
            Issue(
                "qm_apparatus_facticity_closure_missing_derivation",
                f"{QM_APPARATUS_FACTICITY_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [
            symbol for symbol in QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS if symbol not in dependencies
        ]
        if omitted:
            issues.append(
                Issue(
                    "qm_apparatus_facticity_closure_incomplete",
                    f"{QM_APPARATUS_FACTICITY_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [
        gate_id for gate_id in QM_APPARATUS_FACTICITY_REQUIRED_GATES if gate_id not in finite_gate_ids
    ]
    if missing_gates:
        issues.append(
            Issue(
                "qm_apparatus_facticity_gate_missing",
                f"{QM_APPARATUS_FACTICITY_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_qm_continuum_limit_closure(manifest: Manifest) -> list[Issue]:
    if QM_CONTINUUM_LIMIT_TARGET not in manifest.symbols:
        return []
    issues: list[Issue] = []
    missing = [symbol for symbol in QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS if symbol not in manifest.symbols]
    if missing:
        return [
            Issue(
                "qm_continuum_limit_closure_incomplete",
                f"{QM_CONTINUUM_LIMIT_TARGET} missing symbols: {', '.join(missing)}",
            )
        ]

    target_status = manifest.symbols[QM_CONTINUUM_LIMIT_TARGET].status
    if target_status == "derived":
        blocked = [
            symbol
            for symbol in QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS
            if manifest.symbols[symbol].status not in QM_FOUNDATION_CLOSED_STATUSES
        ]
        if blocked:
            issues.append(
                Issue(
                    "qm_continuum_limit_closure_premature",
                    f"{QM_CONTINUUM_LIMIT_TARGET} cannot be derived while unclosed nodes remain: "
                    f"{', '.join(blocked)}",
                )
            )

    derivation = next((item for item in manifest.derivations if item.target == QM_CONTINUUM_LIMIT_TARGET), None)
    if derivation is None:
        issues.append(
            Issue(
                "qm_continuum_limit_closure_missing_derivation",
                f"{QM_CONTINUUM_LIMIT_TARGET} needs an explicit derivation",
            )
        )
    else:
        dependencies = set(derivation.depends_on)
        omitted = [symbol for symbol in QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS if symbol not in dependencies]
        if omitted:
            issues.append(
                Issue(
                    "qm_continuum_limit_closure_incomplete",
                    f"{QM_CONTINUUM_LIMIT_TARGET} derivation omits: {', '.join(omitted)}",
                )
            )

    finite_gate_ids = {gate.identifier for gate in manifest.finite_gates}
    missing_gates = [gate_id for gate_id in QM_CONTINUUM_LIMIT_REQUIRED_GATES if gate_id not in finite_gate_ids]
    if missing_gates:
        issues.append(
            Issue(
                "qm_continuum_limit_gate_missing",
                f"{QM_CONTINUUM_LIMIT_TARGET} missing finite gates: {', '.join(missing_gates)}",
            )
        )
    return issues


def check_cycles(manifest: Manifest) -> list[Issue]:
    graph = dependency_graph(manifest)
    issues: list[Issue] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str, path: tuple[str, ...]) -> None:
        if node in visiting:
            cycle = " -> ".join((*path, node))
            issues.append(Issue("dependency_cycle", f"cycle detected: {cycle}"))
            return
        if node in visited:
            return
        visiting.add(node)
        for dependency in graph.get(node, set()):
            visit(dependency, (*path, node))
        visiting.remove(node)
        visited.add(node)

    for node in graph:
        visit(node, ())
    return issues


def check_forbidden_paths(manifest: Manifest) -> list[Issue]:
    graph = dependency_graph(manifest)
    issues: list[Issue] = []
    for forbidden in manifest.forbidden_paths:
        reachable_nodes = reachable_from(forbidden.target, graph)
        for source in forbidden.sources:
            if source in reachable_nodes:
                issues.append(
                    Issue(
                        "forbidden_input_path",
                        f"{forbidden.target} depends on forbidden source {source}",
                    )
                )
    return issues


def dependency_graph(manifest: Manifest) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for derivation in manifest.derivations:
        graph.setdefault(derivation.target, set()).update(derivation.depends_on)
        for dependency in derivation.depends_on:
            graph.setdefault(dependency, set())
    return graph


def reachable_from(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(graph.get(start, set()))
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(graph.get(node, set()))
    return seen


def expression_symbols(raw: object) -> set[str]:
    if isinstance(raw, str):
        return {raw}
    expr = require_mapping(raw, "expression")
    if "symbol" in expr:
        return {require_string(expr["symbol"], "expression.symbol")}
    if "mul" in expr:
        symbols: set[str] = set()
        for item in require_list(expr["mul"], "expression.mul"):
            symbols.update(expression_symbols(item))
        return symbols
    if "div" in expr:
        pair = require_list(expr["div"], "expression.div")
        if len(pair) != 2:
            raise ManifestError("expression.div must contain two items")
        return expression_symbols(pair[0]) | expression_symbols(pair[1])
    if "pow" in expr:
        pair = require_list(expr["pow"], "expression.pow")
        if len(pair) != 2:
            raise ManifestError("expression.pow must contain expression and integer exponent")
        return expression_symbols(pair[0])
    raise ManifestError(f"unknown expression operator: {sorted(expr)}")


def evaluate_dimension(raw: object, symbols: dict[str, Symbol]) -> Dimension:
    if isinstance(raw, str):
        return symbol_dimension(raw, symbols)
    expr = require_mapping(raw, "expression")
    if "symbol" in expr:
        return symbol_dimension(require_string(expr["symbol"], "expression.symbol"), symbols)
    if "mul" in expr:
        dimension = Dimension.dimensionless()
        for item in require_list(expr["mul"], "expression.mul"):
            dimension = dimension * evaluate_dimension(item, symbols)
        return dimension
    if "div" in expr:
        pair = require_list(expr["div"], "expression.div")
        if len(pair) != 2:
            raise ManifestError("expression.div must contain two items")
        return evaluate_dimension(pair[0], symbols) / evaluate_dimension(pair[1], symbols)
    if "pow" in expr:
        pair = require_list(expr["pow"], "expression.pow")
        if len(pair) != 2:
            raise ManifestError("expression.pow must contain expression and integer exponent")
        exponent_raw = pair[1]
        if not isinstance(exponent_raw, int):
            raise ManifestError("expression.pow exponent must be an integer")
        return evaluate_dimension(pair[0], symbols) ** exponent_raw
    raise ManifestError(f"unknown expression operator: {sorted(expr)}")


def symbol_dimension(name: str, symbols: dict[str, Symbol]) -> Dimension:
    symbol = symbols.get(name)
    if symbol is None:
        raise ManifestError(f"unknown symbol {name}")
    return symbol.dimension


def check_finite_gates(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    for gate in manifest.finite_gates:
        try:
            gate_issues = check_finite_gate(gate)
        except ManifestError as error:
            issues.append(Issue("invalid_finite_gate", f"{gate.identifier}: {error}"))
            continue
        issues.extend(gate_issues)
    return issues


def check_finite_gate(gate: FiniteGate) -> list[Issue]:
    checker = FINITE_GATE_CHECKS.get(gate.gate_type)
    if checker is not None:
        return checker(gate)
    raise ManifestError(f"unknown finite gate type {gate.gate_type!r}")


def check_research_graph_contract_grounding(manifest: Manifest) -> list[Issue]:
    issues: list[Issue] = []
    known_refs = research_graph_known_evidence_refs(manifest)
    for gate in manifest.finite_gates:
        if gate.gate_type != "research_graph_contract":
            continue
        try:
            surfaces = require_list(gate.payload.get("surfaces"), f"{gate.identifier}.surfaces")
        except ManifestError as error:
            issues.append(
                Issue(
                    "research_graph_contract_grounding_invalid",
                    f"{gate.identifier}: {error}",
                )
            )
            continue
        for surface_index, item in enumerate(surfaces):
            try:
                surface = require_mapping(item, f"{gate.identifier}.surfaces[{surface_index}]")
                surface_name = require_string(
                    surface.get("surface"),
                    f"{gate.identifier}.surfaces[{surface_index}].surface",
                )
                evidence_refs = require_string_tuple(
                    surface.get("evidence_refs", []),
                    f"{gate.identifier}.surfaces[{surface_index}].evidence_refs",
                )
            except ManifestError as error:
                issues.append(
                    Issue(
                        "research_graph_contract_grounding_invalid",
                        f"{gate.identifier}: {error}",
                    )
                )
                continue
            for evidence_ref in evidence_refs:
                if evidence_ref in known_refs or research_graph_doc_ref_exists(evidence_ref):
                    continue
                issues.append(
                    Issue(
                        "research_graph_contract_evidence_unresolved",
                        f"{gate.identifier}: {surface_name} evidence ref {evidence_ref!r} is not grounded",
                    )
                )
    return issues


def research_graph_known_evidence_refs(manifest: Manifest) -> set[str]:
    refs = set(RESEARCH_GRAPH_CONTRACT_SCHEMA_REFS)
    refs.update(RESEARCH_GRAPH_CONTRACT_CHECK_REFS)
    refs.update(manifest.symbols)
    refs.update(equation.identifier for equation in manifest.equations)
    refs.update(derivation.identifier for derivation in manifest.derivations)
    refs.update(derivation.target for derivation in manifest.derivations)
    refs.update(gate.identifier for gate in manifest.finite_gates)
    refs.update(experiment.identifier for experiment in manifest.qm_experiments)
    refs.update(pattern.identifier for pattern in manifest.qm_universal_patterns)
    refs.update(obligation.identifier for obligation in manifest.qm_core_proof_obligations)
    refs.update(card.identifier for card in manifest.theorem_cards)
    return refs


def research_graph_doc_ref_exists(evidence_ref: str) -> bool:
    path = Path(evidence_ref)
    if path.is_absolute():
        return path.is_file()
    if not evidence_ref.endswith(".md"):
        return False
    if path.is_file():
        return True
    repo_root = Path(__file__).resolve().parent.parent
    return (repo_root / path).is_file()


def check_psd_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    matrix = parse_matrix(gate.payload.get("matrix"), f"{gate.identifier}.matrix")
    return matrix_psd_issues(gate.identifier, matrix, tolerance)


def check_schur_psd_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    left = parse_matrix(gate.payload.get("left"), f"{gate.identifier}.left")
    right = parse_matrix(gate.payload.get("right"), f"{gate.identifier}.right")
    if len(left) != len(right) or len(left[0]) != len(right[0]):
        raise ManifestError("Schur inputs must have the same shape")
    left_issues = matrix_psd_issues(f"{gate.identifier}.left", left, tolerance)
    right_issues = matrix_psd_issues(f"{gate.identifier}.right", right, tolerance)
    if left_issues or right_issues:
        return [Issue("schur_input_not_psd", f"{gate.identifier}: Schur input is not PSD")]
    product = elementwise_product(left, right)
    product_issues = matrix_psd_issues(f"{gate.identifier}.product", product, tolerance)
    if product_issues:
        return [Issue("schur_product_not_psd", f"{gate.identifier}: Schur product is not PSD")]
    return []


def check_block_psd_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g0 = parse_matrix(gate.payload.get("G0"), f"{gate.identifier}.G0")
    g1 = parse_matrix(gate.payload.get("G1"), f"{gate.identifier}.G1")
    cross = parse_matrix(gate.payload.get("X"), f"{gate.identifier}.X")
    if len(cross) != len(g1):
        raise ManifestError("X row count must match G1 size")
    if cross and len(cross[0]) != len(g0):
        raise ManifestError("X column count must match G0 size")

    top_rows: list[list[complex]] = []
    for row_index, g0_row in enumerate(g0):
        top_rows.append([*g0_row, *[cross[col][row_index].conjugate() for col in range(len(g1))]])

    bottom_rows: list[list[complex]] = []
    for row_index, g1_row in enumerate(g1):
        bottom_rows.append([*cross[row_index], *g1_row])

    return matrix_psd_issues(gate.identifier, [*top_rows, *bottom_rows], tolerance)


def check_contraction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    matrix = parse_matrix(gate.payload.get("matrix"), f"{gate.identifier}.matrix")
    if not matrix:
        raise ManifestError("matrix must not be empty")
    width = len(matrix[0])
    for row in matrix:
        if len(row) != width:
            raise ManifestError("matrix rows must have equal length")
    if len(matrix) > 6 or width > 6:
        raise ManifestError("contraction gate currently supports matrices up to 6x6")
    gram = matrix_multiply(conjugate_transpose(matrix), matrix)
    complement = identity_minus(gram)
    issues = matrix_psd_issues(gate.identifier, complement, tolerance)
    if issues:
        return [Issue("not_contraction", f"{gate.identifier}: I-C^dagger C is not PSD")]
    return []


def check_cycle_holonomy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    edges = parse_phase_edges(gate.payload.get("edges"), f"{gate.identifier}.edges")
    cycle = require_string_tuple(gate.payload.get("cycle"), f"{gate.identifier}.cycle")
    gauge = parse_real_mapping(gate.payload.get("gauge", {}), f"{gate.identifier}.gauge")
    if len(cycle) < 2 or cycle[0] != cycle[-1]:
        raise ManifestError("cycle must be closed")

    phase = cycle_phase(cycle, edges)
    transformed_edges: dict[tuple[str, str], float] = {}
    for edge, edge_phase in edges.items():
        source, target = edge
        transformed_edges[edge] = edge_phase + gauge.get(target, 0.0) - gauge.get(source, 0.0)
    transformed_phase = cycle_phase(cycle, transformed_edges)
    if abs(wrapped_angle(phase - transformed_phase)) > tolerance:
        return [
            Issue(
                "holonomy_not_gauge_invariant",
                f"{gate.identifier}: cycle holonomy changed under endpoint relabeling",
            )
        ]
    return []


def check_cycle_holonomy_class_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    edges = parse_phase_edges(gate.payload.get("edges"), f"{gate.identifier}.edges")
    cycle = require_string_tuple(gate.payload.get("cycle"), f"{gate.identifier}.cycle")
    expected = require_string(gate.payload.get("expected"), f"{gate.identifier}.expected")
    if expected not in {"exact", "non_exact"}:
        raise ManifestError("expected must be exact or non_exact")
    if len(cycle) < 2 or cycle[0] != cycle[-1]:
        raise ManifestError("cycle must be closed")
    phase = cycle_phase(cycle, edges)
    is_exact = abs(phase) <= tolerance
    if expected == "exact" and not is_exact:
        return [Issue("unexpected_non_exact_holonomy", f"{gate.identifier}: expected exact holonomy")]
    if expected == "non_exact" and is_exact:
        return [Issue("unexpected_exact_holonomy", f"{gate.identifier}: expected non-exact holonomy")]
    return []


def check_actualization_i3_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    weights = parse_vector(gate.payload.get("weights"), f"{gate.identifier}.weights")
    gamma = parse_matrix(gate.payload.get("gamma"), f"{gate.identifier}.gamma")
    events = require_mapping(gate.payload.get("events"), f"{gate.identifier}.events")
    event_a = parse_index_tuple(events.get("A"), f"{gate.identifier}.events.A")
    event_b = parse_index_tuple(events.get("B"), f"{gate.identifier}.events.B")
    event_c = parse_index_tuple(events.get("C"), f"{gate.identifier}.events.C")
    validate_events((event_a, event_b, event_c), len(weights), len(gamma))
    if set(event_a) & set(event_b) or set(event_a) & set(event_c) or set(event_b) & set(event_c):
        raise ManifestError("I3 events must be pairwise disjoint")
    i3_value = sorkin_i3(event_a, event_b, event_c, weights, gamma)
    if abs(i3_value) > tolerance:
        return [Issue("i3_nonzero", f"{gate.identifier}: I3={i3_value.real:g}+{i3_value.imag:g}i")]
    return []


def check_two_path_interference_fringe_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    weights = parse_vector(gate.payload.get("weights"), f"{gate.identifier}.weights")
    gamma = parse_matrix(gate.payload.get("gamma"), f"{gate.identifier}.gamma")
    if len(weights) != 2 or len(gamma) != 2:
        raise ManifestError("two-path fringe gate requires exactly two alternatives")
    validate_events(((0,), (1,), (0, 1)), len(weights), len(gamma))
    gamma_issues = matrix_psd_issues(f"{gate.identifier}.gamma", gamma, tolerance)
    if gamma_issues:
        return [Issue("fringe_kernel_not_psd", f"{gate.identifier}: gamma is not PSD")]
    samples = parse_fringe_samples(gate.payload.get("samples"), f"{gate.identifier}.samples")
    expected_visibility = parse_optional_real(
        gate.payload.get("expected_visibility"), f"{gate.identifier}.expected_visibility"
    )
    visibility, offset = fringe_visibility_phase(weights, gamma, tolerance)
    if expected_visibility is not None and abs(visibility - expected_visibility) > tolerance:
        return [
            Issue(
                "fringe_visibility_mismatch",
                f"{gate.identifier}: expected visibility {expected_visibility:g}, computed {visibility:g}",
            )
        ]
    for sample in samples:
        phase = parse_real(sample["phase"], f"{gate.identifier}.sample.phase")
        expected_probability = parse_real(
            sample["expected_probability"],
            f"{gate.identifier}.sample.expected_probability",
        )
        computed_probability = two_path_output_probability(weights, gamma, phase, tolerance)
        formula_probability = 0.5 * (1.0 + (visibility * math.cos(phase - offset)))
        if abs(computed_probability - formula_probability) > tolerance:
            return [
                Issue(
                    "fringe_formula_mismatch",
                    f"{gate.identifier}: direct actualization and derived fringe formula disagree",
                )
            ]
        if abs(computed_probability - expected_probability) > tolerance:
            return [
                Issue(
                    "fringe_probability_mismatch",
                    f"{gate.identifier}: phase {phase:g} expected {expected_probability:g}, "
                    f"computed {computed_probability:g}",
                )
            ]
    return []


def check_born_context_probability_table_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    delta = parse_real(gate.payload.get("delta"), f"{gate.identifier}.delta")
    if delta < 0.0:
        raise ManifestError("delta must be non-negative")
    weights = parse_vector(gate.payload.get("weights"), f"{gate.identifier}.weights")
    gamma = parse_matrix(gate.payload.get("gamma"), f"{gate.identifier}.gamma")
    events = parse_event_context(gate.payload.get("events"), f"{gate.identifier}.events")
    expected = parse_real_list(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
    )
    if len(events) != len(expected):
        raise ManifestError("events and expected_probabilities must have the same length")
    validate_events(tuple(events), len(weights), len(gamma))
    if matrix_psd_issues(f"{gate.identifier}.gamma", gamma, tolerance):
        return [Issue("born_kernel_not_psd", f"{gate.identifier}: gamma is not PSD")]
    context_issue = probability_context_issue(gate.identifier, events, weights, gamma, delta, tolerance)
    if context_issue is not None:
        return [context_issue]
    probabilities = context_probabilities(events, weights, gamma, tolerance)
    for index, probability in enumerate(probabilities):
        if abs(probability - expected[index]) > tolerance:
            return [
                Issue(
                    "born_probability_mismatch",
                    f"{gate.identifier}: event {index} expected {expected[index]:g}, computed {probability:g}",
                )
            ]
    return []


def check_unitary_measurement_context_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state = parse_vector(gate.payload.get("state"), f"{gate.identifier}.state")
    basis = parse_matrix(gate.payload.get("basis"), f"{gate.identifier}.basis")
    expected = parse_real_list(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
    )
    if len(state) != len(expected):
        raise ManifestError("state and expected_probabilities must have the same length")
    validate_square_block(basis, "measurement basis")
    if len(basis) != len(state):
        raise ManifestError("measurement basis size must match state length")
    validate_unitary(basis, tolerance, "measurement basis")
    state_norm = vector_norm_squared(state)
    if abs(state_norm - 1.0) > tolerance:
        raise ManifestError("measurement state must be normalized")
    transformed = matrix_vector_multiply(basis, state)
    probabilities = amplitude_probabilities(transformed, tolerance)
    for index, probability in enumerate(probabilities):
        if abs(probability - expected[index]) > tolerance:
            return [
                Issue(
                    "measurement_probability_mismatch",
                    f"{gate.identifier}: outcome {index} expected {expected[index]:g}, computed {probability:g}",
                )
            ]
    return []


def check_unitary_network_probability_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state = parse_vector(gate.payload.get("state"), f"{gate.identifier}.state")
    unitaries = parse_matrix_list(gate.payload.get("unitaries"), f"{gate.identifier}.unitaries")
    expected = parse_real_list(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
    )
    if len(state) != len(expected):
        raise ManifestError("state and expected_probabilities must have the same length")
    if abs(vector_norm_squared(state) - 1.0) > tolerance:
        raise ManifestError("network input state must be normalized")
    evolved = list(state)
    for index, unitary in enumerate(unitaries):
        validate_square_block(unitary, f"unitaries[{index}]")
        if len(unitary) != len(state):
            raise ManifestError("unitary network dimensions must match state length")
        validate_unitary(unitary, tolerance, f"unitaries[{index}]")
        evolved = matrix_vector_multiply(unitary, evolved)
    probabilities = amplitude_probabilities(evolved, tolerance)
    for index, probability in enumerate(probabilities):
        if abs(probability - expected[index]) > tolerance:
            return [
                Issue(
                    "unitary_network_probability_mismatch",
                    f"{gate.identifier}: output {index} expected {expected[index]:g}, computed {probability:g}",
                )
            ]
    return []


def check_projective_measurement_update_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state = parse_vector(gate.payload.get("state"), f"{gate.identifier}.state")
    projectors = parse_matrix_list(gate.payload.get("projectors"), f"{gate.identifier}.projectors")
    expected = parse_real_list(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
    )
    if len(projectors) != len(expected):
        raise ManifestError("projectors and expected_probabilities must have the same length")
    if abs(vector_norm_squared(state) - 1.0) > tolerance:
        raise ManifestError("measurement input state must be normalized")
    validate_projector_resolution(projectors, len(state), tolerance)
    probabilities = projective_probabilities(state, projectors, tolerance)
    for index, probability in enumerate(probabilities):
        if abs(probability - expected[index]) > tolerance:
            return [
                Issue(
                    "projective_probability_mismatch",
                    f"{gate.identifier}: outcome {index} expected {expected[index]:g}, computed {probability:g}",
                )
            ]
        if probability > tolerance:
            post_state = normalized_projected_state(state, projectors[index], probability)
            repeat_probability = projective_probability(post_state, projectors[index], tolerance)
            if abs(repeat_probability - 1.0) > tolerance:
                return [
                    Issue(
                        "projective_repeatability_failed",
                        f"{gate.identifier}: outcome {index} repeat probability is {repeat_probability:g}",
                    )
                ]
    return []


def check_stern_gerlach_context_readout_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state = parse_two_state(gate.payload.get("state"), f"{gate.identifier}.state", tolerance)
    context = parse_two_state_context(gate.payload.get("context"), f"{gate.identifier}.context", tolerance)
    expected = parse_two_probabilities(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
        tolerance,
    )
    probabilities = amplitude_probabilities(matrix_vector_multiply(context, state), tolerance)
    if not real_lists_close(probabilities, expected, tolerance):
        return [
            Issue(
                "stern_gerlach_probability_mismatch",
                f"{gate.identifier}: expected {expected}, computed {probabilities}",
            )
        ]

    repeat_outcome_raw = gate.payload.get("repeat_outcome")
    if repeat_outcome_raw is not None:
        repeat_outcome = parse_integer(repeat_outcome_raw, f"{gate.identifier}.repeat_outcome")
        if repeat_outcome < 0 or repeat_outcome > 1:
            raise ManifestError("repeat_outcome must be 0 or 1")
        expected_repeat_probability = parse_real(
            gate.payload.get("expected_repeat_probability"),
            f"{gate.identifier}.expected_repeat_probability",
        )
        post_state = context_basis_state(context, repeat_outcome)
        repeat_probabilities = amplitude_probabilities(matrix_vector_multiply(context, post_state), tolerance)
        repeat_probability = repeat_probabilities[repeat_outcome]
        if abs(repeat_probability - expected_repeat_probability) > tolerance:
            return [
                Issue(
                    "stern_gerlach_repeatability_mismatch",
                    f"{gate.identifier}: expected repeat probability {expected_repeat_probability:g}, "
                    f"computed {repeat_probability:g}",
                )
            ]
    return []


def check_sequential_sg_noncommuting_context_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    initial_state = parse_two_state(gate.payload.get("initial_state"), f"{gate.identifier}.initial_state", tolerance)
    sequences = require_list(gate.payload.get("sequences"), f"{gate.identifier}.sequences")
    if not sequences:
        raise ManifestError("sequences must not be empty")
    for index, item in enumerate(sequences):
        sequence = require_mapping(item, f"{gate.identifier}.sequences[{index}]")
        sequence_id = require_string(sequence.get("id"), f"{gate.identifier}.sequences[{index}].id")
        contexts = parse_two_state_contexts(
            sequence.get("contexts"),
            f"{gate.identifier}.sequences[{index}].contexts",
            tolerance,
        )
        expected = parse_two_probabilities(
            sequence.get("expected_final_probabilities"),
            f"{gate.identifier}.sequences[{index}].expected_final_probabilities",
            tolerance,
        )
        rho = density_matrix_from_state(initial_state)
        for context in contexts[:-1]:
            rho = nonselective_context_measurement(rho, context, tolerance)
        probabilities = density_context_probabilities(rho, contexts[-1], tolerance)
        if not real_lists_close(probabilities, expected, tolerance):
            return [
                Issue(
                    "sequential_sg_probability_mismatch",
                    f"{gate.identifier}: sequence {sequence_id} expected {expected}, computed {probabilities}",
                )
            ]
    return []


def check_two_level_update_oscillation_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    initial_state = parse_two_state(gate.payload.get("initial_state"), f"{gate.identifier}.initial_state", tolerance)
    angular_frequency = parse_positive_real(
        gate.payload.get("angular_frequency"),
        f"{gate.identifier}.angular_frequency",
    )
    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if not samples:
        raise ManifestError("samples must not be empty")
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        time = parse_real(sample.get("time"), f"{gate.identifier}.samples[{index}].time")
        if time < -tolerance:
            raise ManifestError("sample time must be non-negative")
        expected = parse_two_probabilities(
            sample.get("expected_probabilities"),
            f"{gate.identifier}.samples[{index}].expected_probabilities",
            tolerance,
        )
        evolved = matrix_vector_multiply(resonant_two_level_unitary(angular_frequency * time), initial_state)
        probabilities = amplitude_probabilities(evolved, tolerance)
        if not real_lists_close(probabilities, expected, tolerance):
            return [
                Issue(
                    "two_level_update_probability_mismatch",
                    f"{gate.identifier}: sample {index} expected {expected}, computed {probabilities}",
                )
            ]
    return []


def check_delayed_context_partition_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state = parse_two_state(gate.payload.get("state"), f"{gate.identifier}.state", tolerance)
    readouts = require_list(gate.payload.get("readouts"), f"{gate.identifier}.readouts")
    if len(readouts) < 2:
        raise ManifestError("delayed context gate requires at least two readouts")
    for index, item in enumerate(readouts):
        readout = require_mapping(item, f"{gate.identifier}.readouts[{index}]")
        readout_id = require_string(readout.get("id"), f"{gate.identifier}.readouts[{index}].id")
        context = parse_two_state_context(
            readout.get("context"),
            f"{gate.identifier}.readouts[{index}].context",
            tolerance,
        )
        expected = parse_two_probabilities(
            readout.get("expected_probabilities"),
            f"{gate.identifier}.readouts[{index}].expected_probabilities",
            tolerance,
        )
        probabilities = amplitude_probabilities(matrix_vector_multiply(context, state), tolerance)
        if not real_lists_close(probabilities, expected, tolerance):
            return [
                Issue(
                    "delayed_context_probability_mismatch",
                    f"{gate.identifier}: readout {readout_id} expected {expected}, computed {probabilities}",
                )
            ]
    return []


def check_ramsey_clock_phase_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    initial_state = parse_two_state(gate.payload.get("initial_state"), f"{gate.identifier}.initial_state", tolerance)
    first_pulse = parse_two_state_context(gate.payload.get("first_pulse"), f"{gate.identifier}.first_pulse", tolerance)
    second_pulse = parse_two_state_context(
        gate.payload.get("second_pulse"), f"{gate.identifier}.second_pulse", tolerance
    )
    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if not samples:
        raise ManifestError("Ramsey gate samples must not be empty")
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        phase = parse_real(sample.get("phase"), f"{gate.identifier}.samples[{index}].phase")
        expected = parse_two_probabilities(
            sample.get("expected_probabilities"),
            f"{gate.identifier}.samples[{index}].expected_probabilities",
            tolerance,
        )
        after_first = matrix_vector_multiply(first_pulse, initial_state)
        after_phase = matrix_vector_multiply(relative_phase_matrix(phase), after_first)
        final_state = matrix_vector_multiply(second_pulse, after_phase)
        probabilities = amplitude_probabilities(final_state, tolerance)
        if not real_lists_close(probabilities, expected, tolerance):
            return [
                Issue(
                    "ramsey_clock_phase_probability_mismatch",
                    f"{gate.identifier}: sample {index} expected {expected}, computed {probabilities}",
                )
            ]
    return []


def check_ab_holonomy_phase_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    charge = parse_real(gate.payload.get("charge"), f"{gate.identifier}.charge")
    flux = parse_real(gate.payload.get("magnetic_flux"), f"{gate.identifier}.magnetic_flux")
    hbar = parse_positive_real(gate.payload.get("hbar"), f"{gate.identifier}.hbar")
    expected_phase = parse_real(gate.payload.get("expected_phase"), f"{gate.identifier}.expected_phase")
    local_force_bound = parse_nonnegative_real(
        gate.payload.get("local_force_bound"),
        f"{gate.identifier}.local_force_bound",
    )
    if local_force_bound > tolerance:
        return [
            Issue(
                "ab_local_force_not_zero",
                f"{gate.identifier}: local force bound {local_force_bound:g} exceeds tolerance",
            )
        ]
    computed_phase = wrapped_angle((charge * flux) / hbar)
    if abs(wrapped_angle(computed_phase - expected_phase)) > tolerance:
        return [
            Issue(
                "ab_holonomy_phase_mismatch",
                f"{gate.identifier}: expected phase {expected_phase:g}, computed {computed_phase:g}",
            )
        ]
    return []


def check_ab_flux_period_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    charge = parse_real(gate.payload.get("charge"), f"{gate.identifier}.charge")
    if abs(charge) <= tolerance:
        raise ManifestError("charge must be nonzero")
    h_value = parse_positive_real(gate.payload.get("h"), f"{gate.identifier}.h")
    expected_flux_period = parse_positive_real(
        gate.payload.get("expected_flux_period"),
        f"{gate.identifier}.expected_flux_period",
    )
    computed_flux_period = h_value / abs(charge)
    if abs(computed_flux_period - expected_flux_period) > tolerance:
        return [
            Issue(
                "ab_flux_period_mismatch",
                f"{gate.identifier}: expected period {expected_flux_period:g}, computed {computed_flux_period:g}",
            )
        ]
    closure_ratio = (abs(charge) * expected_flux_period) / h_value
    if abs(closure_ratio - 1.0) > tolerance:
        return [
            Issue(
                "ab_flux_period_closure_mismatch",
                f"{gate.identifier}: |q|Phi0/h closure ratio is {closure_ratio:g}",
            )
        ]
    return []


def check_action_frequency_threshold_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    h_value = parse_positive_real(gate.payload.get("h"), f"{gate.identifier}.h")
    work_function = parse_positive_real(gate.payload.get("work_function"), f"{gate.identifier}.work_function")
    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if not samples:
        raise ManifestError("threshold gate samples must not be empty")
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        frequency = parse_nonnegative_real(sample.get("frequency"), f"{gate.identifier}.samples[{index}].frequency")
        expected_emission = parse_bool(
            sample.get("expected_emission"),
            f"{gate.identifier}.samples[{index}].expected_emission",
        )
        expected_kinetic_energy = parse_nonnegative_real(
            sample.get("expected_kinetic_energy"),
            f"{gate.identifier}.samples[{index}].expected_kinetic_energy",
        )
        available_energy = h_value * frequency
        computed_emission = available_energy + tolerance >= work_function
        if computed_emission != expected_emission:
            return [
                Issue(
                    "action_frequency_emission_mismatch",
                    f"{gate.identifier}: sample {index} expected emission {expected_emission}, computed {computed_emission}",
                )
            ]
        computed_kinetic_energy = max(0.0, available_energy - work_function)
        if abs(computed_kinetic_energy - expected_kinetic_energy) > tolerance:
            return [
                Issue(
                    "action_frequency_kinetic_energy_mismatch",
                    (
                        f"{gate.identifier}: sample {index} expected kinetic energy "
                        f"{expected_kinetic_energy:g}, computed {computed_kinetic_energy:g}"
                    ),
                )
            ]
    return []


def check_spectral_anchor_consistency_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    h_value = parse_positive_real(gate.payload.get("h"), f"{gate.identifier}.h")
    transitions = require_list(gate.payload.get("transitions"), f"{gate.identifier}.transitions")
    if not transitions:
        raise ManifestError("spectral anchor transitions must not be empty")
    for index, item in enumerate(transitions):
        transition = require_mapping(item, f"{gate.identifier}.transitions[{index}]")
        transition_id = require_string(transition.get("id"), f"{gate.identifier}.transitions[{index}].id")
        delta_energy = parse_positive_real(
            transition.get("delta_energy"),
            f"{gate.identifier}.transitions[{index}].delta_energy",
        )
        frequency = parse_positive_real(
            transition.get("frequency"),
            f"{gate.identifier}.transitions[{index}].frequency",
        )
        computed_frequency = delta_energy / h_value
        if abs(computed_frequency - frequency) > tolerance:
            return [
                Issue(
                    "spectral_anchor_frequency_mismatch",
                    (
                        f"{gate.identifier}: transition {transition_id} expected frequency "
                        f"{frequency:g}, computed {computed_frequency:g}"
                    ),
                )
            ]
    return []


def check_barrier_transmission_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    classically_forbidden = parse_bool(
        gate.payload.get("classically_forbidden", True),
        f"{gate.identifier}.classically_forbidden",
    )
    if not classically_forbidden:
        return [Issue("barrier_not_classically_forbidden", f"{gate.identifier}: barrier is not marked forbidden")]
    decay_constant = parse_positive_real(gate.payload.get("decay_constant"), f"{gate.identifier}.decay_constant")
    width = parse_positive_real(gate.payload.get("width"), f"{gate.identifier}.width")
    expected_transmission = parse_unit_interval(
        gate.payload.get("expected_transmission"),
        f"{gate.identifier}.expected_transmission",
    )
    expected_reflection = parse_unit_interval(
        gate.payload.get("expected_reflection"),
        f"{gate.identifier}.expected_reflection",
    )
    computed_transmission = math.exp(-2.0 * decay_constant * width)
    computed_reflection = 1.0 - computed_transmission
    if abs(expected_transmission + expected_reflection - 1.0) > tolerance:
        return [
            Issue(
                "barrier_probability_closure_mismatch",
                f"{gate.identifier}: expected transmission/reflection probabilities do not sum to one",
            )
        ]
    if abs(computed_transmission - expected_transmission) > tolerance:
        return [
            Issue(
                "barrier_transmission_mismatch",
                (
                    f"{gate.identifier}: expected transmission {expected_transmission:g}, "
                    f"computed {computed_transmission:g}"
                ),
            )
        ]
    if abs(computed_reflection - expected_reflection) > tolerance:
        return [
            Issue(
                "barrier_reflection_mismatch",
                f"{gate.identifier}: expected reflection {expected_reflection:g}, computed {computed_reflection:g}",
            )
        ]
    return []


def check_repeated_context_zeno_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    total_angle = parse_positive_real(gate.payload.get("total_angle"), f"{gate.identifier}.total_angle")
    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if not samples:
        raise ManifestError("Zeno gate samples must not be empty")
    previous_count: int | None = None
    previous_survival: float | None = None
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        readout_count = parse_positive_integer(
            sample.get("readout_count"),
            f"{gate.identifier}.samples[{index}].readout_count",
        )
        expected_survival = parse_unit_interval(
            sample.get("expected_survival"),
            f"{gate.identifier}.samples[{index}].expected_survival",
        )
        step_survival = math.cos(total_angle / (2.0 * readout_count)) ** 2
        computed_survival = step_survival**readout_count
        if abs(computed_survival - expected_survival) > tolerance:
            return [
                Issue(
                    "repeated_context_zeno_survival_mismatch",
                    (
                        f"{gate.identifier}: sample {index} expected survival "
                        f"{expected_survival:g}, computed {computed_survival:g}"
                    ),
                )
            ]
        if (
            previous_count is not None
            and previous_survival is not None
            and readout_count > previous_count
            and computed_survival + tolerance < previous_survival
        ):
            return [
                Issue(
                    "repeated_context_zeno_monotonicity_mismatch",
                    f"{gate.identifier}: survival decreased when readout count increased",
                )
            ]
        previous_count = readout_count
        previous_survival = computed_survival
    return []


def check_bosonic_indistinguishability_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    wavepacket_overlap = parse_unit_interval(
        gate.payload.get("wavepacket_overlap"),
        f"{gate.identifier}.wavepacket_overlap",
    )
    expected_coincidence = parse_unit_interval(
        gate.payload.get("expected_coincidence"),
        f"{gate.identifier}.expected_coincidence",
    )
    expected_bunching = parse_unit_interval(
        gate.payload.get("expected_bunching"),
        f"{gate.identifier}.expected_bunching",
    )
    computed_coincidence = 0.5 * (1.0 - wavepacket_overlap)
    computed_bunching = 1.0 - computed_coincidence
    if abs(expected_coincidence + expected_bunching - 1.0) > tolerance:
        return [
            Issue(
                "bosonic_probability_closure_mismatch",
                f"{gate.identifier}: coincidence and bunching probabilities do not sum to one",
            )
        ]
    if abs(computed_coincidence - expected_coincidence) > tolerance:
        return [
            Issue(
                "bosonic_coincidence_mismatch",
                (
                    f"{gate.identifier}: expected coincidence {expected_coincidence:g}, "
                    f"computed {computed_coincidence:g}"
                ),
            )
        ]
    if abs(computed_bunching - expected_bunching) > tolerance:
        return [
            Issue(
                "bosonic_bunching_mismatch",
                f"{gate.identifier}: expected bunching {expected_bunching:g}, computed {computed_bunching:g}",
            )
        ]
    return []


def check_single_quantum_facticity_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    trial_count = parse_positive_integer(gate.payload.get("trial_count"), f"{gate.identifier}.trial_count")
    detector_a_count = parse_positive_integer(
        gate.payload.get("detector_a_count"),
        f"{gate.identifier}.detector_a_count",
    )
    detector_b_count = parse_positive_integer(
        gate.payload.get("detector_b_count"),
        f"{gate.identifier}.detector_b_count",
    )
    coincidence_count = parse_nonnegative_integer(
        gate.payload.get("coincidence_count"),
        f"{gate.identifier}.coincidence_count",
    )
    expected_g2_zero = parse_nonnegative_real(gate.payload.get("expected_g2_zero"), f"{gate.identifier}.expected_g2_zero")
    max_g2_zero = parse_nonnegative_real(gate.payload.get("max_g2_zero"), f"{gate.identifier}.max_g2_zero")
    computed_g2_zero = (coincidence_count * trial_count) / (detector_a_count * detector_b_count)
    if abs(computed_g2_zero - expected_g2_zero) > tolerance:
        return [
            Issue(
                "single_quantum_g2_mismatch",
                f"{gate.identifier}: expected g2(0) {expected_g2_zero:g}, computed {computed_g2_zero:g}",
            )
        ]
    if computed_g2_zero - max_g2_zero > tolerance:
        return [
            Issue(
                "single_quantum_classical_bound_mismatch",
                f"{gate.identifier}: g2(0) {computed_g2_zero:g} exceeds bound {max_g2_zero:g}",
            )
        ]
    return []


def check_conditional_inheritance_swap_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    bell_outcome = require_string(gate.payload.get("bell_outcome"), f"{gate.identifier}.bell_outcome")
    correlations = require_list(gate.payload.get("remote_correlations"), f"{gate.identifier}.remote_correlations")
    if not correlations:
        raise ManifestError("swapping gate correlations must not be empty")
    for index, item in enumerate(correlations):
        correlation = require_mapping(item, f"{gate.identifier}.remote_correlations[{index}]")
        context = require_string(
            correlation.get("context"),
            f"{gate.identifier}.remote_correlations[{index}].context",
        )
        expected = parse_real(
            correlation.get("expected_correlation"),
            f"{gate.identifier}.remote_correlations[{index}].expected_correlation",
        )
        computed = bell_state_context_correlation(bell_outcome, context)
        if abs(computed - expected) > tolerance:
            return [
                Issue(
                    "conditional_inheritance_swap_correlation_mismatch",
                    f"{gate.identifier}: context {context} expected {expected:g}, computed {computed:g}",
                )
            ]
    return []


def check_context_transfer_no_cloning_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    input_state = parse_two_state(gate.payload.get("input_state"), f"{gate.identifier}.input_state", tolerance)
    bell_branch = require_string(gate.payload.get("bell_branch"), f"{gate.identifier}.bell_branch")
    expected_target_state = parse_two_state(
        gate.payload.get("expected_target_state"),
        f"{gate.identifier}.expected_target_state",
        tolerance,
    )
    branch_state = teleportation_branch_state(input_state, bell_branch)
    corrected_state = teleportation_corrected_state(branch_state, bell_branch)
    if not complex_lists_close(corrected_state, expected_target_state, tolerance):
        return [
            Issue(
                "context_transfer_target_state_mismatch",
                f"{gate.identifier}: corrected target state does not match expected input context",
            )
        ]
    return []


def check_no_cloning_context_invariance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    state_overlap = parse_unit_interval(gate.payload.get("state_overlap"), f"{gate.identifier}.state_overlap")
    min_obstruction = parse_positive_real(gate.payload.get("min_obstruction"), f"{gate.identifier}.min_obstruction")
    expected_obstructed = parse_bool(gate.payload.get("expected_obstructed"), f"{gate.identifier}.expected_obstructed")
    cloned_overlap = state_overlap * state_overlap
    obstruction = abs(state_overlap - cloned_overlap)
    computed_obstructed = obstruction + tolerance >= min_obstruction
    if computed_obstructed != expected_obstructed:
        return [
            Issue(
                "no_cloning_obstruction_mismatch",
                f"{gate.identifier}: obstruction {obstruction:g} did not match expected obstruction status",
            )
        ]
    return []


def check_multipartite_contextuality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    _ = tolerance
    constraints = require_list(gate.payload.get("constraints"), f"{gate.identifier}.constraints")
    if len(constraints) < 2:
        raise ManifestError("multipartite contextuality gate requires at least two constraints")
    expected_obstructed = parse_bool(gate.payload.get("expected_obstructed"), f"{gate.identifier}.expected_obstructed")
    occurrence_counts: dict[str, int] = {}
    product = 1
    for index, item in enumerate(constraints):
        constraint = require_mapping(item, f"{gate.identifier}.constraints[{index}]")
        context = require_list(constraint.get("context"), f"{gate.identifier}.constraints[{index}].context")
        if not context:
            raise ManifestError("contextuality constraint context must not be empty")
        for party_index, observable_raw in enumerate(context):
            observable = require_string(
                observable_raw,
                f"{gate.identifier}.constraints[{index}].context[{party_index}]",
            ).lower()
            key = f"{party_index}:{observable}"
            occurrence_counts[key] = occurrence_counts.get(key, 0) + 1
        product *= parse_bell_outcome(
            constraint.get("expected_product"),
            f"{gate.identifier}.constraints[{index}].expected_product",
        )
    even_occurrences = all(count % 2 == 0 for count in occurrence_counts.values())
    computed_obstructed = even_occurrences and product == -1
    if computed_obstructed != expected_obstructed:
        return [
            Issue(
                "multipartite_contextuality_obstruction_mismatch",
                f"{gate.identifier}: computed obstruction {computed_obstructed}, expected {expected_obstructed}",
            )
        ]
    return []


def check_ks_contextuality_obstruction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    _ = tolerance
    contexts = require_list(gate.payload.get("contexts"), f"{gate.identifier}.contexts")
    if not contexts:
        raise ManifestError("KS gate contexts must not be empty")
    expected_obstructed = parse_bool(gate.payload.get("expected_obstructed"), f"{gate.identifier}.expected_obstructed")
    projector_counts: dict[str, int] = {}
    for context_index, item in enumerate(contexts):
        context = require_list(item, f"{gate.identifier}.contexts[{context_index}]")
        if not context:
            raise ManifestError("KS context must not be empty")
        for projector_index, projector_raw in enumerate(context):
            projector = require_string(projector_raw, f"{gate.identifier}.contexts[{context_index}][{projector_index}]")
            projector_counts[projector] = projector_counts.get(projector, 0) + 1
    even_projector_counts = all(count % 2 == 0 for count in projector_counts.values())
    odd_context_count = len(contexts) % 2 == 1
    computed_obstructed = even_projector_counts and odd_context_count
    if computed_obstructed != expected_obstructed:
        return [
            Issue(
                "ks_contextuality_obstruction_mismatch",
                f"{gate.identifier}: computed obstruction {computed_obstructed}, expected {expected_obstructed}",
            )
        ]
    return []


def check_temporal_facticity_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c12 = parse_real(gate.payload.get("c12"), f"{gate.identifier}.c12")
    c23 = parse_real(gate.payload.get("c23"), f"{gate.identifier}.c23")
    c13 = parse_real(gate.payload.get("c13"), f"{gate.identifier}.c13")
    expected_k = parse_real(gate.payload.get("expected_k"), f"{gate.identifier}.expected_k")
    macrorealist_bound = parse_positive_real(
        gate.payload.get("macrorealist_bound"),
        f"{gate.identifier}.macrorealist_bound",
    )
    expected_violation = parse_bool(gate.payload.get("expected_violation"), f"{gate.identifier}.expected_violation")
    computed_k = c12 + c23 - c13
    if abs(computed_k - expected_k) > tolerance:
        return [
            Issue(
                "temporal_facticity_k_mismatch",
                f"{gate.identifier}: expected K {expected_k:g}, computed {computed_k:g}",
            )
        ]
    computed_violation = computed_k - macrorealist_bound > tolerance
    if computed_violation != expected_violation:
        return [
            Issue(
                "temporal_facticity_violation_mismatch",
                f"{gate.identifier}: computed violation {computed_violation}, expected {expected_violation}",
            )
        ]
    return []


def check_partial_facticity_readout_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    coupling = parse_real(gate.payload.get("coupling"), f"{gate.identifier}.coupling")
    weak_value = parse_real(gate.payload.get("weak_value"), f"{gate.identifier}.weak_value")
    expected_pointer_shift = parse_real(
        gate.payload.get("expected_pointer_shift"),
        f"{gate.identifier}.expected_pointer_shift",
    )
    observed_disturbance = parse_nonnegative_real(
        gate.payload.get("observed_disturbance"),
        f"{gate.identifier}.observed_disturbance",
    )
    max_disturbance = parse_nonnegative_real(gate.payload.get("max_disturbance"), f"{gate.identifier}.max_disturbance")
    distinguishability_gain = parse_nonnegative_real(
        gate.payload.get("distinguishability_gain"),
        f"{gate.identifier}.distinguishability_gain",
    )
    facticity_threshold = parse_positive_real(
        gate.payload.get("facticity_threshold"),
        f"{gate.identifier}.facticity_threshold",
    )
    expected_full_facticity = parse_bool(
        gate.payload.get("expected_full_facticity"),
        f"{gate.identifier}.expected_full_facticity",
    )
    computed_pointer_shift = coupling * weak_value
    if abs(computed_pointer_shift - expected_pointer_shift) > tolerance:
        return [
            Issue(
                "partial_facticity_pointer_shift_mismatch",
                (
                    f"{gate.identifier}: expected pointer shift {expected_pointer_shift:g}, "
                    f"computed {computed_pointer_shift:g}"
                ),
            )
        ]
    if observed_disturbance - max_disturbance > tolerance:
        return [
            Issue(
                "partial_facticity_disturbance_mismatch",
                f"{gate.identifier}: disturbance {observed_disturbance:g} exceeds bound {max_disturbance:g}",
            )
        ]
    computed_full_facticity = distinguishability_gain + tolerance >= facticity_threshold
    if computed_full_facticity != expected_full_facticity:
        return [
            Issue(
                "partial_facticity_status_mismatch",
                f"{gate.identifier}: computed full facticity {computed_full_facticity}, expected {expected_full_facticity}",
            )
        ]
    return []


def check_measurement_facticity_route_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    conditions = require_string_tuple(gate.payload.get("conditions", []), f"{gate.identifier}.conditions")
    if set(conditions) != set(MEASUREMENT_FACTICITY_ROUTE_CONDITIONS):
        return [
            Issue(
                "measurement_facticity_route_conditions_mismatch",
                f"{gate.identifier}: conditions must match the measurement/facticity route set",
            )
        ]

    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if len(samples) < 3:
        raise ManifestError("measurement/facticity route requires at least three samples")
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.samples[{index}].id")
        readout_gain = parse_nonnegative_real(sample.get("readout_gain"), f"{gate.identifier}.samples[{index}].readout_gain")
        facticity_threshold = parse_positive_real(
            sample.get("facticity_threshold"),
            f"{gate.identifier}.samples[{index}].facticity_threshold",
        )
        disturbance = parse_nonnegative_real(sample.get("disturbance"), f"{gate.identifier}.samples[{index}].disturbance")
        max_disturbance = parse_nonnegative_real(sample.get("max_disturbance"), f"{gate.identifier}.samples[{index}].max_disturbance")
        recoverability_loss = parse_nonnegative_real(
            sample.get("recoverability_loss"),
            f"{gate.identifier}.samples[{index}].recoverability_loss",
        )
        recoverability_threshold = parse_positive_real(
            sample.get("recoverability_threshold"),
            f"{gate.identifier}.samples[{index}].recoverability_threshold",
        )
        expected_status = require_string(sample.get("expected_status"), f"{gate.identifier}.samples[{index}].expected_status")
        disturbance_admissible = disturbance <= max_disturbance + tolerance
        full_readout = readout_gain + tolerance >= facticity_threshold
        stable_record = recoverability_loss + tolerance >= recoverability_threshold
        if full_readout and stable_record:
            computed_status = "full_facticity"
        elif disturbance_admissible and readout_gain > tolerance:
            computed_status = "partial_facticity"
        else:
            computed_status = "recoverable_marker"
        if computed_status != expected_status:
            return [
                Issue(
                    "measurement_facticity_route_status_mismatch",
                    f"{gate.identifier}: sample {sample_id} expected {expected_status}, computed {computed_status}",
                )
            ]
    return []


def check_unitary_graph_walk_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    steps = parse_positive_integer(gate.payload.get("steps"), f"{gate.identifier}.steps")
    initial_coin = parse_two_state(gate.payload.get("initial_coin"), f"{gate.identifier}.initial_coin", tolerance)
    expected_distribution = parse_position_distribution(
        gate.payload.get("expected_distribution"),
        f"{gate.identifier}.expected_distribution",
    )
    computed_distribution = hadamard_walk_distribution(steps, initial_coin)
    expected_total = sum(expected_distribution.values())
    if abs(expected_total - 1.0) > tolerance:
        raise ManifestError("expected graph-walk distribution must sum to one")
    for position in sorted(set(expected_distribution) | set(computed_distribution)):
        expected = expected_distribution.get(position, 0.0)
        computed = computed_distribution.get(position, 0.0)
        if abs(computed - expected) > tolerance:
            return [
                Issue(
                    "unitary_graph_walk_distribution_mismatch",
                    f"{gate.identifier}: position {position} expected {expected:g}, computed {computed:g}",
                )
            ]
    return []


def check_distinguishability_geometry_probe_gate(gate: FiniteGate) -> list[Issue]:
    declared_requirements = require_string_tuple(
        gate.payload.get("requirements", []),
        f"{gate.identifier}.requirements",
    )
    if set(declared_requirements) != set(DISTINGUISHABILITY_GEOMETRY_REQUIREMENTS):
        return [
            Issue(
                "distinguishability_geometry_requirements_mismatch",
                f"{gate.identifier}: requirements must match the finite QM geometry requirement set",
            )
        ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if not candidates:
        raise ManifestError("distinguishability geometry probe requires at least one carrier candidate")

    computed_statuses: dict[str, str] = {}
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        capabilities = parse_distinguishability_capabilities(
            candidate.get("capabilities"),
            f"{gate.identifier}.candidates[{index}].capabilities",
        )
        expected_status = require_string(
            candidate.get("expected_status"),
            f"{gate.identifier}.candidates[{index}].expected_status",
        )
        if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.candidates[{index}].expected_status is unknown")
        missing = sorted(set(declared_requirements) - set(capabilities))
        if missing:
            return [
                Issue(
                    "distinguishability_geometry_capabilities_incomplete",
                    f"{gate.identifier}: candidate {candidate_id} missing capabilities: {', '.join(missing)}",
                )
            ]
        computed_status = classify_distinguishability_candidate(capabilities, declared_requirements)
        computed_statuses[candidate_id] = computed_status
        if computed_status != expected_status:
            return [
                Issue(
                    "distinguishability_geometry_candidate_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected {expected_status}, computed {computed_status}",
                )
            ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "distinguishability_geometry_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]
    return []


def check_local_tomography_separator_gate(gate: FiniteGate) -> list[Issue]:
    systems = require_list(gate.payload.get("systems"), f"{gate.identifier}.systems")
    if len(systems) < 2:
        raise ManifestError("local tomography separator requires at least two systems")
    for index, item in enumerate(systems):
        system = require_mapping(item, f"{gate.identifier}.systems[{index}]")
        system_id = require_string(system.get("id"), f"{gate.identifier}.systems[{index}].id")
        local_a = parse_positive_integer(system.get("local_a"), f"{gate.identifier}.systems[{index}].local_a")
        local_b = parse_positive_integer(system.get("local_b"), f"{gate.identifier}.systems[{index}].local_b")
        composite = parse_positive_integer(system.get("composite"), f"{gate.identifier}.systems[{index}].composite")
        expected_locally_tomographic = parse_bool(
            system.get("expected_locally_tomographic"),
            f"{gate.identifier}.systems[{index}].expected_locally_tomographic",
        )
        computed_locally_tomographic = (local_a * local_b) == composite
        if computed_locally_tomographic != expected_locally_tomographic:
            return [
                Issue(
                    "local_tomography_status_mismatch",
                    (
                        f"{gate.identifier}: system {system_id} expected local tomography "
                        f"{expected_locally_tomographic}, computed {computed_locally_tomographic}"
                    ),
                )
            ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if not candidates:
        raise ManifestError("local tomography separator requires at least one candidate")
    computed_statuses: dict[str, str] = {}
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        local_tomography = require_string(
            candidate.get("local_tomography"),
            f"{gate.identifier}.candidates[{index}].local_tomography",
        )
        expected_status = require_string(candidate.get("expected_status"), f"{gate.identifier}.candidates[{index}].expected_status")
        computed_status = classify_local_tomography_candidate(local_tomography)
        computed_statuses[candidate_id] = computed_status
        if computed_status != expected_status:
            return [
                Issue(
                    "local_tomography_candidate_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected {expected_status}, computed {computed_status}",
                )
            ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "local_tomography_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]
    return []


def check_idt_local_tomography_derivation_gate(gate: FiniteGate) -> list[Issue]:
    declared_conditions = require_string_tuple(
        gate.payload.get("idt_conditions", []),
        f"{gate.identifier}.idt_conditions",
    )
    if set(declared_conditions) != set(IDT_LOCAL_TOMOGRAPHY_CONDITIONS):
        return [
            Issue(
                "idt_local_tomography_conditions_mismatch",
                f"{gate.identifier}: IDT conditions must match the local-tomography derivation set",
            )
        ]

    systems = require_list(gate.payload.get("systems"), f"{gate.identifier}.systems")
    if len(systems) < 2:
        raise ManifestError("IDT local tomography derivation requires at least two systems")
    for index, item in enumerate(systems):
        system = require_mapping(item, f"{gate.identifier}.systems[{index}]")
        system_id = require_string(system.get("id"), f"{gate.identifier}.systems[{index}].id")
        local_a = parse_positive_integer(system.get("local_a"), f"{gate.identifier}.systems[{index}].local_a")
        local_b = parse_positive_integer(system.get("local_b"), f"{gate.identifier}.systems[{index}].local_b")
        composite = parse_positive_integer(system.get("composite"), f"{gate.identifier}.systems[{index}].composite")
        declared_joint_only = parse_nonnegative_integer(
            system.get("joint_only_degrees"),
            f"{gate.identifier}.systems[{index}].joint_only_degrees",
        )
        expected_product_dimension = parse_positive_integer(
            system.get("expected_product_dimension"),
            f"{gate.identifier}.systems[{index}].expected_product_dimension",
        )
        expected_locally_tomographic = parse_bool(
            system.get("expected_locally_tomographic"),
            f"{gate.identifier}.systems[{index}].expected_locally_tomographic",
        )
        expected_idt_admissible = parse_bool(
            system.get("expected_idt_admissible"),
            f"{gate.identifier}.systems[{index}].expected_idt_admissible",
        )

        computed_product_dimension = local_a * local_b
        if computed_product_dimension != expected_product_dimension:
            return [
                Issue(
                    "idt_local_tomography_product_dimension_mismatch",
                    (
                        f"{gate.identifier}: system {system_id} expected product dimension "
                        f"{expected_product_dimension}, computed {computed_product_dimension}"
                    ),
                )
            ]
        computed_joint_only = composite - computed_product_dimension
        if computed_joint_only < 0:
            return [
                Issue(
                    "idt_local_tomography_composite_below_product",
                    (
                        f"{gate.identifier}: system {system_id} has composite dimension {composite} below "
                        f"product readout dimension {computed_product_dimension}"
                    ),
                )
            ]
        if computed_joint_only != declared_joint_only:
            return [
                Issue(
                    "idt_local_tomography_joint_only_mismatch",
                    (
                        f"{gate.identifier}: system {system_id} expected joint-only degrees "
                        f"{declared_joint_only}, computed {computed_joint_only}"
                    ),
                )
            ]

        computed_locally_tomographic = computed_joint_only == 0
        if computed_locally_tomographic != expected_locally_tomographic:
            return [
                Issue(
                    "idt_local_tomography_status_mismatch",
                    (
                        f"{gate.identifier}: system {system_id} expected local tomography "
                        f"{expected_locally_tomographic}, computed {computed_locally_tomographic}"
                    ),
                )
            ]

        computed_idt_admissible = computed_locally_tomographic
        if computed_idt_admissible != expected_idt_admissible:
            return [
                Issue(
                    "idt_local_tomography_admissibility_mismatch",
                    (
                        f"{gate.identifier}: system {system_id} expected IDT admissibility "
                        f"{expected_idt_admissible}, computed {computed_idt_admissible}"
                    ),
                )
            ]
    return []


def check_context_product_exhaustion_gate(gate: FiniteGate) -> list[Issue]:
    primitives = require_string_tuple(gate.payload.get("idt_primitives", []), f"{gate.identifier}.idt_primitives")
    if set(primitives) != set(CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES):
        return [
            Issue(
                "context_product_exhaustion_primitives_mismatch",
                f"{gate.identifier}: IDT primitives must match the context-product exhaustion set",
            )
        ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if len(candidates) < 2:
        raise ManifestError("context-product exhaustion requires at least two candidates")

    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        left_contexts = require_string_tuple(
            candidate.get("left_contexts"),
            f"{gate.identifier}.candidates[{index}].left_contexts",
        )
        right_contexts = require_string_tuple(
            candidate.get("right_contexts"),
            f"{gate.identifier}.candidates[{index}].right_contexts",
        )
        product_contexts = require_list(
            candidate.get("product_contexts"),
            f"{gate.identifier}.candidates[{index}].product_contexts",
        )
        expected_context_pairs = {(left, right) for left in left_contexts for right in right_contexts}
        declared_context_pairs: dict[tuple[str, str], str] = {}
        declared_context_ids: set[str] = set()
        for product_index, raw_product in enumerate(product_contexts):
            product = require_mapping(raw_product, f"{gate.identifier}.candidates[{index}].product_contexts[{product_index}]")
            product_id = require_string(product.get("id"), f"{gate.identifier}.candidates[{index}].product_contexts[{product_index}].id")
            left = require_string(product.get("left"), f"{gate.identifier}.candidates[{index}].product_contexts[{product_index}].left")
            right = require_string(product.get("right"), f"{gate.identifier}.candidates[{index}].product_contexts[{product_index}].right")
            pair = (left, right)
            if product_id in declared_context_ids:
                return [
                    Issue(
                        "context_product_exhaustion_duplicate_context",
                        f"{gate.identifier}: candidate {candidate_id} repeats product context {product_id}",
                    )
                ]
            if pair in declared_context_pairs:
                return [
                    Issue(
                        "context_product_exhaustion_duplicate_pair",
                        f"{gate.identifier}: candidate {candidate_id} repeats product pair {left}/{right}",
                    )
                ]
            declared_context_ids.add(product_id)
            declared_context_pairs[pair] = product_id

        if set(declared_context_pairs) != expected_context_pairs:
            return [
                Issue(
                    "context_product_exhaustion_context_closure_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} does not close all product readout contexts",
                )
            ]

        invariants = require_list(candidate.get("stable_invariants"), f"{gate.identifier}.candidates[{index}].stable_invariants")
        if not invariants:
            raise ManifestError("context-product exhaustion candidate requires at least one stable invariant")

        exhausted_invariants = 0
        for invariant_index, raw_invariant in enumerate(invariants):
            invariant = require_mapping(raw_invariant, f"{gate.identifier}.candidates[{index}].stable_invariants[{invariant_index}]")
            invariant_id = require_string(
                invariant.get("id"),
                f"{gate.identifier}.candidates[{index}].stable_invariants[{invariant_index}].id",
            )
            witness_contexts = require_string_tuple(
                invariant.get("witness_contexts"),
                f"{gate.identifier}.candidates[{index}].stable_invariants[{invariant_index}].witness_contexts",
            )
            expected_exhausted = parse_bool(
                invariant.get("expected_exhausted"),
                f"{gate.identifier}.candidates[{index}].stable_invariants[{invariant_index}].expected_exhausted",
            )
            unknown_witnesses = sorted(set(witness_contexts) - declared_context_ids)
            if unknown_witnesses:
                return [
                    Issue(
                        "context_product_exhaustion_unknown_witness",
                        (
                            f"{gate.identifier}: candidate {candidate_id} invariant {invariant_id} "
                            f"references unknown witness contexts: {', '.join(unknown_witnesses)}"
                        ),
                    )
                ]
            computed_exhausted = bool(witness_contexts)
            if computed_exhausted:
                exhausted_invariants += 1
            if computed_exhausted != expected_exhausted:
                return [
                    Issue(
                        "context_product_exhaustion_invariant_mismatch",
                        (
                            f"{gate.identifier}: candidate {candidate_id} invariant {invariant_id} expected "
                            f"exhausted={expected_exhausted}, computed {computed_exhausted}"
                        ),
                    )
                ]

        expected_exhausted = parse_bool(
            candidate.get("expected_context_product_exhausted"),
            f"{gate.identifier}.candidates[{index}].expected_context_product_exhausted",
        )
        expected_admissible = parse_bool(
            candidate.get("expected_idt_admissible"),
            f"{gate.identifier}.candidates[{index}].expected_idt_admissible",
        )
        computed_exhausted = exhausted_invariants == len(invariants)
        if computed_exhausted != expected_exhausted:
            return [
                Issue(
                    "context_product_exhaustion_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected exhausted={expected_exhausted}, computed {computed_exhausted}",
                )
            ]
        computed_admissible = computed_exhausted
        if computed_admissible != expected_admissible:
            return [
                Issue(
                    "context_product_exhaustion_admissibility_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected IDT admissibility {expected_admissible}, computed {computed_admissible}",
                )
            ]
    return []


def check_rebit_hidden_joint_invariant_separator_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    local_a = parse_positive_integer(gate.payload.get("local_a"), f"{gate.identifier}.local_a")
    local_b = parse_positive_integer(gate.payload.get("local_b"), f"{gate.identifier}.local_b")
    composite = parse_positive_integer(gate.payload.get("composite"), f"{gate.identifier}.composite")
    expected_product_dimension = parse_positive_integer(
        gate.payload.get("expected_product_dimension"),
        f"{gate.identifier}.expected_product_dimension",
    )
    expected_joint_only_degrees = parse_nonnegative_integer(
        gate.payload.get("expected_joint_only_degrees"),
        f"{gate.identifier}.expected_joint_only_degrees",
    )
    hidden_invariant = require_string(gate.payload.get("hidden_invariant"), f"{gate.identifier}.hidden_invariant")
    if hidden_invariant != "Y_tensor_Y":
        return [
            Issue(
                "rebit_hidden_joint_invariant_name_mismatch",
                f"{gate.identifier}: hidden invariant must be Y_tensor_Y",
            )
        ]

    computed_product_dimension = local_a * local_b
    if computed_product_dimension != expected_product_dimension:
        return [
            Issue(
                "rebit_hidden_joint_invariant_product_dimension_mismatch",
                f"{gate.identifier}: expected product dimension {expected_product_dimension}, computed {computed_product_dimension}",
            )
        ]

    computed_joint_only_degrees = composite - computed_product_dimension
    if computed_joint_only_degrees != expected_joint_only_degrees:
        return [
            Issue(
                "rebit_hidden_joint_invariant_joint_only_mismatch",
                f"{gate.identifier}: expected joint-only degrees {expected_joint_only_degrees}, computed {computed_joint_only_degrees}",
            )
        ]

    epsilon = parse_unit_interval(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    expected_product_indistinguishable = parse_bool(
        gate.payload.get("expected_product_indistinguishable"),
        f"{gate.identifier}.expected_product_indistinguishable",
    )
    expected_global_distinguishable = parse_bool(
        gate.payload.get("expected_global_distinguishable"),
        f"{gate.identifier}.expected_global_distinguishable",
    )
    expected_status = require_string(gate.payload.get("expected_status"), f"{gate.identifier}.expected_status")

    pauli_i = [[1.0 + 0.0j, 0.0j], [0.0j, 1.0 + 0.0j]]
    pauli_x = [[0.0j, 1.0 + 0.0j], [1.0 + 0.0j, 0.0j]]
    pauli_y = [[0.0j, -1.0j], [1.0j, 0.0j]]
    pauli_z = [[1.0 + 0.0j, 0.0j], [0.0j, -1.0 + 0.0j]]
    local_basis = {
        "I": pauli_i,
        "X": pauli_x,
        "Z": pauli_z,
    }
    basis_labels = require_string_tuple(gate.payload.get("local_basis"), f"{gate.identifier}.local_basis")
    if set(basis_labels) != set(local_basis):
        return [
            Issue(
                "rebit_hidden_joint_invariant_basis_mismatch",
                f"{gate.identifier}: local basis must be I, X, Z",
            )
        ]

    yy = kronecker_product(pauli_y, pauli_y)
    base_density = scalar_multiply_matrix(0.25 + 0.0j, kronecker_product(pauli_i, pauli_i))
    rho_plus = matrix_add(base_density, scalar_multiply_matrix(epsilon / 4.0, yy))
    rho_minus = matrix_add(base_density, scalar_multiply_matrix(-epsilon / 4.0, yy))
    psd_issues = matrix_psd_issues(f"{gate.identifier}.rho_plus", rho_plus, tolerance)
    psd_issues.extend(matrix_psd_issues(f"{gate.identifier}.rho_minus", rho_minus, tolerance))
    if psd_issues:
        return psd_issues

    product_indistinguishable = True
    delta = matrix_add(rho_plus, scalar_multiply_matrix(-1.0 + 0.0j, rho_minus))
    for left_label in basis_labels:
        for right_label in basis_labels:
            product_observable = kronecker_product(local_basis[left_label], local_basis[right_label])
            if abs(complex_matrix_trace(matrix_multiply(product_observable, delta))) > tolerance:
                product_indistinguishable = False
                break
        if not product_indistinguishable:
            break
    if product_indistinguishable != expected_product_indistinguishable:
        return [
            Issue(
                "rebit_hidden_joint_invariant_product_readout_mismatch",
                f"{gate.identifier}: expected product indistinguishability {expected_product_indistinguishable}",
            )
        ]

    plus_global = complex_matrix_trace(matrix_multiply(rho_plus, yy)).real
    minus_global = complex_matrix_trace(matrix_multiply(rho_minus, yy)).real
    global_distinguishable = abs(plus_global - epsilon) <= tolerance and abs(minus_global + epsilon) <= tolerance
    if global_distinguishable != expected_global_distinguishable:
        return [
            Issue(
                "rebit_hidden_joint_invariant_global_readout_mismatch",
                f"{gate.identifier}: expected global distinguishability {expected_global_distinguishable}",
            )
        ]

    computed_status = "rejected_under_context_product_exhaustion" if product_indistinguishable and global_distinguishable else "survives"
    if computed_status != expected_status:
        return [
            Issue(
                "rebit_hidden_joint_invariant_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_context_product_local_tomography_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "context_product_exhaustion_implies_local_tomography":
        return [
            Issue(
                "context_product_local_tomography_theorem_target_mismatch",
                f"{gate.identifier}: target card must be context_product_exhaustion_implies_local_tomography",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "context_product_local_tomography_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional local-tomography theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "context_product_local_tomography_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match local tomography and parameter-product basis",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    required_evidence = {
        "context_product_exhaustion_demo",
        "idt_local_tomography_derivation_demo",
        "local_tomography_separator_demo",
        "real_hilbert_composite_hidden_joint_invariant_demo",
    }
    if set(evidence_refs) != required_evidence:
        return [
            Issue(
                "context_product_local_tomography_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link context-product, local tomography, and rebit separator gates",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(CONTEXT_PRODUCT_LOCAL_TOMOGRAPHY_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "context_product_local_tomography_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_status = "conditional_proof"
    if expected_status != computed_status:
        return [
            Issue(
                "context_product_local_tomography_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_purification_filtering_recoverable_support_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "purification_filtering_implies_recoverable_support_update":
        return [
            Issue(
                "purification_filtering_theorem_target_mismatch",
                f"{gate.identifier}: target card must be purification_filtering_implies_recoverable_support_update",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(PURIFICATION_FILTERING_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "purification_filtering_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional purification/filtering theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(PURIFICATION_FILTERING_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "purification_filtering_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match recoverable extension and support-update claims",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    if set(evidence_refs) != {"idt_purification_filtering_demo"}:
        return [
            Issue(
                "purification_filtering_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link the purification/filtering finite gate",
            )
        ]

    rejected_cases = require_string_tuple(gate.payload.get("rejected_cases", []), f"{gate.identifier}.rejected_cases")
    if set(rejected_cases) != {"insufficient_environment_extension", "zero_support_filter"}:
        return [
            Issue(
                "purification_filtering_theorem_rejected_cases_mismatch",
                f"{gate.identifier}: rejected cases must include insufficient extension and zero-support filter",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(PURIFICATION_FILTERING_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "purification_filtering_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_status = "conditional_proof"
    if expected_status != computed_status:
        return [
            Issue(
                "purification_filtering_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_reversible_filter_closure_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "recoverable_support_update_implies_reversible_filter_closure":
        return [
            Issue(
                "reversible_filter_closure_theorem_target_mismatch",
                f"{gate.identifier}: target card must be recoverable_support_update_implies_reversible_filter_closure",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(REVERSIBLE_FILTER_CLOSURE_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "reversible_filter_closure_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional reversible filter closure theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(REVERSIBLE_FILTER_CLOSURE_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "reversible_filter_closure_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match reversible closure and rejected filter witnesses",
            )
        ]

    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if len(samples) < 3:
        raise ManifestError(f"{gate.identifier}: samples must include reversible, zero-support, and nonbijective witnesses")
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    accepted = 0
    rejected = 0
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.samples[{index}].id")
        prior = parse_nonnegative_real_list(sample.get("prior"), f"{gate.identifier}.samples[{index}].prior")
        filter_indices = parse_index_tuple(sample.get("filter_indices"), f"{gate.identifier}.samples[{index}].filter_indices")
        image_indices = parse_index_tuple(sample.get("reversible_image_indices"), f"{gate.identifier}.samples[{index}].reversible_image_indices")
        expected_acceptance = parse_unit_interval(
            sample.get("expected_acceptance_probability"),
            f"{gate.identifier}.samples[{index}].expected_acceptance_probability",
        )
        expected_status = require_string(sample.get("expected_status"), f"{gate.identifier}.samples[{index}].expected_status")
        if expected_status not in {"survives", "rejected"}:
            raise ManifestError(f"{gate.identifier}: sample {sample_id} expected_status is unknown")
        if abs(sum(prior) - 1.0) > tolerance:
            raise ManifestError(f"{gate.identifier}: sample {sample_id} prior must be normalized")
        if len(filter_indices) != len(image_indices):
            raise ManifestError(f"{gate.identifier}: sample {sample_id} filter/image size mismatch")
        if any(index_value >= len(prior) for index_value in filter_indices):
            raise ManifestError(f"{gate.identifier}: sample {sample_id} filter index out of range")
        if any(index_value >= len(prior) for index_value in image_indices):
            raise ManifestError(f"{gate.identifier}: sample {sample_id} image index out of range")
        acceptance = sum(prior[index_value] for index_value in filter_indices)
        if abs(acceptance - expected_acceptance) > tolerance:
            return [
                Issue(
                    "reversible_filter_closure_acceptance_mismatch",
                    f"{gate.identifier}: sample {sample_id} expected acceptance {expected_acceptance:g}, computed {acceptance:g}",
                )
            ]
        nonzero_support = acceptance > tolerance
        support_unique = len(set(filter_indices)) == len(filter_indices)
        image_unique = len(set(image_indices)) == len(image_indices)
        support_preserved = set(filter_indices) == set(image_indices)
        computed_status = "survives" if nonzero_support and support_unique and image_unique and support_preserved else "rejected"
        if computed_status != expected_status:
            return [
                Issue(
                    "reversible_filter_closure_status_mismatch",
                    f"{gate.identifier}: sample {sample_id} expected {expected_status}, computed {computed_status}",
                )
            ]
        if computed_status == "survives":
            accepted += 1
        if computed_status == "rejected":
            rejected += 1
    if accepted == 0 or rejected < 2:
        return [
            Issue(
                "reversible_filter_closure_separator_incomplete",
                f"{gate.identifier}: theorem gate must include one survivor and rejected zero-support/nonbijective samples",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    required_evidence = {
        "purification_filtering_implies_recoverable_support_update",
        "purification_filtering_recoverable_support_theorem_demo",
        "idt_purification_filtering_demo",
    }
    if set(evidence_refs) != required_evidence:
        return [
            Issue(
                "reversible_filter_closure_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link recoverable support theorem and purification/filtering gate",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(REVERSIBLE_FILTER_CLOSURE_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "reversible_filter_closure_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_theorem_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_theorem_status = "conditional_proof"
    if expected_theorem_status != computed_theorem_status:
        return [
            Issue(
                "reversible_filter_closure_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_theorem_status}, computed {computed_theorem_status}",
            )
        ]
    return []


def check_bounded_correlation_screen_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "bounded_correlation_screen_rejects_superquantum_boxes":
        return [
            Issue(
                "bounded_correlation_theorem_target_mismatch",
                f"{gate.identifier}: target card must be bounded_correlation_screen_rejects_superquantum_boxes",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(BOUNDED_CORRELATION_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "bounded_correlation_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional bounded-correlation theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(BOUNDED_CORRELATION_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "bounded_correlation_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match Tsirelson screen and superquantum rejection claims",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    if set(evidence_refs) != {"idt_bounded_correlation_demo", "gpt_principle_separator_demo"}:
        return [
            Issue(
                "bounded_correlation_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link bounded-correlation and GPT separator gates",
            )
        ]

    surviving_cases = require_string_tuple(gate.payload.get("surviving_cases", []), f"{gate.identifier}.surviving_cases")
    if set(surviving_cases) != {"classical_edge", "tsirelson_edge"}:
        return [
            Issue(
                "bounded_correlation_theorem_surviving_cases_mismatch",
                f"{gate.identifier}: surviving cases must include classical and Tsirelson edges",
            )
        ]

    rejected_cases = require_string_tuple(gate.payload.get("rejected_cases", []), f"{gate.identifier}.rejected_cases")
    if set(rejected_cases) != {"pr_box_like", "boxworld_like_gpt"}:
        return [
            Issue(
                "bounded_correlation_theorem_rejected_cases_mismatch",
                f"{gate.identifier}: rejected cases must include PR-box-like and boxworld-like cases",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(BOUNDED_CORRELATION_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "bounded_correlation_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_status = "conditional_proof"
    if expected_status != computed_status:
        return [
            Issue(
                "bounded_correlation_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_noncomplex_jordan_separator_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "noncomplex_jordan_separator_rejects_noncomplex_samples":
        return [
            Issue(
                "noncomplex_jordan_theorem_target_mismatch",
                f"{gate.identifier}: target card must be noncomplex_jordan_separator_rejects_noncomplex_samples",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(NONCOMPLEX_JORDAN_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "noncomplex_jordan_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional non-complex Jordan theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(NONCOMPLEX_JORDAN_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "noncomplex_jordan_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match non-complex sample rejection claims",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    if set(evidence_refs) != {"noncomplex_jordan_separator_demo"}:
        return [
            Issue(
                "noncomplex_jordan_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link the non-complex Jordan separator gate",
            )
        ]

    rejected_cases = require_string_tuple(gate.payload.get("rejected_cases", []), f"{gate.identifier}.rejected_cases")
    if set(rejected_cases) != {"real_hilbert_like", "quaternionic_hilbert_like", "exceptional_jordan_like"}:
        return [
            Issue(
                "noncomplex_jordan_theorem_rejected_cases_mismatch",
                f"{gate.identifier}: rejected cases must include real, quaternionic, and exceptional Jordan-like samples",
            )
        ]

    remaining_underdetermined = require_string_tuple(
        gate.payload.get("remaining_underdetermined_candidates", []),
        f"{gate.identifier}.remaining_underdetermined_candidates",
    )
    if set(remaining_underdetermined) != {"generic_gpt_cone"}:
        return [
            Issue(
                "noncomplex_jordan_theorem_underdetermined_cases_mismatch",
                f"{gate.identifier}: remaining underdetermination must include generic_gpt_cone",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(NONCOMPLEX_JORDAN_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "noncomplex_jordan_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_status = "conditional_proof"
    if expected_status != computed_status:
        return [
            Issue(
                "noncomplex_jordan_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_generic_gpt_closure_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "generic_gpt_closure_rejects_unconstrained_cone":
        return [
            Issue(
                "generic_gpt_theorem_target_mismatch",
                f"{gate.identifier}: target card must be generic_gpt_closure_rejects_unconstrained_cone",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(GENERIC_GPT_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "generic_gpt_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional generic-GPT theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(GENERIC_GPT_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "generic_gpt_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must reject only the unconstrained cone and retain underdetermination",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    if set(evidence_refs) != {"generic_gpt_closure_separator_demo", "carrier_selection_frontier_demo"}:
        return [
            Issue(
                "generic_gpt_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link generic GPT separator and carrier frontier gates",
            )
        ]

    rejected_cases = require_string_tuple(gate.payload.get("rejected_cases", []), f"{gate.identifier}.rejected_cases")
    if set(rejected_cases) != {"unconstrained_generic_gpt_cone"}:
        return [
            Issue(
                "generic_gpt_theorem_rejected_cases_mismatch",
                f"{gate.identifier}: rejected cases must include only the unconstrained generic GPT cone",
            )
        ]

    remaining_underdetermined = require_string_tuple(
        gate.payload.get("remaining_underdetermined_candidates", []),
        f"{gate.identifier}.remaining_underdetermined_candidates",
    )
    if set(remaining_underdetermined) != {"generic_gpt_cone"}:
        return [
            Issue(
                "generic_gpt_theorem_underdetermined_cases_mismatch",
                f"{gate.identifier}: remaining underdetermination must include only generic_gpt_cone",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "generic_gpt_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    computed_status = "conditional_proof"
    if expected_status != computed_status:
        return [
            Issue(
                "generic_gpt_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_broader_generic_gpt_cone_frontier_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "finite_route_coverage_reduces_broader_generic_gpt_cone":
        return [
            Issue(
                "broader_generic_gpt_frontier_target_mismatch",
                f"{gate.identifier}: target card must be finite_route_coverage_reduces_broader_generic_gpt_cone",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(BROADER_GENERIC_GPT_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "broader_generic_gpt_frontier_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the broader generic-GPT theorem boundary",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(BROADER_GENERIC_GPT_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "broader_generic_gpt_frontier_conclusions_mismatch",
                f"{gate.identifier}: conclusions must reduce only finite route-covered broader GPT slices",
            )
        ]

    slices = require_list(gate.payload.get("slices"), f"{gate.identifier}.slices")
    if len(slices) != len(BROADER_GENERIC_GPT_FRONTIER_SLICES):
        raise ManifestError(f"{gate.identifier}: slices must cover every broader generic-GPT frontier slice")
    status_by_slice: dict[str, str] = {}
    for index, item in enumerate(slices):
        frontier_slice = require_mapping(item, f"{gate.identifier}.slices[{index}]")
        slice_id = require_string(frontier_slice.get("id"), f"{gate.identifier}.slices[{index}].id")
        status = require_string(frontier_slice.get("status"), f"{gate.identifier}.slices[{index}].status")
        evidence_refs = require_string_tuple(
            frontier_slice.get("evidence_refs", []),
            f"{gate.identifier}.slices[{index}].evidence_refs",
        )
        residual_gap = require_string(
            frontier_slice.get("residual_gap", ""),
            f"{gate.identifier}.slices[{index}].residual_gap",
        )
        if slice_id not in BROADER_GENERIC_GPT_FRONTIER_SLICES:
            return [
                Issue(
                    "broader_generic_gpt_frontier_unknown_slice",
                    f"{gate.identifier}: unknown broader generic-GPT slice {slice_id}",
                )
            ]
        if status not in BROADER_GENERIC_GPT_FRONTIER_STATUSES:
            raise ManifestError(f"{gate.identifier}: slice {slice_id} has unknown status {status!r}")
        if slice_id in status_by_slice:
            return [
                Issue(
                    "broader_generic_gpt_frontier_duplicate_slice",
                    f"{gate.identifier}: duplicate broader generic-GPT slice {slice_id}",
                )
            ]
        if not evidence_refs:
            return [
                Issue(
                    "broader_generic_gpt_frontier_evidence_missing",
                    f"{gate.identifier}: slice {slice_id} must cite evidence",
                )
            ]
        if status == "underdetermined" and not residual_gap:
            return [
                Issue(
                    "broader_generic_gpt_frontier_residual_gap_missing",
                    f"{gate.identifier}: underdetermined slice {slice_id} must declare a residual gap",
                )
            ]
        if status != "underdetermined" and residual_gap:
            return [
                Issue(
                    "broader_generic_gpt_frontier_residual_gap_on_closed_slice",
                    f"{gate.identifier}: closed slice {slice_id} must not declare a residual gap",
                )
            ]
        status_by_slice[slice_id] = status

    missing = sorted(set(BROADER_GENERIC_GPT_FRONTIER_SLICES) - set(status_by_slice))
    if missing:
        return [
            Issue(
                "broader_generic_gpt_frontier_slice_missing",
                f"{gate.identifier}: missing broader generic-GPT slices: {', '.join(missing)}",
            )
        ]
    expected_status = require_string(gate.payload.get("expected_frontier_status"), f"{gate.identifier}.expected_frontier_status")
    if expected_status not in {"reduced_to_nonfinite_residual", "closed"}:
        raise ManifestError(f"{gate.identifier}.expected_frontier_status is unknown")
    computed_status = (
        "reduced_to_nonfinite_residual"
        if any(status == "underdetermined" for status in status_by_slice.values())
        else "closed"
    )
    if computed_status != expected_status:
        return [
            Issue(
                "broader_generic_gpt_frontier_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(BROADER_GENERIC_GPT_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "broader_generic_gpt_frontier_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]
    return []


def check_nonfinite_gpt_residual_compactness_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "uniform_route_witness_compactness_closes_nonfinite_gpt_residual":
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_target_mismatch",
                f"{gate.identifier}: target card must be uniform_route_witness_compactness_closes_nonfinite_gpt_residual",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(NONFINITE_GPT_RESIDUAL_COMPACTNESS_ASSUMPTIONS):
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the residual compactness theorem boundary",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(NONFINITE_GPT_RESIDUAL_COMPACTNESS_CONCLUSIONS):
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_conclusions_mismatch",
                f"{gate.identifier}: conclusions must reduce only nonfinite residuals covered by the compactness assumptions",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    if not evidence_refs:
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_evidence_missing",
                f"{gate.identifier}: compactness theorem gate must cite evidence",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(NONFINITE_GPT_RESIDUAL_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the residual boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_theorem_status"), f"{gate.identifier}.expected_theorem_status")
    if expected_status != "conditional_proof":
        return [
            Issue(
                "nonfinite_gpt_residual_compactness_status_mismatch",
                f"{gate.identifier}: compactness theorem must remain conditional_proof",
            )
        ]
    return []


def check_nonfinite_gpt_residual_frontier_gate(gate: FiniteGate) -> list[Issue]:
    target_class = require_string(gate.payload.get("target_class"), f"{gate.identifier}.target_class")
    if target_class != "nonfinite_unwitnessed_residual":
        return [
            Issue(
                "nonfinite_gpt_residual_frontier_target_mismatch",
                f"{gate.identifier}: target class must be nonfinite_unwitnessed_residual",
            )
        ]

    obligations = require_list(gate.payload.get("obligations"), f"{gate.identifier}.obligations")
    if len(obligations) != len(NONFINITE_GPT_RESIDUAL_FRONTIER_OBLIGATIONS):
        raise ManifestError(f"{gate.identifier}: obligations must cover every nonfinite residual frontier obligation")

    status_by_obligation: dict[str, str] = {}
    for index, item in enumerate(obligations):
        obligation = require_mapping(item, f"{gate.identifier}.obligations[{index}]")
        obligation_id = require_string(obligation.get("id"), f"{gate.identifier}.obligations[{index}].id")
        status = require_string(obligation.get("status"), f"{gate.identifier}.obligations[{index}].status")
        evidence_refs = require_string_tuple(
            obligation.get("evidence_refs", []),
            f"{gate.identifier}.obligations[{index}].evidence_refs",
        )
        open_gap = require_string(obligation.get("open_gap", ""), f"{gate.identifier}.obligations[{index}].open_gap")
        if obligation_id not in NONFINITE_GPT_RESIDUAL_FRONTIER_OBLIGATIONS:
            return [
                Issue(
                    "nonfinite_gpt_residual_frontier_unknown_obligation",
                    f"{gate.identifier}: unknown residual obligation {obligation_id}",
                )
            ]
        if status not in NONFINITE_GPT_RESIDUAL_FRONTIER_STATUSES:
            raise ManifestError(f"{gate.identifier}: obligation {obligation_id} has unknown status {status!r}")
        if obligation_id in status_by_obligation:
            return [
                Issue(
                    "nonfinite_gpt_residual_frontier_duplicate_obligation",
                    f"{gate.identifier}: duplicate residual obligation {obligation_id}",
                )
            ]
        if not evidence_refs:
            return [
                Issue(
                    "nonfinite_gpt_residual_frontier_evidence_missing",
                    f"{gate.identifier}: obligation {obligation_id} must cite evidence",
                )
            ]
        if status != "formal_proof" and not open_gap:
            return [
                Issue(
                    "nonfinite_gpt_residual_frontier_gap_missing",
                    f"{gate.identifier}: non-formal obligation {obligation_id} must declare an open gap",
                )
            ]
        if status == "formal_proof" and open_gap:
            return [
                Issue(
                    "nonfinite_gpt_residual_frontier_gap_on_closed_obligation",
                    f"{gate.identifier}: formal obligation {obligation_id} must not declare an open gap",
                )
            ]
        status_by_obligation[obligation_id] = status

    missing = sorted(set(NONFINITE_GPT_RESIDUAL_FRONTIER_OBLIGATIONS) - set(status_by_obligation))
    if missing:
        return [
            Issue(
                "nonfinite_gpt_residual_frontier_obligation_missing",
                f"{gate.identifier}: missing residual obligations: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_residual_status"), f"{gate.identifier}.expected_residual_status")
    if expected_status not in {"open", "closed"}:
        raise ManifestError(f"{gate.identifier}: expected_residual_status is unknown")
    computed_status = (
        "closed"
        if all(status == "formal_proof" for status in status_by_obligation.values())
        else "open"
    )
    if computed_status != expected_status:
        return [
            Issue(
                "nonfinite_gpt_residual_frontier_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_no_emergent_joint_only_invariant_route_gate(gate: FiniteGate) -> list[Issue]:
    target_obligation = require_string(gate.payload.get("target_obligation"), f"{gate.identifier}.target_obligation")
    if target_obligation != "idt_derivation_of_no_emergent_joint_only_invariants":
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_target_mismatch",
                f"{gate.identifier}: target obligation must be idt_derivation_of_no_emergent_joint_only_invariants",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(NO_EMERGENT_JOINT_ONLY_INVARIANT_ASSUMPTIONS):
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the no-emergent joint-only invariant boundary",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(NO_EMERGENT_JOINT_ONLY_INVARIANT_CONCLUSIONS):
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_conclusions_mismatch",
                f"{gate.identifier}: conclusions must only reject unwitnessed joint-only invariants",
            )
        ]

    separator_refs = require_string_tuple(gate.payload.get("separator_refs", []), f"{gate.identifier}.separator_refs")
    required_separator_refs = {
        "context_product_exhaustion_implies_local_tomography",
        "context_product_local_tomography_theorem_demo",
        "context_product_exhaustion_demo",
    }
    if set(separator_refs) != required_separator_refs:
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_separator_refs_mismatch",
                f"{gate.identifier}: separator refs must ground context-product exhaustion and local tomography",
            )
        ]

    rejected_witness_refs = require_string_tuple(
        gate.payload.get("rejected_witness_refs", []),
        f"{gate.identifier}.rejected_witness_refs",
    )
    required_rejected_witness_refs = {
        "real_hilbert_composite_hidden_joint_invariant",
        "real_hilbert_composite_hidden_joint_invariant_demo",
    }
    if set(rejected_witness_refs) != required_rejected_witness_refs:
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_rejected_witness_refs_mismatch",
                f"{gate.identifier}: rejected witness refs must include the rebit hidden joint invariant separator",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(NO_EMERGENT_JOINT_ONLY_INVARIANT_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the residual boundary",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_obligation_status"), f"{gate.identifier}.expected_obligation_status")
    if expected_status != "conditional_proof":
        return [
            Issue(
                "no_emergent_joint_only_invariant_route_status_mismatch",
                f"{gate.identifier}: no-emergence route must remain conditional_proof",
            )
        ]
    return []


def check_idt_purification_filtering_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    conditions = require_string_tuple(gate.payload.get("idt_conditions", []), f"{gate.identifier}.idt_conditions")
    if set(conditions) != set(IDT_PURIFICATION_FILTERING_CONDITIONS):
        return [
            Issue(
                "idt_purification_filtering_conditions_mismatch",
                f"{gate.identifier}: IDT conditions must match the purification/filtering route set",
            )
        ]

    purification_samples = require_list(gate.payload.get("purification_samples"), f"{gate.identifier}.purification_samples")
    if not purification_samples:
        raise ManifestError("purification/filtering gate requires at least one purification sample")
    for index, item in enumerate(purification_samples):
        sample = require_mapping(item, f"{gate.identifier}.purification_samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.purification_samples[{index}].id")
        amplitudes = parse_vector(sample.get("schmidt_amplitudes"), f"{gate.identifier}.purification_samples[{index}].schmidt_amplitudes")
        expected_marginal = parse_real_list(
            sample.get("expected_marginal"),
            f"{gate.identifier}.purification_samples[{index}].expected_marginal",
        )
        environment_dimension = parse_positive_integer(
            sample.get("environment_dimension"),
            f"{gate.identifier}.purification_samples[{index}].environment_dimension",
        )
        expected_recoverable = parse_bool(
            sample.get("expected_recoverable_extension"),
            f"{gate.identifier}.purification_samples[{index}].expected_recoverable_extension",
        )
        if len(amplitudes) != len(expected_marginal):
            raise ManifestError(f"{gate.identifier}: purification sample {sample_id} amplitude/marginal size mismatch")
        computed_marginal = amplitude_probabilities(amplitudes, tolerance)
        support_size = sum(1 for probability in computed_marginal if probability > tolerance)
        computed_recoverable = environment_dimension >= support_size
        if computed_recoverable != expected_recoverable:
            return [
                Issue(
                    "idt_purification_filtering_recoverability_mismatch",
                    (
                        f"{gate.identifier}: purification sample {sample_id} expected recoverable="
                        f"{expected_recoverable}, computed {computed_recoverable}"
                    ),
                )
            ]
        for marginal_index, probability in enumerate(computed_marginal):
            if abs(probability - expected_marginal[marginal_index]) > tolerance:
                return [
                    Issue(
                        "idt_purification_filtering_marginal_mismatch",
                        (
                            f"{gate.identifier}: purification sample {sample_id} marginal {marginal_index} "
                            f"expected {expected_marginal[marginal_index]:g}, computed {probability:g}"
                        ),
                    )
                ]

    filtering_samples = require_list(gate.payload.get("filtering_samples"), f"{gate.identifier}.filtering_samples")
    if not filtering_samples:
        raise ManifestError("purification/filtering gate requires at least one filtering sample")
    for index, item in enumerate(filtering_samples):
        sample = require_mapping(item, f"{gate.identifier}.filtering_samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.filtering_samples[{index}].id")
        prior = parse_nonnegative_real_list(sample.get("prior"), f"{gate.identifier}.filtering_samples[{index}].prior")
        filter_indices = parse_index_tuple(
            sample.get("filter_indices"),
            f"{gate.identifier}.filtering_samples[{index}].filter_indices",
        )
        expected_acceptance = parse_unit_interval(
            sample.get("expected_acceptance_probability"),
            f"{gate.identifier}.filtering_samples[{index}].expected_acceptance_probability",
        )
        expected_posterior = parse_real_list(
            sample.get("expected_posterior"),
            f"{gate.identifier}.filtering_samples[{index}].expected_posterior",
        )
        expected_filter_admissible = parse_bool(
            sample.get("expected_filter_admissible"),
            f"{gate.identifier}.filtering_samples[{index}].expected_filter_admissible",
        )
        if abs(sum(prior) - 1.0) > tolerance:
            raise ManifestError(f"{gate.identifier}: filtering sample {sample_id} prior must be normalized")
        if len(expected_posterior) != len(filter_indices):
            raise ManifestError(f"{gate.identifier}: filtering sample {sample_id} posterior/filter size mismatch")
        if any(index_value >= len(prior) for index_value in filter_indices):
            raise ManifestError(f"{gate.identifier}: filtering sample {sample_id} filter index out of range")
        acceptance = sum(prior[index_value] for index_value in filter_indices)
        computed_filter_admissible = acceptance > tolerance
        if abs(acceptance - expected_acceptance) > tolerance:
            return [
                Issue(
                    "idt_purification_filtering_acceptance_mismatch",
                    (
                        f"{gate.identifier}: filtering sample {sample_id} expected acceptance "
                        f"{expected_acceptance:g}, computed {acceptance:g}"
                    ),
                )
            ]
        if computed_filter_admissible != expected_filter_admissible:
            return [
                Issue(
                    "idt_purification_filtering_admissibility_mismatch",
                    (
                        f"{gate.identifier}: filtering sample {sample_id} expected admissible="
                        f"{expected_filter_admissible}, computed {computed_filter_admissible}"
                    ),
                )
            ]
        if not computed_filter_admissible:
            continue
        posterior = [prior[index_value] / acceptance for index_value in filter_indices]
        for posterior_index, probability in enumerate(posterior):
            if abs(probability - expected_posterior[posterior_index]) > tolerance:
                return [
                    Issue(
                        "idt_purification_filtering_posterior_mismatch",
                        (
                            f"{gate.identifier}: filtering sample {sample_id} posterior {posterior_index} "
                            f"expected {expected_posterior[posterior_index]:g}, computed {probability:g}"
                        ),
                    )
                ]
    return []


def check_idt_bounded_correlation_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    conditions = require_string_tuple(gate.payload.get("idt_conditions", []), f"{gate.identifier}.idt_conditions")
    if set(conditions) != set(IDT_BOUNDED_CORRELATION_CONDITIONS):
        return [
            Issue(
                "idt_bounded_correlation_conditions_mismatch",
                f"{gate.identifier}: IDT conditions must match the bounded-correlation route set",
            )
        ]

    max_abs_s = parse_positive_real(gate.payload.get("max_abs_s"), f"{gate.identifier}.max_abs_s")
    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if len(samples) < 2:
        raise ManifestError("bounded-correlation gate requires at least two samples")

    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.samples[{index}].id")
        correlations = parse_real_list(sample.get("correlations"), f"{gate.identifier}.samples[{index}].correlations")
        if len(correlations) != 4:
            raise ManifestError(f"{gate.identifier}: sample {sample_id} requires four CHSH correlations")
        for correlation_index, correlation in enumerate(correlations):
            if correlation < -1.0 - tolerance or correlation > 1.0 + tolerance:
                raise ManifestError(f"{gate.identifier}: sample {sample_id} correlation {correlation_index} must be in [-1, 1]")
        expected_abs_s = parse_nonnegative_real(sample.get("expected_abs_s"), f"{gate.identifier}.samples[{index}].expected_abs_s")
        expected_status = require_string(sample.get("expected_status"), f"{gate.identifier}.samples[{index}].expected_status")
        if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.samples[{index}].expected_status is unknown")

        computed_abs_s = abs(correlations[0] + correlations[1] + correlations[2] - correlations[3])
        if abs(computed_abs_s - expected_abs_s) > tolerance:
            return [
                Issue(
                    "idt_bounded_correlation_chsh_mismatch",
                    f"{gate.identifier}: sample {sample_id} expected |S|={expected_abs_s:g}, computed {computed_abs_s:g}",
                )
            ]
        computed_status = "survives" if computed_abs_s <= max_abs_s + tolerance else "rejected"
        if computed_status != expected_status:
            return [
                Issue(
                    "idt_bounded_correlation_status_mismatch",
                    f"{gate.identifier}: sample {sample_id} expected {expected_status}, computed {computed_status}",
                )
            ]
    return []


def check_noncomplex_jordan_separator_gate(gate: FiniteGate) -> list[Issue]:
    conditions = require_string_tuple(gate.payload.get("conditions", []), f"{gate.identifier}.conditions")
    if set(conditions) != set(NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS):
        return [
            Issue(
                "noncomplex_jordan_separator_conditions_mismatch",
                f"{gate.identifier}: conditions must match the noncomplex-Jordan separator set",
            )
        ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if len(candidates) < 2:
        raise ManifestError("noncomplex-Jordan separator requires at least two candidates")

    computed_statuses: dict[str, str] = {}
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        capabilities = parse_gpt_separator_capabilities(
            candidate.get("capabilities"),
            f"{gate.identifier}.candidates[{index}].capabilities",
        )
        expected_status = require_string(candidate.get("expected_status"), f"{gate.identifier}.candidates[{index}].expected_status")
        if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.candidates[{index}].expected_status is unknown")
        missing = sorted(set(conditions) - set(capabilities))
        if missing:
            return [
                Issue(
                    "noncomplex_jordan_separator_capabilities_incomplete",
                    f"{gate.identifier}: candidate {candidate_id} missing capabilities: {', '.join(missing)}",
                )
            ]
        computed_status = classify_gpt_principle_candidate(capabilities, conditions)
        computed_statuses[candidate_id] = computed_status
        if computed_status != expected_status:
            return [
                Issue(
                    "noncomplex_jordan_separator_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected {expected_status}, computed {computed_status}",
                )
            ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "noncomplex_jordan_separator_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]
    return []


def check_generic_gpt_closure_separator_gate(gate: FiniteGate) -> list[Issue]:
    conditions = require_string_tuple(gate.payload.get("conditions", []), f"{gate.identifier}.conditions")
    if set(conditions) != set(GENERIC_GPT_CLOSURE_CONDITIONS):
        return [
            Issue(
                "generic_gpt_closure_conditions_mismatch",
                f"{gate.identifier}: conditions must match the generic-GPT closure set",
            )
        ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if len(candidates) < 2:
        raise ManifestError("generic-GPT closure separator requires at least two candidates")

    computed_statuses: dict[str, str] = {}
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        capabilities = parse_gpt_separator_capabilities(
            candidate.get("capabilities"),
            f"{gate.identifier}.candidates[{index}].capabilities",
        )
        expected_status = require_string(candidate.get("expected_status"), f"{gate.identifier}.candidates[{index}].expected_status")
        if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.candidates[{index}].expected_status is unknown")
        missing = sorted(set(conditions) - set(capabilities))
        if missing:
            return [
                Issue(
                    "generic_gpt_closure_capabilities_incomplete",
                    f"{gate.identifier}: candidate {candidate_id} missing capabilities: {', '.join(missing)}",
                )
            ]
        computed_status = classify_gpt_principle_candidate(capabilities, conditions)
        computed_statuses[candidate_id] = computed_status
        if computed_status != expected_status:
            return [
                Issue(
                    "generic_gpt_closure_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected {expected_status}, computed {computed_status}",
                )
            ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "generic_gpt_closure_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]
    return []


def check_born_quadratic_readout_route_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    conditions = require_string_tuple(gate.payload.get("conditions", []), f"{gate.identifier}.conditions")
    if set(conditions) != set(BORN_READOUT_ROUTE_CONDITIONS):
        return [
            Issue(
                "born_quadratic_route_conditions_mismatch",
                f"{gate.identifier}: conditions must match the Born readout route set",
            )
        ]

    samples = require_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    if not samples:
        raise ManifestError("Born quadratic readout route requires at least one sample")
    for index, item in enumerate(samples):
        sample = require_mapping(item, f"{gate.identifier}.samples[{index}]")
        sample_id = require_string(sample.get("id"), f"{gate.identifier}.samples[{index}].id")
        amplitudes = parse_vector(sample.get("amplitudes"), f"{gate.identifier}.samples[{index}].amplitudes")
        expected_probabilities = parse_real_list(
            sample.get("expected_probabilities"),
            f"{gate.identifier}.samples[{index}].expected_probabilities",
        )
        if len(amplitudes) != len(expected_probabilities):
            raise ManifestError(f"{gate.identifier}: sample {sample_id} amplitude/probability size mismatch")
        born_probabilities = amplitude_probabilities(amplitudes, tolerance)
        for probability_index, probability in enumerate(born_probabilities):
            if abs(probability - expected_probabilities[probability_index]) > tolerance:
                return [
                    Issue(
                        "born_quadratic_route_probability_mismatch",
                        (
                            f"{gate.identifier}: sample {sample_id} probability {probability_index} expected "
                            f"{expected_probabilities[probability_index]:g}, computed {probability:g}"
                        ),
                    )
                ]

        alternatives = require_list(sample.get("candidate_readouts"), f"{gate.identifier}.samples[{index}].candidate_readouts")
        if len(alternatives) < 2:
            raise ManifestError(f"{gate.identifier}: sample {sample_id} requires at least two candidate readouts")
        for alternative_index, raw_alternative in enumerate(alternatives):
            alternative = require_mapping(raw_alternative, f"{gate.identifier}.samples[{index}].candidate_readouts[{alternative_index}]")
            readout_id = require_string(
                alternative.get("id"),
                f"{gate.identifier}.samples[{index}].candidate_readouts[{alternative_index}].id",
            )
            readout_type = require_string(
                alternative.get("type"),
                f"{gate.identifier}.samples[{index}].candidate_readouts[{alternative_index}].type",
            )
            expected_status = require_string(
                alternative.get("expected_status"),
                f"{gate.identifier}.samples[{index}].candidate_readouts[{alternative_index}].expected_status",
            )
            if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
                raise ManifestError(f"{gate.identifier}: readout {readout_id} expected_status is unknown")
            if readout_type == "quadratic_modulus":
                candidate_probabilities = born_probabilities
            elif readout_type == "linear_modulus":
                magnitudes = [abs(amplitude) for amplitude in amplitudes]
                total = sum(magnitudes)
                if total <= tolerance:
                    raise ManifestError(f"{gate.identifier}: readout {readout_id} cannot normalize zero magnitudes")
                candidate_probabilities = [magnitude / total for magnitude in magnitudes]
            else:
                raise ManifestError(f"{gate.identifier}: readout {readout_id} has unknown type {readout_type!r}")
            max_deviation = max(
                abs(candidate - born)
                for candidate, born in zip(candidate_probabilities, born_probabilities, strict=True)
            )
            computed_status = "survives" if max_deviation <= tolerance else "rejected"
            if computed_status != expected_status:
                return [
                    Issue(
                        "born_quadratic_route_candidate_status_mismatch",
                        f"{gate.identifier}: readout {readout_id} expected {expected_status}, computed {computed_status}",
                    )
                ]
    return []


def check_tensor_composition_route_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    conditions = require_string_tuple(gate.payload.get("conditions", []), f"{gate.identifier}.conditions")
    if set(conditions) != set(TENSOR_COMPOSITION_ROUTE_CONDITIONS):
        return [
            Issue(
                "tensor_composition_route_conditions_mismatch",
                f"{gate.identifier}: conditions must match the tensor-composition route set",
            )
        ]

    systems = require_list(gate.payload.get("systems"), f"{gate.identifier}.systems")
    if not systems:
        raise ManifestError("tensor-composition route requires at least one system")
    for index, item in enumerate(systems):
        system = require_mapping(item, f"{gate.identifier}.systems[{index}]")
        system_id = require_string(system.get("id"), f"{gate.identifier}.systems[{index}].id")
        local_a = parse_positive_integer(system.get("local_a"), f"{gate.identifier}.systems[{index}].local_a")
        local_b = parse_positive_integer(system.get("local_b"), f"{gate.identifier}.systems[{index}].local_b")
        expected_composite = parse_positive_integer(system.get("expected_composite"), f"{gate.identifier}.systems[{index}].expected_composite")
        expected_basis_count = parse_positive_integer(
            system.get("expected_product_basis_count"),
            f"{gate.identifier}.systems[{index}].expected_product_basis_count",
        )
        computed_composite = local_a * local_b
        if computed_composite != expected_composite:
            return [
                Issue(
                    "tensor_composition_dimension_mismatch",
                    f"{gate.identifier}: system {system_id} expected composite {expected_composite}, computed {computed_composite}",
                )
            ]
        if computed_composite != expected_basis_count:
            return [
                Issue(
                    "tensor_composition_basis_count_mismatch",
                    f"{gate.identifier}: system {system_id} expected basis count {expected_basis_count}, computed {computed_composite}",
                )
            ]

    states = require_list(gate.payload.get("states"), f"{gate.identifier}.states")
    if len(states) < 2:
        raise ManifestError("tensor-composition route requires at least two states")
    for index, item in enumerate(states):
        state = require_mapping(item, f"{gate.identifier}.states[{index}]")
        state_id = require_string(state.get("id"), f"{gate.identifier}.states[{index}].id")
        coefficients = parse_nonnegative_real_list(
            state.get("schmidt_coefficients"),
            f"{gate.identifier}.states[{index}].schmidt_coefficients",
        )
        expected_rank = parse_positive_integer(state.get("expected_schmidt_rank"), f"{gate.identifier}.states[{index}].expected_schmidt_rank")
        expected_factorizable = parse_bool(state.get("expected_factorizable"), f"{gate.identifier}.states[{index}].expected_factorizable")
        norm = sum(coefficient * coefficient for coefficient in coefficients)
        if abs(norm - 1.0) > tolerance:
            raise ManifestError(f"{gate.identifier}: state {state_id} Schmidt coefficients must be normalized")
        computed_rank = sum(1 for coefficient in coefficients if coefficient > tolerance)
        if computed_rank != expected_rank:
            return [
                Issue(
                    "tensor_composition_schmidt_rank_mismatch",
                    f"{gate.identifier}: state {state_id} expected Schmidt rank {expected_rank}, computed {computed_rank}",
                )
            ]
        computed_factorizable = computed_rank == 1
        if computed_factorizable != expected_factorizable:
            return [
                Issue(
                    "tensor_composition_factorization_mismatch",
                    f"{gate.identifier}: state {state_id} expected factorizable={expected_factorizable}, computed {computed_factorizable}",
                )
            ]
    return []


def check_qm_core_recompile_route_gate(gate: FiniteGate) -> list[Issue]:
    shared_operations = require_string_tuple(gate.payload.get("shared_operations", []), f"{gate.identifier}.shared_operations")
    if set(shared_operations) != set(QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS):
        return [
            Issue(
                "qm_core_recompile_operations_mismatch",
                f"{gate.identifier}: shared operations must match the QM universal pattern operations",
            )
        ]
    route_gates = require_string_tuple(gate.payload.get("route_gates", []), f"{gate.identifier}.route_gates")
    if set(route_gates) != set(QM_CORE_RECOMPILE_REQUIRED_ROUTES):
        return [
            Issue(
                "qm_core_recompile_routes_mismatch",
                f"{gate.identifier}: route gates must match the finite QM core route set",
            )
        ]
    kernel_count = parse_positive_integer(gate.payload.get("kernel_count"), f"{gate.identifier}.kernel_count")
    experiment_count = parse_positive_integer(gate.payload.get("experiment_count"), f"{gate.identifier}.experiment_count")
    finite_gate_reference_count = parse_positive_integer(
        gate.payload.get("finite_gate_reference_count"),
        f"{gate.identifier}.finite_gate_reference_count",
    )
    expected_kernel_count = parse_positive_integer(
        gate.payload.get("expected_kernel_count"),
        f"{gate.identifier}.expected_kernel_count",
    )
    expected_experiment_count = parse_positive_integer(
        gate.payload.get("expected_experiment_count"),
        f"{gate.identifier}.expected_experiment_count",
    )
    expected_finite_gate_reference_count = parse_positive_integer(
        gate.payload.get("expected_finite_gate_reference_count"),
        f"{gate.identifier}.expected_finite_gate_reference_count",
    )
    if kernel_count != expected_kernel_count:
        return [
            Issue(
                "qm_core_recompile_kernel_count_mismatch",
                f"{gate.identifier}: expected {expected_kernel_count} kernels, got {kernel_count}",
            )
        ]
    if experiment_count != expected_experiment_count:
        return [
            Issue(
                "qm_core_recompile_experiment_count_mismatch",
                f"{gate.identifier}: expected {expected_experiment_count} experiments, got {experiment_count}",
            )
        ]
    if finite_gate_reference_count != expected_finite_gate_reference_count:
        return [
            Issue(
                "qm_core_recompile_gate_reference_count_mismatch",
                (
                    f"{gate.identifier}: expected {expected_finite_gate_reference_count} finite gate refs, "
                    f"got {finite_gate_reference_count}"
                ),
            )
        ]
    return []


def check_continuum_action_frontier_gate(gate: FiniteGate) -> list[Issue]:
    requirements = require_string_tuple(gate.payload.get("requirements", []), f"{gate.identifier}.requirements")
    if set(requirements) != set(CONTINUUM_ACTION_FRONTIER_REQUIREMENTS):
        return [
            Issue(
                "continuum_action_frontier_requirements_mismatch",
                f"{gate.identifier}: requirements must match the continuum/action frontier set",
            )
        ]
    components = require_list(gate.payload.get("components"), f"{gate.identifier}.components")
    if len(components) != len(requirements):
        raise ManifestError(f"{gate.identifier}: components must cover every continuum/action frontier requirement")
    status_by_requirement: dict[str, str] = {}
    for index, item in enumerate(components):
        component = require_mapping(item, f"{gate.identifier}.components[{index}]")
        requirement = require_string(component.get("requirement"), f"{gate.identifier}.components[{index}].requirement")
        status = require_string(component.get("status"), f"{gate.identifier}.components[{index}].status")
        if requirement not in CONTINUUM_ACTION_FRONTIER_REQUIREMENTS:
            return [
                Issue(
                    "continuum_action_frontier_unknown_requirement",
                    f"{gate.identifier}: unknown requirement {requirement}",
                )
            ]
        if status not in {"supported", "blocked", "open"}:
            raise ManifestError(f"{gate.identifier}: component {requirement} has unknown status {status!r}")
        if requirement in status_by_requirement:
            return [
                Issue(
                    "continuum_action_frontier_duplicate_requirement",
                    f"{gate.identifier}: duplicate requirement {requirement}",
                )
            ]
        status_by_requirement[requirement] = status
    missing = sorted(set(requirements) - set(status_by_requirement))
    if missing:
        return [
            Issue(
                "continuum_action_frontier_component_missing",
                f"{gate.identifier}: missing components: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_extension_status"), f"{gate.identifier}.expected_extension_status")
    if expected_status not in {"blocked", "finite_supported", "derived"}:
        raise ManifestError(f"{gate.identifier}: expected_extension_status is unknown")
    has_blocked = any(status == "blocked" for status in status_by_requirement.values())
    has_open = any(status == "open" for status in status_by_requirement.values())
    if has_blocked:
        computed_status = "blocked"
    elif has_open:
        computed_status = "finite_supported"
    else:
        computed_status = "derived"
    if computed_status != expected_status:
        return [
            Issue(
                "continuum_action_frontier_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_full_qm_closure_frontier_gate(gate: FiniteGate) -> list[Issue]:
    requirements = require_string_tuple(gate.payload.get("requirements", []), f"{gate.identifier}.requirements")
    if set(requirements) != set(FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS):
        return [
            Issue(
                "full_qm_closure_frontier_requirements_mismatch",
                f"{gate.identifier}: requirements must match the full-QM closure frontier set",
            )
        ]
    components = require_list(gate.payload.get("components"), f"{gate.identifier}.components")
    if len(components) != len(requirements):
        raise ManifestError(f"{gate.identifier}: components must cover every full-QM closure frontier requirement")
    status_by_requirement: dict[str, str] = {}
    for index, item in enumerate(components):
        component = require_mapping(item, f"{gate.identifier}.components[{index}]")
        requirement = require_string(component.get("requirement"), f"{gate.identifier}.components[{index}].requirement")
        status = require_string(component.get("status"), f"{gate.identifier}.components[{index}].status")
        if requirement not in FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS:
            return [
                Issue(
                    "full_qm_closure_frontier_unknown_requirement",
                    f"{gate.identifier}: unknown requirement {requirement}",
                )
            ]
        if status not in {"supported", "open", "blocked"}:
            raise ManifestError(f"{gate.identifier}: component {requirement} has unknown status {status!r}")
        if requirement in status_by_requirement:
            return [
                Issue(
                    "full_qm_closure_frontier_duplicate_requirement",
                    f"{gate.identifier}: duplicate requirement {requirement}",
                )
            ]
        status_by_requirement[requirement] = status
    missing = sorted(set(requirements) - set(status_by_requirement))
    if missing:
        return [
            Issue(
                "full_qm_closure_frontier_component_missing",
                f"{gate.identifier}: missing components: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_full_qm_status"), f"{gate.identifier}.expected_full_qm_status")
    if expected_status not in {"blocked", "target", "derived"}:
        raise ManifestError(f"{gate.identifier}: expected_full_qm_status is unknown")
    has_blocked = any(status == "blocked" for status in status_by_requirement.values())
    has_open = any(status == "open" for status in status_by_requirement.values())
    if has_blocked:
        computed_status = "blocked"
    elif has_open:
        computed_status = "target"
    else:
        computed_status = "derived"
    if computed_status != expected_status:
        return [
            Issue(
                "full_qm_closure_frontier_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    ledger_items = require_list(gate.payload.get("obstruction_ledger"), f"{gate.identifier}.obstruction_ledger")
    if len(ledger_items) != len(requirements):
        raise ManifestError(f"{gate.identifier}: obstruction_ledger must cover every full-QM closure requirement")
    ledger_by_requirement: dict[str, str] = {}
    for index, item in enumerate(ledger_items):
        ledger = require_mapping(item, f"{gate.identifier}.obstruction_ledger[{index}]")
        requirement = require_string(
            ledger.get("requirement"),
            f"{gate.identifier}.obstruction_ledger[{index}].requirement",
        )
        blocker_kind = require_string(
            ledger.get("blocker_kind"),
            f"{gate.identifier}.obstruction_ledger[{index}].blocker_kind",
        )
        if requirement not in FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS:
            return [
                Issue(
                    "full_qm_obstruction_ledger_unknown_requirement",
                    f"{gate.identifier}: obstruction ledger has unknown requirement {requirement}",
                )
            ]
        if blocker_kind not in FULL_QM_OBSTRUCTION_KINDS:
            return [
                Issue(
                    "full_qm_obstruction_ledger_unknown_kind",
                    f"{gate.identifier}: obstruction ledger has unknown blocker kind {blocker_kind}",
                )
            ]
        if requirement in ledger_by_requirement:
            return [
                Issue(
                    "full_qm_obstruction_ledger_duplicate_requirement",
                    f"{gate.identifier}: obstruction ledger duplicates {requirement}",
                )
            ]
        next_obligation = require_string(
            ledger.get("next_proof_obligation"),
            f"{gate.identifier}.obstruction_ledger[{index}].next_proof_obligation",
        )
        forbidden_upgrade = require_string(
            ledger.get("forbidden_upgrade"),
            f"{gate.identifier}.obstruction_ledger[{index}].forbidden_upgrade",
        )
        if not next_obligation:
            return [
                Issue(
                    "full_qm_obstruction_ledger_obligation_missing",
                    f"{gate.identifier}: obstruction ledger for {requirement} must name the next proof obligation",
                )
            ]
        if not forbidden_upgrade:
            return [
                Issue(
                    "full_qm_obstruction_ledger_forbidden_upgrade_missing",
                    f"{gate.identifier}: obstruction ledger for {requirement} must name the forbidden upgrade",
                )
            ]
        ledger_by_requirement[requirement] = blocker_kind
    missing_ledger = sorted(set(requirements) - set(ledger_by_requirement))
    if missing_ledger:
        return [
            Issue(
                "full_qm_obstruction_ledger_requirement_missing",
                f"{gate.identifier}: obstruction ledger missing requirements: {', '.join(missing_ledger)}",
            )
        ]
    return []


def check_gpt_principle_separator_gate(gate: FiniteGate) -> list[Issue]:
    principles = require_string_tuple(gate.payload.get("principles", []), f"{gate.identifier}.principles")
    if set(principles) != set(GPT_SEPARATOR_PRINCIPLES):
        return [
            Issue(
                "gpt_principle_separator_principles_mismatch",
                f"{gate.identifier}: principles must match the GPT separator principle set",
            )
        ]

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if len(candidates) < 2:
        raise ManifestError("GPT principle separator requires at least two candidates")

    computed_statuses: dict[str, str] = {}
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        capabilities = parse_gpt_separator_capabilities(
            candidate.get("capabilities"),
            f"{gate.identifier}.candidates[{index}].capabilities",
        )
        expected_status = require_string(candidate.get("expected_status"), f"{gate.identifier}.candidates[{index}].expected_status")
        if expected_status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.candidates[{index}].expected_status is unknown")
        missing = sorted(set(principles) - set(capabilities))
        if missing:
            return [
                Issue(
                    "gpt_principle_separator_capabilities_incomplete",
                    f"{gate.identifier}: candidate {candidate_id} missing capabilities: {', '.join(missing)}",
                )
            ]
        computed_status = classify_gpt_principle_candidate(capabilities, principles)
        computed_statuses[candidate_id] = computed_status
        if computed_status != expected_status:
            return [
                Issue(
                    "gpt_principle_separator_candidate_status_mismatch",
                    f"{gate.identifier}: candidate {candidate_id} expected {expected_status}, computed {computed_status}",
                )
            ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "gpt_principle_separator_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]
    return []


def check_carrier_selection_frontier_gate(gate: FiniteGate) -> list[Issue]:
    declared_obstructions = require_string_tuple(
        gate.payload.get("open_obstructions", []),
        f"{gate.identifier}.open_obstructions",
    )
    if set(declared_obstructions) != set(CARRIER_SELECTION_OPEN_OBSTRUCTIONS):
        return [
            Issue(
                "carrier_selection_frontier_obstructions_mismatch",
                f"{gate.identifier}: open obstructions must match the carrier-selection frontier set",
            )
        ]

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    expected_frontier_status = require_string(
        gate.payload.get("expected_frontier_status"),
        f"{gate.identifier}.expected_frontier_status",
    )
    if expected_frontier_status not in CARRIER_SELECTION_FRONTIER_STATUSES:
        raise ManifestError(f"{gate.identifier}.expected_frontier_status is unknown")

    candidates = require_list(gate.payload.get("candidates"), f"{gate.identifier}.candidates")
    if len(candidates) < 2:
        raise ManifestError("carrier selection frontier requires at least two candidates")

    computed_statuses: dict[str, str] = {}
    covered_obstructions: set[str] = set()
    for index, item in enumerate(candidates):
        candidate = require_mapping(item, f"{gate.identifier}.candidates[{index}]")
        candidate_id = require_string(candidate.get("id"), f"{gate.identifier}.candidates[{index}].id")
        status = require_string(candidate.get("status"), f"{gate.identifier}.candidates[{index}].status")
        if status not in DISTINGUISHABILITY_GEOMETRY_STATUSES:
            raise ManifestError(f"{gate.identifier}.candidates[{index}].status is unknown")
        obstructions = require_string_tuple(
            candidate.get("blocking_obstructions", []),
            f"{gate.identifier}.candidates[{index}].blocking_obstructions",
        )
        unknown_obstructions = sorted(set(obstructions) - set(declared_obstructions))
        if unknown_obstructions:
            return [
                Issue(
                    "carrier_selection_frontier_unknown_obstruction",
                    (
                        f"{gate.identifier}: candidate {candidate_id} references unknown obstructions: "
                        f"{', '.join(unknown_obstructions)}"
                    ),
                )
            ]
        if status == "underdetermined" and not obstructions:
            return [
                Issue(
                    "carrier_selection_frontier_obstruction_missing",
                    f"{gate.identifier}: underdetermined candidate {candidate_id} needs at least one obstruction",
                )
            ]
        if status != "underdetermined" and obstructions:
            return [
                Issue(
                    "carrier_selection_frontier_obstruction_on_closed_candidate",
                    f"{gate.identifier}: closed candidate {candidate_id} must not carry open obstructions",
                )
            ]
        computed_statuses[candidate_id] = status
        covered_obstructions.update(obstructions)

    missing_obstructions = sorted(set(declared_obstructions) - covered_obstructions)
    if missing_obstructions:
        return [
            Issue(
                "carrier_selection_frontier_obstructions_uncovered",
                f"{gate.identifier}: open obstructions are not attached to any candidate: {', '.join(missing_obstructions)}",
            )
        ]

    surviving = [candidate_id for candidate_id, status in computed_statuses.items() if status == "survives"]
    underdetermined = [candidate_id for candidate_id, status in computed_statuses.items() if status == "underdetermined"]
    computed_selected = surviving[0] if len(surviving) == 1 and not underdetermined else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "carrier_selection_frontier_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]

    computed_frontier_status = "selected_by_current_gates" if computed_selected != "none" else "not_derived"
    if computed_frontier_status != expected_frontier_status:
        return [
            Issue(
                "carrier_selection_frontier_status_mismatch",
                f"{gate.identifier}: expected frontier status {expected_frontier_status}, computed {computed_frontier_status}",
            )
        ]
    return []


def check_carrier_quantifier_frontier_gate(gate: FiniteGate) -> list[Issue]:
    classes = require_list(gate.payload.get("classes"), f"{gate.identifier}.classes")
    if len(classes) != len(CARRIER_QUANTIFIER_FRONTIER_CLASSES):
        raise ManifestError(f"{gate.identifier}: classes must cover every carrier quantifier frontier class")

    expected_selected = require_string(gate.payload.get("expected_selected_carrier"), f"{gate.identifier}.expected_selected_carrier")
    expected_status = require_string(gate.payload.get("expected_quantifier_status"), f"{gate.identifier}.expected_quantifier_status")
    if expected_status not in CARRIER_QUANTIFIER_FRONTIER_STATUSES:
        raise ManifestError(f"{gate.identifier}.expected_quantifier_status is unknown")

    status_by_class: dict[str, str] = {}
    surviving: list[str] = []
    unresolved: list[str] = []
    for index, item in enumerate(classes):
        carrier_class = require_mapping(item, f"{gate.identifier}.classes[{index}]")
        class_id = require_string(carrier_class.get("id"), f"{gate.identifier}.classes[{index}].id")
        status = require_string(carrier_class.get("status"), f"{gate.identifier}.classes[{index}].status")
        evidence_refs = require_string_tuple(
            carrier_class.get("evidence_refs", []),
            f"{gate.identifier}.classes[{index}].evidence_refs",
        )
        open_gap = require_string(carrier_class.get("open_gap", ""), f"{gate.identifier}.classes[{index}].open_gap")
        if class_id not in CARRIER_QUANTIFIER_FRONTIER_CLASSES:
            return [
                Issue(
                    "carrier_quantifier_frontier_unknown_class",
                    f"{gate.identifier}: unknown carrier class {class_id}",
                )
            ]
        if status not in CARRIER_QUANTIFIER_STATUSES:
            raise ManifestError(f"{gate.identifier}: class {class_id} has unknown status {status!r}")
        if class_id in status_by_class:
            return [
                Issue(
                    "carrier_quantifier_frontier_duplicate_class",
                    f"{gate.identifier}: duplicate carrier class {class_id}",
                )
            ]
        if not evidence_refs:
            return [
                Issue(
                    "carrier_quantifier_frontier_evidence_missing",
                    f"{gate.identifier}: carrier class {class_id} must cite evidence",
                )
            ]
        if status in {"underdetermined", "out_of_scope"} and not open_gap:
            return [
                Issue(
                    "carrier_quantifier_frontier_gap_missing",
                    f"{gate.identifier}: unresolved carrier class {class_id} must declare an open gap",
                )
            ]
        if status == "survives":
            surviving.append(class_id)
        if status in {"underdetermined", "out_of_scope"}:
            unresolved.append(class_id)
        status_by_class[class_id] = status

    missing = sorted(set(CARRIER_QUANTIFIER_FRONTIER_CLASSES) - set(status_by_class))
    if missing:
        return [
            Issue(
                "carrier_quantifier_frontier_class_missing",
                f"{gate.identifier}: missing carrier classes: {', '.join(missing)}",
            )
        ]

    computed_selected = surviving[0] if len(surviving) == 1 and not unresolved else "none"
    if computed_selected != expected_selected:
        return [
            Issue(
                "carrier_quantifier_frontier_selection_mismatch",
                f"{gate.identifier}: expected selected carrier {expected_selected}, computed {computed_selected}",
            )
        ]

    computed_status = "closed" if computed_selected != "none" else "open"
    if computed_status != expected_status:
        return [
            Issue(
                "carrier_quantifier_frontier_status_mismatch",
                f"{gate.identifier}: expected quantifier status {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_route_closed_gpt_subtheory_frontier_gate(gate: FiniteGate) -> list[Issue]:
    target_class = require_string(gate.payload.get("target_class"), f"{gate.identifier}.target_class")
    if target_class != "route_closed_gpt_subtheory":
        return [
            Issue(
                "route_closed_gpt_frontier_target_mismatch",
                f"{gate.identifier}: target_class must be route_closed_gpt_subtheory",
            )
        ]

    inherited_support = require_string_tuple(
        gate.payload.get("inherited_support", []),
        f"{gate.identifier}.inherited_support",
    )
    if set(inherited_support) != set(ROUTE_CLOSED_GPT_FRONTIER_INHERITED_SUPPORT):
        return [
            Issue(
                "route_closed_gpt_frontier_inherited_support_mismatch",
                f"{gate.identifier}: inherited support must match the route-closed GPT support set",
            )
        ]

    requirements = require_list(gate.payload.get("open_requirements"), f"{gate.identifier}.open_requirements")
    if len(requirements) != len(ROUTE_CLOSED_GPT_FRONTIER_REQUIREMENTS):
        raise ManifestError(f"{gate.identifier}: open_requirements must cover every route-closed GPT frontier requirement")

    seen: set[str] = set()
    for index, item in enumerate(requirements):
        requirement = require_mapping(item, f"{gate.identifier}.open_requirements[{index}]")
        requirement_id = require_string(
            requirement.get("id"),
            f"{gate.identifier}.open_requirements[{index}].id",
        )
        status = require_string(
            requirement.get("status"),
            f"{gate.identifier}.open_requirements[{index}].status",
        )
        evidence_refs = require_string_tuple(
            requirement.get("evidence_refs", []),
            f"{gate.identifier}.open_requirements[{index}].evidence_refs",
        )
        next_obligation = require_string(
            requirement.get("next_proof_obligation", ""),
            f"{gate.identifier}.open_requirements[{index}].next_proof_obligation",
        )
        if requirement_id not in ROUTE_CLOSED_GPT_FRONTIER_REQUIREMENTS:
            return [
                Issue(
                    "route_closed_gpt_frontier_unknown_requirement",
                    f"{gate.identifier}: unknown route-closed GPT requirement {requirement_id}",
                )
            ]
        if requirement_id in seen:
            return [
                Issue(
                    "route_closed_gpt_frontier_duplicate_requirement",
                    f"{gate.identifier}: duplicate route-closed GPT requirement {requirement_id}",
                )
            ]
        if status not in {"open", "conditional_proof"}:
            raise ManifestError(f"{gate.identifier}: requirement {requirement_id} has unknown status {status!r}")
        conditional_refs = require_string_tuple(
            requirement.get("conditional_theorem_refs", []),
            f"{gate.identifier}.open_requirements[{index}].conditional_theorem_refs",
        )
        if status == "conditional_proof" and not conditional_refs:
            return [
                Issue(
                    "route_closed_gpt_frontier_requirement_status_mismatch",
                    f"{gate.identifier}: conditional requirement {requirement_id} must cite a conditional theorem",
                )
            ]
        if status == "open" and conditional_refs:
            return [
                Issue(
                    "route_closed_gpt_frontier_requirement_status_mismatch",
                    f"{gate.identifier}: open requirement {requirement_id} must not cite a conditional theorem",
                )
            ]
        if not evidence_refs:
            return [
                Issue(
                    "route_closed_gpt_frontier_evidence_missing",
                    f"{gate.identifier}: requirement {requirement_id} must cite evidence",
                )
            ]
        if status == "open" and not next_obligation:
            return [
                Issue(
                    "route_closed_gpt_frontier_obligation_missing",
                    f"{gate.identifier}: requirement {requirement_id} must name the next proof obligation",
                )
            ]
        seen.add(requirement_id)

    missing = sorted(set(ROUTE_CLOSED_GPT_FRONTIER_REQUIREMENTS) - seen)
    if missing:
        return [
            Issue(
                "route_closed_gpt_frontier_requirement_missing",
                f"{gate.identifier}: missing route-closed GPT requirements: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_status"), f"{gate.identifier}.expected_status")
    if expected_status not in ROUTE_CLOSED_GPT_FRONTIER_STATUSES:
        raise ManifestError(f"{gate.identifier}.expected_status is unknown")
    has_open_requirement = any(
        require_string(
            require_mapping(item, f"{gate.identifier}.open_requirements[{index}]").get("status"),
            f"{gate.identifier}.open_requirements[{index}].status",
        )
        == "open"
        for index, item in enumerate(requirements)
    )
    computed_status = "underdetermined" if has_open_requirement else "collapses_to_complex_hilbert_like"
    if computed_status != expected_status:
        return [
            Issue(
                "route_closed_gpt_frontier_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_carrier_selection_proof_route_gate(gate: FiniteGate) -> list[Issue]:
    target_theorem = require_string(gate.payload.get("target_theorem"), f"{gate.identifier}.target_theorem")
    if target_theorem != "universal_carrier_selection_theorem":
        return [
            Issue(
                "carrier_selection_proof_route_target_mismatch",
                f"{gate.identifier}: target theorem must be universal_carrier_selection_theorem",
            )
        ]

    lemmas = require_list(gate.payload.get("lemmas"), f"{gate.identifier}.lemmas")
    if len(lemmas) != len(CARRIER_SELECTION_OPEN_OBSTRUCTIONS):
        raise ManifestError(f"{gate.identifier}: lemmas must cover every carrier-selection obstruction")

    status_by_lemma: dict[str, str] = {}
    for index, item in enumerate(lemmas):
        lemma = require_mapping(item, f"{gate.identifier}.lemmas[{index}]")
        lemma_id = require_string(lemma.get("id"), f"{gate.identifier}.lemmas[{index}].id")
        status = require_string(lemma.get("status"), f"{gate.identifier}.lemmas[{index}].status")
        evidence_refs = require_string_tuple(
            lemma.get("evidence_refs", []),
            f"{gate.identifier}.lemmas[{index}].evidence_refs",
        )
        open_gap = require_string(lemma.get("open_gap"), f"{gate.identifier}.lemmas[{index}].open_gap")
        if lemma_id not in CARRIER_SELECTION_OPEN_OBSTRUCTIONS:
            return [
                Issue(
                    "carrier_selection_proof_route_unknown_lemma",
                    f"{gate.identifier}: unknown lemma {lemma_id}",
                )
            ]
        if status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
            raise ManifestError(f"{gate.identifier}: lemma {lemma_id} has unknown status {status!r}")
        if lemma_id in status_by_lemma:
            return [
                Issue(
                    "carrier_selection_proof_route_duplicate_lemma",
                    f"{gate.identifier}: duplicate lemma {lemma_id}",
                )
            ]
        if status in {"finite_witnessed", "conditional_proof", "formal_proof"} and not evidence_refs:
            return [
                Issue(
                    "carrier_selection_proof_route_evidence_missing",
                    f"{gate.identifier}: lemma {lemma_id} needs evidence refs",
                )
            ]
        if status != "formal_proof" and not open_gap.strip():
            return [
                Issue(
                    "carrier_selection_proof_route_gap_missing",
                    f"{gate.identifier}: lemma {lemma_id} needs an open gap",
                )
            ]
        status_by_lemma[lemma_id] = status

    missing = sorted(set(CARRIER_SELECTION_OPEN_OBSTRUCTIONS) - set(status_by_lemma))
    if missing:
        return [
            Issue(
                "carrier_selection_proof_route_lemma_missing",
                f"{gate.identifier}: missing lemmas: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(gate.payload.get("expected_proof_status"), f"{gate.identifier}.expected_proof_status")
    if expected_status not in THEOREM_CARD_PROOF_STATUS_VALUES:
        raise ManifestError(f"{gate.identifier}: expected_proof_status is unknown")
    if any(status == "blocked" for status in status_by_lemma.values()):
        computed_status = "blocked"
    elif all(status == "formal_proof" for status in status_by_lemma.values()):
        computed_status = "formal_proof"
    else:
        computed_status = "open"
    if computed_status != expected_status:
        return [
            Issue(
                "carrier_selection_proof_route_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_context_product_carrier_lemma_route_gate(gate: FiniteGate) -> list[Issue]:
    target_lemma = require_string(gate.payload.get("target_lemma"), f"{gate.identifier}.target_lemma")
    if target_lemma != CONTEXT_PRODUCT_CARRIER_LEMMA_TARGET:
        return [
            Issue(
                "context_product_carrier_lemma_target_mismatch",
                f"{gate.identifier}: target lemma must be {CONTEXT_PRODUCT_CARRIER_LEMMA_TARGET}",
            )
        ]

    primitives = require_string_tuple(gate.payload.get("required_primitives", []), f"{gate.identifier}.required_primitives")
    if set(primitives) != set(CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES):
        return [
            Issue(
                "context_product_carrier_lemma_primitives_mismatch",
                f"{gate.identifier}: required primitives must match context-product exhaustion primitives",
            )
        ]

    conditions = require_string_tuple(gate.payload.get("required_conditions", []), f"{gate.identifier}.required_conditions")
    if set(conditions) != set(IDT_LOCAL_TOMOGRAPHY_CONDITIONS):
        return [
            Issue(
                "context_product_carrier_lemma_conditions_mismatch",
                f"{gate.identifier}: required conditions must match IDT local-tomography conditions",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("finite_evidence_refs", []), f"{gate.identifier}.finite_evidence_refs")
    if set(evidence_refs) != {"context_product_exhaustion_demo", "idt_local_tomography_derivation_demo"}:
        return [
            Issue(
                "context_product_carrier_lemma_evidence_mismatch",
                f"{gate.identifier}: finite evidence refs must link context-product and local-tomography witnesses",
            )
        ]

    excluded_counterexamples = require_string_tuple(
        gate.payload.get("excluded_counterexamples", []),
        f"{gate.identifier}.excluded_counterexamples",
    )
    expected_exclusion_count = parse_positive_integer(
        gate.payload.get("expected_exclusion_count"),
        f"{gate.identifier}.expected_exclusion_count",
    )
    if len(excluded_counterexamples) != expected_exclusion_count:
        return [
            Issue(
                "context_product_carrier_lemma_exclusion_count_mismatch",
                f"{gate.identifier}: expected {expected_exclusion_count} exclusions, got {len(excluded_counterexamples)}",
            )
        ]

    open_gaps = require_string_tuple(gate.payload.get("open_generalization_gaps", []), f"{gate.identifier}.open_generalization_gaps")
    conditional_refs = require_string_tuple(gate.payload.get("conditional_theorem_refs", []), f"{gate.identifier}.conditional_theorem_refs")
    expected_status = require_string(gate.payload.get("expected_lemma_status"), f"{gate.identifier}.expected_lemma_status")
    if expected_status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
        raise ManifestError(f"{gate.identifier}: expected_lemma_status is unknown")
    required_conditional_refs = {
        "context_product_exhaustion_implies_local_tomography",
        "context_product_local_tomography_theorem_demo",
        "real_hilbert_composite_hidden_joint_invariant",
    }
    if conditional_refs and set(conditional_refs) != required_conditional_refs:
        return [
            Issue(
                "context_product_carrier_lemma_conditional_refs_mismatch",
                f"{gate.identifier}: conditional theorem refs must link the local-tomography theorem and rebit candidate card",
            )
        ]
    if conditional_refs:
        computed_status = "conditional_proof"
    elif open_gaps:
        computed_status = "finite_witnessed"
    else:
        computed_status = "formal_proof"
    if computed_status != expected_status:
        return [
            Issue(
                "context_product_carrier_lemma_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_tomographic_state_effect_duality_theorem_gate(gate: FiniteGate) -> list[Issue]:
    target_card = require_string(gate.payload.get("target_theorem_card"), f"{gate.identifier}.target_theorem_card")
    if target_card != "route_witness_completeness_implies_tomographic_state_effect_duality":
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_target_mismatch",
                f"{gate.identifier}: target card must be route_witness_completeness_implies_tomographic_state_effect_duality",
            )
        ]

    assumptions = require_string_tuple(gate.payload.get("assumptions", []), f"{gate.identifier}.assumptions")
    if set(assumptions) != set(TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_ASSUMPTIONS):
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_assumptions_mismatch",
                f"{gate.identifier}: assumptions must match the conditional state-effect duality theorem",
            )
        ]

    conclusions = require_string_tuple(gate.payload.get("conclusions", []), f"{gate.identifier}.conclusions")
    if set(conclusions) != set(TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_CONCLUSIONS):
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_conclusions_mismatch",
                f"{gate.identifier}: conclusions must match state-effect duality and hidden-kernel rejection",
            )
        ]

    systems = require_list(gate.payload.get("systems"), f"{gate.identifier}.systems")
    if len(systems) < 2:
        raise ManifestError(f"{gate.identifier}: systems must include a full-rank witness and a rank-deficient separator")
    accepted = 0
    rejected = 0
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    for index, item in enumerate(systems):
        system = require_mapping(item, f"{gate.identifier}.systems[{index}]")
        system_id = require_string(system.get("id"), f"{gate.identifier}.systems[{index}].id")
        state_dimension = parse_positive_integer(
            system.get("state_dimension"),
            f"{gate.identifier}.systems[{index}].state_dimension",
        )
        witness_matrix = parse_matrix(
            system.get("effect_witness_matrix"),
            f"{gate.identifier}.systems[{index}].effect_witness_matrix",
        )
        if any(len(row) != state_dimension for row in witness_matrix):
            raise ManifestError(f"{gate.identifier}: system {system_id} witness rows must match state_dimension")
        expected_rank = parse_nonnegative_integer(
            system.get("expected_rank"),
            f"{gate.identifier}.systems[{index}].expected_rank",
        )
        computed_rank = complex_matrix_rank(witness_matrix, tolerance)
        if computed_rank != expected_rank:
            return [
                Issue(
                    "tomographic_state_effect_duality_rank_mismatch",
                    f"{gate.identifier}: system {system_id} expected rank {expected_rank}, computed {computed_rank}",
                )
            ]
        expected_status = require_string(
            system.get("expected_status"),
            f"{gate.identifier}.systems[{index}].expected_status",
        )
        if expected_status not in {"survives", "rejected"}:
            raise ManifestError(f"{gate.identifier}: system {system_id} expected_status is unknown")
        computed_status = "survives" if computed_rank == state_dimension else "rejected"
        if computed_status != expected_status:
            return [
                Issue(
                    "tomographic_state_effect_duality_status_mismatch",
                    f"{gate.identifier}: system {system_id} expected {expected_status}, computed {computed_status}",
                )
            ]
        if computed_status == "survives":
            accepted += 1
        if computed_status == "rejected":
            rejected += 1

    if accepted == 0 or rejected == 0:
        return [
            Issue(
                "tomographic_state_effect_duality_separator_incomplete",
                f"{gate.identifier}: theorem gate must include both a survivor and a rejected hidden-kernel sample",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("evidence_refs", []), f"{gate.identifier}.evidence_refs")
    required_evidence = {
        "context_product_exhaustion_implies_local_tomography",
        "context_product_local_tomography_theorem_demo",
        "generic_gpt_closure_separator_demo",
    }
    if set(evidence_refs) != required_evidence:
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_evidence_mismatch",
                f"{gate.identifier}: evidence refs must link local tomography theorem and generic-GPT closure screen",
            )
        ]

    forbidden_upgrades = require_string_tuple(gate.payload.get("forbidden_upgrades", []), f"{gate.identifier}.forbidden_upgrades")
    if set(forbidden_upgrades) != set(TOMOGRAPHIC_STATE_EFFECT_DUALITY_THEOREM_FORBIDDEN_UPGRADES):
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_forbidden_upgrades_mismatch",
                f"{gate.identifier}: forbidden upgrades must preserve the public QM claim boundary",
            )
        ]

    expected_theorem_status = require_string(
        gate.payload.get("expected_theorem_status"),
        f"{gate.identifier}.expected_theorem_status",
    )
    computed_theorem_status = "conditional_proof"
    if expected_theorem_status != computed_theorem_status:
        return [
            Issue(
                "tomographic_state_effect_duality_theorem_status_mismatch",
                f"{gate.identifier}: expected {expected_theorem_status}, computed {computed_theorem_status}",
            )
        ]
    return []


def check_purification_filtering_carrier_lemma_route_gate(gate: FiniteGate) -> list[Issue]:
    target_lemma = require_string(gate.payload.get("target_lemma"), f"{gate.identifier}.target_lemma")
    if target_lemma != PURIFICATION_FILTERING_CARRIER_LEMMA_TARGET:
        return [
            Issue(
                "purification_filtering_carrier_lemma_target_mismatch",
                f"{gate.identifier}: target lemma must be {PURIFICATION_FILTERING_CARRIER_LEMMA_TARGET}",
            )
        ]

    conditions = require_string_tuple(gate.payload.get("required_conditions", []), f"{gate.identifier}.required_conditions")
    if set(conditions) != set(IDT_PURIFICATION_FILTERING_CONDITIONS):
        return [
            Issue(
                "purification_filtering_carrier_lemma_conditions_mismatch",
                f"{gate.identifier}: required conditions must match IDT purification/filtering conditions",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("finite_evidence_refs", []), f"{gate.identifier}.finite_evidence_refs")
    if set(evidence_refs) != {"idt_purification_filtering_demo"}:
        return [
            Issue(
                "purification_filtering_carrier_lemma_evidence_mismatch",
                f"{gate.identifier}: finite evidence refs must link the purification/filtering witness",
            )
        ]

    excluded_counterexamples = require_string_tuple(
        gate.payload.get("excluded_counterexamples", []),
        f"{gate.identifier}.excluded_counterexamples",
    )
    expected_exclusion_count = parse_positive_integer(
        gate.payload.get("expected_exclusion_count"),
        f"{gate.identifier}.expected_exclusion_count",
    )
    if len(excluded_counterexamples) != expected_exclusion_count:
        return [
            Issue(
                "purification_filtering_carrier_lemma_exclusion_count_mismatch",
                f"{gate.identifier}: expected {expected_exclusion_count} exclusions, got {len(excluded_counterexamples)}",
            )
        ]

    open_gaps = require_string_tuple(gate.payload.get("open_generalization_gaps", []), f"{gate.identifier}.open_generalization_gaps")
    conditional_refs = require_string_tuple(gate.payload.get("conditional_theorem_refs", []), f"{gate.identifier}.conditional_theorem_refs")
    expected_status = require_string(gate.payload.get("expected_lemma_status"), f"{gate.identifier}.expected_lemma_status")
    if expected_status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
        raise ManifestError(f"{gate.identifier}: expected_lemma_status is unknown")
    required_conditional_refs = {
        "purification_filtering_implies_recoverable_support_update",
        "purification_filtering_recoverable_support_theorem_demo",
    }
    if conditional_refs and set(conditional_refs) != required_conditional_refs:
        return [
            Issue(
                "purification_filtering_carrier_lemma_conditional_refs_mismatch",
                f"{gate.identifier}: conditional theorem refs must link the purification/filtering theorem",
            )
        ]
    if conditional_refs:
        computed_status = "conditional_proof"
    elif open_gaps:
        computed_status = "finite_witnessed"
    else:
        computed_status = "formal_proof"
    if computed_status != expected_status:
        return [
            Issue(
                "purification_filtering_carrier_lemma_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_bounded_correlation_carrier_lemma_route_gate(gate: FiniteGate) -> list[Issue]:
    target_lemma = require_string(gate.payload.get("target_lemma"), f"{gate.identifier}.target_lemma")
    if target_lemma != BOUNDED_CORRELATION_CARRIER_LEMMA_TARGET:
        return [
            Issue(
                "bounded_correlation_carrier_lemma_target_mismatch",
                f"{gate.identifier}: target lemma must be {BOUNDED_CORRELATION_CARRIER_LEMMA_TARGET}",
            )
        ]

    conditions = require_string_tuple(gate.payload.get("required_conditions", []), f"{gate.identifier}.required_conditions")
    if set(conditions) != set(IDT_BOUNDED_CORRELATION_CONDITIONS):
        return [
            Issue(
                "bounded_correlation_carrier_lemma_conditions_mismatch",
                f"{gate.identifier}: required conditions must match IDT bounded-correlation conditions",
            )
        ]

    principles = require_string_tuple(gate.payload.get("required_principles", []), f"{gate.identifier}.required_principles")
    if set(principles) != set(GPT_SEPARATOR_PRINCIPLES):
        return [
            Issue(
                "bounded_correlation_carrier_lemma_principles_mismatch",
                f"{gate.identifier}: required principles must match GPT separator principles",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("finite_evidence_refs", []), f"{gate.identifier}.finite_evidence_refs")
    if set(evidence_refs) != {"idt_bounded_correlation_demo", "gpt_principle_separator_demo"}:
        return [
            Issue(
                "bounded_correlation_carrier_lemma_evidence_mismatch",
                f"{gate.identifier}: finite evidence refs must link bounded-correlation and GPT separator witnesses",
            )
        ]

    excluded_counterexamples = require_string_tuple(
        gate.payload.get("excluded_counterexamples", []),
        f"{gate.identifier}.excluded_counterexamples",
    )
    expected_exclusion_count = parse_positive_integer(
        gate.payload.get("expected_exclusion_count"),
        f"{gate.identifier}.expected_exclusion_count",
    )
    if len(excluded_counterexamples) != expected_exclusion_count:
        return [
            Issue(
                "bounded_correlation_carrier_lemma_exclusion_count_mismatch",
                f"{gate.identifier}: expected {expected_exclusion_count} exclusions, got {len(excluded_counterexamples)}",
            )
        ]

    open_gaps = require_string_tuple(gate.payload.get("open_generalization_gaps", []), f"{gate.identifier}.open_generalization_gaps")
    conditional_refs = require_string_tuple(gate.payload.get("conditional_theorem_refs", []), f"{gate.identifier}.conditional_theorem_refs")
    expected_status = require_string(gate.payload.get("expected_lemma_status"), f"{gate.identifier}.expected_lemma_status")
    if expected_status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
        raise ManifestError(f"{gate.identifier}: expected_lemma_status is unknown")
    required_conditional_refs = {
        "bounded_correlation_screen_rejects_superquantum_boxes",
        "bounded_correlation_screen_theorem_demo",
    }
    if conditional_refs and set(conditional_refs) != required_conditional_refs:
        return [
            Issue(
                "bounded_correlation_carrier_lemma_conditional_refs_mismatch",
                f"{gate.identifier}: conditional theorem refs must link the bounded-correlation theorem",
            )
        ]
    if conditional_refs:
        computed_status = "conditional_proof"
    elif open_gaps:
        computed_status = "finite_witnessed"
    else:
        computed_status = "formal_proof"
    if computed_status != expected_status:
        return [
            Issue(
                "bounded_correlation_carrier_lemma_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_noncomplex_jordan_classification_lemma_route_gate(gate: FiniteGate) -> list[Issue]:
    target_lemma = require_string(gate.payload.get("target_lemma"), f"{gate.identifier}.target_lemma")
    if target_lemma != NONCOMPLEX_JORDAN_CLASSIFICATION_LEMMA_TARGET:
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_target_mismatch",
                f"{gate.identifier}: target lemma must be {NONCOMPLEX_JORDAN_CLASSIFICATION_LEMMA_TARGET}",
            )
        ]

    conditions = require_string_tuple(gate.payload.get("required_conditions", []), f"{gate.identifier}.required_conditions")
    if set(conditions) != set(NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS):
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_conditions_mismatch",
                f"{gate.identifier}: required conditions must match non-complex Jordan separator conditions",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("finite_evidence_refs", []), f"{gate.identifier}.finite_evidence_refs")
    if set(evidence_refs) != {"noncomplex_jordan_separator_demo"}:
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_evidence_mismatch",
                f"{gate.identifier}: finite evidence refs must link the non-complex Jordan separator witness",
            )
        ]

    excluded_counterexamples = require_string_tuple(
        gate.payload.get("excluded_counterexamples", []),
        f"{gate.identifier}.excluded_counterexamples",
    )
    expected_exclusion_count = parse_positive_integer(
        gate.payload.get("expected_exclusion_count"),
        f"{gate.identifier}.expected_exclusion_count",
    )
    if len(excluded_counterexamples) != expected_exclusion_count:
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_exclusion_count_mismatch",
                f"{gate.identifier}: expected {expected_exclusion_count} exclusions, got {len(excluded_counterexamples)}",
            )
        ]

    open_gaps = require_string_tuple(gate.payload.get("open_generalization_gaps", []), f"{gate.identifier}.open_generalization_gaps")
    conditional_refs = require_string_tuple(gate.payload.get("conditional_theorem_refs", []), f"{gate.identifier}.conditional_theorem_refs")
    expected_status = require_string(gate.payload.get("expected_lemma_status"), f"{gate.identifier}.expected_lemma_status")
    if expected_status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
        raise ManifestError(f"{gate.identifier}: expected_lemma_status is unknown")
    required_conditional_refs = {
        "noncomplex_jordan_separator_rejects_noncomplex_samples",
        "noncomplex_jordan_separator_theorem_demo",
    }
    if conditional_refs and set(conditional_refs) != required_conditional_refs:
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_conditional_refs_mismatch",
                f"{gate.identifier}: conditional theorem refs must link the non-complex Jordan theorem",
            )
        ]
    if conditional_refs:
        computed_status = "conditional_proof"
    elif open_gaps:
        computed_status = "finite_witnessed"
    else:
        computed_status = "formal_proof"
    if computed_status != expected_status:
        return [
            Issue(
                "noncomplex_jordan_classification_lemma_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_generic_gpt_classification_lemma_route_gate(gate: FiniteGate) -> list[Issue]:
    target_lemma = require_string(gate.payload.get("target_lemma"), f"{gate.identifier}.target_lemma")
    if target_lemma != GENERIC_GPT_CLASSIFICATION_LEMMA_TARGET:
        return [
            Issue(
                "generic_gpt_classification_lemma_target_mismatch",
                f"{gate.identifier}: target lemma must be {GENERIC_GPT_CLASSIFICATION_LEMMA_TARGET}",
            )
        ]

    conditions = require_string_tuple(gate.payload.get("required_conditions", []), f"{gate.identifier}.required_conditions")
    if set(conditions) != set(GENERIC_GPT_CLOSURE_CONDITIONS):
        return [
            Issue(
                "generic_gpt_classification_lemma_conditions_mismatch",
                f"{gate.identifier}: required conditions must match generic GPT closure separator conditions",
            )
        ]

    evidence_refs = require_string_tuple(gate.payload.get("finite_evidence_refs", []), f"{gate.identifier}.finite_evidence_refs")
    if set(evidence_refs) != {"generic_gpt_closure_separator_demo", "carrier_selection_frontier_demo"}:
        return [
            Issue(
                "generic_gpt_classification_lemma_evidence_mismatch",
                f"{gate.identifier}: finite evidence refs must link the generic GPT separator and carrier frontier",
            )
        ]

    excluded_counterexamples = require_string_tuple(
        gate.payload.get("excluded_counterexamples", []),
        f"{gate.identifier}.excluded_counterexamples",
    )
    expected_exclusion_count = parse_positive_integer(
        gate.payload.get("expected_exclusion_count"),
        f"{gate.identifier}.expected_exclusion_count",
    )
    if len(excluded_counterexamples) != expected_exclusion_count:
        return [
            Issue(
                "generic_gpt_classification_lemma_exclusion_count_mismatch",
                f"{gate.identifier}: expected {expected_exclusion_count} exclusions, got {len(excluded_counterexamples)}",
            )
        ]

    remaining_underdetermined = require_string_tuple(
        gate.payload.get("remaining_underdetermined_candidates", []),
        f"{gate.identifier}.remaining_underdetermined_candidates",
    )
    expected_underdetermined_count = parse_nonnegative_integer(
        gate.payload.get("expected_underdetermined_count"),
        f"{gate.identifier}.expected_underdetermined_count",
    )
    if len(remaining_underdetermined) != expected_underdetermined_count:
        return [
            Issue(
                "generic_gpt_classification_lemma_underdetermined_count_mismatch",
                (
                    f"{gate.identifier}: expected {expected_underdetermined_count} underdetermined candidates, "
                    f"got {len(remaining_underdetermined)}"
                ),
            )
        ]

    open_gaps = require_string_tuple(gate.payload.get("open_generalization_gaps", []), f"{gate.identifier}.open_generalization_gaps")
    conditional_refs = require_string_tuple(gate.payload.get("conditional_theorem_refs", []), f"{gate.identifier}.conditional_theorem_refs")
    expected_status = require_string(gate.payload.get("expected_lemma_status"), f"{gate.identifier}.expected_lemma_status")
    if expected_status not in CARRIER_SELECTION_PROOF_ROUTE_LEMMA_STATUSES:
        raise ManifestError(f"{gate.identifier}: expected_lemma_status is unknown")
    required_conditional_refs = {
        "generic_gpt_closure_rejects_unconstrained_cone",
        "generic_gpt_closure_theorem_demo",
    }
    if conditional_refs and set(conditional_refs) != required_conditional_refs:
        return [
            Issue(
                "generic_gpt_classification_lemma_conditional_refs_mismatch",
                f"{gate.identifier}: conditional theorem refs must link the generic GPT theorem",
            )
        ]
    if conditional_refs:
        computed_status = "conditional_proof"
    elif open_gaps or remaining_underdetermined:
        computed_status = "finite_witnessed"
    else:
        computed_status = "formal_proof"
    if computed_status != expected_status:
        return [
            Issue(
                "generic_gpt_classification_lemma_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_triple_path_sorkin_parameter_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    max_abs_kappa = parse_tolerance(gate.payload.get("max_abs_kappa"), f"{gate.identifier}.max_abs_kappa")
    weights = parse_vector(gate.payload.get("weights"), f"{gate.identifier}.weights")
    gamma = parse_matrix(gate.payload.get("gamma"), f"{gate.identifier}.gamma")
    events = require_mapping(gate.payload.get("events"), f"{gate.identifier}.events")
    event_a = parse_index_tuple(events.get("A"), f"{gate.identifier}.events.A")
    event_b = parse_index_tuple(events.get("B"), f"{gate.identifier}.events.B")
    event_c = parse_index_tuple(events.get("C"), f"{gate.identifier}.events.C")
    validate_events((event_a, event_b, event_c), len(weights), len(gamma))
    if set(event_a) & set(event_b) or set(event_a) & set(event_c) or set(event_b) & set(event_c):
        raise ManifestError("Sorkin events must be pairwise disjoint")
    if matrix_psd_issues(f"{gate.identifier}.gamma", gamma, tolerance):
        return [Issue("sorkin_kernel_not_psd", f"{gate.identifier}: gamma is not PSD")]
    i3_value = sorkin_i3(event_a, event_b, event_c, weights, gamma)
    denominator = (
        abs(second_order_interference(event_a, event_b, weights, gamma))
        + abs(second_order_interference(event_a, event_c, weights, gamma))
        + abs(second_order_interference(event_b, event_c, weights, gamma))
    )
    if denominator <= tolerance:
        raise ManifestError("Sorkin normalization denominator must be positive")
    kappa = abs(i3_value) / denominator
    if kappa > max_abs_kappa + tolerance:
        return [
            Issue(
                "sorkin_parameter_exceeds_bound",
                f"{gate.identifier}: kappa {kappa:g} exceeds {max_abs_kappa:g}",
            )
        ]
    return []


def check_marker_eraser_visibility_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    initial_visibility = parse_real(gate.payload.get("initial_visibility"), f"{gate.identifier}.initial_visibility")
    if initial_visibility < 0.0 or initial_visibility > 1.0 + tolerance:
        raise ManifestError("initial_visibility must be in [0, 1]")
    marker_overlap = parse_complex(gate.payload.get("marker_overlap"), f"{gate.identifier}.marker_overlap")
    marker_magnitude = abs(marker_overlap)
    if marker_magnitude > 1.0 + tolerance:
        raise ManifestError("marker_overlap magnitude must not exceed one")
    marked_visibility = initial_visibility * min(1.0, marker_magnitude)
    distinguishability = math.sqrt(max(0.0, 1.0 - (min(1.0, marker_magnitude) ** 2)))
    expected_marked_visibility = parse_real(
        gate.payload.get("expected_marked_visibility"),
        f"{gate.identifier}.expected_marked_visibility",
    )
    expected_distinguishability = parse_real(
        gate.payload.get("expected_distinguishability"),
        f"{gate.identifier}.expected_distinguishability",
    )
    if abs(marked_visibility - expected_marked_visibility) > tolerance:
        return [
            Issue(
                "marker_visibility_mismatch",
                f"{gate.identifier}: expected marked visibility {expected_marked_visibility:g}, "
                f"computed {marked_visibility:g}",
            )
        ]
    if abs(distinguishability - expected_distinguishability) > tolerance:
        return [
            Issue(
                "marker_distinguishability_mismatch",
                f"{gate.identifier}: expected distinguishability {expected_distinguishability:g}, "
                f"computed {distinguishability:g}",
            )
        ]
    conditioned_raw = gate.payload.get("conditioned_overlap")
    if conditioned_raw is not None:
        conditioned_overlap = parse_complex(conditioned_raw, f"{gate.identifier}.conditioned_overlap")
        conditioned_magnitude = abs(conditioned_overlap)
        if conditioned_magnitude > 1.0 + tolerance:
            raise ManifestError("conditioned_overlap magnitude must not exceed one")
        erased_visibility = initial_visibility * min(1.0, conditioned_magnitude)
        expected_erased_visibility = parse_real(
            gate.payload.get("expected_erased_visibility"),
            f"{gate.identifier}.expected_erased_visibility",
        )
        if abs(erased_visibility - expected_erased_visibility) > tolerance:
            return [
                Issue(
                    "eraser_visibility_mismatch",
                    f"{gate.identifier}: expected erased visibility {expected_erased_visibility:g}, "
                    f"computed {erased_visibility:g}",
                )
            ]
    return []


def check_bell_chsh_table_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    expected_abs_s = parse_real(gate.payload.get("expected_abs_s"), f"{gate.identifier}.expected_abs_s")
    max_abs_s = parse_real(gate.payload.get("max_abs_s"), f"{gate.identifier}.max_abs_s")
    contexts = parse_bell_contexts(gate.payload.get("contexts"), f"{gate.identifier}.contexts")
    for key, table in contexts.items():
        context_sum = sum(table.values())
        if abs(context_sum - 1.0) > tolerance:
            return [Issue("bell_context_not_normalized", f"{gate.identifier}: context {key} is not normalized")]
        if any(probability < -tolerance for probability in table.values()):
            return [Issue("bell_negative_probability", f"{gate.identifier}: context {key} has negative probability")]
    signalling_issue = bell_no_signalling_issue(gate.identifier, contexts, tolerance)
    if signalling_issue is not None:
        return [signalling_issue]
    correlations = {key: bell_correlation(table) for key, table in contexts.items()}
    required_keys = ((0, 0), (0, 1), (1, 0), (1, 1))
    if any(key not in correlations for key in required_keys):
        raise ManifestError("Bell CHSH gate requires contexts (0,0), (0,1), (1,0), (1,1)")
    s_value = correlations[(0, 0)] + correlations[(0, 1)] + correlations[(1, 0)] - correlations[(1, 1)]
    abs_s = abs(s_value)
    if abs(abs_s - expected_abs_s) > tolerance:
        return [
            Issue(
                "bell_chsh_mismatch",
                f"{gate.identifier}: expected |S| {expected_abs_s:g}, computed {abs_s:g}",
            )
        ]
    if abs_s > max_abs_s + tolerance:
        return [
            Issue(
                "bell_chsh_bound_exceeded",
                f"{gate.identifier}: |S| {abs_s:g} exceeds {max_abs_s:g}",
            )
        ]
    return []


def check_bell_chsh_from_amplitudes_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    expected_abs_s = parse_real(gate.payload.get("expected_abs_s"), f"{gate.identifier}.expected_abs_s")
    max_abs_s = parse_real(gate.payload.get("max_abs_s"), f"{gate.identifier}.max_abs_s")
    amplitude_contexts = parse_bell_amplitude_contexts(
        gate.payload.get("contexts"),
        f"{gate.identifier}.contexts",
    )
    contexts = {
        key: bell_probabilities_from_amplitudes(value, tolerance)
        for key, value in amplitude_contexts.items()
    }
    for key, table in contexts.items():
        context_sum = sum(table.values())
        if abs(context_sum - 1.0) > tolerance:
            return [Issue("bell_context_not_normalized", f"{gate.identifier}: context {key} is not normalized")]
    signalling_issue = bell_no_signalling_issue(gate.identifier, contexts, tolerance)
    if signalling_issue is not None:
        return [signalling_issue]
    correlations = {key: bell_correlation(table) for key, table in contexts.items()}
    required_keys = ((0, 0), (0, 1), (1, 0), (1, 1))
    if any(key not in correlations for key in required_keys):
        raise ManifestError("Bell CHSH amplitude gate requires contexts (0,0), (0,1), (1,0), (1,1)")
    s_value = correlations[(0, 0)] + correlations[(0, 1)] + correlations[(1, 0)] - correlations[(1, 1)]
    abs_s = abs(s_value)
    if abs(abs_s - expected_abs_s) > tolerance:
        return [
            Issue(
                "bell_chsh_mismatch",
                f"{gate.identifier}: expected |S| {expected_abs_s:g}, computed {abs_s:g}",
            )
        ]
    if abs_s > max_abs_s + tolerance:
        return [
            Issue(
                "bell_chsh_bound_exceeded",
                f"{gate.identifier}: |S| {abs_s:g} exceeds {max_abs_s:g}",
            )
        ]
    return []


def check_spin_bell_angle_model_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    expected_abs_s = parse_real(gate.payload.get("expected_abs_s"), f"{gate.identifier}.expected_abs_s")
    max_abs_s = parse_real(gate.payload.get("max_abs_s"), f"{gate.identifier}.max_abs_s")
    alice_angles = parse_real_list(gate.payload.get("alice_angles"), f"{gate.identifier}.alice_angles")
    bob_angles = parse_real_list(gate.payload.get("bob_angles"), f"{gate.identifier}.bob_angles")
    if len(alice_angles) != 2 or len(bob_angles) != 2:
        raise ManifestError("spin Bell angle model requires two Alice and two Bob angles")
    contexts: dict[tuple[int, int], dict[tuple[int, int], float]] = {}
    for x_value, alice_angle in enumerate(alice_angles):
        for y_value, bob_angle in enumerate(bob_angles):
            contexts[(x_value, y_value)] = singlet_spin_probabilities(alice_angle - bob_angle)
    signalling_issue = bell_no_signalling_issue(gate.identifier, contexts, tolerance)
    if signalling_issue is not None:
        return [signalling_issue]
    correlations = {key: bell_correlation(table) for key, table in contexts.items()}
    s_value = correlations[(0, 0)] + correlations[(0, 1)] + correlations[(1, 0)] - correlations[(1, 1)]
    abs_s = abs(s_value)
    if abs(abs_s - expected_abs_s) > tolerance:
        return [
            Issue(
                "spin_bell_chsh_mismatch",
                f"{gate.identifier}: expected |S| {expected_abs_s:g}, computed {abs_s:g}",
            )
        ]
    if abs_s > max_abs_s + tolerance:
        return [
            Issue(
                "spin_bell_bound_exceeded",
                f"{gate.identifier}: |S| {abs_s:g} exceeds {max_abs_s:g}",
            )
        ]
    return []


def check_unitary_generator_reconstruction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    dt = parse_real(gate.payload.get("dt"), f"{gate.identifier}.dt")
    if abs(dt) <= tolerance:
        raise ManifestError("dt must be nonzero")
    omegas = parse_real_list(gate.payload.get("omegas"), f"{gate.identifier}.omegas")
    expected_unitary = parse_matrix(
        gate.payload.get("expected_unitary"), f"{gate.identifier}.expected_unitary"
    )
    validate_square_block(expected_unitary, "expected_unitary")
    if len(expected_unitary) != len(omegas):
        raise ManifestError("expected_unitary size must match omegas")
    computed_unitary = diagonal_phase_matrix([-dt * omega for omega in omegas])
    if not matrices_close(computed_unitary, expected_unitary, tolerance):
        return [
            Issue(
                "unitary_generator_mismatch",
                f"{gate.identifier}: U(dt) does not match exp(-i dt Omega)",
            )
        ]
    validate_unitary(computed_unitary, tolerance, "computed_unitary")

    hbar_raw = gate.payload.get("hbar")
    expected_hamiltonian_raw = gate.payload.get("expected_hamiltonian")
    if hbar_raw is not None or expected_hamiltonian_raw is not None:
        hbar = parse_real(hbar_raw, f"{gate.identifier}.hbar")
        expected_hamiltonian = parse_real_list(
            expected_hamiltonian_raw, f"{gate.identifier}.expected_hamiltonian"
        )
        if len(expected_hamiltonian) != len(omegas):
            raise ManifestError("expected_hamiltonian size must match omegas")
        computed_hamiltonian = [hbar * omega for omega in omegas]
        if not real_lists_close(computed_hamiltonian, expected_hamiltonian, tolerance):
            return [
                Issue(
                    "hamiltonian_scale_mismatch",
                    f"{gate.identifier}: H diagonal does not match hbar*Omega",
                )
            ]
    return []


def check_translation_de_broglie_scale_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    shift = parse_real(gate.payload.get("shift"), f"{gate.identifier}.shift")
    wave_numbers = parse_real_list(gate.payload.get("wave_numbers"), f"{gate.identifier}.wave_numbers")
    hbar = parse_real(gate.payload.get("hbar"), f"{gate.identifier}.hbar")
    expected_translation = parse_matrix(
        gate.payload.get("expected_translation"), f"{gate.identifier}.expected_translation"
    )
    validate_square_block(expected_translation, "expected_translation")
    if len(expected_translation) != len(wave_numbers):
        raise ManifestError("expected_translation size must match wave_numbers")
    computed_translation = diagonal_phase_matrix([-shift * wave_number for wave_number in wave_numbers])
    if not matrices_close(computed_translation, expected_translation, tolerance):
        return [
            Issue(
                "translation_generator_mismatch",
                f"{gate.identifier}: T(a) does not match exp(-i a k)",
            )
        ]
    validate_unitary(computed_translation, tolerance, "computed_translation")

    expected_momenta = parse_real_list(gate.payload.get("expected_momenta"), f"{gate.identifier}.expected_momenta")
    if len(expected_momenta) != len(wave_numbers):
        raise ManifestError("expected_momenta size must match wave_numbers")
    computed_momenta = [hbar * wave_number for wave_number in wave_numbers]
    if not real_lists_close(computed_momenta, expected_momenta, tolerance):
        return [
            Issue(
                "momentum_scale_mismatch",
                f"{gate.identifier}: p values do not match hbar*k",
            )
        ]

    expected_wavelengths = parse_real_list(
        gate.payload.get("expected_wavelengths"), f"{gate.identifier}.expected_wavelengths"
    )
    if len(expected_wavelengths) != len(wave_numbers):
        raise ManifestError("expected_wavelengths size must match wave_numbers")
    computed_wavelengths = []
    for wave_number in wave_numbers:
        if abs(wave_number) <= tolerance:
            raise ManifestError("wave_numbers must be nonzero for de Broglie wavelength")
        computed_wavelengths.append((2.0 * math.pi) / abs(wave_number))
    if not real_lists_close(computed_wavelengths, expected_wavelengths, tolerance):
        return [
            Issue(
                "de_broglie_mismatch",
                f"{gate.identifier}: wavelengths do not match 2*pi/|k|",
            )
        ]
    return []


def check_finite_weyl_relation_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    dimension = parse_integer(gate.payload.get("dimension"), f"{gate.identifier}.dimension")
    if dimension < 2 or dimension > 12:
        raise ManifestError("finite Weyl dimension must be between 2 and 12")
    expected_phase = parse_real(gate.payload.get("expected_phase"), f"{gate.identifier}.expected_phase")
    if abs(expected_phase - ((2.0 * math.pi) / dimension)) > tolerance:
        return [
            Issue(
                "weyl_phase_mismatch",
                f"{gate.identifier}: expected phase does not match 2*pi/N",
            )
        ]
    clock = finite_clock_matrix(dimension)
    shift = finite_shift_matrix(dimension)
    left = matrix_multiply(clock, shift)
    right = scalar_multiply_matrix(complex(math.cos(expected_phase), math.sin(expected_phase)), matrix_multiply(shift, clock))
    if not matrices_close(left, right, tolerance):
        return [
            Issue(
                "weyl_relation_mismatch",
                f"{gate.identifier}: ZX does not match exp(2*pi*i/N)XZ",
            )
        ]
    return []


def check_pointer_sector_stability_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    kernel = parse_matrix(gate.payload.get("pointer_kernel"), f"{gate.identifier}.pointer_kernel")
    max_offdiag = parse_tolerance(gate.payload.get("max_offdiag"), f"{gate.identifier}.max_offdiag")
    expected_stable = parse_bool(gate.payload.get("expected_stable"), f"{gate.identifier}.expected_stable")
    validate_square_block(kernel, "pointer_kernel")
    if matrix_psd_issues(f"{gate.identifier}.pointer_kernel", kernel, tolerance):
        return [Issue("pointer_kernel_not_psd", f"{gate.identifier}: pointer kernel is not PSD")]
    for index, row in enumerate(kernel):
        if abs(row[index] - 1.0) > tolerance:
            raise ManifestError("pointer kernel diagonal must be normalized to one")
    stable = max_off_diagonal_abs(kernel) <= max_offdiag + tolerance
    if stable != expected_stable:
        return [
            Issue(
                "pointer_sector_stability_mismatch",
                f"{gate.identifier}: expected stable={expected_stable}, computed stable={stable}",
            )
        ]
    if not stable:
        return [
            Issue(
                "pointer_sector_not_stable",
                f"{gate.identifier}: pointer sectors exceed off-diagonal distinguishability bound",
            )
        ]
    return []


def check_premeasurement_decoherence_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitudes = parse_vector(gate.payload.get("amplitudes"), f"{gate.identifier}.amplitudes")
    environment_kernel = parse_matrix(
        gate.payload.get("environment_kernel"),
        f"{gate.identifier}.environment_kernel",
    )
    expected_probabilities = parse_real_list(
        gate.payload.get("expected_probabilities"),
        f"{gate.identifier}.expected_probabilities",
    )
    max_residual_coherence = parse_tolerance(
        gate.payload.get("max_residual_coherence"),
        f"{gate.identifier}.max_residual_coherence",
    )
    validate_square_block(environment_kernel, "environment_kernel")
    if len(environment_kernel) != len(amplitudes):
        raise ManifestError("environment kernel size must match amplitudes")
    if len(expected_probabilities) != len(amplitudes):
        raise ManifestError("expected probabilities size must match amplitudes")
    if matrix_psd_issues(f"{gate.identifier}.environment_kernel", environment_kernel, tolerance):
        return [Issue("environment_kernel_not_psd", f"{gate.identifier}: environment kernel is not PSD")]
    probabilities = amplitude_probabilities(amplitudes, tolerance)
    if not real_lists_close(probabilities, expected_probabilities, tolerance):
        return [
            Issue(
                "premeasurement_probability_mismatch",
                f"{gate.identifier}: Born weights do not match expected probabilities",
            )
        ]
    residual = reduced_density_max_offdiag(amplitudes, environment_kernel)
    if residual > max_residual_coherence + tolerance:
        return [
            Issue(
                "premeasurement_residual_coherence",
                f"{gate.identifier}: residual coherence {residual:g} exceeds {max_residual_coherence:g}",
            )
        ]
    return []


def check_recoverability_loss_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    observed_visibility = parse_real(gate.payload.get("observed_visibility"), f"{gate.identifier}.observed_visibility")
    environment_visibility = parse_real(
        gate.payload.get("environment_recoverable_visibility"),
        f"{gate.identifier}.environment_recoverable_visibility",
    )
    expected_lambda = parse_real(gate.payload.get("expected_lambda"), f"{gate.identifier}.expected_lambda")
    facticity_threshold = parse_real(
        gate.payload.get("facticity_threshold"),
        f"{gate.identifier}.facticity_threshold",
    )
    expected_facticity = parse_bool(gate.payload.get("expected_facticity"), f"{gate.identifier}.expected_facticity")
    if environment_visibility <= tolerance:
        raise ManifestError("environment_recoverable_visibility must be positive")
    if observed_visibility < -tolerance:
        raise ManifestError("observed_visibility must be non-negative")
    if observed_visibility - environment_visibility > tolerance:
        raise ManifestError("observed_visibility must not exceed environment_recoverable_visibility")
    recoverability_loss = -math.log(max(observed_visibility, tolerance) / environment_visibility)
    if abs(recoverability_loss - expected_lambda) > tolerance:
        return [
            Issue(
                "recoverability_loss_mismatch",
                f"{gate.identifier}: expected lambda {expected_lambda:g}, computed {recoverability_loss:g}",
            )
        ]
    computed_facticity = recoverability_loss >= facticity_threshold - tolerance
    if computed_facticity != expected_facticity:
        return [
            Issue(
                "facticity_threshold_mismatch",
                f"{gate.identifier}: expected facticity={expected_facticity}, computed {computed_facticity}",
            )
        ]
    return []


def check_one_parameter_unitary_flow_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    omegas = parse_real_list(gate.payload.get("omegas"), f"{gate.identifier}.omegas")
    times = parse_real_list(gate.payload.get("times"), f"{gate.identifier}.times")
    if not omegas:
        raise ManifestError("omegas must not be empty")
    if not any(abs(time) <= tolerance for time in times):
        raise ManifestError("times must include zero")
    expected_pairs = parse_flow_pairs(gate.payload.get("pairs"), f"{gate.identifier}.pairs")
    for time in times:
        unitary = diagonal_phase_matrix([-time * omega for omega in omegas])
        validate_unitary(unitary, tolerance, "unitary_flow")
        if abs(time) <= tolerance and not matrices_close(unitary, identity_matrix(len(omegas)), tolerance):
            return [Issue("unitary_flow_identity_mismatch", f"{gate.identifier}: U(0) is not identity")]
    for left_time, right_time, sum_time in expected_pairs:
        left = diagonal_phase_matrix([-left_time * omega for omega in omegas])
        right = diagonal_phase_matrix([-right_time * omega for omega in omegas])
        expected = diagonal_phase_matrix([-sum_time * omega for omega in omegas])
        composed = matrix_multiply(left, right)
        if not matrices_close(composed, expected, tolerance):
            return [
                Issue(
                    "unitary_flow_group_law_mismatch",
                    f"{gate.identifier}: U(t)U(s) does not match U(t+s)",
                )
            ]
    return []


def check_strong_continuity_modulus_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    omegas = parse_real_list(gate.payload.get("omegas"), f"{gate.identifier}.omegas")
    max_time = parse_tolerance(gate.payload.get("max_time"), f"{gate.identifier}.max_time")
    max_deviation = parse_tolerance(gate.payload.get("max_deviation"), f"{gate.identifier}.max_deviation")
    if not omegas:
        raise ManifestError("omegas must not be empty")
    samples = parse_real_list(gate.payload.get("samples"), f"{gate.identifier}.samples")
    for sample in samples:
        if abs(sample) > max_time + tolerance:
            raise ManifestError("samples must be inside max_time")
        deviation = max(abs(complex(math.cos(-sample * omega), math.sin(-sample * omega)) - 1.0) for omega in omegas)
        if deviation > max_deviation + tolerance:
            return [
                Issue(
                    "strong_continuity_modulus_exceeded",
                    f"{gate.identifier}: deviation {deviation:g} exceeds {max_deviation:g}",
                )
            ]
    return []


def check_generator_difference_convergence_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    omega = parse_real(gate.payload.get("omega"), f"{gate.identifier}.omega")
    steps = parse_positive_real_vector(gate.payload.get("steps"), f"{gate.identifier}.steps")
    max_error = parse_tolerance(gate.payload.get("max_error"), f"{gate.identifier}.max_error")
    previous_error: float | None = None
    for step in steps:
        estimated = -wrapped_angle(-omega * step) / step
        error = abs(estimated - omega)
        if error > max_error + tolerance:
            return [
                Issue(
                    "generator_difference_error_exceeded",
                    f"{gate.identifier}: generator estimate error {error:g} exceeds {max_error:g}",
                )
            ]
        if previous_error is not None and error > previous_error + tolerance:
            return [
                Issue(
                    "generator_difference_not_convergent",
                    f"{gate.identifier}: generator estimate error increased",
                )
            ]
        previous_error = error
    return []


def check_action_standard_provenance_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    action_standard_status = require_string(
        gate.payload.get("action_standard_status"),
        f"{gate.identifier}.action_standard_status",
    )
    normalization_only = parse_bool(
        gate.payload.get("normalization_only"),
        f"{gate.identifier}.normalization_only",
    )
    claims_physical_hbar = parse_bool(
        gate.payload.get("claims_physical_hbar"),
        f"{gate.identifier}.claims_physical_hbar",
    )
    if not candidate_sources:
        raise ManifestError("candidate_sources must not be empty")
    if action_standard_status not in {"candidate", "derived_independent"}:
        raise ManifestError("action_standard_status must be candidate or derived_independent")
    overlap = sorted(candidate_sources & forbidden_sources)
    if overlap:
        return [
            Issue(
                "action_standard_forbidden_source",
                f"{gate.identifier}: action standard uses forbidden sources: {', '.join(overlap)}",
            )
        ]
    if claims_physical_hbar and normalization_only:
        return [
            Issue(
                "hbar_physical_claim_from_normalization",
                f"{gate.identifier}: normalization-only action unit cannot support a physical hbar claim",
            )
        ]
    if claims_physical_hbar and action_standard_status != "derived_independent":
        return [
            Issue(
                "hbar_physical_claim_without_independent_action",
                f"{gate.identifier}: physical hbar claim requires an independently derived action standard",
            )
        ]
    return []


def check_ell0_radar_consistency_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    round_trip_time = parse_positive_real(
        gate.payload.get("round_trip_time"),
        f"{gate.identifier}.round_trip_time",
    )
    order_weight = parse_positive_real(gate.payload.get("order_weight"), f"{gate.identifier}.order_weight")
    expected_ell0 = parse_positive_real(gate.payload.get("expected_ell0"), f"{gate.identifier}.expected_ell0")
    computed_ell0 = c_value * round_trip_time / (2.0 * order_weight)
    if abs(computed_ell0 - expected_ell0) > tolerance:
        return [
            Issue(
                "ell0_radar_consistency_mismatch",
                f"{gate.identifier}: expected ell0 {expected_ell0:g}, computed {computed_ell0:g}",
            )
        ]
    return []


def check_ell0_link_frequency_consistency_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    omega_link = parse_positive_real(gate.payload.get("omega_link"), f"{gate.identifier}.omega_link")
    expected_ell0 = parse_positive_real(gate.payload.get("expected_ell0"), f"{gate.identifier}.expected_ell0")
    computed_ell0 = c_value / omega_link
    if abs(computed_ell0 - expected_ell0) > tolerance:
        return [
            Issue(
                "ell0_link_frequency_mismatch",
                f"{gate.identifier}: expected ell0 {expected_ell0:g}, computed {computed_ell0:g}",
            )
        ]
    return []


def check_ell0_no_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    ell0_status = require_string(gate.payload.get("ell0_status"), f"{gate.identifier}.ell0_status")
    claims_physical_length = parse_bool(
        gate.payload.get("claims_physical_length"),
        f"{gate.identifier}.claims_physical_length",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        ell0_status,
        claims_physical_length,
        "length",
    )


def check_clock_vacuum_pole_candidate_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    candidate_edges = parse_positive_real_vector(
        gate.payload.get("candidate_edges"),
        f"{gate.identifier}.candidate_edges",
    )
    expected_omega_link = parse_positive_real(
        gate.payload.get("expected_omega_link"),
        f"{gate.identifier}.expected_omega_link",
    )
    computed_omega_link = min(candidate_edges)
    if relative_error(computed_omega_link, expected_omega_link) > tolerance:
        return [
            Issue(
                "clock_vacuum_pole_mismatch",
                f"{gate.identifier}: expected omega_ell {expected_omega_link:g}, computed {computed_omega_link:g}",
            )
        ]
    return []


def check_clock_vacuum_pole_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    species_omega_values = parse_positive_real_vector(
        gate.payload.get("species_omega_values"),
        f"{gate.identifier}.species_omega_values",
    )
    if relative_spread(species_omega_values) > tolerance:
        return [
            Issue(
                "clock_vacuum_pole_universality_failed",
                f"{gate.identifier}: species pole spread exceeds tolerance",
            )
        ]
    return []


def check_clock_vacuum_pole_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    pole_status = require_string(gate.payload.get("pole_status"), f"{gate.identifier}.pole_status")
    claims_physical_frequency = parse_bool(
        gate.payload.get("claims_physical_frequency"),
        f"{gate.identifier}.claims_physical_frequency",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        pole_status,
        claims_physical_frequency,
        "clock_vacuum_pole",
    )


def check_ell0_candidate_from_clock_pole_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    omega_link = parse_positive_real(gate.payload.get("omega_link"), f"{gate.identifier}.omega_link")
    expected_ell0 = parse_positive_real(gate.payload.get("expected_ell0"), f"{gate.identifier}.expected_ell0")
    computed_ell0 = c_value / omega_link
    if relative_error(computed_ell0, expected_ell0) > tolerance:
        return [
            Issue(
                "ell0_clock_pole_candidate_mismatch",
                f"{gate.identifier}: expected ell0 {expected_ell0:g}, computed {computed_ell0:g}",
            )
        ]
    return []


def check_ell0_candidate_no_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    ell0_status = require_string(gate.payload.get("ell0_status"), f"{gate.identifier}.ell0_status")
    claims_physical_length = parse_bool(
        gate.payload.get("claims_physical_length"),
        f"{gate.identifier}.claims_physical_length",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        ell0_status,
        claims_physical_length,
        "length",
    )


def check_ell0_bound_not_value_gate(gate: FiniteGate) -> list[Issue]:
    bound_status = require_string(gate.payload.get("bound_status"), f"{gate.identifier}.bound_status")
    if bound_status not in {"lower_bound", "upper_bound", "derived_conditional"}:
        raise ManifestError(f"{gate.identifier}.bound_status must be a bound-only status")
    uses_bound_only_input = parse_bool(
        gate.payload.get("uses_bound_only_input"),
        f"{gate.identifier}.uses_bound_only_input",
    )
    claims_exact_length = parse_bool(
        gate.payload.get("claims_exact_length"),
        f"{gate.identifier}.claims_exact_length",
    )
    if uses_bound_only_input and claims_exact_length:
        return [
            Issue(
                "ell0_bound_used_as_value",
                f"{gate.identifier}: bound-only evidence cannot be promoted to an exact ell0 value",
            )
        ]
    return []


def check_spectral_law_free_parameter_audit_gate(gate: FiniteGate) -> list[Issue]:
    free_parameters = require_string_tuple(
        gate.payload.get("free_parameters"),
        f"{gate.identifier}.free_parameters",
    )
    claims_predictive = parse_bool(
        gate.payload.get("claims_predictive"),
        f"{gate.identifier}.claims_predictive",
    )
    if claims_predictive and free_parameters:
        return [
            Issue(
                "spectral_law_parametric_not_predictive",
                f"{gate.identifier}: predictive spectral law still has free parameters: "
                f"{', '.join(free_parameters)}",
            )
        ]
    return []


def check_spectral_law_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    spectral_law_status = require_string(
        gate.payload.get("spectral_law_status"),
        f"{gate.identifier}.spectral_law_status",
    )
    claims_physical_spectral_law = parse_bool(
        gate.payload.get("claims_physical_spectral_law"),
        f"{gate.identifier}.claims_physical_spectral_law",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        spectral_law_status,
        claims_physical_spectral_law,
        "spectral_law",
    )


def check_fixed_point_component_status_gate(gate: FiniteGate) -> list[Issue]:
    component_map = require_mapping(gate.payload.get("components"), f"{gate.identifier}.components")
    component_statuses = {
        key: require_string(value, f"{gate.identifier}.components.{key}") for key, value in component_map.items()
    }
    claims_predictive = parse_bool(
        gate.payload.get("claims_predictive"),
        f"{gate.identifier}.claims_predictive",
    )
    if claims_predictive:
        blocked = sorted(
            component
            for component, status in component_statuses.items()
            if status not in {"derived", "derived_independent"}
        )
        if blocked:
            return [
                Issue(
                    "fixed_point_route_underived",
                    f"{gate.identifier}: predictive fixed-point route has underived components: "
                    f"{', '.join(blocked)}",
                )
            ]
    return []


def check_non_exact_holonomy_source_gate(gate: FiniteGate) -> list[Issue]:
    source_status = require_string(gate.payload.get("source_status"), f"{gate.identifier}.source_status")
    exact_cocycle = parse_bool(gate.payload.get("exact_cocycle"), f"{gate.identifier}.exact_cocycle")
    claims_nontrivial_rotation = parse_bool(
        gate.payload.get("claims_nontrivial_rotation"),
        f"{gate.identifier}.claims_nontrivial_rotation",
    )
    if not claims_nontrivial_rotation:
        return []
    if exact_cocycle:
        return [
            Issue(
                "nonexact_holonomy_missing",
                f"{gate.identifier}: exact cocycle cannot support nontrivial fixed-point rotation",
            )
        ]
    if source_status not in {"derived", "derived_independent"}:
        return [
            Issue(
                "nonexact_holonomy_source_underived",
                f"{gate.identifier}: non-exact holonomy source is {source_status}, not derived",
            )
        ]
    return []


def check_rho_chi_protocol_invariance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    expected_rho = parse_positive_real(gate.payload.get("expected_rho"), f"{gate.identifier}.expected_rho")
    protocol_items = require_list(gate.payload.get("protocols"), f"{gate.identifier}.protocols")
    rho_values: list[float] = []
    for index, item in enumerate(protocol_items):
        protocol = require_mapping(item, f"{gate.identifier}.protocols[{index}]")
        eta_tau = parse_positive_real(
            protocol.get("eta_tau"),
            f"{gate.identifier}.protocols[{index}].eta_tau",
        )
        c_chi = parse_positive_real(
            protocol.get("C_chi"),
            f"{gate.identifier}.protocols[{index}].C_chi",
        )
        rho_values.append(eta_tau / c_chi)
    for rho_value in rho_values:
        if relative_error(rho_value, expected_rho) > tolerance:
            return [
                Issue(
                    "rho_chi_protocol_mismatch",
                    f"{gate.identifier}: expected rho {expected_rho:g}, computed {rho_value:g}",
                )
            ]
    if relative_spread(rho_values) > tolerance:
        return [
            Issue(
                "rho_chi_protocol_not_invariant",
                f"{gate.identifier}: rho_chi varies across sampling protocols",
            )
        ]
    return []


def check_rho_chi_no_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    rho_status = require_string(gate.payload.get("rho_status"), f"{gate.identifier}.rho_status")
    claims_physical_rho = parse_bool(
        gate.payload.get("claims_physical_rho"),
        f"{gate.identifier}.claims_physical_rho",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        rho_status,
        claims_physical_rho,
        "rho_chi",
    )


def check_kappa_omega_consistency_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    hbar_value = parse_positive_real(gate.payload.get("hbar_value"), f"{gate.identifier}.hbar_value")
    omega_link = parse_positive_real(gate.payload.get("omega_link"), f"{gate.identifier}.omega_link")
    rho_chi = parse_positive_real(gate.payload.get("rho_chi"), f"{gate.identifier}.rho_chi")
    expected_kappa = parse_positive_real(gate.payload.get("expected_kappa"), f"{gate.identifier}.expected_kappa")
    computed_kappa = hbar_value * omega_link / rho_chi
    if relative_error(computed_kappa, expected_kappa) > tolerance:
        return [
            Issue(
                "kappa_omega_consistency_mismatch",
                f"{gate.identifier}: expected kappa {expected_kappa:g}, computed {computed_kappa:g}",
            )
        ]
    return []


def check_kappa_omega_no_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    relation_status = require_string(gate.payload.get("relation_status"), f"{gate.identifier}.relation_status")
    claims_physical_relation = parse_bool(
        gate.payload.get("claims_physical_relation"),
        f"{gate.identifier}.claims_physical_relation",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        relation_status,
        claims_physical_relation,
        "kappa_omega",
    )


def check_contraction_phase_degeneracy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    recoverability_scores = parse_positive_real_vector(
        gate.payload.get("recoverability_scores"),
        f"{gate.identifier}.recoverability_scores",
    )
    phase_values = parse_real_list(gate.payload.get("phase_values"), f"{gate.identifier}.phase_values")
    claims_unique_selection = parse_bool(
        gate.payload.get("claims_unique_selection"),
        f"{gate.identifier}.claims_unique_selection",
    )
    if len(recoverability_scores) != len(phase_values):
        raise ManifestError(f"{gate.identifier}: recoverability_scores and phase_values must have equal length")
    if len(recoverability_scores) < 2:
        raise ManifestError(f"{gate.identifier}: at least two candidate contractions are required")

    score_spread = relative_spread(recoverability_scores)
    sorted_phases = sorted(wrapped_angle(phase) for phase in phase_values)
    phase_span = max(sorted_phases) - min(sorted_phases)
    if claims_unique_selection and score_spread <= tolerance and phase_span > tolerance:
        return [
            Issue(
                "contraction_phase_degeneracy",
                f"{gate.identifier}: equal recoverability leaves distinct contraction phases",
            )
        ]
    return []


def check_support_matching_phase_freedom_gate(gate: FiniteGate) -> list[Issue]:
    unique_support_matching = parse_bool(
        gate.payload.get("unique_support_matching"),
        f"{gate.identifier}.unique_support_matching",
    )
    diagonal_phase_freedom = parse_bool(
        gate.payload.get("diagonal_phase_freedom"),
        f"{gate.identifier}.diagonal_phase_freedom",
    )
    claims_phase_selected = parse_bool(
        gate.payload.get("claims_phase_selected"),
        f"{gate.identifier}.claims_phase_selected",
    )
    if unique_support_matching and diagonal_phase_freedom and claims_phase_selected:
        return [
            Issue(
                "support_matching_phase_unselected",
                f"{gate.identifier}: support matching can select transport but not diagonal phase",
            )
        ]
    return []


def check_contraction_selection_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    selection_status = require_string(
        gate.payload.get("selection_status"),
        f"{gate.identifier}.selection_status",
    )
    claims_physical_selection = parse_bool(
        gate.payload.get("claims_physical_selection"),
        f"{gate.identifier}.claims_physical_selection",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        selection_status,
        claims_physical_selection,
        "contraction_selection",
    )


def check_fixed_point_step_integer_obstruction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    cycle_steps = parse_positive_integer(gate.payload.get("cycle_steps"), f"{gate.identifier}.cycle_steps")
    winding = parse_positive_integer(gate.payload.get("winding"), f"{gate.identifier}.winding")
    half_radar_steps = parse_positive_integer(
        gate.payload.get("half_radar_steps"),
        f"{gate.identifier}.half_radar_steps",
    )
    claims_exact_compatibility = parse_bool(
        gate.payload.get("claims_exact_compatibility"),
        f"{gate.identifier}.claims_exact_compatibility",
    )
    theta = 2.0 * math.pi * float(winding) / float(cycle_steps)
    zeta = 1.0 / float(half_radar_steps)
    if claims_exact_compatibility and abs(theta - zeta) > tolerance:
        return [
            Issue(
                "fixed_point_step_integer_obstruction",
                f"{gate.identifier}: finite cycle phase {theta:g} does not equal step invariant {zeta:g}",
            )
        ]
    return []


def check_fixed_point_step_free_parameter_audit_gate(gate: FiniteGate) -> list[Issue]:
    free_parameters = require_string_tuple(
        gate.payload.get("free_parameters"),
        f"{gate.identifier}.free_parameters",
    )
    claims_derived_step = parse_bool(
        gate.payload.get("claims_derived_step"),
        f"{gate.identifier}.claims_derived_step",
    )
    if claims_derived_step and free_parameters:
        return [
            Issue(
                "fixed_point_step_parametric",
                f"{gate.identifier}: fixed-point step invariant still has free parameters: "
                f"{', '.join(free_parameters)}",
            )
        ]
    return []


def check_fixed_point_step_no_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    step_status = require_string(gate.payload.get("step_status"), f"{gate.identifier}.step_status")
    claims_physical_step = parse_bool(
        gate.payload.get("claims_physical_step"),
        f"{gate.identifier}.claims_physical_step",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        step_status,
        claims_physical_step,
        "fixed_point_step",
    )


def check_transition_phase_unit_readout_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    transfer = parse_complex(gate.payload.get("transfer"), f"{gate.identifier}.transfer")
    expected_unit_phase = validate_unit_complex(
        parse_complex(gate.payload.get("expected_unit_phase"), f"{gate.identifier}.expected_unit_phase"),
        tolerance,
        "expected_unit_phase",
    )
    computed_unit_phase = transfer_phase_unit(transfer, tolerance)
    if abs(computed_unit_phase - expected_unit_phase) > tolerance:
        return [
            Issue(
                "transition_phase_unit_mismatch",
                f"{gate.identifier}: transition phase unit does not match expected readout",
            )
        ]
    return []


def check_cycle_holonomy_composition_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    unit_edges = parse_unit_edges(gate.payload.get("unit_edges"), f"{gate.identifier}.unit_edges", tolerance)
    cycle = require_string_tuple(gate.payload.get("cycle"), f"{gate.identifier}.cycle")
    expected_holonomy = validate_unit_complex(
        parse_complex(gate.payload.get("expected_holonomy"), f"{gate.identifier}.expected_holonomy"),
        tolerance,
        "expected_holonomy",
    )
    computed_holonomy = cycle_unit_holonomy(cycle, unit_edges)
    if abs(computed_holonomy - expected_holonomy) > tolerance:
        return [
            Issue(
                "cycle_holonomy_composition_mismatch",
                f"{gate.identifier}: composed cycle holonomy does not match expected value",
            )
        ]
    return []


def check_primitive_transition_phase_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    phase_status = require_string(gate.payload.get("phase_status"), f"{gate.identifier}.phase_status")
    claims_physical_phase = parse_bool(
        gate.payload.get("claims_physical_phase"),
        f"{gate.identifier}.claims_physical_phase",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        phase_status,
        claims_physical_phase,
        "transition_phase",
    )


def check_holonomy_source_classification_gate(gate: FiniteGate) -> list[Issue]:
    source_class = require_string(gate.payload.get("source_class"), f"{gate.identifier}.source_class")
    if source_class not in HOLONOMY_SOURCE_CLASSES_WITH_NONE:
        raise ManifestError(f"{gate.identifier}.source_class must be an allowed holonomy source class")
    source_status = require_string(gate.payload.get("source_status"), f"{gate.identifier}.source_status")
    exact_cocycle = parse_bool(gate.payload.get("exact_cocycle"), f"{gate.identifier}.exact_cocycle")
    claims_nonexact_source = parse_bool(
        gate.payload.get("claims_nonexact_source"),
        f"{gate.identifier}.claims_nonexact_source",
    )
    if not claims_nonexact_source:
        return []
    if source_class == "none" or exact_cocycle:
        return [
            Issue(
                "holonomy_source_not_nonexact",
                f"{gate.identifier}: declared source cannot support non-exact holonomy",
            )
        ]
    if source_status not in {"derived", "derived_independent"}:
        return [
            Issue(
                "holonomy_source_underived",
                f"{gate.identifier}: holonomy source is {source_status}, not derived",
            )
        ]
    return []


def check_holonomy_selector_class_registry_gate(gate: FiniteGate) -> list[Issue]:
    registered_classes = set(
        require_string_tuple(gate.payload.get("registered_classes"), f"{gate.identifier}.registered_classes")
    )
    unknown_classes = sorted(registered_classes - set(HOLONOMY_SOURCE_CLASSES))
    if unknown_classes:
        raise ManifestError(
            f"{gate.identifier}.registered_classes has unknown classes: {', '.join(unknown_classes)}"
        )
    missing_classes = sorted(set(HOLONOMY_SOURCE_CLASSES) - registered_classes)
    if missing_classes:
        return [
            Issue(
                "holonomy_selector_class_registry_incomplete",
                f"{gate.identifier}: selector class registry omits: {', '.join(missing_classes)}",
            )
        ]
    return []


def check_holonomy_selector_status_gate(gate: FiniteGate) -> list[Issue]:
    selected_class = require_string(gate.payload.get("selected_class"), f"{gate.identifier}.selected_class")
    if selected_class not in HOLONOMY_SOURCE_CLASSES_WITH_NONE:
        raise ManifestError(f"{gate.identifier}.selected_class must be an allowed holonomy source class")
    selector_status = require_string(gate.payload.get("selector_status"), f"{gate.identifier}.selector_status")
    claims_physical_selector = parse_bool(
        gate.payload.get("claims_physical_selector"),
        f"{gate.identifier}.claims_physical_selector",
    )
    if not claims_physical_selector:
        return []
    if selected_class == "none":
        return [
            Issue(
                "holonomy_selector_missing_source_class",
                f"{gate.identifier}: physical selector claim needs a non-empty source class",
            )
        ]
    if selector_status != "derived_independent":
        return [
            Issue(
                "holonomy_selector_underived",
                f"{gate.identifier}: physical selector is {selector_status}, not derived_independent",
            )
        ]
    return []


def check_holonomy_selector_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    selector_status = require_string(gate.payload.get("selector_status"), f"{gate.identifier}.selector_status")
    claims_physical_selector = parse_bool(
        gate.payload.get("claims_physical_selector"),
        f"{gate.identifier}.claims_physical_selector",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        selector_status,
        claims_physical_selector,
        "holonomy_selector",
    )


def check_winding_selector_homotopy_consistency_gate(gate: FiniteGate) -> list[Issue]:
    assignments = require_list(gate.payload.get("assignments"), f"{gate.identifier}.assignments")
    winding_by_class: dict[str, int] = {}
    for index, assignment in enumerate(assignments):
        assignment_map = require_mapping(assignment, f"{gate.identifier}.assignments[{index}]")
        homotopy_class = require_string(
            assignment_map.get("homotopy_class"),
            f"{gate.identifier}.assignments[{index}].homotopy_class",
        )
        winding = parse_integer(
            assignment_map.get("winding"),
            f"{gate.identifier}.assignments[{index}].winding",
        )
        previous = winding_by_class.get(homotopy_class)
        if previous is not None and previous != winding:
            return [
                Issue(
                    "winding_selector_homotopy_mismatch",
                    f"{gate.identifier}: homotopy class {homotopy_class} has inconsistent winding",
                )
            ]
        winding_by_class[homotopy_class] = winding
    if not winding_by_class:
        raise ManifestError(f"{gate.identifier}.assignments must not be empty")
    return []


def check_winding_selector_orientation_reversal_gate(gate: FiniteGate) -> list[Issue]:
    pairs = require_list(gate.payload.get("pairs"), f"{gate.identifier}.pairs")
    if not pairs:
        raise ManifestError(f"{gate.identifier}.pairs must not be empty")
    for index, pair in enumerate(pairs):
        pair_map = require_mapping(pair, f"{gate.identifier}.pairs[{index}]")
        left_winding = parse_integer(pair_map.get("left_winding"), f"{gate.identifier}.pairs[{index}].left_winding")
        right_winding = parse_integer(
            pair_map.get("right_winding"),
            f"{gate.identifier}.pairs[{index}].right_winding",
        )
        if right_winding != -left_winding:
            return [
                Issue(
                    "winding_selector_orientation_mismatch",
                    f"{gate.identifier}: orientation reversal does not negate winding",
                )
            ]
    return []


def check_winding_selector_additivity_gate(gate: FiniteGate) -> list[Issue]:
    relations = require_list(gate.payload.get("relations"), f"{gate.identifier}.relations")
    if not relations:
        raise ManifestError(f"{gate.identifier}.relations must not be empty")
    for index, relation in enumerate(relations):
        relation_map = require_mapping(relation, f"{gate.identifier}.relations[{index}]")
        left_winding = parse_integer(
            relation_map.get("left_winding"),
            f"{gate.identifier}.relations[{index}].left_winding",
        )
        right_winding = parse_integer(
            relation_map.get("right_winding"),
            f"{gate.identifier}.relations[{index}].right_winding",
        )
        composed_winding = parse_integer(
            relation_map.get("composed_winding"),
            f"{gate.identifier}.relations[{index}].composed_winding",
        )
        if left_winding + right_winding != composed_winding:
            return [
                Issue(
                    "winding_selector_additivity_failed",
                    f"{gate.identifier}: composed winding is not additive",
                )
            ]
    return []


def check_winding_selector_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    selector_status = require_string(gate.payload.get("selector_status"), f"{gate.identifier}.selector_status")
    claims_physical_selector = parse_bool(
        gate.payload.get("claims_physical_selector"),
        f"{gate.identifier}.claims_physical_selector",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        selector_status,
        claims_physical_selector,
        "winding_selector",
    )


def check_sector_role_registry_gate(gate: FiniteGate) -> list[Issue]:
    declared_roles = set(require_string_tuple(gate.payload.get("roles"), f"{gate.identifier}.roles"))
    unknown_roles = sorted(declared_roles - set(SECTOR_ROLE_VALUES))
    if unknown_roles:
        raise ManifestError(f"{gate.identifier}.roles has unknown roles: {', '.join(unknown_roles)}")
    missing_roles = sorted(set(SECTOR_ROLE_VALUES) - declared_roles)
    if missing_roles:
        return [
            Issue(
                "sector_role_registry_incomplete",
                f"{gate.identifier}: sector role registry omits: {', '.join(missing_roles)}",
            )
        ]
    return []


def check_sector_role_assignment_partition_gate(gate: FiniteGate) -> list[Issue]:
    assignments = require_list(gate.payload.get("assignments"), f"{gate.identifier}.assignments")
    roles_by_symbol: dict[str, set[str]] = {}
    for index, assignment in enumerate(assignments):
        assignment_map = require_mapping(assignment, f"{gate.identifier}.assignments[{index}]")
        symbol = require_string(assignment_map.get("symbol"), f"{gate.identifier}.assignments[{index}].symbol")
        role = require_string(assignment_map.get("role"), f"{gate.identifier}.assignments[{index}].role")
        if role not in SECTOR_ROLE_VALUES:
            raise ManifestError(f"{gate.identifier}.assignments[{index}].role has unknown value")
        roles_by_symbol.setdefault(symbol, set()).add(role)
    if not roles_by_symbol:
        raise ManifestError(f"{gate.identifier}.assignments must not be empty")
    collisions = sorted(symbol for symbol, roles in roles_by_symbol.items() if len(roles) > 1)
    if collisions:
        return [
            Issue(
                "sector_role_assignment_overlap",
                f"{gate.identifier}: symbols have multiple sector roles: {', '.join(collisions)}",
            )
        ]
    return []


def check_research_graph_contract_gate(gate: FiniteGate) -> list[Issue]:
    surfaces = require_list(gate.payload.get("surfaces"), f"{gate.identifier}.surfaces")
    if len(surfaces) != len(RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES):
        raise ManifestError(
            f"{gate.identifier}: surfaces must cover every research graph contract surface"
        )

    status_by_surface: dict[str, str] = {}
    for index, item in enumerate(surfaces):
        item_map = require_mapping(item, f"{gate.identifier}.surfaces[{index}]")
        surface = require_string(
            item_map.get("surface"),
            f"{gate.identifier}.surfaces[{index}].surface",
        )
        status = require_string(
            item_map.get("status"),
            f"{gate.identifier}.surfaces[{index}].status",
        )
        evidence_refs = require_string_tuple(
            item_map.get("evidence_refs", []),
            f"{gate.identifier}.surfaces[{index}].evidence_refs",
        )
        open_gap = require_string(
            item_map.get("open_gap"),
            f"{gate.identifier}.surfaces[{index}].open_gap",
        )
        if surface not in RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES:
            return [
                Issue(
                    "research_graph_contract_unknown_surface",
                    f"{gate.identifier}: unknown research graph surface {surface}",
                )
            ]
        if status not in {"implemented", "partial", "missing"}:
            raise ManifestError(f"{gate.identifier}: surface {surface} has unknown status {status!r}")
        if surface in status_by_surface:
            return [
                Issue(
                    "research_graph_contract_duplicate_surface",
                    f"{gate.identifier}: duplicate research graph surface {surface}",
                )
            ]
        if status in {"implemented", "partial"} and not evidence_refs:
            return [
                Issue(
                    "research_graph_contract_evidence_missing",
                    f"{gate.identifier}: surface {surface} needs evidence refs",
                )
            ]
        if status in {"partial", "missing"} and not open_gap.strip():
            return [
                Issue(
                    "research_graph_contract_gap_missing",
                    f"{gate.identifier}: surface {surface} needs an open gap",
                )
            ]
        status_by_surface[surface] = status

    missing = sorted(set(RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES) - set(status_by_surface))
    if missing:
        return [
            Issue(
                "research_graph_contract_surface_missing",
                f"{gate.identifier}: missing research graph surfaces: {', '.join(missing)}",
            )
        ]

    expected_status = require_string(
        gate.payload.get("expected_contract_status"),
        f"{gate.identifier}.expected_contract_status",
    )
    if expected_status not in {"complete", "partial", "incomplete"}:
        raise ManifestError(f"{gate.identifier}: expected_contract_status is unknown")
    if any(status == "missing" for status in status_by_surface.values()):
        computed_status = "incomplete"
    elif any(status == "partial" for status in status_by_surface.values()):
        computed_status = "partial"
    else:
        computed_status = "complete"
    if computed_status != expected_status:
        return [
            Issue(
                "research_graph_contract_status_mismatch",
                f"{gate.identifier}: expected {expected_status}, computed {computed_status}",
            )
        ]
    return []


def check_dimensionful_anchor_policy_gate(gate: FiniteGate) -> list[Issue]:
    entries = require_list(gate.payload.get("entries"), f"{gate.identifier}.entries")
    if not entries:
        raise ManifestError(f"{gate.identifier}.entries must not be empty")
    for index, entry in enumerate(entries):
        entry_map = require_mapping(entry, f"{gate.identifier}.entries[{index}]")
        symbol = require_string(entry_map.get("symbol"), f"{gate.identifier}.entries[{index}].symbol")
        role = require_string(entry_map.get("role"), f"{gate.identifier}.entries[{index}].role")
        if role not in SECTOR_ROLE_VALUES:
            raise ManifestError(f"{gate.identifier}.entries[{index}].role has unknown value")
        anchor_status = require_string(
            entry_map.get("anchor_status"),
            f"{gate.identifier}.entries[{index}].anchor_status",
        )
        dimensionful = parse_bool(entry_map.get("dimensionful"), f"{gate.identifier}.entries[{index}].dimensionful")
        claims_first_principles_output = parse_bool(
            entry_map.get("claims_first_principles_output"),
            f"{gate.identifier}.entries[{index}].claims_first_principles_output",
        )
        if dimensionful and claims_first_principles_output and anchor_status != "derived_independent":
            return [
                Issue(
                    "dimensionful_claim_without_anchor",
                    f"{gate.identifier}: {symbol} is claimed without a derived independent anchor",
                )
            ]
    return []


def check_dimensionless_coupling_policy_gate(gate: FiniteGate) -> list[Issue]:
    entries = require_list(gate.payload.get("entries"), f"{gate.identifier}.entries")
    if not entries:
        raise ManifestError(f"{gate.identifier}.entries must not be empty")
    for index, entry in enumerate(entries):
        entry_map = require_mapping(entry, f"{gate.identifier}.entries[{index}]")
        symbol = require_string(entry_map.get("symbol"), f"{gate.identifier}.entries[{index}].symbol")
        role = require_string(entry_map.get("role"), f"{gate.identifier}.entries[{index}].role")
        if role != "dimensionless_coupling":
            raise ManifestError(f"{gate.identifier}.entries[{index}].role must be dimensionless_coupling")
        selector_status = require_string(
            entry_map.get("selector_status"),
            f"{gate.identifier}.entries[{index}].selector_status",
        )
        coupling_status = require_string(
            entry_map.get("coupling_status"),
            f"{gate.identifier}.entries[{index}].coupling_status",
        )
        claims_derived_coupling = parse_bool(
            entry_map.get("claims_derived_coupling"),
            f"{gate.identifier}.entries[{index}].claims_derived_coupling",
        )
        calibrated_once = parse_bool(
            entry_map.get("calibrated_once"),
            f"{gate.identifier}.entries[{index}].calibrated_once",
        )
        if claims_derived_coupling and selector_status != "derived_independent":
            return [
                Issue(
                    "dimensionless_coupling_without_selector",
                    f"{gate.identifier}: {symbol} is claimed without a derived sector selector",
                )
            ]
        if coupling_status == "calibrated" and not calibrated_once:
            return [
                Issue(
                    "dimensionless_coupling_refit",
                    f"{gate.identifier}: {symbol} is calibrated but not frozen once",
                )
            ]
    return []


def check_bridge_assumption_boundary_gate(gate: FiniteGate) -> list[Issue]:
    entries = require_list(gate.payload.get("entries"), f"{gate.identifier}.entries")
    if not entries:
        raise ManifestError(f"{gate.identifier}.entries must not be empty")
    for index, entry in enumerate(entries):
        entry_map = require_mapping(entry, f"{gate.identifier}.entries[{index}]")
        symbol = require_string(entry_map.get("symbol"), f"{gate.identifier}.entries[{index}].symbol")
        role = require_string(entry_map.get("role"), f"{gate.identifier}.entries[{index}].role")
        if role not in SECTOR_ROLE_VALUES:
            raise ManifestError(f"{gate.identifier}.entries[{index}].role has unknown value")
        status = require_string(entry_map.get("status"), f"{gate.identifier}.entries[{index}].status")
        claims_derived = parse_bool(entry_map.get("claims_derived"), f"{gate.identifier}.entries[{index}].claims_derived")
        if (role == "bridge_assumption" or status == "bridge_assumption") and claims_derived:
            return [
                Issue(
                    "bridge_assumption_relabelled_derived",
                    f"{gate.identifier}: {symbol} is a bridge assumption but is claimed as derived",
                )
            ]
    return []


def check_phase_branch_additivity_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    theta_left = parse_real(gate.payload.get("theta_left"), f"{gate.identifier}.theta_left")
    theta_right = parse_real(gate.payload.get("theta_right"), f"{gate.identifier}.theta_right")
    theta_composed = parse_real(gate.payload.get("theta_composed"), f"{gate.identifier}.theta_composed")
    if abs((theta_left + theta_right) - theta_composed) > tolerance:
        return [
            Issue(
                "phase_branch_additivity_failed",
                f"{gate.identifier}: lifted phase is not additive under cycle composition",
            )
        ]
    return []


def check_phase_branch_no_postfit_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    branch_status = require_string(gate.payload.get("branch_status"), f"{gate.identifier}.branch_status")
    claims_physical_branch = parse_bool(
        gate.payload.get("claims_physical_branch"),
        f"{gate.identifier}.claims_physical_branch",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        branch_status,
        claims_physical_branch,
        "phase_branch",
    )


def check_phase_cost_independence_gate(gate: FiniteGate) -> list[Issue]:
    phase_defined_cost = parse_bool(
        gate.payload.get("phase_defined_cost"),
        f"{gate.identifier}.phase_defined_cost",
    )
    claims_independent_cost = parse_bool(
        gate.payload.get("claims_independent_cost"),
        f"{gate.identifier}.claims_independent_cost",
    )
    if phase_defined_cost and claims_independent_cost:
        return [
            Issue(
                "phase_cost_circular",
                f"{gate.identifier}: cost defined from phase cannot be an independent holonomy source",
            )
        ]
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    cost_status = require_string(gate.payload.get("cost_status"), f"{gate.identifier}.cost_status")
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        cost_status,
        claims_independent_cost,
        "phase_cost",
    )


def check_primitive_mass_anchor_inertia_response_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    impulse = parse_positive_real(gate.payload.get("impulse"), f"{gate.identifier}.impulse")
    velocity_delta = parse_positive_real(
        gate.payload.get("velocity_delta"),
        f"{gate.identifier}.velocity_delta",
    )
    expected_mass = parse_positive_real(gate.payload.get("expected_mass"), f"{gate.identifier}.expected_mass")
    computed_mass = impulse / velocity_delta
    if abs(computed_mass - expected_mass) > tolerance:
        return [
            Issue(
                "primitive_mass_anchor_inertia_mismatch",
                f"{gate.identifier}: expected mass {expected_mass:g}, computed {computed_mass:g}",
            )
        ]
    return []


def check_primitive_mass_anchor_no_quantum_gravity_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    mass_status = require_string(gate.payload.get("mass_status"), f"{gate.identifier}.mass_status")
    claims_physical_mass = parse_bool(
        gate.payload.get("claims_physical_mass"),
        f"{gate.identifier}.claims_physical_mass",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        mass_status,
        claims_physical_mass,
        "mass",
    )


def check_source_response_charge_normalization_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    stiffness_scale = parse_positive_real(
        gate.payload.get("stiffness_scale"),
        f"{gate.identifier}.stiffness_scale",
    )
    clock_strain_response = parse_positive_real(
        gate.payload.get("clock_strain_response"),
        f"{gate.identifier}.clock_strain_response",
    )
    geometry_factor = parse_positive_real(
        gate.payload.get("geometry_factor"),
        f"{gate.identifier}.geometry_factor",
    )
    expected_source_charge = parse_positive_real(
        gate.payload.get("expected_source_charge"),
        f"{gate.identifier}.expected_source_charge",
    )
    computed_source_charge = stiffness_scale * clock_strain_response / geometry_factor
    if abs(computed_source_charge - expected_source_charge) > tolerance:
        return [
            Issue(
                "source_response_charge_normalization_mismatch",
                f"{gate.identifier}: expected source charge {expected_source_charge:g}, "
                f"computed {computed_source_charge:g}",
            )
        ]
    return []


def check_source_response_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    source_charge_status = require_string(
        gate.payload.get("source_charge_status"),
        f"{gate.identifier}.source_charge_status",
    )
    claims_physical_source_charge = parse_bool(
        gate.payload.get("claims_physical_source_charge"),
        f"{gate.identifier}.claims_physical_source_charge",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        source_charge_status,
        claims_physical_source_charge,
        "source_response_charge",
    )


def check_active_passive_inertial_equality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    inertial_mass = parse_positive_real(gate.payload.get("inertial_mass"), f"{gate.identifier}.inertial_mass")
    passive_charge = parse_positive_real(gate.payload.get("passive_charge"), f"{gate.identifier}.passive_charge")
    active_charge = parse_positive_real(gate.payload.get("active_charge"), f"{gate.identifier}.active_charge")
    if abs(inertial_mass - passive_charge) > tolerance or abs(inertial_mass - active_charge) > tolerance:
        return [
            Issue(
                "active_passive_inertial_equality_mismatch",
                f"{gate.identifier}: inertial {inertial_mass:g}, passive {passive_charge:g}, "
                f"active {active_charge:g}",
            )
        ]
    return []


def check_source_response_packet_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    charges = parse_positive_real_vector(gate.payload.get("source_charges"), f"{gate.identifier}.source_charges")
    max_relative_spread = parse_nonnegative_real(
        gate.payload.get("max_relative_spread"),
        f"{gate.identifier}.max_relative_spread",
    )
    if len(charges) < 2:
        raise ManifestError(f"{gate.identifier}.source_charges must contain at least two values")
    mean_charge = sum(charges) / len(charges)
    relative_spread = (max(charges) - min(charges)) / mean_charge
    if relative_spread > max_relative_spread + tolerance:
        return [
            Issue(
                "source_response_packet_universality_failed",
                f"{gate.identifier}: relative spread {relative_spread:g} exceeds {max_relative_spread:g}",
            )
        ]
    return []


def check_geometry_response_factor_freeze_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    max_relative_spread = parse_nonnegative_real(
        gate.payload.get("max_relative_spread"),
        f"{gate.identifier}.max_relative_spread",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"frozen", "not_frozen"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be frozen or not_frozen")

    factors = {
        "D_S": parse_positive_real_vector(gate.payload.get("D_S_values"), f"{gate.identifier}.D_S_values"),
        "z_I": parse_positive_real_vector(gate.payload.get("z_values"), f"{gate.identifier}.z_values"),
        "q_V_I": parse_positive_real_vector(gate.payload.get("q_V_values"), f"{gate.identifier}.q_V_values"),
        "ell0": parse_positive_real_vector(gate.payload.get("ell0_values"), f"{gate.identifier}.ell0_values"),
    }
    spreads = {name: relative_spread(values) for name, values in factors.items()}
    computed_status = (
        "frozen"
        if all(spread <= max_relative_spread + tolerance for spread in spreads.values())
        else "not_frozen"
    )
    if declared_status != computed_status:
        spread_text = ", ".join(f"{name}={spread:g}" for name, spread in spreads.items())
        return [
            Issue(
                "geometry_response_factor_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}; spreads {spread_text}",
            )
        ]
    return []


def check_geometry_response_no_gravity_anchor_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    geometry_status = require_string(gate.payload.get("geometry_status"), f"{gate.identifier}.geometry_status")
    claims_physical_geometry = parse_bool(
        gate.payload.get("claims_physical_geometry"),
        f"{gate.identifier}.claims_physical_geometry",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        geometry_status,
        claims_physical_geometry,
        "geometry_response_factor",
    )


def check_clock_vacuum_stiffness_from_source_response_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    source_charge = parse_positive_real(gate.payload.get("source_charge"), f"{gate.identifier}.source_charge")
    geometry_factor = parse_positive_real(gate.payload.get("geometry_factor"), f"{gate.identifier}.geometry_factor")
    clock_strain_response = parse_positive_real(
        gate.payload.get("clock_strain_response"),
        f"{gate.identifier}.clock_strain_response",
    )
    expected_kappa = parse_positive_real(gate.payload.get("expected_kappa"), f"{gate.identifier}.expected_kappa")
    computed_kappa = source_charge * geometry_factor / clock_strain_response
    if abs(computed_kappa - expected_kappa) > tolerance:
        return [
            Issue(
                "clock_vacuum_stiffness_mismatch",
                f"{gate.identifier}: expected kappa {expected_kappa:g}, computed {computed_kappa:g}",
            )
        ]
    return []


def check_clock_vacuum_stiffness_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    kappa_values = parse_positive_real_vector(gate.payload.get("kappa_values"), f"{gate.identifier}.kappa_values")
    max_relative_spread = parse_nonnegative_real(
        gate.payload.get("max_relative_spread"),
        f"{gate.identifier}.max_relative_spread",
    )
    if len(kappa_values) < 2:
        raise ManifestError(f"{gate.identifier}.kappa_values must contain at least two values")
    spread = relative_spread(kappa_values)
    if spread > max_relative_spread + tolerance:
        return [
            Issue(
                "clock_vacuum_stiffness_universality_failed",
                f"{gate.identifier}: relative spread {spread:g} exceeds {max_relative_spread:g}",
            )
        ]
    return []


def check_clock_vacuum_stiffness_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    stiffness_status = require_string(gate.payload.get("stiffness_status"), f"{gate.identifier}.stiffness_status")
    claims_physical_stiffness = parse_bool(
        gate.payload.get("claims_physical_stiffness"),
        f"{gate.identifier}.claims_physical_stiffness",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        stiffness_status,
        claims_physical_stiffness,
        "clock_vacuum_stiffness",
    )


def check_G_symbolic_clock_strain_candidate_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    ell0_value = parse_positive_real(gate.payload.get("ell0_value"), f"{gate.identifier}.ell0_value")
    dimension_factor = parse_positive_real(
        gate.payload.get("dimension_factor"),
        f"{gate.identifier}.dimension_factor",
    )
    kappa_value = parse_positive_real(gate.payload.get("kappa_value"), f"{gate.identifier}.kappa_value")
    adjacency_factor = parse_positive_real(
        gate.payload.get("adjacency_factor"),
        f"{gate.identifier}.adjacency_factor",
    )
    volume_factor = parse_positive_real(gate.payload.get("volume_factor"), f"{gate.identifier}.volume_factor")
    expected_G = parse_positive_real(gate.payload.get("expected_G"), f"{gate.identifier}.expected_G")
    computed_G = (c_value**4 * ell0_value * dimension_factor) / (
        kappa_value * adjacency_factor * volume_factor
    )
    if abs(computed_G - expected_G) > tolerance:
        return [
            Issue(
                "G_symbolic_clock_strain_mismatch",
                f"{gate.identifier}: expected G candidate {expected_G:g}, computed {computed_G:g}",
            )
        ]
    return []


def check_G_candidate_no_calibrated_input_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    G_candidate_status = require_string(
        gate.payload.get("G_candidate_status"),
        f"{gate.identifier}.G_candidate_status",
    )
    claims_physical_G = parse_bool(gate.payload.get("claims_physical_G"), f"{gate.identifier}.claims_physical_G")
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        G_candidate_status,
        claims_physical_G,
        "G_candidate",
    )


def check_photon_dispersion_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    alpha_abs = parse_positive_real(gate.payload.get("alpha_abs"), f"{gate.identifier}.alpha_abs")
    omega_qg = parse_positive_real(gate.payload.get("omega_qg"), f"{gate.identifier}.omega_qg")
    convention_kappa = parse_positive_real(
        gate.payload.get("convention_kappa"),
        f"{gate.identifier}.convention_kappa",
    )
    expected_omega_min = parse_positive_real(
        gate.payload.get("expected_omega_min"),
        f"{gate.identifier}.expected_omega_min",
    )
    computed_omega_min = math.sqrt(alpha_abs / convention_kappa) * omega_qg
    if relative_error(computed_omega_min, expected_omega_min) > tolerance:
        return [
            Issue(
                "photon_dispersion_bound_mismatch",
                f"{gate.identifier}: expected {expected_omega_min:g}, computed {computed_omega_min:g}",
            )
        ]
    return []


def check_matter_wave_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    wave_number = parse_positive_real(gate.payload.get("wave_number"), f"{gate.identifier}.wave_number")
    coefficient_abs = parse_positive_real(
        gate.payload.get("coefficient_abs"),
        f"{gate.identifier}.coefficient_abs",
    )
    phase_residual_bound = parse_positive_real(
        gate.payload.get("phase_residual_bound"),
        f"{gate.identifier}.phase_residual_bound",
    )
    expected_omega_min = parse_positive_real(
        gate.payload.get("expected_omega_min"),
        f"{gate.identifier}.expected_omega_min",
    )
    computed_omega_min = c_value * wave_number * math.sqrt(coefficient_abs / phase_residual_bound)
    if relative_error(computed_omega_min, expected_omega_min) > tolerance:
        return [
            Issue(
                "matter_wave_bound_mismatch",
                f"{gate.identifier}: expected {expected_omega_min:g}, computed {computed_omega_min:g}",
            )
        ]
    return []


def check_composite_omega_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    omega_bounds = parse_positive_real_vector(gate.payload.get("omega_bounds"), f"{gate.identifier}.omega_bounds")
    expected_omega_min = parse_positive_real(
        gate.payload.get("expected_omega_min"),
        f"{gate.identifier}.expected_omega_min",
    )
    computed_omega_min = max(omega_bounds)
    if relative_error(computed_omega_min, expected_omega_min) > tolerance:
        return [
            Issue(
                "composite_omega_bound_mismatch",
                f"{gate.identifier}: expected {expected_omega_min:g}, computed {computed_omega_min:g}",
            )
        ]
    return []


def check_ell0_tick_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    omega_lower_bound = parse_positive_real(
        gate.payload.get("omega_lower_bound"),
        f"{gate.identifier}.omega_lower_bound",
    )
    radar_steps = parse_positive_integer(gate.payload.get("radar_steps", 1), f"{gate.identifier}.radar_steps")
    expected_ell0_upper = parse_positive_real(
        gate.payload.get("expected_ell0_upper"),
        f"{gate.identifier}.expected_ell0_upper",
    )
    expected_tick_upper = parse_positive_real(
        gate.payload.get("expected_tick_upper"),
        f"{gate.identifier}.expected_tick_upper",
    )
    computed_ell0_upper = c_value / omega_lower_bound
    computed_tick_upper = 1.0 / (omega_lower_bound * float(radar_steps))
    if relative_error(computed_ell0_upper, expected_ell0_upper) > tolerance:
        return [
            Issue(
                "ell0_upper_bound_mismatch",
                f"{gate.identifier}: expected ell0 {expected_ell0_upper:g}, computed {computed_ell0_upper:g}",
            )
        ]
    if relative_error(computed_tick_upper, expected_tick_upper) > tolerance:
        return [
            Issue(
                "tick_upper_bound_mismatch",
                f"{gate.identifier}: expected tick {expected_tick_upper:g}, computed {computed_tick_upper:g}",
            )
        ]
    return []


def check_clock_redshift_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-20), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    potential_a = parse_real(gate.payload.get("potential_a"), f"{gate.identifier}.potential_a")
    potential_b = parse_real(gate.payload.get("potential_b"), f"{gate.identifier}.potential_b")
    expected_fractional_shift = parse_real(
        gate.payload.get("expected_fractional_shift"),
        f"{gate.identifier}.expected_fractional_shift",
    )
    computed_fractional_shift = (potential_a - potential_b) / (c_value * c_value)
    if abs(computed_fractional_shift - expected_fractional_shift) > tolerance:
        return [
            Issue(
                "clock_redshift_mismatch",
                (
                    f"{gate.identifier}: expected shift {expected_fractional_shift:g}, "
                    f"computed {computed_fractional_shift:g}"
                ),
            )
        ]
    return []


def check_combined_clock_rate_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-12), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    potential = parse_real(gate.payload.get("potential"), f"{gate.identifier}.potential")
    speed = parse_nonnegative_real(gate.payload.get("speed"), f"{gate.identifier}.speed")
    expected_rate = parse_positive_real(gate.payload.get("expected_rate"), f"{gate.identifier}.expected_rate")
    computed_rate = 1.0 + potential / (c_value * c_value) - (speed * speed) / (2.0 * c_value * c_value)
    if abs(computed_rate - expected_rate) > tolerance:
        return [
            Issue(
                "combined_clock_rate_mismatch",
                f"{gate.identifier}: expected rate {expected_rate:g}, computed {computed_rate:g}",
            )
        ]
    return []


def check_newtonian_point_mass_clock_field_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    radius = parse_positive_real(gate.payload.get("radius"), f"{gate.identifier}.radius")
    expected_potential = parse_real(gate.payload.get("expected_potential"), f"{gate.identifier}.expected_potential")
    expected_acceleration = parse_positive_real(
        gate.payload.get("expected_acceleration"),
        f"{gate.identifier}.expected_acceleration",
    )
    expected_redshift_to_infinity = parse_positive_real(
        gate.payload.get("expected_redshift_to_infinity"),
        f"{gate.identifier}.expected_redshift_to_infinity",
    )

    computed_potential = -g_value * mass / radius
    computed_acceleration = g_value * mass / (radius * radius)
    computed_redshift_to_infinity = -computed_potential / (c_value * c_value)

    if relative_error(computed_potential, expected_potential) > tolerance:
        return [
            Issue(
                "newtonian_point_mass_potential_mismatch",
                f"{gate.identifier}: expected potential {expected_potential:g}, computed {computed_potential:g}",
            )
        ]
    if relative_error(computed_acceleration, expected_acceleration) > tolerance:
        return [
            Issue(
                "newtonian_point_mass_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected acceleration {expected_acceleration:g}, "
                    f"computed {computed_acceleration:g}"
                ),
            )
        ]
    if relative_error(computed_redshift_to_infinity, expected_redshift_to_infinity) > tolerance:
        return [
            Issue(
                "newtonian_point_mass_redshift_mismatch",
                (
                    f"{gate.identifier}: expected redshift {expected_redshift_to_infinity:g}, "
                    f"computed {computed_redshift_to_infinity:g}"
                ),
            )
        ]
    return []


def check_source_flux_gauss_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    expected_flux = parse_positive_real(gate.payload.get("expected_flux"), f"{gate.identifier}.expected_flux")
    computed_flux = 4.0 * math.pi * g_value * mass
    if relative_error(computed_flux, expected_flux) > tolerance:
        return [
            Issue(
                "source_flux_gauss_mismatch",
                f"{gate.identifier}: expected flux {expected_flux:g}, computed {computed_flux:g}",
            )
        ]
    return []


def check_ppn_light_bending_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    impact_parameter = parse_positive_real(
        gate.payload.get("impact_parameter"),
        f"{gate.identifier}.impact_parameter",
    )
    gamma_ppn = parse_nonnegative_real(gate.payload.get("gamma_ppn"), f"{gate.identifier}.gamma_ppn")
    expected_deflection = parse_positive_real(
        gate.payload.get("expected_deflection"),
        f"{gate.identifier}.expected_deflection",
    )
    computed_deflection = 2.0 * (1.0 + gamma_ppn) * g_value * mass / (c_value * c_value * impact_parameter)
    if relative_error(computed_deflection, expected_deflection) > tolerance:
        return [
            Issue(
                "ppn_light_bending_mismatch",
                f"{gate.identifier}: expected deflection {expected_deflection:g}, computed {computed_deflection:g}",
            )
        ]
    return []


def check_clock_strain_variational_poisson_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    alpha = parse_positive_real(gate.payload.get("alpha"), f"{gate.identifier}.alpha")
    beta = parse_positive_real(gate.payload.get("beta"), f"{gate.identifier}.beta")
    phi_values = parse_real_list(gate.payload.get("phi_values"), f"{gate.identifier}.phi_values")
    source_values = parse_real_list(gate.payload.get("source_values"), f"{gate.identifier}.source_values")
    if len(phi_values) != len(source_values):
        raise ManifestError(f"{gate.identifier}: phi_values and source_values must have equal length")
    if len(phi_values) < 3:
        raise ManifestError(f"{gate.identifier}: at least three cells are required")

    max_residual = 0.0
    for index in range(1, len(phi_values) - 1):
        discrete_laplacian = phi_values[index + 1] - 2.0 * phi_values[index] + phi_values[index - 1]
        residual = alpha * discrete_laplacian - beta * source_values[index]
        max_residual = max(max_residual, abs(residual))

    if max_residual > tolerance:
        return [
            Issue(
                "clock_strain_variational_poisson_mismatch",
                f"{gate.identifier}: max residual {max_residual:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_source_law_coefficient_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    alpha = parse_positive_real(gate.payload.get("alpha"), f"{gate.identifier}.alpha")
    beta = parse_positive_real(gate.payload.get("beta"), f"{gate.identifier}.beta")
    zeta = parse_positive_real(gate.payload.get("zeta"), f"{gate.identifier}.zeta")
    expected_coefficient = parse_positive_real(
        gate.payload.get("expected_coefficient"),
        f"{gate.identifier}.expected_coefficient",
    )
    computed_coefficient = (c_value**4) * beta / (alpha * zeta)
    if relative_error(computed_coefficient, expected_coefficient) > tolerance:
        return [
            Issue(
                "source_law_coefficient_mismatch",
                f"{gate.identifier}: expected coefficient {expected_coefficient:g}, computed {computed_coefficient:g}",
            )
        ]
    return []


def check_ppn_gamma_from_potentials_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    phi_values = parse_real_list(gate.payload.get("phi_values"), f"{gate.identifier}.phi_values")
    psi_values = parse_real_list(gate.payload.get("psi_values"), f"{gate.identifier}.psi_values")
    expected_gamma = parse_nonnegative_real(gate.payload.get("expected_gamma"), f"{gate.identifier}.expected_gamma")
    max_slip_fraction = parse_nonnegative_real(
        gate.payload.get("max_slip_fraction"),
        f"{gate.identifier}.max_slip_fraction",
    )
    if len(phi_values) != len(psi_values):
        raise ManifestError(f"{gate.identifier}: phi_values and psi_values must have equal length")
    if not phi_values:
        raise ManifestError(f"{gate.identifier}: at least one potential pair is required")

    ratios: list[float] = []
    worst_slip = 0.0
    for index, phi in enumerate(phi_values):
        if phi == 0.0:
            raise ManifestError(f"{gate.identifier}.phi_values[{index}] must be nonzero")
        psi = psi_values[index]
        ratios.append(psi / phi)
        worst_slip = max(worst_slip, abs((psi - phi) / phi))

    computed_gamma = sum(ratios) / float(len(ratios))
    if worst_slip > max_slip_fraction:
        return [
            Issue(
                "ppn_gamma_slip_bound_exceeded",
                f"{gate.identifier}: slip fraction {worst_slip:g} exceeds {max_slip_fraction:g}",
            )
        ]
    if abs(computed_gamma - expected_gamma) > tolerance:
        return [
            Issue(
                "ppn_gamma_from_potentials_mismatch",
                f"{gate.identifier}: expected gamma {expected_gamma:g}, computed {computed_gamma:g}",
            )
        ]
    return []


def check_shapiro_delay_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    emitter_radius = parse_positive_real(gate.payload.get("emitter_radius"), f"{gate.identifier}.emitter_radius")
    receiver_radius = parse_positive_real(gate.payload.get("receiver_radius"), f"{gate.identifier}.receiver_radius")
    impact_parameter = parse_positive_real(
        gate.payload.get("impact_parameter"),
        f"{gate.identifier}.impact_parameter",
    )
    gamma_ppn = parse_nonnegative_real(gate.payload.get("gamma_ppn"), f"{gate.identifier}.gamma_ppn")
    expected_delay = parse_positive_real(gate.payload.get("expected_delay"), f"{gate.identifier}.expected_delay")
    log_argument = 4.0 * emitter_radius * receiver_radius / (impact_parameter * impact_parameter)
    if log_argument <= 1.0:
        raise ManifestError(f"{gate.identifier}: Shapiro log argument must be greater than one")
    computed_delay = 2.0 * (1.0 + gamma_ppn) * g_value * mass * math.log(log_argument) / (c_value**3)
    if relative_error(computed_delay, expected_delay) > tolerance:
        return [
            Issue(
                "shapiro_delay_mismatch",
                f"{gate.identifier}: expected delay {expected_delay:g}, computed {computed_delay:g}",
            )
        ]
    return []


def check_ppn_perihelion_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    c_value = parse_positive_real(gate.payload.get("c_value"), f"{gate.identifier}.c_value")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    semi_major_axis = parse_positive_real(
        gate.payload.get("semi_major_axis"),
        f"{gate.identifier}.semi_major_axis",
    )
    eccentricity = parse_nonnegative_real(gate.payload.get("eccentricity"), f"{gate.identifier}.eccentricity")
    if eccentricity >= 1.0:
        raise ManifestError(f"{gate.identifier}.eccentricity must be less than one")
    beta_ppn = parse_positive_real(gate.payload.get("beta_ppn"), f"{gate.identifier}.beta_ppn")
    gamma_ppn = parse_nonnegative_real(gate.payload.get("gamma_ppn"), f"{gate.identifier}.gamma_ppn")
    expected_precession = parse_positive_real(
        gate.payload.get("expected_precession"),
        f"{gate.identifier}.expected_precession",
    )
    ppn_factor = (2.0 + 2.0 * gamma_ppn - beta_ppn) / 3.0
    if ppn_factor <= 0.0:
        raise ManifestError(f"{gate.identifier}: PPN perihelion factor must be positive")
    computed_precession = (
        ppn_factor
        * 6.0
        * math.pi
        * g_value
        * mass
        / (semi_major_axis * (1.0 - eccentricity * eccentricity) * c_value * c_value)
    )
    if relative_error(computed_precession, expected_precession) > tolerance:
        return [
            Issue(
                "ppn_perihelion_mismatch",
                f"{gate.identifier}: expected precession {expected_precession:g}, computed {computed_precession:g}",
            )
        ]
    return []


def check_slip_source_poisson_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    coupling = parse_real(gate.payload.get("coupling"), f"{gate.identifier}.coupling")
    slip_values = parse_real_list(gate.payload.get("slip_values"), f"{gate.identifier}.slip_values")
    stress_values = parse_real_list(gate.payload.get("stress_values"), f"{gate.identifier}.stress_values")
    residual_values = parse_real_list(gate.payload.get("residual_values"), f"{gate.identifier}.residual_values")
    if len(slip_values) != len(stress_values) or len(slip_values) != len(residual_values):
        raise ManifestError(f"{gate.identifier}: slip, stress, and residual arrays must have equal length")
    if len(slip_values) < 3:
        raise ManifestError(f"{gate.identifier}: at least three cells are required")

    max_residual = 0.0
    for index in range(1, len(slip_values) - 1):
        discrete_laplacian = slip_values[index + 1] - 2.0 * slip_values[index] + slip_values[index - 1]
        expected_source = coupling * stress_values[index] + residual_values[index]
        max_residual = max(max_residual, abs(discrete_laplacian - expected_source))

    if max_residual > tolerance:
        return [
            Issue(
                "slip_source_poisson_mismatch",
                f"{gate.identifier}: max residual {max_residual:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_zero_stress_boundary_no_slip_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    slip_values = parse_real_list(gate.payload.get("slip_values"), f"{gate.identifier}.slip_values")
    stress_values = parse_real_list(gate.payload.get("stress_values"), f"{gate.identifier}.stress_values")
    residual_values = parse_real_list(gate.payload.get("residual_values"), f"{gate.identifier}.residual_values")
    if len(slip_values) != len(stress_values) or len(slip_values) != len(residual_values):
        raise ManifestError(f"{gate.identifier}: slip, stress, and residual arrays must have equal length")
    if len(slip_values) < 2:
        raise ManifestError(f"{gate.identifier}: at least two boundary cells are required")

    max_source = max(abs(value) for value in [*stress_values, *residual_values])
    max_slip = max(abs(value) for value in slip_values)
    boundary_slip = max(abs(slip_values[0]), abs(slip_values[-1]))
    if max_source > tolerance:
        return [
            Issue(
                "no_slip_source_not_zero",
                f"{gate.identifier}: source residual {max_source:g} exceeds tolerance {tolerance:g}",
            )
        ]
    if boundary_slip > tolerance:
        return [
            Issue(
                "no_slip_boundary_not_flat",
                f"{gate.identifier}: boundary slip {boundary_slip:g} exceeds tolerance {tolerance:g}",
            )
        ]
    if max_slip > tolerance:
        return [
            Issue(
                "no_slip_solution_not_zero",
                f"{gate.identifier}: slip {max_slip:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_source_continuity_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    delta_t = parse_positive_real(gate.payload.get("delta_t"), f"{gate.identifier}.delta_t")
    density_initial = parse_real_list(gate.payload.get("density_initial"), f"{gate.identifier}.density_initial")
    density_final = parse_real_list(gate.payload.get("density_final"), f"{gate.identifier}.density_final")
    flux_divergence = parse_real_list(gate.payload.get("flux_divergence"), f"{gate.identifier}.flux_divergence")
    if len(density_initial) != len(density_final) or len(density_initial) != len(flux_divergence):
        raise ManifestError(f"{gate.identifier}: density and flux arrays must have equal length")
    if not density_initial:
        raise ManifestError(f"{gate.identifier}: at least one cell is required")

    max_residual = 0.0
    for index, initial in enumerate(density_initial):
        continuity_residual = (density_final[index] - initial) / delta_t + flux_divergence[index]
        max_residual = max(max_residual, abs(continuity_residual))

    if max_residual > tolerance:
        return [
            Issue(
                "source_continuity_mismatch",
                f"{gate.identifier}: max residual {max_residual:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_stress_tensor_decomposition_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    stress_matrix = parse_real_square_matrix(gate.payload.get("stress_matrix"), f"{gate.identifier}.stress_matrix")
    expected_pressure = parse_real(gate.payload.get("expected_pressure"), f"{gate.identifier}.expected_pressure")
    expected_anisotropic = parse_real_square_matrix(
        gate.payload.get("expected_anisotropic"),
        f"{gate.identifier}.expected_anisotropic",
    )
    pressure, anisotropic = stress_decomposition(stress_matrix)
    if len(expected_anisotropic) != len(anisotropic):
        raise ManifestError(f"{gate.identifier}.expected_anisotropic has incompatible dimension")

    if abs(pressure - expected_pressure) > tolerance:
        return [
            Issue(
                "stress_decomposition_pressure_mismatch",
                f"{gate.identifier}: expected pressure {expected_pressure:g}, computed {pressure:g}",
            )
        ]
    if abs(matrix_trace(anisotropic)) > tolerance:
        return [
            Issue(
                "stress_decomposition_not_traceless",
                f"{gate.identifier}: anisotropic trace {matrix_trace(anisotropic):g}",
            )
        ]
    mismatch = max_matrix_abs_difference(anisotropic, expected_anisotropic)
    if mismatch > tolerance:
        return [
            Issue(
                "stress_decomposition_anisotropy_mismatch",
                f"{gate.identifier}: anisotropic mismatch {mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_anisotropic_stress_norm_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    stress_matrix = parse_real_square_matrix(gate.payload.get("stress_matrix"), f"{gate.identifier}.stress_matrix")
    expected_norm = parse_nonnegative_real(gate.payload.get("expected_norm"), f"{gate.identifier}.expected_norm")
    _, anisotropic = stress_decomposition(stress_matrix)
    computed_norm = frobenius_norm(anisotropic)
    if abs(computed_norm - expected_norm) > tolerance:
        return [
            Issue(
                "anisotropic_stress_norm_mismatch",
                f"{gate.identifier}: expected norm {expected_norm:g}, computed {computed_norm:g}",
            )
        ]
    return []


def check_coarse_grained_anisotropy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    weights = parse_nonnegative_real_list(gate.payload.get("weights"), f"{gate.identifier}.weights")
    stress_tensors = parse_real_square_matrix_list(gate.payload.get("stress_tensors"), f"{gate.identifier}.stress_tensors")
    expected_norm = parse_nonnegative_real(gate.payload.get("expected_norm"), f"{gate.identifier}.expected_norm")
    if len(weights) != len(stress_tensors):
        raise ManifestError(f"{gate.identifier}: weights and stress_tensors must have equal length")
    weight_sum = sum(weights)
    if weight_sum <= 0.0:
        raise ManifestError(f"{gate.identifier}: weight sum must be positive")
    dimension = len(stress_tensors[0])
    averaged = [[0.0 for _ in range(dimension)] for _ in range(dimension)]
    for tensor_index, tensor in enumerate(stress_tensors):
        if len(tensor) != dimension:
            raise ManifestError(f"{gate.identifier}.stress_tensors[{tensor_index}] has incompatible dimension")
        for row_index, row in enumerate(tensor):
            for col_index, value in enumerate(row):
                averaged[row_index][col_index] += weights[tensor_index] * value / weight_sum
    _, anisotropic = stress_decomposition(averaged)
    computed_norm = frobenius_norm(anisotropic)
    if abs(computed_norm - expected_norm) > tolerance:
        return [
            Issue(
                "coarse_grained_anisotropy_mismatch",
                f"{gate.identifier}: expected norm {expected_norm:g}, computed {computed_norm:g}",
            )
        ]
    return []


def check_slip_source_bound_from_anisotropy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    coupling = parse_nonnegative_real(gate.payload.get("coupling"), f"{gate.identifier}.coupling")
    anisotropy_norm = parse_nonnegative_real(gate.payload.get("anisotropy_norm"), f"{gate.identifier}.anisotropy_norm")
    non_gravity_residual_norm = parse_nonnegative_real(
        gate.payload.get("non_gravity_residual_norm"),
        f"{gate.identifier}.non_gravity_residual_norm",
    )
    expected_bound = parse_nonnegative_real(gate.payload.get("expected_bound"), f"{gate.identifier}.expected_bound")
    computed_bound = coupling * anisotropy_norm + non_gravity_residual_norm
    if abs(computed_bound - expected_bound) > tolerance:
        return [
            Issue(
                "slip_source_bound_mismatch",
                f"{gate.identifier}: expected bound {expected_bound:g}, computed {computed_bound:g}",
            )
        ]
    return []


def check_scale_residual_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    scales = parse_positive_real_vector(gate.payload.get("scales"), f"{gate.identifier}.scales")
    residuals = parse_nonnegative_real_list(gate.payload.get("residuals"), f"{gate.identifier}.residuals")
    validated_max_scale = parse_positive_real(
        gate.payload.get("validated_max_scale"),
        f"{gate.identifier}.validated_max_scale",
    )
    validated_bound = parse_nonnegative_real(gate.payload.get("validated_bound"), f"{gate.identifier}.validated_bound")
    expected_validated_max = parse_nonnegative_real(
        gate.payload.get("expected_validated_max"),
        f"{gate.identifier}.expected_validated_max",
    )
    if len(scales) != len(residuals):
        raise ManifestError(f"{gate.identifier}: scales and residuals must have equal length")
    validated_residuals = [residual for index, residual in enumerate(residuals) if scales[index] <= validated_max_scale]
    if not validated_residuals:
        raise ManifestError(f"{gate.identifier}: no samples inside validated domain")
    computed_validated_max = max(validated_residuals)
    if computed_validated_max > validated_bound:
        return [
            Issue(
                "validated_residual_bound_exceeded",
                f"{gate.identifier}: residual {computed_validated_max:g} exceeds bound {validated_bound:g}",
            )
        ]
    if abs(computed_validated_max - expected_validated_max) > tolerance:
        return [
            Issue(
                "validated_residual_max_mismatch",
                f"{gate.identifier}: expected max {expected_validated_max:g}, computed {computed_validated_max:g}",
            )
        ]
    return []


def check_scale_residual_activation_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    scales = parse_positive_real_vector(gate.payload.get("scales"), f"{gate.identifier}.scales")
    expected_residuals = parse_nonnegative_real_list(
        gate.payload.get("expected_residuals"),
        f"{gate.identifier}.expected_residuals",
    )
    if len(scales) != len(expected_residuals):
        raise ManifestError(f"{gate.identifier}: scales and expected_residuals must have equal length")
    computed = [amplitude * ((scale / transition_scale) ** exponent) for scale in scales]
    computed = [value / (1.0 + (scale / transition_scale) ** exponent) for value, scale in zip(computed, scales)]
    max_mismatch = max(abs(value - expected_residuals[index]) for index, value in enumerate(computed))
    if max_mismatch > tolerance:
        return [
            Issue(
                "scale_residual_activation_mismatch",
                f"{gate.identifier}: max mismatch {max_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_domain_no_refit_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    constants = parse_positive_real_vector(gate.payload.get("constants"), f"{gate.identifier}.constants")
    reference = parse_positive_real(gate.payload.get("reference"), f"{gate.identifier}.reference")
    expected_max_fractional_mismatch = parse_nonnegative_real(
        gate.payload.get("expected_max_fractional_mismatch"),
        f"{gate.identifier}.expected_max_fractional_mismatch",
    )
    max_fractional_mismatch = max(abs((constant / reference) - 1.0) for constant in constants)
    if max_fractional_mismatch > tolerance:
        return [
            Issue(
                "domain_no_refit_mismatch",
                f"{gate.identifier}: mismatch {max_fractional_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    if abs(max_fractional_mismatch - expected_max_fractional_mismatch) > tolerance:
        return [
            Issue(
                "domain_no_refit_expected_mismatch",
                (
                    f"{gate.identifier}: expected mismatch {expected_max_fractional_mismatch:g}, "
                    f"computed {max_fractional_mismatch:g}"
                ),
            )
        ]
    return []


def screened_residual_value(scale: float, amplitude: float, transition_scale: float, exponent: float) -> float:
    ratio_power = math.pow(scale / transition_scale, exponent)
    return amplitude * ratio_power / (1.0 + ratio_power)


def check_screened_transition_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_positive_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    residual_bound = parse_positive_real(gate.payload.get("residual_bound"), f"{gate.identifier}.residual_bound")
    validated_scale = parse_positive_real(gate.payload.get("validated_scale"), f"{gate.identifier}.validated_scale")
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    expected_transition_min = parse_positive_real(
        gate.payload.get("expected_transition_min"),
        f"{gate.identifier}.expected_transition_min",
    )
    if residual_bound >= amplitude:
        raise ManifestError(f"{gate.identifier}: residual_bound must be below amplitude")
    computed_transition_min = validated_scale * math.pow((amplitude / residual_bound) - 1.0, 1.0 / exponent)
    if relative_error(computed_transition_min, expected_transition_min) > tolerance:
        return [
            Issue(
                "screened_transition_bound_mismatch",
                (
                    f"{gate.identifier}: expected transition {expected_transition_min:g}, "
                    f"computed {computed_transition_min:g}"
                ),
            )
        ]
    return []


def check_screened_profile_prediction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_positive_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    scales = parse_positive_real_vector(gate.payload.get("scales"), f"{gate.identifier}.scales")
    expected_residuals = parse_nonnegative_real_list(
        gate.payload.get("expected_residuals"),
        f"{gate.identifier}.expected_residuals",
    )
    if len(scales) != len(expected_residuals):
        raise ManifestError(f"{gate.identifier}: scales and expected_residuals must have equal length")
    computed = [screened_residual_value(scale, amplitude, transition_scale, exponent) for scale in scales]
    max_mismatch = max(abs(value - expected_residuals[index]) for index, value in enumerate(computed))
    if max_mismatch > tolerance:
        return [
            Issue(
                "screened_profile_prediction_mismatch",
                f"{gate.identifier}: max mismatch {max_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    return []


def check_residual_acceleration_output_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g_value = parse_positive_real(gate.payload.get("g_value"), f"{gate.identifier}.g_value")
    mass = parse_positive_real(gate.payload.get("mass"), f"{gate.identifier}.mass")
    radius = parse_positive_real(gate.payload.get("radius"), f"{gate.identifier}.radius")
    residual_fraction = parse_nonnegative_real(
        gate.payload.get("residual_fraction"),
        f"{gate.identifier}.residual_fraction",
    )
    expected_newtonian_acceleration = parse_positive_real(
        gate.payload.get("expected_newtonian_acceleration"),
        f"{gate.identifier}.expected_newtonian_acceleration",
    )
    expected_residual_acceleration = parse_nonnegative_real(
        gate.payload.get("expected_residual_acceleration"),
        f"{gate.identifier}.expected_residual_acceleration",
    )
    expected_total_acceleration = parse_positive_real(
        gate.payload.get("expected_total_acceleration"),
        f"{gate.identifier}.expected_total_acceleration",
    )
    newtonian_acceleration = g_value * mass / (radius * radius)
    residual_acceleration = residual_fraction * newtonian_acceleration
    total_acceleration = newtonian_acceleration + residual_acceleration
    if relative_error(newtonian_acceleration, expected_newtonian_acceleration) > tolerance:
        return [
            Issue(
                "residual_newtonian_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected Newtonian acceleration {expected_newtonian_acceleration:g}, "
                    f"computed {newtonian_acceleration:g}"
                ),
            )
        ]
    if abs(residual_acceleration - expected_residual_acceleration) > tolerance:
        return [
            Issue(
                "residual_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected residual acceleration {expected_residual_acceleration:g}, "
                    f"computed {residual_acceleration:g}"
                ),
            )
        ]
    if relative_error(total_acceleration, expected_total_acceleration) > tolerance:
        return [
            Issue(
                "residual_total_acceleration_mismatch",
                f"{gate.identifier}: expected total {expected_total_acceleration:g}, computed {total_acceleration:g}",
            )
        ]
    return []


def check_residual_light_bending_output_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    base_gr_deflection = parse_positive_real(
        gate.payload.get("base_gr_deflection"),
        f"{gate.identifier}.base_gr_deflection",
    )
    gamma_residual = parse_real(gate.payload.get("gamma_residual"), f"{gate.identifier}.gamma_residual")
    expected_deflection = parse_positive_real(
        gate.payload.get("expected_deflection"),
        f"{gate.identifier}.expected_deflection",
    )
    computed_deflection = base_gr_deflection * (1.0 + gamma_residual / 2.0)
    if relative_error(computed_deflection, expected_deflection) > tolerance:
        return [
            Issue(
                "residual_light_bending_mismatch",
                f"{gate.identifier}: expected deflection {expected_deflection:g}, computed {computed_deflection:g}",
            )
        ]
    return []


def check_screened_observational_profile_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_positive_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    solar_scale = parse_positive_real(gate.payload.get("solar_scale"), f"{gate.identifier}.solar_scale")
    solar_bound = parse_positive_real(gate.payload.get("solar_bound"), f"{gate.identifier}.solar_bound")
    expected_solar_residual = parse_nonnegative_real(
        gate.payload.get("expected_solar_residual"),
        f"{gate.identifier}.expected_solar_residual",
    )
    galactic_scale = parse_positive_real(gate.payload.get("galactic_scale"), f"{gate.identifier}.galactic_scale")
    expected_galactic_residual = parse_nonnegative_real(
        gate.payload.get("expected_galactic_residual"),
        f"{gate.identifier}.expected_galactic_residual",
    )
    galactic_min = parse_nonnegative_real(gate.payload.get("galactic_min"), f"{gate.identifier}.galactic_min")
    galactic_max = parse_nonnegative_real(gate.payload.get("galactic_max"), f"{gate.identifier}.galactic_max")
    if galactic_max < galactic_min:
        raise ManifestError(f"{gate.identifier}: galactic_max must be at least galactic_min")

    solar_residual = screened_residual_value(solar_scale, amplitude, transition_scale, exponent)
    galactic_residual = screened_residual_value(galactic_scale, amplitude, transition_scale, exponent)
    if solar_residual > solar_bound:
        return [
            Issue(
                "screened_observation_solar_bound_exceeded",
                f"{gate.identifier}: solar residual {solar_residual:g} exceeds bound {solar_bound:g}",
            )
        ]
    if abs(solar_residual - expected_solar_residual) > tolerance:
        return [
            Issue(
                "screened_observation_solar_prediction_mismatch",
                f"{gate.identifier}: expected solar {expected_solar_residual:g}, computed {solar_residual:g}",
            )
        ]
    if abs(galactic_residual - expected_galactic_residual) > tolerance:
        return [
            Issue(
                "screened_observation_galactic_prediction_mismatch",
                f"{gate.identifier}: expected galactic {expected_galactic_residual:g}, computed {galactic_residual:g}",
            )
        ]
    if galactic_residual < galactic_min or galactic_residual > galactic_max:
        return [
            Issue(
                "screened_observation_galactic_range_failed",
                (
                    f"{gate.identifier}: galactic residual {galactic_residual:g} outside "
                    f"[{galactic_min:g}, {galactic_max:g}]"
                ),
            )
        ]
    return []


def load_sparc_rotmod_row(source_path: Path, member_path: str, row_number: int, gate_id: str) -> SparcRotmodRow:
    rows = load_sparc_rotmod_rows(source_path, member_path, gate_id)
    if row_number > len(rows):
        raise ManifestError(f"{gate_id}: SPARC row {row_number} is outside {len(rows)} data rows")
    return rows[row_number - 1]


def sparc_member_path(source_path: Path, member_path: str, gate_id: str) -> Path:
    relative_member_path = Path(member_path)
    if relative_member_path.is_absolute() or ".." in relative_member_path.parts:
        raise ManifestError(f"{gate_id}: SPARC member path must be relative and stay inside source")
    return source_path / relative_member_path


def list_sparc_rotmod_members(source_path: Path, gate_id: str) -> list[str]:
    if source_path.is_dir():
        return sorted(
            path.relative_to(source_path).as_posix()
            for path in source_path.rglob("*_rotmod.dat")
            if path.is_file()
        )
    try:
        with zipfile.ZipFile(source_path) as archive:
            return sorted(name for name in archive.namelist() if name.endswith("_rotmod.dat"))
    except FileNotFoundError as error:
        raise ManifestError(f"{gate_id}: SPARC source file not found: {source_path}") from error
    except zipfile.BadZipFile as error:
        raise ManifestError(f"{gate_id}: SPARC source is not a valid zip file: {source_path}") from error


def load_sparc_rotmod_rows(source_path: Path, member_path: str, gate_id: str) -> list[SparcRotmodRow]:
    if source_path.is_dir():
        try:
            raw_bytes = sparc_member_path(source_path, member_path, gate_id).read_bytes()
        except FileNotFoundError as error:
            raise ManifestError(f"{gate_id}: SPARC member not found in directory: {member_path}") from error
    else:
        try:
            with zipfile.ZipFile(source_path) as archive:
                raw_bytes = archive.read(member_path)
        except FileNotFoundError as error:
            raise ManifestError(f"{gate_id}: SPARC source file not found: {source_path}") from error
        except KeyError as error:
            raise ManifestError(f"{gate_id}: SPARC member not found in zip: {member_path}") from error
        except zipfile.BadZipFile as error:
            raise ManifestError(f"{gate_id}: SPARC source is not a valid zip file: {source_path}") from error

    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ManifestError(f"{gate_id}: SPARC member is not utf-8 text: {member_path}") from error

    rows: list[SparcRotmodRow] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        parts = stripped.split()
        if len(parts) < 6:
            raise ManifestError(f"{gate_id}: SPARC row has fewer than six columns")
        try:
            parsed_values = [float(item) for item in parts[:6]]
        except ValueError as error:
            raise ManifestError(f"{gate_id}: SPARC row contains a non-numeric value") from error
        radius, observed, _error, gas, disk, bulge = parsed_values
        values = (radius, observed, gas, disk, bulge)
        if not all(math.isfinite(value) for value in values):
            raise ManifestError(f"{gate_id}: SPARC row contains a non-finite value")
        rows.append(
            SparcRotmodRow(
                radius_kpc=radius,
                observed_velocity_km_s=observed,
                gas_velocity_km_s=gas,
                disk_velocity_km_s=disk,
                bulge_velocity_km_s=bulge,
            )
        )

    if not rows:
        raise ManifestError(f"{gate_id}: SPARC member has no data rows")
    return rows


def source_checksum_issue(source_path: Path, expected_sha256: str, gate_id: str) -> Issue | None:
    try:
        if source_path.is_dir():
            files = sorted(path for path in source_path.rglob("*") if path.is_file())
            if not files:
                raise ManifestError(f"{gate_id}: SPARC source directory has no files: {source_path}")
            digest = hashlib.sha256()
            for path in files:
                digest.update(path.relative_to(source_path).as_posix().encode("utf-8") + b"\0")
                digest.update(path.read_bytes())
                digest.update(b"\0")
            computed_sha256 = digest.hexdigest()
        else:
            computed_sha256 = hashlib.sha256(source_path.read_bytes()).hexdigest()
    except FileNotFoundError as error:
        raise ManifestError(f"{gate_id}: SPARC source file not found: {source_path}") from error
    if computed_sha256 != expected_sha256:
        return Issue(
            "sparc_source_checksum_mismatch",
            f"{gate_id}: expected source SHA-256 {expected_sha256}, computed {computed_sha256}",
        )
    return None


def sparc_residual_fractions(
    rows: list[SparcRotmodRow],
    upsilon_disk: float,
    upsilon_bulge: float,
) -> list[float]:
    residuals: list[float] = []
    for row in rows:
        observed_acceleration = row.observed_velocity_km_s * row.observed_velocity_km_s / row.radius_kpc
        baryonic_acceleration = (
            row.gas_velocity_km_s * row.gas_velocity_km_s
            + upsilon_disk * row.disk_velocity_km_s * row.disk_velocity_km_s
            + upsilon_bulge * row.bulge_velocity_km_s * row.bulge_velocity_km_s
        ) / row.radius_kpc
        if baryonic_acceleration <= 0.0:
            raise ManifestError("SPARC baryonic acceleration must be positive")
        residuals.append(observed_acceleration / baryonic_acceleration - 1.0)
    return residuals


def check_sparc_baryonic_residual_point_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    source_path = Path(require_string(gate.payload.get("source_path"), f"{gate.identifier}.source_path"))
    source_sha256 = require_string(gate.payload.get("source_sha256"), f"{gate.identifier}.source_sha256")
    member_path = require_string(gate.payload.get("member_path"), f"{gate.identifier}.member_path")
    row_number = parse_positive_integer(gate.payload.get("row_number"), f"{gate.identifier}.row_number")
    upsilon_disk = parse_nonnegative_real(gate.payload.get("upsilon_disk"), f"{gate.identifier}.upsilon_disk")
    upsilon_bulge = parse_nonnegative_real(gate.payload.get("upsilon_bulge"), f"{gate.identifier}.upsilon_bulge")
    expected_radius = parse_positive_real(
        gate.payload.get("expected_radius_kpc"),
        f"{gate.identifier}.expected_radius_kpc",
    )
    expected_observed_velocity = parse_positive_real(
        gate.payload.get("expected_observed_velocity_km_s"),
        f"{gate.identifier}.expected_observed_velocity_km_s",
    )
    expected_gas_velocity = parse_nonnegative_real(
        gate.payload.get("expected_gas_velocity_km_s"),
        f"{gate.identifier}.expected_gas_velocity_km_s",
    )
    expected_disk_velocity = parse_nonnegative_real(
        gate.payload.get("expected_disk_velocity_km_s"),
        f"{gate.identifier}.expected_disk_velocity_km_s",
    )
    expected_bulge_velocity = parse_nonnegative_real(
        gate.payload.get("expected_bulge_velocity_km_s"),
        f"{gate.identifier}.expected_bulge_velocity_km_s",
    )
    expected_observed_acceleration = parse_positive_real(
        gate.payload.get("expected_observed_acceleration"),
        f"{gate.identifier}.expected_observed_acceleration",
    )
    expected_baryonic_acceleration = parse_positive_real(
        gate.payload.get("expected_baryonic_acceleration"),
        f"{gate.identifier}.expected_baryonic_acceleration",
    )
    expected_missing_acceleration = parse_nonnegative_real(
        gate.payload.get("expected_missing_acceleration"),
        f"{gate.identifier}.expected_missing_acceleration",
    )
    expected_residual_fraction = parse_nonnegative_real(
        gate.payload.get("expected_residual_fraction"),
        f"{gate.identifier}.expected_residual_fraction",
    )

    checksum_issue = source_checksum_issue(source_path, source_sha256, gate.identifier)
    if checksum_issue is not None:
        return [checksum_issue]

    row = load_sparc_rotmod_row(source_path, member_path, row_number, gate.identifier)
    row_values = (
        row.radius_kpc,
        row.observed_velocity_km_s,
        row.gas_velocity_km_s,
        row.disk_velocity_km_s,
        row.bulge_velocity_km_s,
    )
    expected_row_values = (
        expected_radius,
        expected_observed_velocity,
        expected_gas_velocity,
        expected_disk_velocity,
        expected_bulge_velocity,
    )
    row_mismatch = max(abs(value - expected_row_values[index]) for index, value in enumerate(row_values))
    if row_mismatch > tolerance:
        return [
            Issue(
                "sparc_rotmod_row_mismatch",
                f"{gate.identifier}: row mismatch {row_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]

    observed_acceleration = row.observed_velocity_km_s * row.observed_velocity_km_s / row.radius_kpc
    baryonic_acceleration = (
        row.gas_velocity_km_s * row.gas_velocity_km_s
        + upsilon_disk * row.disk_velocity_km_s * row.disk_velocity_km_s
        + upsilon_bulge * row.bulge_velocity_km_s * row.bulge_velocity_km_s
    ) / row.radius_kpc
    if baryonic_acceleration <= 0.0:
        raise ManifestError(f"{gate.identifier}: baryonic acceleration must be positive")
    missing_acceleration = observed_acceleration - baryonic_acceleration
    residual_fraction = observed_acceleration / baryonic_acceleration - 1.0

    if relative_error(observed_acceleration, expected_observed_acceleration) > tolerance:
        return [
            Issue(
                "sparc_observed_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected observed acceleration {expected_observed_acceleration:g}, "
                    f"computed {observed_acceleration:g}"
                ),
            )
        ]
    if relative_error(baryonic_acceleration, expected_baryonic_acceleration) > tolerance:
        return [
            Issue(
                "sparc_baryonic_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected baryonic acceleration {expected_baryonic_acceleration:g}, "
                    f"computed {baryonic_acceleration:g}"
                ),
            )
        ]
    if abs(missing_acceleration - expected_missing_acceleration) > tolerance:
        return [
            Issue(
                "sparc_missing_acceleration_mismatch",
                (
                    f"{gate.identifier}: expected missing acceleration {expected_missing_acceleration:g}, "
                    f"computed {missing_acceleration:g}"
                ),
            )
        ]
    if abs(residual_fraction - expected_residual_fraction) > tolerance:
        return [
            Issue(
                "sparc_residual_fraction_mismatch",
                f"{gate.identifier}: expected residual {expected_residual_fraction:g}, computed {residual_fraction:g}",
            )
        ]
    return []


def check_sparc_residual_packet_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    source_path = Path(require_string(gate.payload.get("source_path"), f"{gate.identifier}.source_path"))
    source_sha256 = require_string(gate.payload.get("source_sha256"), f"{gate.identifier}.source_sha256")
    member_path = require_string(gate.payload.get("member_path"), f"{gate.identifier}.member_path")
    upsilon_disk = parse_nonnegative_real(gate.payload.get("upsilon_disk"), f"{gate.identifier}.upsilon_disk")
    upsilon_bulge = parse_nonnegative_real(gate.payload.get("upsilon_bulge"), f"{gate.identifier}.upsilon_bulge")
    expected_count = parse_positive_integer(gate.payload.get("expected_count"), f"{gate.identifier}.expected_count")
    expected_radius_min = parse_positive_real(
        gate.payload.get("expected_radius_min_kpc"),
        f"{gate.identifier}.expected_radius_min_kpc",
    )
    expected_radius_max = parse_positive_real(
        gate.payload.get("expected_radius_max_kpc"),
        f"{gate.identifier}.expected_radius_max_kpc",
    )
    expected_residuals = parse_nonnegative_real_list(
        gate.payload.get("expected_residual_fractions"),
        f"{gate.identifier}.expected_residual_fractions",
    )
    expected_min_residual = parse_nonnegative_real(
        gate.payload.get("expected_min_residual"),
        f"{gate.identifier}.expected_min_residual",
    )
    expected_max_residual = parse_nonnegative_real(
        gate.payload.get("expected_max_residual"),
        f"{gate.identifier}.expected_max_residual",
    )
    expected_mean_residual = parse_nonnegative_real(
        gate.payload.get("expected_mean_residual"),
        f"{gate.identifier}.expected_mean_residual",
    )

    checksum_issue = source_checksum_issue(source_path, source_sha256, gate.identifier)
    if checksum_issue is not None:
        return [checksum_issue]
    rows = load_sparc_rotmod_rows(source_path, member_path, gate.identifier)
    if len(rows) != expected_count:
        return [
            Issue(
                "sparc_packet_count_mismatch",
                f"{gate.identifier}: expected {expected_count} rows, computed {len(rows)}",
            )
        ]
    if len(expected_residuals) != len(rows):
        raise ManifestError(f"{gate.identifier}: expected_residual_fractions length must equal row count")

    radius_min = min(row.radius_kpc for row in rows)
    radius_max = max(row.radius_kpc for row in rows)
    if abs(radius_min - expected_radius_min) > tolerance or abs(radius_max - expected_radius_max) > tolerance:
        return [
            Issue(
                "sparc_packet_radius_range_mismatch",
                (
                    f"{gate.identifier}: expected radius range [{expected_radius_min:g}, {expected_radius_max:g}], "
                    f"computed [{radius_min:g}, {radius_max:g}]"
                ),
            )
        ]

    residuals = sparc_residual_fractions(rows, upsilon_disk, upsilon_bulge)
    max_vector_mismatch = max(abs(value - expected_residuals[index]) for index, value in enumerate(residuals))
    if max_vector_mismatch > tolerance:
        return [
            Issue(
                "sparc_packet_residual_vector_mismatch",
                f"{gate.identifier}: residual vector mismatch {max_vector_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    min_residual = min(residuals)
    max_residual = max(residuals)
    mean_residual = math.fsum(residuals) / float(len(residuals))
    if abs(min_residual - expected_min_residual) > tolerance:
        return [
            Issue(
                "sparc_packet_min_residual_mismatch",
                f"{gate.identifier}: expected min {expected_min_residual:g}, computed {min_residual:g}",
            )
        ]
    if abs(max_residual - expected_max_residual) > tolerance:
        return [
            Issue(
                "sparc_packet_max_residual_mismatch",
                f"{gate.identifier}: expected max {expected_max_residual:g}, computed {max_residual:g}",
            )
        ]
    if abs(mean_residual - expected_mean_residual) > tolerance:
        return [
            Issue(
                "sparc_packet_mean_residual_mismatch",
                f"{gate.identifier}: expected mean {expected_mean_residual:g}, computed {mean_residual:g}",
            )
        ]
    return []


def check_screened_sparc_capacity_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    candidate_max_residual = parse_nonnegative_real(
        gate.payload.get("candidate_max_residual"),
        f"{gate.identifier}.candidate_max_residual",
    )
    required_max_residual = parse_positive_real(
        gate.payload.get("required_max_residual"),
        f"{gate.identifier}.required_max_residual",
    )
    expected_capacity_ratio = parse_nonnegative_real(
        gate.payload.get("expected_capacity_ratio"),
        f"{gate.identifier}.expected_capacity_ratio",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"sufficient", "insufficient"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be sufficient or insufficient")

    capacity_ratio = candidate_max_residual / required_max_residual
    computed_status = "sufficient" if candidate_max_residual >= required_max_residual else "insufficient"
    if abs(capacity_ratio - expected_capacity_ratio) > tolerance:
        return [
            Issue(
                "screened_sparc_capacity_ratio_mismatch",
                f"{gate.identifier}: expected ratio {expected_capacity_ratio:g}, computed {capacity_ratio:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_sparc_capacity_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_amplitude_lower_bound_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    residual_fractions = parse_nonnegative_real_list(
        gate.payload.get("residual_fractions"),
        f"{gate.identifier}.residual_fractions",
    )
    candidate_amplitude = parse_nonnegative_real(
        gate.payload.get("candidate_amplitude"),
        f"{gate.identifier}.candidate_amplitude",
    )
    expected_lower_bound = parse_nonnegative_real(
        gate.payload.get("expected_lower_bound"),
        f"{gate.identifier}.expected_lower_bound",
    )
    expected_shortfall = parse_nonnegative_real(
        gate.payload.get("expected_shortfall"),
        f"{gate.identifier}.expected_shortfall",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"satisfies_bound", "below_bound"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be satisfies_bound or below_bound")
    if not residual_fractions:
        raise ManifestError(f"{gate.identifier}: residual_fractions must not be empty")

    lower_bound = max(residual_fractions)
    shortfall = max(0.0, lower_bound - candidate_amplitude)
    computed_status = "satisfies_bound" if candidate_amplitude + tolerance >= lower_bound else "below_bound"
    if abs(lower_bound - expected_lower_bound) > tolerance:
        return [
            Issue(
                "screened_amplitude_lower_bound_mismatch",
                f"{gate.identifier}: expected lower bound {expected_lower_bound:g}, computed {lower_bound:g}",
            )
        ]
    if abs(shortfall - expected_shortfall) > tolerance:
        return [
            Issue(
                "screened_amplitude_shortfall_mismatch",
                f"{gate.identifier}: expected shortfall {expected_shortfall:g}, computed {shortfall:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_amplitude_bound_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_residual_no_postfit_provenance_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"predeclared", "postfit_contaminated"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be predeclared or postfit_contaminated")
    contamination = sorted(candidate_sources & forbidden_sources)
    computed_status = "postfit_contaminated" if contamination else "predeclared"
    if declared_status != computed_status:
        return [
            Issue(
                "residual_postfit_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_profile_bound_status_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    validated_scale = parse_positive_real(
        gate.payload.get("validated_scale"),
        f"{gate.identifier}.validated_scale",
    )
    residual_bound = parse_positive_real(gate.payload.get("residual_bound"), f"{gate.identifier}.residual_bound")
    expected_residual = parse_nonnegative_real(
        gate.payload.get("expected_residual"),
        f"{gate.identifier}.expected_residual",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"compatible", "excluded"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be compatible or excluded")

    residual = screened_residual_value(validated_scale, amplitude, transition_scale, exponent)
    computed_status = "compatible" if residual <= residual_bound + tolerance else "excluded"
    if abs(residual - expected_residual) > tolerance:
        return [
            Issue(
                "screened_profile_bound_residual_mismatch",
                f"{gate.identifier}: expected residual {expected_residual:g}, computed {residual:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_profile_bound_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_corridor_feasibility_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    solar_scale = parse_positive_real(gate.payload.get("solar_scale"), f"{gate.identifier}.solar_scale")
    solar_bound = parse_positive_real(gate.payload.get("solar_bound"), f"{gate.identifier}.solar_bound")
    required_amplitude = parse_positive_real(
        gate.payload.get("required_amplitude"),
        f"{gate.identifier}.required_amplitude",
    )
    galactic_scale = parse_positive_real(gate.payload.get("galactic_scale"), f"{gate.identifier}.galactic_scale")
    galactic_activation_min = parse_nonnegative_real(
        gate.payload.get("galactic_activation_min"),
        f"{gate.identifier}.galactic_activation_min",
    )
    expected_solar_residual = parse_nonnegative_real(
        gate.payload.get("expected_solar_residual"),
        f"{gate.identifier}.expected_solar_residual",
    )
    expected_galactic_residual = parse_nonnegative_real(
        gate.payload.get("expected_galactic_residual"),
        f"{gate.identifier}.expected_galactic_residual",
    )
    expected_activation_fraction = parse_nonnegative_real(
        gate.payload.get("expected_activation_fraction"),
        f"{gate.identifier}.expected_activation_fraction",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"open", "closed"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be open or closed")
    if amplitude <= 0.0:
        raise ManifestError(f"{gate.identifier}: amplitude must be positive")

    solar_residual = screened_residual_value(solar_scale, amplitude, transition_scale, exponent)
    galactic_residual = screened_residual_value(galactic_scale, amplitude, transition_scale, exponent)
    activation_fraction = galactic_residual / amplitude
    computed_status = (
        "open"
        if amplitude + tolerance >= required_amplitude
        and solar_residual <= solar_bound + tolerance
        and activation_fraction + tolerance >= galactic_activation_min
        else "closed"
    )
    if abs(solar_residual - expected_solar_residual) > tolerance:
        return [
            Issue(
                "screened_corridor_solar_residual_mismatch",
                f"{gate.identifier}: expected solar {expected_solar_residual:g}, computed {solar_residual:g}",
            )
        ]
    if abs(galactic_residual - expected_galactic_residual) > tolerance:
        return [
            Issue(
                "screened_corridor_galactic_residual_mismatch",
                f"{gate.identifier}: expected galactic {expected_galactic_residual:g}, computed {galactic_residual:g}",
            )
        ]
    if abs(activation_fraction - expected_activation_fraction) > tolerance:
        return [
            Issue(
                "screened_corridor_activation_mismatch",
                f"{gate.identifier}: expected activation {expected_activation_fraction:g}, computed {activation_fraction:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_corridor_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_residual_fit_claim_status_gate(gate: FiniteGate) -> list[Issue]:
    profile_source_status = require_string(
        gate.payload.get("profile_source_status"),
        f"{gate.identifier}.profile_source_status",
    )
    radius_scale_map_status = require_string(
        gate.payload.get("radius_scale_map_status"),
        f"{gate.identifier}.radius_scale_map_status",
    )
    heldout_validation_status = require_string(
        gate.payload.get("heldout_validation_status"),
        f"{gate.identifier}.heldout_validation_status",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if profile_source_status not in {"predeclared", "postfit", "missing"}:
        raise ManifestError(f"{gate.identifier}: profile_source_status has invalid value")
    if radius_scale_map_status not in {"derived", "postfit", "missing"}:
        raise ManifestError(f"{gate.identifier}: radius_scale_map_status has invalid value")
    if heldout_validation_status not in {"passed", "failed", "missing"}:
        raise ManifestError(f"{gate.identifier}: heldout_validation_status has invalid value")
    if declared_status not in {"not_fit", "candidate_fit", "validated"}:
        raise ManifestError(f"{gate.identifier}: declared_status has invalid value")

    if (
        profile_source_status == "predeclared"
        and radius_scale_map_status == "derived"
        and heldout_validation_status == "passed"
    ):
        computed_status = "validated"
    elif profile_source_status == "predeclared" and radius_scale_map_status == "derived":
        computed_status = "candidate_fit"
    else:
        computed_status = "not_fit"
    if declared_status != computed_status:
        return [
            Issue(
                "residual_fit_claim_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_radius_scale_prediction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    exponent = parse_positive_real(gate.payload.get("exponent"), f"{gate.identifier}.exponent")
    radii = parse_positive_real_vector(gate.payload.get("radii_kpc"), f"{gate.identifier}.radii_kpc")
    observed_residuals = parse_nonnegative_real_list(
        gate.payload.get("observed_residuals"),
        f"{gate.identifier}.observed_residuals",
    )
    anchor_radius = parse_positive_real(
        gate.payload.get("anchor_radius_kpc"),
        f"{gate.identifier}.anchor_radius_kpc",
    )
    anchor_scale = parse_positive_real(gate.payload.get("anchor_scale"), f"{gate.identifier}.anchor_scale")
    expected_map_factor = parse_positive_real(
        gate.payload.get("expected_map_factor"),
        f"{gate.identifier}.expected_map_factor",
    )
    expected_predictions = parse_nonnegative_real_list(
        gate.payload.get("expected_predicted_residuals"),
        f"{gate.identifier}.expected_predicted_residuals",
    )
    expected_rms_error = parse_nonnegative_real(
        gate.payload.get("expected_rms_error"),
        f"{gate.identifier}.expected_rms_error",
    )
    expected_max_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_max_abs_error"),
        f"{gate.identifier}.expected_max_abs_error",
    )
    expected_mean_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_mean_abs_error"),
        f"{gate.identifier}.expected_mean_abs_error",
    )
    acceptance_max_abs_error = parse_nonnegative_real(
        gate.payload.get("acceptance_max_abs_error"),
        f"{gate.identifier}.acceptance_max_abs_error",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"accepted", "rejected"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be accepted or rejected")
    if len(radii) != len(observed_residuals):
        raise ManifestError(f"{gate.identifier}: radii_kpc and observed_residuals must have equal length")
    if len(expected_predictions) != len(radii):
        raise ManifestError(f"{gate.identifier}: expected_predicted_residuals length must equal radii length")

    map_factor = anchor_scale / anchor_radius
    predicted = [
        screened_residual_value(radius * map_factor, amplitude, transition_scale, exponent)
        for radius in radii
    ]
    errors = [predicted[index] - observed_residuals[index] for index in range(len(predicted))]
    rms_error = math.sqrt(math.fsum(error * error for error in errors) / float(len(errors)))
    max_abs_error = max(abs(error) for error in errors)
    mean_abs_error = math.fsum(abs(error) for error in errors) / float(len(errors))
    computed_status = "accepted" if max_abs_error <= acceptance_max_abs_error + tolerance else "rejected"

    if abs(map_factor - expected_map_factor) > tolerance:
        return [
            Issue(
                "screened_radius_map_factor_mismatch",
                f"{gate.identifier}: expected map factor {expected_map_factor:g}, computed {map_factor:g}",
            )
        ]
    max_prediction_mismatch = max(abs(value - expected_predictions[index]) for index, value in enumerate(predicted))
    if max_prediction_mismatch > tolerance:
        return [
            Issue(
                "screened_radius_map_prediction_mismatch",
                f"{gate.identifier}: prediction mismatch {max_prediction_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    if abs(rms_error - expected_rms_error) > tolerance:
        return [
            Issue(
                "screened_radius_map_rms_mismatch",
                f"{gate.identifier}: expected RMS {expected_rms_error:g}, computed {rms_error:g}",
            )
        ]
    if abs(max_abs_error - expected_max_abs_error) > tolerance:
        return [
            Issue(
                "screened_radius_map_max_error_mismatch",
                f"{gate.identifier}: expected max error {expected_max_abs_error:g}, computed {max_abs_error:g}",
            )
        ]
    if abs(mean_abs_error - expected_mean_abs_error) > tolerance:
        return [
            Issue(
                "screened_radius_map_mean_error_mismatch",
                f"{gate.identifier}: expected mean error {expected_mean_abs_error:g}, computed {mean_abs_error:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_radius_map_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_baryonic_acceleration_map_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    screened_exponent = parse_positive_real(
        gate.payload.get("screened_exponent"),
        f"{gate.identifier}.screened_exponent",
    )
    baryonic_accelerations = parse_positive_real_vector(
        gate.payload.get("baryonic_accelerations"),
        f"{gate.identifier}.baryonic_accelerations",
    )
    observed_residuals = parse_nonnegative_real_list(
        gate.payload.get("observed_residuals"),
        f"{gate.identifier}.observed_residuals",
    )
    anchor_baryonic_acceleration = parse_positive_real(
        gate.payload.get("anchor_baryonic_acceleration"),
        f"{gate.identifier}.anchor_baryonic_acceleration",
    )
    anchor_scale = parse_positive_real(gate.payload.get("anchor_scale"), f"{gate.identifier}.anchor_scale")
    map_exponent = parse_positive_real(gate.payload.get("map_exponent"), f"{gate.identifier}.map_exponent")
    expected_scales = parse_positive_real_vector(
        gate.payload.get("expected_scales"),
        f"{gate.identifier}.expected_scales",
    )
    expected_predictions = parse_nonnegative_real_list(
        gate.payload.get("expected_predicted_residuals"),
        f"{gate.identifier}.expected_predicted_residuals",
    )
    expected_rms_error = parse_nonnegative_real(
        gate.payload.get("expected_rms_error"),
        f"{gate.identifier}.expected_rms_error",
    )
    expected_max_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_max_abs_error"),
        f"{gate.identifier}.expected_max_abs_error",
    )
    expected_mean_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_mean_abs_error"),
        f"{gate.identifier}.expected_mean_abs_error",
    )
    acceptance_max_abs_error = parse_nonnegative_real(
        gate.payload.get("acceptance_max_abs_error"),
        f"{gate.identifier}.acceptance_max_abs_error",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"accepted", "rejected"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be accepted or rejected")
    if len(baryonic_accelerations) != len(observed_residuals):
        raise ManifestError(f"{gate.identifier}: baryonic_accelerations and observed_residuals must have equal length")
    if len(expected_scales) != len(baryonic_accelerations):
        raise ManifestError(f"{gate.identifier}: expected_scales length must equal acceleration length")
    if len(expected_predictions) != len(baryonic_accelerations):
        raise ManifestError(f"{gate.identifier}: expected_predicted_residuals length must equal acceleration length")

    scales = [
        anchor_scale * math.pow(anchor_baryonic_acceleration / acceleration, map_exponent)
        for acceleration in baryonic_accelerations
    ]
    predicted = [
        screened_residual_value(scale, amplitude, transition_scale, screened_exponent)
        for scale in scales
    ]
    errors = [predicted[index] - observed_residuals[index] for index in range(len(predicted))]
    rms_error = math.sqrt(math.fsum(error * error for error in errors) / float(len(errors)))
    max_abs_error = max(abs(error) for error in errors)
    mean_abs_error = math.fsum(abs(error) for error in errors) / float(len(errors))
    computed_status = "accepted" if max_abs_error <= acceptance_max_abs_error + tolerance else "rejected"

    max_scale_mismatch = max(abs(value - expected_scales[index]) for index, value in enumerate(scales))
    if max_scale_mismatch > tolerance:
        return [
            Issue(
                "screened_baryonic_map_scale_mismatch",
                f"{gate.identifier}: scale mismatch {max_scale_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    max_prediction_mismatch = max(abs(value - expected_predictions[index]) for index, value in enumerate(predicted))
    if max_prediction_mismatch > tolerance:
        return [
            Issue(
                "screened_baryonic_map_prediction_mismatch",
                f"{gate.identifier}: prediction mismatch {max_prediction_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    if abs(rms_error - expected_rms_error) > tolerance:
        return [
            Issue(
                "screened_baryonic_map_rms_mismatch",
                f"{gate.identifier}: expected RMS {expected_rms_error:g}, computed {rms_error:g}",
            )
        ]
    if abs(max_abs_error - expected_max_abs_error) > tolerance:
        return [
            Issue(
                "screened_baryonic_map_max_error_mismatch",
                f"{gate.identifier}: expected max error {expected_max_abs_error:g}, computed {max_abs_error:g}",
            )
        ]
    if abs(mean_abs_error - expected_mean_abs_error) > tolerance:
        return [
            Issue(
                "screened_baryonic_map_mean_error_mismatch",
                f"{gate.identifier}: expected mean error {expected_mean_abs_error:g}, computed {mean_abs_error:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_baryonic_map_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_baryonic_exponent_scan_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    screened_exponent = parse_positive_real(
        gate.payload.get("screened_exponent"),
        f"{gate.identifier}.screened_exponent",
    )
    baryonic_accelerations = parse_positive_real_vector(
        gate.payload.get("baryonic_accelerations"),
        f"{gate.identifier}.baryonic_accelerations",
    )
    observed_residuals = parse_nonnegative_real_list(
        gate.payload.get("observed_residuals"),
        f"{gate.identifier}.observed_residuals",
    )
    anchor_baryonic_acceleration = parse_positive_real(
        gate.payload.get("anchor_baryonic_acceleration"),
        f"{gate.identifier}.anchor_baryonic_acceleration",
    )
    anchor_scale = parse_positive_real(gate.payload.get("anchor_scale"), f"{gate.identifier}.anchor_scale")
    map_exponents = parse_positive_real_vector(gate.payload.get("map_exponents"), f"{gate.identifier}.map_exponents")
    expected_rms_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_rms_errors"),
        f"{gate.identifier}.expected_rms_errors",
    )
    expected_max_abs_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_max_abs_errors"),
        f"{gate.identifier}.expected_max_abs_errors",
    )
    expected_mean_abs_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_mean_abs_errors"),
        f"{gate.identifier}.expected_mean_abs_errors",
    )
    acceptance_max_abs_error = parse_nonnegative_real(
        gate.payload.get("acceptance_max_abs_error"),
        f"{gate.identifier}.acceptance_max_abs_error",
    )
    expected_best_exponent = parse_positive_real(
        gate.payload.get("expected_best_exponent"),
        f"{gate.identifier}.expected_best_exponent",
    )
    expected_best_max_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_best_max_abs_error"),
        f"{gate.identifier}.expected_best_max_abs_error",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"all_rejected", "diagnostic_pass_not_validated"}:
        raise ManifestError(f"{gate.identifier}: declared_status has invalid value")
    if len(baryonic_accelerations) != len(observed_residuals):
        raise ManifestError(f"{gate.identifier}: baryonic_accelerations and observed_residuals must have equal length")
    if not map_exponents:
        raise ManifestError(f"{gate.identifier}: map_exponents must not be empty")
    if len(expected_rms_errors) != len(map_exponents):
        raise ManifestError(f"{gate.identifier}: expected_rms_errors length must equal map_exponents length")
    if len(expected_max_abs_errors) != len(map_exponents):
        raise ManifestError(f"{gate.identifier}: expected_max_abs_errors length must equal map_exponents length")
    if len(expected_mean_abs_errors) != len(map_exponents):
        raise ManifestError(f"{gate.identifier}: expected_mean_abs_errors length must equal map_exponents length")

    rms_errors: list[float] = []
    max_abs_errors: list[float] = []
    mean_abs_errors: list[float] = []
    for map_exponent in map_exponents:
        predicted: list[float] = []
        for acceleration in baryonic_accelerations:
            scale = anchor_scale * math.pow(anchor_baryonic_acceleration / acceleration, map_exponent)
            predicted.append(screened_residual_value(scale, amplitude, transition_scale, screened_exponent))
        errors = [predicted[index] - observed_residuals[index] for index in range(len(predicted))]
        rms_errors.append(math.sqrt(math.fsum(error * error for error in errors) / float(len(errors))))
        max_abs_errors.append(max(abs(error) for error in errors))
        mean_abs_errors.append(math.fsum(abs(error) for error in errors) / float(len(errors)))

    max_rms_mismatch = max(abs(value - expected_rms_errors[index]) for index, value in enumerate(rms_errors))
    if max_rms_mismatch > tolerance:
        return [
            Issue(
                "screened_baryonic_exponent_scan_rms_mismatch",
                f"{gate.identifier}: RMS mismatch {max_rms_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    max_error_mismatch = max(
        abs(value - expected_max_abs_errors[index]) for index, value in enumerate(max_abs_errors)
    )
    if max_error_mismatch > tolerance:
        return [
            Issue(
                "screened_baryonic_exponent_scan_max_mismatch",
                f"{gate.identifier}: max-error mismatch {max_error_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    max_mean_mismatch = max(
        abs(value - expected_mean_abs_errors[index]) for index, value in enumerate(mean_abs_errors)
    )
    if max_mean_mismatch > tolerance:
        return [
            Issue(
                "screened_baryonic_exponent_scan_mean_mismatch",
                f"{gate.identifier}: mean-error mismatch {max_mean_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]

    best_index = min(range(len(map_exponents)), key=lambda index: max_abs_errors[index])
    best_exponent = map_exponents[best_index]
    best_max_abs_error = max_abs_errors[best_index]
    computed_status = (
        "diagnostic_pass_not_validated"
        if best_max_abs_error <= acceptance_max_abs_error + tolerance
        else "all_rejected"
    )
    if abs(best_exponent - expected_best_exponent) > tolerance:
        return [
            Issue(
                "screened_baryonic_exponent_scan_best_q_mismatch",
                f"{gate.identifier}: expected best q {expected_best_exponent:g}, computed {best_exponent:g}",
            )
        ]
    if abs(best_max_abs_error - expected_best_max_abs_error) > tolerance:
        return [
            Issue(
                "screened_baryonic_exponent_scan_best_error_mismatch",
                f"{gate.identifier}: expected best error {expected_best_max_abs_error:g}, computed {best_max_abs_error:g}",
            )
        ]
    if declared_status != computed_status:
        return [
            Issue(
                "screened_baryonic_exponent_scan_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_screened_baryonic_exponent_transfer_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    source_path = Path(require_string(gate.payload.get("source_path"), f"{gate.identifier}.source_path"))
    source_sha256 = require_string(gate.payload.get("source_sha256"), f"{gate.identifier}.source_sha256")
    selection_start_after = require_string(
        gate.payload.get("selection_start_after"),
        f"{gate.identifier}.selection_start_after",
    )
    heldout_count = parse_positive_integer(gate.payload.get("heldout_count"), f"{gate.identifier}.heldout_count")
    min_row_count = parse_positive_integer(gate.payload.get("min_row_count"), f"{gate.identifier}.min_row_count")
    expected_member_paths = require_string_tuple(
        gate.payload.get("expected_member_paths"),
        f"{gate.identifier}.expected_member_paths",
    )
    upsilon_disk = parse_nonnegative_real(gate.payload.get("upsilon_disk"), f"{gate.identifier}.upsilon_disk")
    upsilon_bulge = parse_nonnegative_real(gate.payload.get("upsilon_bulge"), f"{gate.identifier}.upsilon_bulge")
    amplitude = parse_nonnegative_real(gate.payload.get("amplitude"), f"{gate.identifier}.amplitude")
    transition_scale = parse_positive_real(
        gate.payload.get("transition_scale"),
        f"{gate.identifier}.transition_scale",
    )
    screened_exponent = parse_positive_real(
        gate.payload.get("screened_exponent"),
        f"{gate.identifier}.screened_exponent",
    )
    map_exponent = parse_positive_real(gate.payload.get("map_exponent"), f"{gate.identifier}.map_exponent")
    anchor_scale = parse_positive_real(gate.payload.get("anchor_scale"), f"{gate.identifier}.anchor_scale")
    expected_row_count_items = require_list(
        gate.payload.get("expected_row_counts"),
        f"{gate.identifier}.expected_row_counts",
    )
    expected_row_counts = [
        parse_positive_integer(item, f"{gate.identifier}.expected_row_counts[{index}]")
        for index, item in enumerate(expected_row_count_items)
    ]
    expected_rms_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_rms_errors"),
        f"{gate.identifier}.expected_rms_errors",
    )
    expected_max_abs_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_max_abs_errors"),
        f"{gate.identifier}.expected_max_abs_errors",
    )
    expected_mean_abs_errors = parse_nonnegative_real_list(
        gate.payload.get("expected_mean_abs_errors"),
        f"{gate.identifier}.expected_mean_abs_errors",
    )
    expected_aggregate_count = parse_positive_integer(
        gate.payload.get("expected_aggregate_count"),
        f"{gate.identifier}.expected_aggregate_count",
    )
    expected_aggregate_rms_error = parse_nonnegative_real(
        gate.payload.get("expected_aggregate_rms_error"),
        f"{gate.identifier}.expected_aggregate_rms_error",
    )
    expected_aggregate_max_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_aggregate_max_abs_error"),
        f"{gate.identifier}.expected_aggregate_max_abs_error",
    )
    expected_aggregate_mean_abs_error = parse_nonnegative_real(
        gate.payload.get("expected_aggregate_mean_abs_error"),
        f"{gate.identifier}.expected_aggregate_mean_abs_error",
    )
    acceptance_max_abs_error = parse_nonnegative_real(
        gate.payload.get("acceptance_max_abs_error"),
        f"{gate.identifier}.acceptance_max_abs_error",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"accepted", "rejected"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be accepted or rejected")
    if len(expected_member_paths) != heldout_count:
        raise ManifestError(f"{gate.identifier}: expected_member_paths length must equal heldout_count")
    if len(expected_row_counts) != heldout_count:
        raise ManifestError(f"{gate.identifier}: expected_row_counts length must equal heldout_count")
    if len(expected_rms_errors) != heldout_count:
        raise ManifestError(f"{gate.identifier}: expected_rms_errors length must equal heldout_count")
    if len(expected_max_abs_errors) != heldout_count:
        raise ManifestError(f"{gate.identifier}: expected_max_abs_errors length must equal heldout_count")
    if len(expected_mean_abs_errors) != heldout_count:
        raise ManifestError(f"{gate.identifier}: expected_mean_abs_errors length must equal heldout_count")

    checksum_issue = source_checksum_issue(source_path, source_sha256, gate.identifier)
    if checksum_issue is not None:
        return [checksum_issue]

    member_names = list_sparc_rotmod_members(source_path, gate.identifier)

    selected_members: list[str] = []
    selected_rows: dict[str, list[SparcRotmodRow]] = {}
    for member_name in member_names:
        if member_name <= selection_start_after:
            continue
        rows = load_sparc_rotmod_rows(source_path, member_name, gate.identifier)
        if len(rows) < min_row_count:
            continue
        selected_members.append(member_name)
        selected_rows[member_name] = rows
        if len(selected_members) == heldout_count:
            break
    if len(selected_members) != heldout_count:
        raise ManifestError(f"{gate.identifier}: not enough held-out SPARC members selected")
    if tuple(selected_members) != expected_member_paths:
        return [
            Issue(
                "screened_transfer_member_selection_mismatch",
                f"{gate.identifier}: expected {expected_member_paths}, computed {tuple(selected_members)}",
            )
        ]

    row_counts: list[int] = []
    rms_errors: list[float] = []
    max_abs_errors: list[float] = []
    mean_abs_errors: list[float] = []
    aggregate_errors: list[float] = []
    for member_name in selected_members:
        rows = selected_rows[member_name]
        row_counts.append(len(rows))
        anchor_baryonic_acceleration = (
            rows[-1].gas_velocity_km_s * rows[-1].gas_velocity_km_s
            + upsilon_disk * rows[-1].disk_velocity_km_s * rows[-1].disk_velocity_km_s
            + upsilon_bulge * rows[-1].bulge_velocity_km_s * rows[-1].bulge_velocity_km_s
        ) / rows[-1].radius_kpc
        if anchor_baryonic_acceleration <= 0.0:
            raise ManifestError(f"{gate.identifier}: anchor baryonic acceleration must be positive")
        errors: list[float] = []
        for row in rows:
            baryonic_acceleration = (
                row.gas_velocity_km_s * row.gas_velocity_km_s
                + upsilon_disk * row.disk_velocity_km_s * row.disk_velocity_km_s
                + upsilon_bulge * row.bulge_velocity_km_s * row.bulge_velocity_km_s
            ) / row.radius_kpc
            if baryonic_acceleration <= 0.0:
                raise ManifestError(f"{gate.identifier}: baryonic acceleration must be positive")
            observed_acceleration = (
                row.observed_velocity_km_s * row.observed_velocity_km_s / row.radius_kpc
            )
            observed_residual = observed_acceleration / baryonic_acceleration - 1.0
            scale = anchor_scale * math.pow(anchor_baryonic_acceleration / baryonic_acceleration, map_exponent)
            predicted_residual = screened_residual_value(
                scale,
                amplitude,
                transition_scale,
                screened_exponent,
            )
            errors.append(predicted_residual - observed_residual)
        aggregate_errors.extend(errors)
        rms_errors.append(math.sqrt(math.fsum(error * error for error in errors) / float(len(errors))))
        max_abs_errors.append(max(abs(error) for error in errors))
        mean_abs_errors.append(math.fsum(abs(error) for error in errors) / float(len(errors)))

    if row_counts != expected_row_counts:
        return [
            Issue(
                "screened_transfer_row_count_mismatch",
                f"{gate.identifier}: expected row counts {expected_row_counts}, computed {row_counts}",
            )
        ]
    max_rms_mismatch = max(abs(value - expected_rms_errors[index]) for index, value in enumerate(rms_errors))
    if max_rms_mismatch > tolerance:
        return [
            Issue(
                "screened_transfer_rms_mismatch",
                f"{gate.identifier}: RMS mismatch {max_rms_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    max_error_mismatch = max(
        abs(value - expected_max_abs_errors[index]) for index, value in enumerate(max_abs_errors)
    )
    if max_error_mismatch > tolerance:
        return [
            Issue(
                "screened_transfer_max_mismatch",
                f"{gate.identifier}: max-error mismatch {max_error_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]
    max_mean_mismatch = max(
        abs(value - expected_mean_abs_errors[index]) for index, value in enumerate(mean_abs_errors)
    )
    if max_mean_mismatch > tolerance:
        return [
            Issue(
                "screened_transfer_mean_mismatch",
                f"{gate.identifier}: mean-error mismatch {max_mean_mismatch:g} exceeds tolerance {tolerance:g}",
            )
        ]

    aggregate_count = len(aggregate_errors)
    aggregate_rms_error = math.sqrt(
        math.fsum(error * error for error in aggregate_errors) / float(aggregate_count)
    )
    aggregate_max_abs_error = max(abs(error) for error in aggregate_errors)
    aggregate_mean_abs_error = math.fsum(abs(error) for error in aggregate_errors) / float(aggregate_count)
    if aggregate_count != expected_aggregate_count:
        return [
            Issue(
                "screened_transfer_aggregate_count_mismatch",
                f"{gate.identifier}: expected aggregate count {expected_aggregate_count}, computed {aggregate_count}",
            )
        ]
    if abs(aggregate_rms_error - expected_aggregate_rms_error) > tolerance:
        return [
            Issue(
                "screened_transfer_aggregate_rms_mismatch",
                f"{gate.identifier}: expected aggregate RMS {expected_aggregate_rms_error:g}, "
                f"computed {aggregate_rms_error:g}",
            )
        ]
    if abs(aggregate_max_abs_error - expected_aggregate_max_abs_error) > tolerance:
        return [
            Issue(
                "screened_transfer_aggregate_max_mismatch",
                f"{gate.identifier}: expected aggregate max {expected_aggregate_max_abs_error:g}, "
                f"computed {aggregate_max_abs_error:g}",
            )
        ]
    if abs(aggregate_mean_abs_error - expected_aggregate_mean_abs_error) > tolerance:
        return [
            Issue(
                "screened_transfer_aggregate_mean_mismatch",
                f"{gate.identifier}: expected aggregate mean {expected_aggregate_mean_abs_error:g}, "
                f"computed {aggregate_mean_abs_error:g}",
            )
        ]
    computed_status = (
        "accepted"
        if aggregate_max_abs_error <= acceptance_max_abs_error + tolerance
        and all(max_error <= acceptance_max_abs_error + tolerance for max_error in max_abs_errors)
        else "rejected"
    )
    if declared_status != computed_status:
        return [
            Issue(
                "screened_transfer_validation_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_primitive_tick_clock_count_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    clock_interval = parse_positive_real(gate.payload.get("clock_interval"), f"{gate.identifier}.clock_interval")
    step_count = parse_positive_integer(gate.payload.get("step_count"), f"{gate.identifier}.step_count")
    expected_tick = parse_positive_real(gate.payload.get("expected_tick"), f"{gate.identifier}.expected_tick")
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    tick_status = require_string(gate.payload.get("tick_status"), f"{gate.identifier}.tick_status")
    claims_physical_tick = parse_bool(
        gate.payload.get("claims_physical_tick"),
        f"{gate.identifier}.claims_physical_tick",
    )
    tick_issues = check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        tick_status,
        claims_physical_tick,
        "tick",
    )
    if tick_issues:
        return tick_issues
    computed_tick = clock_interval / float(step_count)
    if abs(computed_tick - expected_tick) > tolerance:
        return [
            Issue(
                "primitive_tick_clock_count_mismatch",
                f"{gate.identifier}: expected tick {expected_tick:g}, computed {computed_tick:g}",
            )
        ]
    return []


def check_primitive_tick_radar_consistency_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    radar_half_time = parse_positive_real(
        gate.payload.get("radar_half_time"),
        f"{gate.identifier}.radar_half_time",
    )
    step_count = parse_positive_integer(gate.payload.get("step_count"), f"{gate.identifier}.step_count")
    expected_tick = parse_positive_real(gate.payload.get("expected_tick"), f"{gate.identifier}.expected_tick")
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    tick_status = require_string(gate.payload.get("tick_status"), f"{gate.identifier}.tick_status")
    claims_physical_tick = parse_bool(
        gate.payload.get("claims_physical_tick"),
        f"{gate.identifier}.claims_physical_tick",
    )
    tick_issues = check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        tick_status,
        claims_physical_tick,
        "tick",
    )
    if tick_issues:
        return tick_issues
    computed_tick = radar_half_time / float(step_count)
    if abs(computed_tick - expected_tick) > tolerance:
        return [
            Issue(
                "primitive_tick_radar_mismatch",
                f"{gate.identifier}: expected tick {expected_tick:g}, computed {computed_tick:g}",
            )
        ]
    return []


def check_primitive_tick_reparam_invariance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    rates_before = parse_positive_real_vector(gate.payload.get("rates_before"), f"{gate.identifier}.rates_before")
    rates_after = parse_positive_real_vector(gate.payload.get("rates_after"), f"{gate.identifier}.rates_after")
    reparam_factor = parse_positive_real(
        gate.payload.get("reparam_factor"),
        f"{gate.identifier}.reparam_factor",
    )
    reference_index = parse_integer(gate.payload.get("reference_index", 0), f"{gate.identifier}.reference_index")
    if len(rates_before) != len(rates_after):
        raise ManifestError("rates_before and rates_after must have the same length")
    if not rates_before:
        raise ManifestError("rates_before must not be empty")
    if reference_index < 0 or reference_index >= len(rates_before):
        raise ManifestError("reference_index out of range")
    for before, after in zip(rates_before, rates_after, strict=True):
        expected_after = before / reparam_factor
        if abs(after - expected_after) > tolerance:
            return [
                Issue(
                    "primitive_tick_reparam_rate_mismatch",
                    f"{gate.identifier}: expected transformed rate {expected_after:g}, got {after:g}",
                )
            ]
    before_reference = rates_before[reference_index]
    after_reference = rates_after[reference_index]
    for before, after in zip(rates_before, rates_after, strict=True):
        before_ratio = before / before_reference
        after_ratio = after / after_reference
        if abs(before_ratio - after_ratio) > tolerance:
            return [
                Issue(
                    "primitive_tick_reparam_ratio_mismatch",
                    f"{gate.identifier}: rate ratio changed from {before_ratio:g} to {after_ratio:g}",
                )
            ]
    return []


def check_primitive_tick_clock_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    tick_estimates = parse_positive_real_vector(
        gate.payload.get("tick_estimates"),
        f"{gate.identifier}.tick_estimates",
    )
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    tick_status = require_string(gate.payload.get("tick_status"), f"{gate.identifier}.tick_status")
    claims_physical_tick = parse_bool(
        gate.payload.get("claims_physical_tick"),
        f"{gate.identifier}.claims_physical_tick",
    )
    tick_issues = check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        tick_status,
        claims_physical_tick,
        "tick",
    )
    if tick_issues:
        return tick_issues
    mean_tick = sum(tick_estimates) / float(len(tick_estimates))
    for estimate in tick_estimates:
        residual = abs((estimate / mean_tick) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "primitive_tick_universality_failed",
                    f"{gate.identifier}: tick residual {residual:g} exceeds epsilon",
                )
            ]
    return []


def check_primitive_work_balance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    work_inputs = parse_nonnegative_real_list(
        gate.payload.get("work_inputs"),
        f"{gate.identifier}.work_inputs",
    )
    work_outputs = parse_nonnegative_real_list(
        gate.payload.get("work_outputs", []),
        f"{gate.identifier}.work_outputs",
    )
    expected_work_unit = parse_positive_real(
        gate.payload.get("expected_work_unit"),
        f"{gate.identifier}.expected_work_unit",
    )
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    work_unit_status = require_string(
        gate.payload.get("work_unit_status"),
        f"{gate.identifier}.work_unit_status",
    )
    claims_physical_work = parse_bool(
        gate.payload.get("claims_physical_work"),
        f"{gate.identifier}.claims_physical_work",
    )
    work_issues = check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        work_unit_status,
        claims_physical_work,
        "work",
    )
    if work_issues:
        return work_issues
    computed_work = sum(work_inputs) - sum(work_outputs)
    if computed_work <= tolerance:
        return [
            Issue(
                "primitive_work_balance_nonpositive",
                f"{gate.identifier}: computed work unit must be positive",
            )
        ]
    if abs(computed_work - expected_work_unit) > tolerance:
        return [
            Issue(
                "primitive_work_balance_mismatch",
                f"{gate.identifier}: expected work {expected_work_unit:g}, computed {computed_work:g}",
            )
        ]
    return []


def check_primitive_work_no_quantum_energy_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    work_unit_status = require_string(
        gate.payload.get("work_unit_status"),
        f"{gate.identifier}.work_unit_status",
    )
    claims_physical_work = parse_bool(
        gate.payload.get("claims_physical_work"),
        f"{gate.identifier}.claims_physical_work",
    )
    return check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        work_unit_status,
        claims_physical_work,
        "work",
    )


def check_primitive_work_coarse_grain_balance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    fine_inputs = parse_nonnegative_real_list(gate.payload.get("fine_inputs"), f"{gate.identifier}.fine_inputs")
    fine_outputs = parse_nonnegative_real_list(
        gate.payload.get("fine_outputs", []),
        f"{gate.identifier}.fine_outputs",
    )
    coarse_inputs = parse_nonnegative_real_list(
        gate.payload.get("coarse_inputs"),
        f"{gate.identifier}.coarse_inputs",
    )
    coarse_outputs = parse_nonnegative_real_list(
        gate.payload.get("coarse_outputs", []),
        f"{gate.identifier}.coarse_outputs",
    )
    fine_net = sum(fine_inputs) - sum(fine_outputs)
    coarse_net = sum(coarse_inputs) - sum(coarse_outputs)
    if fine_net <= tolerance or coarse_net <= tolerance:
        return [
            Issue(
                "primitive_work_coarse_grain_nonpositive",
                f"{gate.identifier}: fine and coarse work units must be positive",
            )
        ]
    if abs(fine_net - coarse_net) > tolerance:
        return [
            Issue(
                "primitive_work_coarse_grain_mismatch",
                f"{gate.identifier}: fine work {fine_net:g}, coarse work {coarse_net:g}",
            )
        ]
    return []


def check_primitive_work_sector_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    work_units = parse_positive_real_vector(gate.payload.get("work_units"), f"{gate.identifier}.work_units")
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    work_unit_status = require_string(
        gate.payload.get("work_unit_status"),
        f"{gate.identifier}.work_unit_status",
    )
    claims_physical_work = parse_bool(
        gate.payload.get("claims_physical_work"),
        f"{gate.identifier}.claims_physical_work",
    )
    work_issues = check_primitive_source_claims(
        gate.identifier,
        candidate_sources,
        forbidden_sources,
        work_unit_status,
        claims_physical_work,
        "work",
    )
    if work_issues:
        return work_issues
    mean_work = sum(work_units) / float(len(work_units))
    for work_unit in work_units:
        residual = abs((work_unit / mean_work) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "primitive_work_universality_failed",
                    f"{gate.identifier}: work residual {residual:g} exceeds epsilon",
                )
            ]
    return []


def check_primitive_work_dimensional_obstruction_gate(gate: FiniteGate) -> list[Issue]:
    target_dimension = Dimension.from_mapping(
        gate.payload.get("target_dimension", {}),
        f"{gate.identifier}.target_dimension",
    )
    source_dimensions = parse_dimension_list(
        gate.payload.get("source_dimensions"),
        f"{gate.identifier}.source_dimensions",
    )
    expected_obstructed = parse_bool(
        gate.payload.get("expected_obstructed"),
        f"{gate.identifier}.expected_obstructed",
    )
    actual_obstructed = not dimension_in_rational_span(target_dimension, source_dimensions)
    if actual_obstructed != expected_obstructed:
        return [
            Issue(
                "dimension_span_obstruction_mismatch",
                f"{gate.identifier}: expected obstructed={expected_obstructed}, got {actual_obstructed}",
            )
        ]
    return []


def check_primitive_source_claims(
    gate_id: str,
    candidate_sources: set[str],
    forbidden_sources: set[str],
    standard_status: str,
    claims_physical_standard: bool,
    standard_kind: str,
) -> list[Issue]:
    if standard_status not in {"candidate", "derived_independent"}:
        raise ManifestError(f"{standard_kind}_status must be candidate or derived_independent")
    if not candidate_sources:
        raise ManifestError("candidate_sources must not be empty")
    overlap = sorted(candidate_sources & forbidden_sources)
    if overlap:
        return [
            Issue(
                f"primitive_{standard_kind}_forbidden_source",
                f"{gate_id}: primitive {standard_kind} uses forbidden sources: {', '.join(overlap)}",
            )
        ]
    if claims_physical_standard and standard_status != "derived_independent":
        return [
            Issue(
                f"physical_{standard_kind}_claim_without_independent_standard",
                f"{gate_id}: physical {standard_kind} standard requires independent derivation",
            )
        ]
    return []


def check_action_standard_work_time_provenance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    work_unit = parse_positive_real(gate.payload.get("work_unit"), f"{gate.identifier}.work_unit")
    tick = parse_positive_real(gate.payload.get("tick"), f"{gate.identifier}.tick")
    expected_action = parse_positive_real(gate.payload.get("expected_action"), f"{gate.identifier}.expected_action")
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    action_standard_status = require_string(
        gate.payload.get("action_standard_status"),
        f"{gate.identifier}.action_standard_status",
    )
    claims_physical_action = parse_bool(
        gate.payload.get("claims_physical_action"),
        f"{gate.identifier}.claims_physical_action",
    )
    if action_standard_status not in {"candidate", "derived_independent"}:
        raise ManifestError("action_standard_status must be candidate or derived_independent")
    if not candidate_sources:
        raise ManifestError("candidate_sources must not be empty")
    overlap = sorted(candidate_sources & forbidden_sources)
    if overlap:
        return [
            Issue(
                "action_standard_forbidden_source",
                f"{gate.identifier}: action standard uses forbidden sources: {', '.join(overlap)}",
            )
        ]
    computed_action = work_unit * tick
    if abs(computed_action - expected_action) > tolerance:
        return [
            Issue(
                "action_standard_work_time_mismatch",
                f"{gate.identifier}: expected action {expected_action:g}, computed {computed_action:g}",
            )
        ]
    if claims_physical_action and action_standard_status != "derived_independent":
        return [
            Issue(
                "physical_action_claim_without_independent_standard",
                f"{gate.identifier}: physical action standard requires independently derived work and tick",
            )
        ]
    return []


def check_action_scale_gauge_obstruction_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    tick_samples = parse_positive_real_vector(gate.payload.get("tick_samples"), f"{gate.identifier}.tick_samples")
    work_samples = parse_positive_real_vector(gate.payload.get("work_samples"), f"{gate.identifier}.work_samples")
    tick_gauge_factor = parse_positive_real(
        gate.payload.get("tick_gauge_factor"),
        f"{gate.identifier}.tick_gauge_factor",
    )
    work_gauge_factor = parse_positive_real(
        gate.payload.get("work_gauge_factor"),
        f"{gate.identifier}.work_gauge_factor",
    )
    expected_action_scale_factor = parse_positive_real(
        gate.payload.get("expected_action_scale_factor"),
        f"{gate.identifier}.expected_action_scale_factor",
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if declared_status not in {"scale_locked", "scale_not_locked"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be scale_locked or scale_not_locked")
    if len(tick_samples) < 2:
        raise ManifestError(f"{gate.identifier}: tick_samples must contain at least two values")
    if len(work_samples) < 2:
        raise ManifestError(f"{gate.identifier}: work_samples must contain at least two values")

    tick_ratios = [tick_samples[index] / tick_samples[0] for index in range(1, len(tick_samples))]
    transformed_tick_samples = [tick_gauge_factor * value for value in tick_samples]
    transformed_tick_ratios = [
        transformed_tick_samples[index] / transformed_tick_samples[0]
        for index in range(1, len(transformed_tick_samples))
    ]
    if not real_lists_close(tick_ratios, transformed_tick_ratios, tolerance):
        return [
            Issue(
                "action_scale_tick_ratio_not_gauge_invariant",
                f"{gate.identifier}: tick ratios changed under uniform gauge scaling",
            )
        ]

    work_ratios = [work_samples[index] / work_samples[0] for index in range(1, len(work_samples))]
    transformed_work_samples = [work_gauge_factor * value for value in work_samples]
    transformed_work_ratios = [
        transformed_work_samples[index] / transformed_work_samples[0]
        for index in range(1, len(transformed_work_samples))
    ]
    if not real_lists_close(work_ratios, transformed_work_ratios, tolerance):
        return [
            Issue(
                "action_scale_work_ratio_not_gauge_invariant",
                f"{gate.identifier}: work ratios changed under uniform gauge scaling",
            )
        ]

    action_scale_factor = tick_gauge_factor * work_gauge_factor
    if abs(action_scale_factor - expected_action_scale_factor) > tolerance:
        return [
            Issue(
                "action_scale_factor_mismatch",
                f"{gate.identifier}: expected action scale factor {expected_action_scale_factor:g}, "
                f"computed {action_scale_factor:g}",
            )
        ]
    computed_status = "scale_locked" if abs(action_scale_factor - 1.0) <= tolerance else "scale_not_locked"
    if declared_status != computed_status:
        return [
            Issue(
                "action_scale_gauge_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_tick_scale_lock_status_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    lower_bound = parse_nonnegative_real(gate.payload.get("lower_bound"), f"{gate.identifier}.lower_bound")
    upper_bound = parse_positive_real(gate.payload.get("upper_bound"), f"{gate.identifier}.upper_bound")
    expected_width = parse_nonnegative_real(
        gate.payload.get("expected_width"),
        f"{gate.identifier}.expected_width",
    )
    source_status = require_string(gate.payload.get("source_status"), f"{gate.identifier}.source_status")
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if source_status not in {"exact", "bound_only", "candidate"}:
        raise ManifestError(f"{gate.identifier}: source_status has invalid value")
    if declared_status not in {"locked", "bound_only"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be locked or bound_only")
    if lower_bound > upper_bound:
        raise ManifestError(f"{gate.identifier}: lower_bound must not exceed upper_bound")

    width = upper_bound - lower_bound
    if abs(width - expected_width) > tolerance:
        return [
            Issue(
                "tick_scale_lock_width_mismatch",
                f"{gate.identifier}: expected width {expected_width:g}, computed {width:g}",
            )
        ]
    computed_status = (
        "locked"
        if source_status == "exact" and lower_bound > 0.0 and width <= tolerance
        else "bound_only"
    )
    if declared_status != computed_status:
        return [
            Issue(
                "tick_scale_lock_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_work_scale_lock_status_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    impulse = parse_positive_real(gate.payload.get("impulse"), f"{gate.identifier}.impulse")
    velocity_delta = parse_positive_real(
        gate.payload.get("velocity_delta"),
        f"{gate.identifier}.velocity_delta",
    )
    expected_mass = parse_positive_real(gate.payload.get("expected_mass"), f"{gate.identifier}.expected_mass")
    impulse_scale_status = require_string(
        gate.payload.get("impulse_scale_status"),
        f"{gate.identifier}.impulse_scale_status",
    )
    mass_anchor_status = require_string(
        gate.payload.get("mass_anchor_status"),
        f"{gate.identifier}.mass_anchor_status",
    )
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if impulse_scale_status not in {"locked", "candidate", "ratio_only"}:
        raise ManifestError(f"{gate.identifier}: impulse_scale_status has invalid value")
    if mass_anchor_status not in {"derived_independent", "candidate"}:
        raise ManifestError(f"{gate.identifier}: mass_anchor_status has invalid value")
    if declared_status not in {"locked", "not_locked"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be locked or not_locked")

    computed_mass = impulse / velocity_delta
    if abs(computed_mass - expected_mass) > tolerance:
        return [
            Issue(
                "work_scale_lock_mass_mismatch",
                f"{gate.identifier}: expected mass {expected_mass:g}, computed {computed_mass:g}",
            )
        ]
    overlap = sorted(candidate_sources & forbidden_sources)
    if overlap:
        return [
            Issue(
                "work_scale_lock_forbidden_source",
                f"{gate.identifier}: work scale lock uses forbidden sources: {', '.join(overlap)}",
            )
        ]
    computed_status = (
        "locked"
        if impulse_scale_status == "locked" and mass_anchor_status == "derived_independent"
        else "not_locked"
    )
    if declared_status != computed_status:
        return [
            Issue(
                "work_scale_lock_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_action_anchor_lock_status_gate(gate: FiniteGate) -> list[Issue]:
    tick_lock_status = require_string(
        gate.payload.get("tick_lock_status"),
        f"{gate.identifier}.tick_lock_status",
    )
    work_lock_status = require_string(
        gate.payload.get("work_lock_status"),
        f"{gate.identifier}.work_lock_status",
    )
    gauge_status = require_string(gate.payload.get("gauge_status"), f"{gate.identifier}.gauge_status")
    declared_status = require_string(gate.payload.get("declared_status"), f"{gate.identifier}.declared_status")
    if tick_lock_status not in {"locked", "bound_only"}:
        raise ManifestError(f"{gate.identifier}: tick_lock_status has invalid value")
    if work_lock_status not in {"locked", "not_locked"}:
        raise ManifestError(f"{gate.identifier}: work_lock_status has invalid value")
    if gauge_status not in {"scale_locked", "scale_not_locked"}:
        raise ManifestError(f"{gate.identifier}: gauge_status has invalid value")
    if declared_status not in {"locked", "not_locked"}:
        raise ManifestError(f"{gate.identifier}: declared_status must be locked or not_locked")
    computed_status = (
        "locked"
        if tick_lock_status == "locked"
        and work_lock_status == "locked"
        and gauge_status == "scale_locked"
        else "not_locked"
    )
    if declared_status != computed_status:
        return [
            Issue(
                "action_anchor_lock_status_mismatch",
                f"{gate.identifier}: declared {declared_status}, computed {computed_status}",
            )
        ]
    return []


def check_phase_action_scale_universality_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    action_standard = parse_positive_real(gate.payload.get("action_standard"), f"{gate.identifier}.action_standard")
    cycles = parse_phase_action_scale_cycles(gate.payload.get("cycles"), f"{gate.identifier}.cycles")
    calibration_estimates = [
        action_standard * cycle.cost / cycle.phase
        for cycle in cycles
        if cycle.role == "calibration"
    ]
    validation_cycles = [cycle for cycle in cycles if cycle.role == "validation"]
    if not calibration_estimates:
        raise ManifestError("phase/action scale needs at least one calibration cycle")
    if not validation_cycles:
        raise ManifestError("phase/action scale needs at least one validation cycle")
    hbar_estimate = sum(calibration_estimates) / float(len(calibration_estimates))
    if abs(hbar_estimate) <= tolerance:
        return [Issue("zero_hbar_scale_estimate", f"{gate.identifier}: hbar scale estimate is zero")]
    for estimate in calibration_estimates:
        residual = abs((estimate / hbar_estimate) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "phase_action_scale_calibration_inconsistent",
                    f"{gate.identifier}: calibration residual {residual:g} exceeds epsilon",
                )
            ]
    for cycle in validation_cycles:
        estimate = action_standard * cycle.cost / cycle.phase
        residual = abs((estimate / hbar_estimate) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "phase_action_scale_validation_failed",
                    f"{gate.identifier}: validation cycle {cycle.identifier} residual {residual:g} exceeds epsilon",
                )
            ]
    return []


def check_action_standard_independence_gate(gate: FiniteGate) -> list[Issue]:
    candidate_sources = set(
        require_string_tuple(gate.payload.get("candidate_sources"), f"{gate.identifier}.candidate_sources")
    )
    forbidden_sources = set(
        require_string_tuple(gate.payload.get("forbidden_sources"), f"{gate.identifier}.forbidden_sources")
    )
    if not candidate_sources:
        raise ManifestError("candidate_sources must not be empty")
    overlap = sorted(candidate_sources & forbidden_sources)
    if overlap:
        return [
            Issue(
                "action_standard_forbidden_source",
                f"{gate.identifier}: action standard uses forbidden sources: {', '.join(overlap)}",
            )
        ]
    return []


def check_hbar_known_gate_holdout_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    hbar_estimate = parse_positive_real(gate.payload.get("hbar_estimate"), f"{gate.identifier}.hbar_estimate")
    for index, item in enumerate(require_list(gate.payload.get("frequency_pairs"), f"{gate.identifier}.frequency_pairs")):
        pair = require_mapping(item, f"{gate.identifier}.frequency_pairs[{index}]")
        omega = parse_real(pair.get("omega"), f"{gate.identifier}.frequency_pairs[{index}].omega")
        expected_energy = parse_real(pair.get("energy"), f"{gate.identifier}.frequency_pairs[{index}].energy")
        if abs((hbar_estimate * omega) - expected_energy) > tolerance:
            return [
                Issue(
                    "hbar_energy_holdout_mismatch",
                    f"{gate.identifier}: E=hbar*omega holdout {index} failed",
                )
            ]
    for index, item in enumerate(require_list(gate.payload.get("momentum_pairs"), f"{gate.identifier}.momentum_pairs")):
        pair = require_mapping(item, f"{gate.identifier}.momentum_pairs[{index}]")
        wave_number = parse_real(pair.get("k"), f"{gate.identifier}.momentum_pairs[{index}].k")
        expected_momentum = parse_real(pair.get("p"), f"{gate.identifier}.momentum_pairs[{index}].p")
        if abs((hbar_estimate * wave_number) - expected_momentum) > tolerance:
            return [
                Issue(
                    "hbar_momentum_holdout_mismatch",
                    f"{gate.identifier}: p=hbar*k holdout {index} failed",
                )
            ]
    for index, item in enumerate(require_list(gate.payload.get("phase_pairs"), f"{gate.identifier}.phase_pairs")):
        pair = require_mapping(item, f"{gate.identifier}.phase_pairs[{index}]")
        action = parse_real(pair.get("action"), f"{gate.identifier}.phase_pairs[{index}].action")
        expected_phase = parse_real(pair.get("phase"), f"{gate.identifier}.phase_pairs[{index}].phase")
        if abs((action / hbar_estimate) - expected_phase) > tolerance:
            return [
                Issue(
                    "hbar_phase_holdout_mismatch",
                    f"{gate.identifier}: phase=S/hbar holdout {index} failed",
                )
            ]
    return []


def check_probability_admissible_context_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    delta = parse_real(gate.payload.get("delta"), f"{gate.identifier}.delta")
    if delta < 0.0:
        raise ManifestError("delta must be non-negative")
    weights = parse_vector(gate.payload.get("weights"), f"{gate.identifier}.weights")
    gamma = parse_matrix(gate.payload.get("gamma"), f"{gate.identifier}.gamma")
    events = parse_event_context(gate.payload.get("events"), f"{gate.identifier}.events")
    validate_events(tuple(events), len(weights), len(gamma))
    measures = [mu_event(event, weights, gamma) for event in events]
    if any(abs(measure.imag) > tolerance or measure.real <= tolerance for measure in measures):
        return [Issue("nonpositive_context_measure", f"{gate.identifier}: context has non-positive measure")]
    denominator = sum(measure.real for measure in measures)
    if denominator <= tolerance:
        return [Issue("nonpositive_context_denominator", f"{gate.identifier}: context denominator is not positive")]
    for left_index, left_event in enumerate(events):
        for right_index in range(left_index + 1, len(events)):
            right_event = events[right_index]
            offdiag = actualization(left_event, right_event, weights, gamma)
            bound = delta * math.sqrt(measures[left_index].real * measures[right_index].real)
            if abs(offdiag) > bound + tolerance:
                return [
                    Issue(
                        "context_not_probability_admissible",
                        f"{gate.identifier}: off-diagonal ({left_index},{right_index}) exceeds delta gate",
                    )
                ]
    return []


def check_relative_phase_cost_family_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    cycles = parse_phase_cost_cycles(gate.payload.get("cycles"), f"{gate.identifier}.cycles")
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_edges_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_edge_costs(gate.payload.get("edge_costs"), f"{gate.identifier}.edge_costs")
    cycles = parse_phase_cost_cycles_from_edges(
        gate.payload.get("cycles"), f"{gate.identifier}.cycles", edge_costs
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_edges_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    cycles = parse_phase_cost_cycles_from_edges(
        gate.payload.get("cycles"), f"{gate.identifier}.cycles", edge_costs
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_holonomy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    phase_edges = parse_phase_edges(gate.payload.get("phase_edges"), f"{gate.identifier}.phase_edges")
    cycles = parse_phase_cost_cycles_from_holonomy(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        phase_edges,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_unit_holonomy_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    cycles = parse_phase_cost_cycles_from_unit_holonomy(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_unit_edges_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_unit_edges(gate.payload.get("unit_edges"), f"{gate.identifier}.unit_edges", tolerance)
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_transfer_elements_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_transfer_edges(
        gate.payload.get("transfer_edges"), f"{gate.identifier}.transfer_edges", tolerance
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_transfer_blocks_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_transfer_block_edges(
        gate.payload.get("transfer_blocks"), f"{gate.identifier}.transfer_blocks", tolerance
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_block_kernels_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_block_kernel_edges(
        gate.payload.get("block_kernel_edges"),
        f"{gate.identifier}.block_kernel_edges",
        tolerance,
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_normalized_blocks_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_normalized_block_kernel_edges(
        gate.payload.get("normalized_block_edges"),
        f"{gate.identifier}.normalized_block_edges",
        tolerance,
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_kernel_spectral_blocks_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs = parse_kernel_edge_costs(gate.payload.get("kernel_edges"), f"{gate.identifier}.kernel_edges")
    unit_edges = parse_spectral_block_kernel_edges(
        gate.payload.get("spectral_block_edges"),
        f"{gate.identifier}.spectral_block_edges",
        tolerance,
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_relative_phase_cost_from_spectral_kernel_blocks_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    epsilon = parse_tolerance(gate.payload.get("epsilon"), f"{gate.identifier}.epsilon")
    edge_costs, unit_edges = parse_spectral_kernel_block_readouts(
        gate.payload.get("spectral_block_edges"),
        f"{gate.identifier}.spectral_block_edges",
        tolerance,
    )
    cycles = parse_phase_cost_cycles_from_unit_edges(
        gate.payload.get("cycles"),
        f"{gate.identifier}.cycles",
        edge_costs,
        unit_edges,
        tolerance,
    )
    return check_phase_cost_cycles(gate.identifier, cycles, epsilon, tolerance)


def check_diagonal_kernel_strain_cost_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g0_diag = parse_positive_real_vector(gate.payload.get("G0_diag"), f"{gate.identifier}.G0_diag")
    g1_diag = parse_positive_real_vector(gate.payload.get("G1_diag"), f"{gate.identifier}.G1_diag")
    alignment = parse_index_tuple(gate.payload.get("alignment"), f"{gate.identifier}.alignment")
    expected_cost = parse_real(gate.payload.get("expected_cost"), f"{gate.identifier}.expected_cost")
    cost = diagonal_kernel_strain_cost(g0_diag, g1_diag, alignment)
    if abs(cost - expected_cost) > tolerance:
        return [
            Issue(
                "kernel_strain_cost_mismatch",
                f"{gate.identifier}: expected {expected_cost:g}, computed {cost:g}",
            )
        ]
    return []


def check_spectral_kernel_strain_cost_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g0 = parse_matrix(gate.payload.get("G0"), f"{gate.identifier}.G0")
    g1 = parse_matrix(gate.payload.get("G1"), f"{gate.identifier}.G1")
    cross = parse_matrix(gate.payload.get("X"), f"{gate.identifier}.X")
    expected_cost = parse_real(gate.payload.get("expected_cost"), f"{gate.identifier}.expected_cost")
    cost, _unit_phase = spectral_kernel_block_readout(g0, g1, cross, tolerance)
    if abs(cost - expected_cost) > tolerance:
        return [
            Issue(
                "kernel_strain_cost_mismatch",
                f"{gate.identifier}: expected {expected_cost:g}, computed {cost:g}",
            )
        ]
    return []


def check_spectral_kernel_diagonal_limit_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g0_diag = parse_positive_real_vector(gate.payload.get("G0_diag"), f"{gate.identifier}.G0_diag")
    g1_diag = parse_positive_real_vector(gate.payload.get("G1_diag"), f"{gate.identifier}.G1_diag")
    alignment = parse_index_tuple(gate.payload.get("alignment"), f"{gate.identifier}.alignment")
    diagonal_cost = diagonal_kernel_strain_cost(g0_diag, g1_diag, alignment)
    g0 = diagonal_matrix(g0_diag)
    g1 = diagonal_matrix(g1_diag)
    cross = diagonal_limit_cross_block(g0_diag, g1_diag, alignment)
    spectral_cost, _unit_phase = spectral_kernel_block_readout(g0, g1, cross, tolerance)
    if abs(spectral_cost - diagonal_cost) > tolerance:
        return [
            Issue(
                "spectral_diagonal_limit_mismatch",
                f"{gate.identifier}: diagonal cost {diagonal_cost:g}, spectral cost {spectral_cost:g}",
            )
        ]
    return []


def check_spectral_kernel_readout_covariance_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    g0 = parse_matrix(gate.payload.get("G0"), f"{gate.identifier}.G0")
    g1 = parse_matrix(gate.payload.get("G1"), f"{gate.identifier}.G1")
    cross = parse_matrix(gate.payload.get("X"), f"{gate.identifier}.X")
    u0 = parse_matrix(gate.payload.get("U0"), f"{gate.identifier}.U0")
    u1 = parse_matrix(gate.payload.get("U1"), f"{gate.identifier}.U1")
    validate_unitary(u0, tolerance, "U0")
    validate_unitary(u1, tolerance, "U1")
    cost, unit_phase = spectral_kernel_block_readout(g0, g1, cross, tolerance)
    transformed_g0 = unitary_conjugate(u0, g0)
    transformed_g1 = unitary_conjugate(u1, g1)
    transformed_cross = matrix_multiply(matrix_multiply(u1, cross), conjugate_transpose(u0))
    transformed_cost, transformed_unit_phase = spectral_kernel_block_readout(
        transformed_g0,
        transformed_g1,
        transformed_cross,
        tolerance,
    )
    phase_delta = wrapped_angle(
        math.atan2(unit_phase.imag, unit_phase.real)
        - math.atan2(transformed_unit_phase.imag, transformed_unit_phase.real)
    )
    if abs(cost - transformed_cost) > tolerance or abs(phase_delta) > tolerance:
        return [
            Issue(
                "spectral_readout_not_covariant",
                f"{gate.identifier}: cost/phase changed under unitary basis relabeling",
            )
        ]
    return []


def check_cycle_cost_sum_gate(gate: FiniteGate) -> list[Issue]:
    tolerance = parse_tolerance(gate.payload.get("tolerance", 1.0e-10), f"{gate.identifier}.tolerance")
    edge_costs = parse_edge_costs(gate.payload.get("edge_costs"), f"{gate.identifier}.edge_costs")
    cycles = parse_cycle_cost_expectations(gate.payload.get("cycles"), f"{gate.identifier}.cycles")
    for cycle in cycles:
        cycle_id = require_string(cycle["id"], f"{gate.identifier}.cycle.id")
        word = require_parsed_string_tuple(cycle["word"], f"{gate.identifier}.{cycle_id}.word")
        if len(word) < 2 or word[0] != word[-1]:
            raise ManifestError(f"{cycle_id} cycle word must be closed")
        expected_cost = parse_real(cycle["expected_cost"], f"{gate.identifier}.{cycle_id}.expected_cost")
        actual_cost = cycle_word_cost(word, edge_costs)
        if abs(actual_cost - expected_cost) > tolerance:
            return [
                Issue(
                    "cycle_cost_mismatch",
                    f"{gate.identifier}: cycle {cycle_id} expected {expected_cost:g}, computed {actual_cost:g}",
                )
            ]
    return []


def check_phase_cost_cycles(
    gate_id: str, cycles: list[dict[str, object]], epsilon: float, tolerance: float
) -> list[Issue]:
    active_cycles = [cycle for cycle in cycles if cycle["role"] != "excluded"]
    calibration_cycles = [cycle for cycle in active_cycles if cycle["role"] == "calibration"]
    validation_cycles = [cycle for cycle in active_cycles if cycle["role"] == "validation"]
    if not calibration_cycles:
        raise ManifestError("relative phase-cost family needs at least one calibration cycle")
    if not validation_cycles:
        raise ManifestError("relative phase-cost family needs at least one validation cycle")

    issues = validate_phase_cost_cycles(gate_id, active_cycles, tolerance)
    if issues:
        return issues

    calibration_slopes = [phase_cost_slope(cycle) for cycle in calibration_cycles]
    calibration_mean = sum(calibration_slopes) / float(len(calibration_slopes))
    if abs(calibration_mean) <= tolerance:
        return [Issue("zero_calibration_slope", f"{gate_id}: calibration slope is zero")]

    for slope in calibration_slopes:
        residual = abs((slope / calibration_mean) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "phase_cost_calibration_inconsistent",
                    f"{gate_id}: calibration residual {residual:g} exceeds epsilon",
                )
            ]

    for cycle in validation_cycles:
        slope = phase_cost_slope(cycle)
        residual = abs((slope / calibration_mean) - 1.0)
        if residual > epsilon + tolerance:
            return [
                Issue(
                    "phase_cost_validation_failed",
                    f"{gate_id}: validation cycle {cycle['id']} residual {residual:g} exceeds epsilon",
                )
            ]
    return []


def matrix_psd_issues(identifier: str, matrix: list[list[complex]], tolerance: float) -> list[Issue]:
    issues: list[Issue] = []
    if not matrix:
        raise ManifestError("matrix must not be empty")
    width = len(matrix[0])
    if width != len(matrix):
        raise ManifestError("matrix must be square")
    if width > 6:
        raise ManifestError("PSD gate currently supports matrices up to 6x6")
    for row in matrix:
        if len(row) != width:
            raise ManifestError("matrix rows must have equal length")
    if not is_hermitian(matrix, tolerance):
        issues.append(Issue("matrix_not_hermitian", f"{identifier}: matrix is not Hermitian"))
        return issues
    for subset in nonempty_index_subsets(width):
        minor = determinant(principal_submatrix(matrix, subset))
        if abs(minor.imag) > tolerance or minor.real < -tolerance:
            issues.append(
                Issue(
                    "matrix_not_psd",
                    f"{identifier}: principal minor {subset} is {minor.real:g}+{minor.imag:g}i",
                )
            )
            return issues
    return issues


def parse_matrix(raw: object, field: str) -> list[list[complex]]:
    rows = require_list(raw, field)
    matrix: list[list[complex]] = []
    for row_index, row_raw in enumerate(rows):
        row = require_list(row_raw, f"{field}[{row_index}]")
        matrix.append(
            [parse_complex(item, f"{field}[{row_index}][{col_index}]") for col_index, item in enumerate(row)]
        )
    return matrix


def parse_matrix_list(raw: object, field: str) -> list[list[list[complex]]]:
    items = require_list(raw, field)
    if not items:
        raise ManifestError(f"{field} must not be empty")
    return [parse_matrix(item, f"{field}[{index}]") for index, item in enumerate(items)]


def parse_real_square_matrix(raw: object, field: str) -> list[list[float]]:
    rows = require_list(raw, field)
    if not rows:
        raise ManifestError(f"{field} must not be empty")
    matrix: list[list[float]] = []
    for row_index, row_raw in enumerate(rows):
        row = require_list(row_raw, f"{field}[{row_index}]")
        matrix.append([parse_real(item, f"{field}[{row_index}][{col_index}]") for col_index, item in enumerate(row)])
    dimension = len(matrix)
    for row_index, parsed_row in enumerate(matrix):
        if len(parsed_row) != dimension:
            raise ManifestError(f"{field}[{row_index}] must have length {dimension}")
    return matrix


def parse_real_square_matrix_list(raw: object, field: str) -> list[list[list[float]]]:
    items = require_list(raw, field)
    if not items:
        raise ManifestError(f"{field} must not be empty")
    matrices = [parse_real_square_matrix(item, f"{field}[{index}]") for index, item in enumerate(items)]
    dimension = len(matrices[0])
    for index, matrix in enumerate(matrices):
        if len(matrix) != dimension:
            raise ManifestError(f"{field}[{index}] has incompatible dimension")
    return matrices


def parse_vector(raw: object, field: str) -> list[complex]:
    items = require_list(raw, field)
    return [parse_complex(item, f"{field}[{index}]") for index, item in enumerate(items)]


def parse_complex(raw: object, field: str) -> complex:
    if isinstance(raw, bool):
        raise ManifestError(f"{field} must be numeric, not boolean")
    if isinstance(raw, int | float):
        return complex(float(raw), 0.0)
    mapping = require_mapping(raw, field)
    return complex(parse_real(mapping.get("re", 0.0), f"{field}.re"), parse_real(mapping.get("im", 0.0), f"{field}.im"))


def parse_real(raw: object, field: str) -> float:
    if isinstance(raw, bool) or not isinstance(raw, int | float):
        raise ManifestError(f"{field} must be numeric")
    value = float(raw)
    if not math.isfinite(value):
        raise ManifestError(f"{field} must be finite")
    return value


def parse_optional_real(raw: object, field: str) -> float | None:
    if raw is None:
        return None
    return parse_real(raw, field)


def parse_tolerance(raw: object, field: str) -> float:
    tolerance = parse_real(raw, field)
    if tolerance <= 0.0:
        raise ManifestError(f"{field} must be positive")
    return tolerance


def parse_positive_real(raw: object, field: str) -> float:
    value = parse_real(raw, field)
    if value <= 0.0:
        raise ManifestError(f"{field} must be positive")
    return value


def parse_nonnegative_real(raw: object, field: str) -> float:
    value = parse_real(raw, field)
    if value < 0.0:
        raise ManifestError(f"{field} must be nonnegative")
    return value


def parse_unit_interval(raw: object, field: str) -> float:
    value = parse_nonnegative_real(raw, field)
    if value > 1.0:
        raise ManifestError(f"{field} must be <= 1")
    return value


def parse_nonnegative_real_list(raw: object, field: str) -> list[float]:
    items = require_list(raw, field)
    return [parse_nonnegative_real(item, f"{field}[{index}]") for index, item in enumerate(items)]


def parse_dimension_list(raw: object, field: str) -> list[Dimension]:
    items = require_list(raw, field)
    dimensions: list[Dimension] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        dimensions.append(Dimension.from_mapping(item_map.get("dimension", {}), f"{field}[{index}].dimension"))
    return dimensions


def dimension_in_rational_span(target: Dimension, sources: list[Dimension]) -> bool:
    if not sources:
        return target == Dimension.dimensionless()
    rows = [
        [Fraction(source.exponents[row_index]) for source in sources]
        for row_index in range(len(BASE_UNITS))
    ]
    augmented_rows = [
        [*row, Fraction(target.exponents[row_index])] for row_index, row in enumerate(rows)
    ]
    return rational_rank(rows) == rational_rank(augmented_rows)


def rational_rank(rows: list[list[Fraction]]) -> int:
    matrix = [row[:] for row in rows]
    if not matrix:
        return 0
    row_count = len(matrix)
    column_count = len(matrix[0])
    rank = 0
    for column in range(column_count):
        pivot = next((row for row in range(rank, row_count) if matrix[row][column] != 0), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        pivot_value = matrix[rank][column]
        matrix[rank] = [value / pivot_value for value in matrix[rank]]
        for row in range(row_count):
            if row == rank or matrix[row][column] == 0:
                continue
            factor = matrix[row][column]
            matrix[row] = [
                value - factor * pivot_row_value
                for value, pivot_row_value in zip(matrix[row], matrix[rank], strict=True)
            ]
        rank += 1
        if rank == row_count:
            break
    return rank


def parse_positive_integer(raw: object, field: str) -> int:
    value = parse_integer(raw, field)
    if value <= 0:
        raise ManifestError(f"{field} must be positive")
    return value


def parse_nonnegative_integer(raw: object, field: str) -> int:
    value = parse_integer(raw, field)
    if value < 0:
        raise ManifestError(f"{field} must be nonnegative")
    return value


def relative_error(computed: float, expected: float) -> float:
    return abs((computed / expected) - 1.0)


def relative_spread(values: list[float]) -> float:
    mean_value = sum(values) / len(values)
    if mean_value <= 0.0:
        raise ManifestError("relative spread requires positive mean")
    return (max(values) - min(values)) / mean_value


def matrix_trace(matrix: list[list[float]]) -> float:
    return sum(matrix[index][index] for index in range(len(matrix)))


def stress_decomposition(stress_matrix: list[list[float]]) -> tuple[float, list[list[float]]]:
    dimension = len(stress_matrix)
    pressure = matrix_trace(stress_matrix) / float(dimension)
    anisotropic = [row[:] for row in stress_matrix]
    for index in range(dimension):
        anisotropic[index][index] -= pressure
    return pressure, anisotropic


def frobenius_norm(matrix: list[list[float]]) -> float:
    return math.sqrt(sum(value * value for row in matrix for value in row))


def max_matrix_abs_difference(left: list[list[float]], right: list[list[float]]) -> float:
    if len(left) != len(right):
        raise ManifestError("matrix dimensions must match")
    max_difference = 0.0
    for row_index, row in enumerate(left):
        if len(row) != len(right[row_index]):
            raise ManifestError("matrix dimensions must match")
        for col_index, value in enumerate(row):
            max_difference = max(max_difference, abs(value - right[row_index][col_index]))
    return max_difference


def parse_phase_edges(raw: object, field: str) -> dict[tuple[str, str], float]:
    items = require_list(raw, field)
    edges: dict[tuple[str, str], float] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        phase = parse_real(item_map.get("phase"), f"{field}[{index}].phase")
        edges[(source, target)] = phase
    return edges


def parse_real_mapping(raw: object, field: str) -> dict[str, float]:
    mapping = require_mapping(raw, field)
    return {key: parse_real(value, f"{field}.{key}") for key, value in mapping.items()}


def parse_index_tuple(raw: object, field: str) -> tuple[int, ...]:
    items = require_list(raw, field)
    indexes: list[int] = []
    for index, item in enumerate(items):
        if isinstance(item, bool) or not isinstance(item, int):
            raise ManifestError(f"{field}[{index}] must be an integer")
        indexes.append(item)
    return tuple(indexes)


def parse_event_context(raw: object, field: str) -> list[tuple[int, ...]]:
    items = require_list(raw, field)
    return [parse_index_tuple(item, f"{field}[{index}]") for index, item in enumerate(items)]


def parse_fringe_samples(raw: object, field: str) -> list[dict[str, object]]:
    items = require_list(raw, field)
    samples: list[dict[str, object]] = []
    if not items:
        raise ManifestError(f"{field} must not be empty")
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        samples.append(
            {
                "phase": parse_real(item_map.get("phase"), f"{field}[{index}].phase"),
                "expected_probability": parse_real(
                    item_map.get("expected_probability"),
                    f"{field}[{index}].expected_probability",
                ),
            }
        )
    return samples


def parse_real_list(raw: object, field: str) -> list[float]:
    items = require_list(raw, field)
    return [parse_real(item, f"{field}[{index}]") for index, item in enumerate(items)]


def parse_flow_pairs(raw: object, field: str) -> list[tuple[float, float, float]]:
    items = require_list(raw, field)
    pairs: list[tuple[float, float, float]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        pairs.append(
            (
                parse_real(item_map.get("left"), f"{field}[{index}].left"),
                parse_real(item_map.get("right"), f"{field}[{index}].right"),
                parse_real(item_map.get("sum"), f"{field}[{index}].sum"),
            )
        )
    return pairs


def parse_bell_contexts(raw: object, field: str) -> dict[tuple[int, int], dict[tuple[int, int], float]]:
    items = require_list(raw, field)
    contexts: dict[tuple[int, int], dict[tuple[int, int], float]] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        x_value = parse_binary_setting(item_map.get("x"), f"{field}[{index}].x")
        y_value = parse_binary_setting(item_map.get("y"), f"{field}[{index}].y")
        key = (x_value, y_value)
        if key in contexts:
            raise ManifestError(f"{field}[{index}] duplicates context {key}")
        contexts[key] = parse_bell_probabilities(item_map.get("probabilities"), f"{field}[{index}].probabilities")
    return contexts


def parse_bell_amplitude_contexts(raw: object, field: str) -> dict[tuple[int, int], dict[tuple[int, int], complex]]:
    items = require_list(raw, field)
    contexts: dict[tuple[int, int], dict[tuple[int, int], complex]] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        x_value = parse_binary_setting(item_map.get("x"), f"{field}[{index}].x")
        y_value = parse_binary_setting(item_map.get("y"), f"{field}[{index}].y")
        key = (x_value, y_value)
        if key in contexts:
            raise ManifestError(f"{field}[{index}] duplicates context {key}")
        contexts[key] = parse_bell_amplitudes(item_map.get("amplitudes"), f"{field}[{index}].amplitudes")
    return contexts


def parse_bell_probabilities(raw: object, field: str) -> dict[tuple[int, int], float]:
    items = require_list(raw, field)
    probabilities: dict[tuple[int, int], float] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        outcome_a = parse_bell_outcome(item_map.get("a"), f"{field}[{index}].a")
        outcome_b = parse_bell_outcome(item_map.get("b"), f"{field}[{index}].b")
        key = (outcome_a, outcome_b)
        if key in probabilities:
            raise ManifestError(f"{field}[{index}] duplicates outcome {key}")
        probabilities[key] = parse_real(item_map.get("p"), f"{field}[{index}].p")
    expected_outcomes = {(-1, -1), (-1, 1), (1, -1), (1, 1)}
    if set(probabilities) != expected_outcomes:
        raise ManifestError(f"{field} must contain all four +-1 outcomes")
    return probabilities


def parse_bell_amplitudes(raw: object, field: str) -> dict[tuple[int, int], complex]:
    items = require_list(raw, field)
    amplitudes: dict[tuple[int, int], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        outcome_a = parse_bell_outcome(item_map.get("a"), f"{field}[{index}].a")
        outcome_b = parse_bell_outcome(item_map.get("b"), f"{field}[{index}].b")
        key = (outcome_a, outcome_b)
        if key in amplitudes:
            raise ManifestError(f"{field}[{index}] duplicates outcome {key}")
        amplitudes[key] = parse_complex(item_map.get("amp"), f"{field}[{index}].amp")
    expected_outcomes = {(-1, -1), (-1, 1), (1, -1), (1, 1)}
    if set(amplitudes) != expected_outcomes:
        raise ManifestError(f"{field} must contain all four +-1 outcomes")
    return amplitudes


def parse_binary_setting(raw: object, field: str) -> int:
    value = parse_integer(raw, field)
    if value not in {0, 1}:
        raise ManifestError(f"{field} must be 0 or 1")
    return value


def parse_bell_outcome(raw: object, field: str) -> int:
    value = parse_integer(raw, field)
    if value not in {-1, 1}:
        raise ManifestError(f"{field} must be -1 or 1")
    return value


def parse_positive_real_vector(raw: object, field: str) -> list[float]:
    items = require_list(raw, field)
    values = [parse_real(item, f"{field}[{index}]") for index, item in enumerate(items)]
    if not values:
        raise ManifestError(f"{field} must not be empty")
    for value in values:
        if value <= 0.0:
            raise ManifestError(f"{field} values must be positive")
    return values


def parse_phase_action_scale_cycles(raw: object, field: str) -> list[PhaseActionScaleCycle]:
    items = require_list(raw, field)
    cycles: list[PhaseActionScaleCycle] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cost = parse_positive_real(item_map.get("cost"), f"{field}[{index}].cost")
        phase = parse_real(item_map.get("phase"), f"{field}[{index}].phase")
        if phase == 0.0:
            raise ManifestError(f"{field}[{index}].phase must be nonzero")
        if role == "excluded":
            continue
        cycles.append(
            PhaseActionScaleCycle(
                identifier=require_string(item_map.get("id"), f"{field}[{index}].id"),
                role=role,
                cost=cost,
                phase=phase,
            )
        )
    return cycles


def parse_phase_cost_cycles(raw: object, field: str) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cycle_class = require_string(item_map.get("class"), f"{field}[{index}].class")
        if cycle_class not in {"small", "topological", "clock_strain", "other"}:
            raise ManifestError(f"{field}[{index}].class has unknown cycle class")
        branch_source = require_string(item_map.get("branch_source"), f"{field}[{index}].branch_source")
        if branch_source not in {"principal", "winding", "grammar"}:
            raise ManifestError(f"{field}[{index}].branch_source has unknown source")
        admissible = parse_bool(item_map.get("admissible", True), f"{field}[{index}].admissible")
        if role == "excluded" and not item_map.get("reason"):
            raise ManifestError(f"{field}[{index}] excluded cycle must provide reason")
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": require_string_tuple(item_map.get("word"), f"{field}[{index}].word"),
                "role": role,
                "class": cycle_class,
                "branch_source": branch_source,
                "admissible": admissible,
                "theta": parse_real(item_map.get("theta"), f"{field}[{index}].theta"),
                "cost": parse_real(item_map.get("cost"), f"{field}[{index}].cost"),
            }
        )
    return cycles


def parse_phase_cost_cycles_from_edges(
    raw: object, field: str, edge_costs: dict[tuple[str, str], float]
) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cycle_class = require_string(item_map.get("class"), f"{field}[{index}].class")
        if cycle_class not in {"small", "topological", "clock_strain", "other"}:
            raise ManifestError(f"{field}[{index}].class has unknown cycle class")
        branch_source = require_string(item_map.get("branch_source"), f"{field}[{index}].branch_source")
        if branch_source not in {"principal", "winding", "grammar"}:
            raise ManifestError(f"{field}[{index}].branch_source has unknown source")
        admissible = parse_bool(item_map.get("admissible", True), f"{field}[{index}].admissible")
        if role == "excluded" and not item_map.get("reason"):
            raise ManifestError(f"{field}[{index}] excluded cycle must provide reason")
        word = require_string_tuple(item_map.get("word"), f"{field}[{index}].word")
        cost = 0.0 if role == "excluded" else cycle_word_cost(word, edge_costs)
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": word,
                "role": role,
                "class": cycle_class,
                "branch_source": branch_source,
                "admissible": admissible,
                "theta": parse_real(item_map.get("theta"), f"{field}[{index}].theta"),
                "cost": cost,
            }
        )
    return cycles


def parse_phase_cost_cycles_from_holonomy(
    raw: object,
    field: str,
    edge_costs: dict[tuple[str, str], float],
    phase_edges: dict[tuple[str, str], float],
) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cycle_class = require_string(item_map.get("class"), f"{field}[{index}].class")
        if cycle_class not in {"small", "topological", "clock_strain", "other"}:
            raise ManifestError(f"{field}[{index}].class has unknown cycle class")
        branch_source = require_string(item_map.get("branch_source"), f"{field}[{index}].branch_source")
        if branch_source not in {"principal", "winding"}:
            raise ManifestError(f"{field}[{index}].branch_source must be principal or winding")
        winding = parse_integer(item_map.get("winding", 0), f"{field}[{index}].winding")
        if branch_source == "principal" and winding != 0:
            raise ManifestError(f"{field}[{index}] principal branch must use winding 0")
        admissible = parse_bool(item_map.get("admissible", True), f"{field}[{index}].admissible")
        if role == "excluded" and not item_map.get("reason"):
            raise ManifestError(f"{field}[{index}] excluded cycle must provide reason")
        word = require_string_tuple(item_map.get("word"), f"{field}[{index}].word")
        cost = 0.0 if role == "excluded" else cycle_word_cost(word, edge_costs)
        theta = 0.0 if role == "excluded" else cycle_lifted_phase(word, phase_edges, winding)
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": word,
                "role": role,
                "class": cycle_class,
                "branch_source": branch_source,
                "admissible": admissible,
                "theta": theta,
                "cost": cost,
            }
        )
    return cycles


def parse_phase_cost_cycles_from_unit_holonomy(
    raw: object,
    field: str,
    edge_costs: dict[tuple[str, str], float],
    tolerance: float,
) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cycle_class = require_string(item_map.get("class"), f"{field}[{index}].class")
        if cycle_class not in {"small", "topological", "clock_strain", "other"}:
            raise ManifestError(f"{field}[{index}].class has unknown cycle class")
        branch_source = require_string(item_map.get("branch_source"), f"{field}[{index}].branch_source")
        if branch_source not in {"principal", "winding"}:
            raise ManifestError(f"{field}[{index}].branch_source must be principal or winding")
        winding = parse_integer(item_map.get("winding", 0), f"{field}[{index}].winding")
        if branch_source == "principal" and winding != 0:
            raise ManifestError(f"{field}[{index}] principal branch must use winding 0")
        admissible = parse_bool(item_map.get("admissible", True), f"{field}[{index}].admissible")
        if role == "excluded" and not item_map.get("reason"):
            raise ManifestError(f"{field}[{index}] excluded cycle must provide reason")
        word = require_string_tuple(item_map.get("word"), f"{field}[{index}].word")
        cost = 0.0 if role == "excluded" else cycle_word_cost(word, edge_costs)
        theta = 0.0
        if role != "excluded":
            unit_holonomy = parse_complex(item_map.get("unit_holonomy"), f"{field}[{index}].unit_holonomy")
            theta = lifted_phase_from_unit_holonomy(unit_holonomy, winding, tolerance)
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": word,
                "role": role,
                "class": cycle_class,
                "branch_source": branch_source,
                "admissible": admissible,
                "theta": theta,
                "cost": cost,
            }
        )
    return cycles


def parse_phase_cost_cycles_from_unit_edges(
    raw: object,
    field: str,
    edge_costs: dict[tuple[str, str], float],
    unit_edges: dict[tuple[str, str], complex],
    tolerance: float,
) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        role = require_string(item_map.get("role"), f"{field}[{index}].role")
        if role not in {"calibration", "validation", "excluded"}:
            raise ManifestError(f"{field}[{index}].role must be calibration, validation, or excluded")
        cycle_class = require_string(item_map.get("class"), f"{field}[{index}].class")
        if cycle_class not in {"small", "topological", "clock_strain", "other"}:
            raise ManifestError(f"{field}[{index}].class has unknown cycle class")
        branch_source = require_string(item_map.get("branch_source"), f"{field}[{index}].branch_source")
        if branch_source not in {"principal", "winding"}:
            raise ManifestError(f"{field}[{index}].branch_source must be principal or winding")
        winding = parse_integer(item_map.get("winding", 0), f"{field}[{index}].winding")
        if branch_source == "principal" and winding != 0:
            raise ManifestError(f"{field}[{index}] principal branch must use winding 0")
        admissible = parse_bool(item_map.get("admissible", True), f"{field}[{index}].admissible")
        if role == "excluded" and not item_map.get("reason"):
            raise ManifestError(f"{field}[{index}] excluded cycle must provide reason")
        word = require_string_tuple(item_map.get("word"), f"{field}[{index}].word")
        cost = 0.0 if role == "excluded" else cycle_word_cost(word, edge_costs)
        theta = 0.0
        if role != "excluded":
            unit_holonomy = cycle_unit_holonomy(word, unit_edges)
            theta = lifted_phase_from_unit_holonomy(unit_holonomy, winding, tolerance)
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": word,
                "role": role,
                "class": cycle_class,
                "branch_source": branch_source,
                "admissible": admissible,
                "theta": theta,
                "cost": cost,
            }
        )
    return cycles


def parse_edge_costs(raw: object, field: str) -> dict[tuple[str, str], float]:
    items = require_list(raw, field)
    edge_costs: dict[tuple[str, str], float] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        cost = parse_real(item_map.get("cost"), f"{field}[{index}].cost")
        if cost < 0.0:
            raise ManifestError(f"{field}[{index}].cost must be non-negative")
        edge_costs[(source, target)] = cost
    return edge_costs


def parse_kernel_edge_costs(raw: object, field: str) -> dict[tuple[str, str], float]:
    items = require_list(raw, field)
    edge_costs: dict[tuple[str, str], float] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        g0_diag = parse_positive_real_vector(item_map.get("G0_diag"), f"{field}[{index}].G0_diag")
        g1_diag = parse_positive_real_vector(item_map.get("G1_diag"), f"{field}[{index}].G1_diag")
        alignment = parse_index_tuple(item_map.get("alignment"), f"{field}[{index}].alignment")
        edge_costs[(source, target)] = diagonal_kernel_strain_cost(g0_diag, g1_diag, alignment)
    return edge_costs


def parse_unit_edges(raw: object, field: str, tolerance: float) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        unit_transfer = parse_complex(item_map.get("unit_transfer"), f"{field}[{index}].unit_transfer")
        unit_edges[(source, target)] = validate_unit_complex(unit_transfer, tolerance, "unit_transfer")
    return unit_edges


def parse_transfer_edges(raw: object, field: str, tolerance: float) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        transfer = parse_complex(item_map.get("transfer"), f"{field}[{index}].transfer")
        unit_edges[(source, target)] = transfer_phase_unit(transfer, tolerance)
    return unit_edges


def parse_transfer_block_edges(raw: object, field: str, tolerance: float) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        block = parse_matrix(item_map.get("block"), f"{field}[{index}].block")
        unit_edges[(source, target)] = transfer_block_phase_unit(block, tolerance)
    return unit_edges


def parse_block_kernel_edges(raw: object, field: str, tolerance: float) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        g0 = parse_matrix(item_map.get("G0"), f"{field}[{index}].G0")
        g1 = parse_matrix(item_map.get("G1"), f"{field}[{index}].G1")
        cross = parse_matrix(item_map.get("X"), f"{field}[{index}].X")
        unit_edges[(source, target)] = block_kernel_transfer_phase_unit(g0, g1, cross, tolerance)
    return unit_edges


def parse_normalized_block_kernel_edges(
    raw: object, field: str, tolerance: float
) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        g0_diag = parse_positive_real_vector(item_map.get("G0_diag"), f"{field}[{index}].G0_diag")
        g1_diag = parse_positive_real_vector(item_map.get("G1_diag"), f"{field}[{index}].G1_diag")
        cross = parse_matrix(item_map.get("X"), f"{field}[{index}].X")
        unit_edges[(source, target)] = normalized_block_kernel_phase_unit(
            g0_diag, g1_diag, cross, tolerance
        )
    return unit_edges


def parse_spectral_block_kernel_edges(
    raw: object, field: str, tolerance: float
) -> dict[tuple[str, str], complex]:
    items = require_list(raw, field)
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        g0 = parse_matrix(item_map.get("G0"), f"{field}[{index}].G0")
        g1 = parse_matrix(item_map.get("G1"), f"{field}[{index}].G1")
        cross = parse_matrix(item_map.get("X"), f"{field}[{index}].X")
        unit_edges[(source, target)] = spectral_block_kernel_phase_unit(g0, g1, cross, tolerance)
    return unit_edges


def parse_spectral_kernel_block_readouts(
    raw: object, field: str, tolerance: float
) -> tuple[dict[tuple[str, str], float], dict[tuple[str, str], complex]]:
    items = require_list(raw, field)
    edge_costs: dict[tuple[str, str], float] = {}
    unit_edges: dict[tuple[str, str], complex] = {}
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        source = require_string(item_map.get("from"), f"{field}[{index}].from")
        target = require_string(item_map.get("to"), f"{field}[{index}].to")
        g0 = parse_matrix(item_map.get("G0"), f"{field}[{index}].G0")
        g1 = parse_matrix(item_map.get("G1"), f"{field}[{index}].G1")
        cross = parse_matrix(item_map.get("X"), f"{field}[{index}].X")
        edge_cost, unit_phase = spectral_kernel_block_readout(g0, g1, cross, tolerance)
        edge_costs[(source, target)] = edge_cost
        unit_edges[(source, target)] = unit_phase
    return edge_costs, unit_edges


def parse_cycle_cost_expectations(raw: object, field: str) -> list[dict[str, object]]:
    items = require_list(raw, field)
    cycles: list[dict[str, object]] = []
    for index, item in enumerate(items):
        item_map = require_mapping(item, f"{field}[{index}]")
        cycles.append(
            {
                "id": require_string(item_map.get("id"), f"{field}[{index}].id"),
                "word": require_string_tuple(item_map.get("word"), f"{field}[{index}].word"),
                "expected_cost": parse_real(item_map.get("expected_cost"), f"{field}[{index}].expected_cost"),
            }
        )
    return cycles


def parse_bool(raw: object, field: str) -> bool:
    if not isinstance(raw, bool):
        raise ManifestError(f"{field} must be boolean")
    return raw


def parse_integer(raw: object, field: str) -> int:
    if isinstance(raw, bool) or not isinstance(raw, int):
        raise ManifestError(f"{field} must be an integer")
    return raw


def validate_phase_cost_cycles(
    gate_id: str, cycles: list[dict[str, object]], tolerance: float
) -> list[Issue]:
    seen_words: set[tuple[str, ...]] = set()
    seen_ids: set[str] = set()
    for cycle in cycles:
        cycle_id = require_string(cycle["id"], f"{gate_id}.cycle.id")
        word = require_parsed_string_tuple(cycle["word"], f"{gate_id}.{cycle_id}.word")
        if cycle_id in seen_ids:
            return [Issue("duplicate_cycle_id", f"{gate_id}: duplicate cycle id {cycle_id}")]
        seen_ids.add(cycle_id)
        if word in seen_words:
            return [Issue("duplicate_active_cycle", f"{gate_id}: duplicate active cycle word {cycle_id}")]
        seen_words.add(word)
        if len(word) < 2 or word[0] != word[-1]:
            return [Issue("cycle_word_not_closed", f"{gate_id}: cycle {cycle_id} is not closed")]
        if not parse_bool(cycle["admissible"], f"{gate_id}.{cycle_id}.admissible"):
            return [Issue("inadmissible_active_cycle", f"{gate_id}: active cycle {cycle_id} is inadmissible")]
        if abs(parse_real(cycle["theta"], f"{gate_id}.{cycle_id}.theta")) <= tolerance:
            return [Issue("zero_cycle_phase", f"{gate_id}: active cycle {cycle_id} has zero lifted phase")]
        if parse_real(cycle["cost"], f"{gate_id}.{cycle_id}.cost") <= tolerance:
            return [Issue("nonpositive_cycle_cost", f"{gate_id}: active cycle {cycle_id} has non-positive cost")]
    return []


def phase_cost_slope(cycle: dict[str, object]) -> float:
    return parse_real(cycle["theta"], "cycle.theta") / parse_real(cycle["cost"], "cycle.cost")


def require_parsed_string_tuple(value: object, field: str) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise ManifestError(f"{field} must be a parsed tuple")
    output: list[str] = []
    for index, item in enumerate(value):
        output.append(require_string(item, f"{field}[{index}]"))
    return tuple(output)


def normalize_positive_vector(values: list[float]) -> list[float]:
    total = sum(values)
    if total <= 0.0:
        raise ManifestError("cannot normalize vector with non-positive total")
    return [value / total for value in values]


def diagonal_kernel_strain_cost(
    g0_diag: list[float], g1_diag: list[float], alignment: tuple[int, ...]
) -> float:
    if len(alignment) != len(g1_diag):
        raise ManifestError("alignment length must match G1_diag length")
    if set(alignment) != set(range(len(g0_diag))):
        raise ManifestError("alignment must be a permutation of G0 indexes")
    if len(g0_diag) != len(g1_diag):
        raise ManifestError("diagonal kernel cost currently requires equal dimensions")
    p0 = normalize_positive_vector(g0_diag)
    p1 = normalize_positive_vector(g1_diag)
    transported_p0 = [p0[source_index] for source_index in alignment]
    return bures_angle_cost_diagonal(transported_p0, p1)


def bures_angle_cost_diagonal(left: list[float], right: list[float]) -> float:
    if len(left) != len(right):
        raise ManifestError("Bures diagonal inputs must have equal length")
    fidelity = sum(math.sqrt(left[index] * right[index]) for index in range(len(left)))
    clamped_fidelity = min(1.0, max(0.0, fidelity))
    return math.acos(clamped_fidelity) ** 2


def density_matrix_from_psd(
    matrix: list[list[complex]], tolerance: float, name: str
) -> list[list[complex]]:
    validate_square_block(matrix, name)
    if len(matrix) > 2:
        raise ManifestError(f"{name} density readout currently supports size 1 or 2")
    if matrix_psd_issues(name, matrix, tolerance):
        raise ManifestError(f"{name} must be PSD")
    trace_value = real_trace(matrix, tolerance, name)
    if trace_value <= tolerance:
        raise ManifestError(f"{name} trace must be positive")
    return [[value / trace_value for value in row] for row in matrix]


def real_trace(matrix: list[list[complex]], tolerance: float, name: str) -> float:
    trace_value = sum(matrix[index][index] for index in range(len(matrix)))
    if abs(trace_value.imag) > tolerance:
        raise ManifestError(f"{name} trace must be real")
    return trace_value.real


def bures_angle_cost_density(
    left: list[list[complex]], right: list[list[complex]], tolerance: float
) -> float:
    validate_square_block(left, "left density")
    validate_square_block(right, "right density")
    if len(left) != len(right):
        raise ManifestError("Bures density inputs must have equal size")
    if len(left) == 1:
        return 0.0
    if len(left) > 2:
        raise ManifestError("Bures density readout currently supports size 1 or 2")
    left_issues = matrix_psd_issues("left_density", left, tolerance)
    right_issues = matrix_psd_issues("right_density", right, tolerance)
    if left_issues or right_issues:
        raise ManifestError("Bures density inputs must be PSD")
    trace_product = real_trace(matrix_multiply(left, right), tolerance, "density_product")
    left_det = real_determinant(left, tolerance, "left_density")
    right_det = real_determinant(right, tolerance, "right_density")
    squared_fidelity = trace_product + (2.0 * math.sqrt(max(0.0, left_det * right_det)))
    root_fidelity = math.sqrt(min(1.0, max(0.0, squared_fidelity)))
    return math.acos(root_fidelity) ** 2


def real_determinant(matrix: list[list[complex]], tolerance: float, name: str) -> float:
    det = determinant(matrix)
    if abs(det.imag) > tolerance:
        raise ManifestError(f"{name} determinant must be real")
    return det.real


def cycle_word_cost(word: tuple[str, ...], edge_costs: dict[tuple[str, str], float]) -> float:
    total = 0.0
    for index in range(len(word) - 1):
        edge = (word[index], word[index + 1])
        if edge not in edge_costs:
            raise ManifestError(f"cycle references missing cost edge {edge[0]}->{edge[1]}")
        total += edge_costs[edge]
    return total


def cycle_lifted_phase(
    word: tuple[str, ...], phase_edges: dict[tuple[str, str], float], winding: int
) -> float:
    return cycle_phase(word, phase_edges) + (2.0 * math.pi * float(winding))


def lifted_phase_from_unit_holonomy(unit_holonomy: complex, winding: int, tolerance: float) -> float:
    unit_value = validate_unit_complex(unit_holonomy, tolerance, "unit_holonomy")
    return math.atan2(unit_value.imag, unit_value.real) + (2.0 * math.pi * float(winding))


def cycle_unit_holonomy(word: tuple[str, ...], unit_edges: dict[tuple[str, str], complex]) -> complex:
    unit_holonomy = complex(1.0, 0.0)
    for index in range(len(word) - 1):
        edge = (word[index], word[index + 1])
        if edge not in unit_edges:
            raise ManifestError(f"cycle references missing unit edge {edge[0]}->{edge[1]}")
        unit_holonomy *= unit_edges[edge]
    return unit_holonomy


def validate_unit_complex(value: complex, tolerance: float, name: str) -> complex:
    if abs(abs(value) - 1.0) > tolerance:
        raise ManifestError(f"{name} must have unit magnitude")
    return value


def transfer_phase_unit(transfer: complex, tolerance: float) -> complex:
    magnitude = abs(transfer)
    if magnitude <= tolerance:
        raise ManifestError("transfer element must be nonzero")
    if magnitude > 1.0 + tolerance:
        raise ManifestError("transfer element violates contraction bound")
    return transfer / magnitude


def transfer_block_phase_unit(block: list[list[complex]], tolerance: float) -> complex:
    validate_square_block(block, "transfer block")
    if len(block) > 6:
        raise ManifestError("transfer block currently supports matrices up to 6x6")
    gram = matrix_multiply(conjugate_transpose(block), block)
    complement = identity_minus(gram)
    if matrix_psd_issues("transfer_block", complement, tolerance):
        raise ManifestError("transfer block violates contraction bound")
    det = determinant(block)
    return transfer_phase_unit(det, tolerance)


def block_kernel_transfer_phase_unit(
    g0: list[list[complex]], g1: list[list[complex]], cross: list[list[complex]], tolerance: float
) -> complex:
    validate_square_block(g0, "G0")
    validate_square_block(g1, "G1")
    if len(g0) != len(g1):
        raise ManifestError("block kernel phase readout currently requires equal block sizes")
    validate_square_block(cross, "X")
    if len(cross) != len(g1):
        raise ManifestError("X size must match G0 and G1")
    block_kernel = compose_block_kernel(g0, g1, cross)
    if matrix_psd_issues("block_kernel", block_kernel, tolerance):
        raise ManifestError("block kernel is not PSD")
    return transfer_block_phase_unit(cross, tolerance)


def normalized_block_kernel_phase_unit(
    g0_diag: list[float], g1_diag: list[float], cross: list[list[complex]], tolerance: float
) -> complex:
    if len(g0_diag) != len(g1_diag):
        raise ManifestError("normalized block kernel currently requires equal support dimensions")
    validate_square_block(cross, "X")
    if len(cross) != len(g1_diag):
        raise ManifestError("X size must match G0_diag and G1_diag")
    g0 = diagonal_matrix(g0_diag)
    g1 = diagonal_matrix(g1_diag)
    block_kernel = compose_block_kernel(g0, g1, cross)
    if matrix_psd_issues("normalized_block_kernel", block_kernel, tolerance):
        raise ManifestError("normalized block kernel is not PSD")
    support_contraction = normalize_cross_block(g0_diag, g1_diag, cross)
    return transfer_block_phase_unit(support_contraction, tolerance)


def spectral_block_kernel_phase_unit(
    g0: list[list[complex]], g1: list[list[complex]], cross: list[list[complex]], tolerance: float
) -> complex:
    _cost, unit_phase = spectral_kernel_block_readout(g0, g1, cross, tolerance)
    return unit_phase


def spectral_kernel_block_readout(
    g0: list[list[complex]], g1: list[list[complex]], cross: list[list[complex]], tolerance: float
) -> tuple[float, complex]:
    validate_square_block(g0, "G0")
    validate_square_block(g1, "G1")
    validate_square_block(cross, "X")
    if len(g0) != len(g1) or len(cross) != len(g0):
        raise ManifestError("spectral block kernel inputs must have matching square sizes")
    g0_inv_sqrt = hermitian_inverse_sqrt_small(g0, tolerance, "G0")
    g1_inv_sqrt = hermitian_inverse_sqrt_small(g1, tolerance, "G1")
    block_kernel = compose_block_kernel(g0, g1, cross)
    if matrix_psd_issues("spectral_block_kernel", block_kernel, tolerance):
        raise ManifestError("spectral block kernel is not PSD")
    support_contraction = matrix_multiply(matrix_multiply(g1_inv_sqrt, cross), g0_inv_sqrt)
    rho0 = density_matrix_from_psd(g0, tolerance, "rho0")
    rho1 = density_matrix_from_psd(g1, tolerance, "rho1")
    transported = matrix_multiply(
        matrix_multiply(support_contraction, rho0),
        conjugate_transpose(support_contraction),
    )
    transported_rho0 = density_matrix_from_psd(transported, tolerance, "rho0_transported")
    cost = bures_angle_cost_density(transported_rho0, rho1, tolerance)
    unit_phase = transfer_block_phase_unit(support_contraction, tolerance)
    return cost, unit_phase


def normalize_cross_block(
    g0_diag: list[float], g1_diag: list[float], cross: list[list[complex]]
) -> list[list[complex]]:
    return [
        [
            cross[row][col] / math.sqrt(g1_diag[row] * g0_diag[col])
            for col in range(len(g0_diag))
        ]
        for row in range(len(g1_diag))
    ]


def diagonal_matrix(values: list[float]) -> list[list[complex]]:
    return [
        [complex(values[row], 0.0) if row == col else 0.0 + 0.0j for col in range(len(values))]
        for row in range(len(values))
    ]


def diagonal_limit_cross_block(
    g0_diag: list[float], g1_diag: list[float], alignment: tuple[int, ...]
) -> list[list[complex]]:
    if len(g0_diag) != len(g1_diag):
        raise ManifestError("diagonal limit currently requires equal support dimensions")
    if len(alignment) != len(g1_diag):
        raise ManifestError("alignment length must match G1_diag length")
    if set(alignment) != set(range(len(g0_diag))):
        raise ManifestError("alignment must be a permutation of G0 indexes")
    cross = [[0.0 + 0.0j for _col in range(len(g0_diag))] for _row in range(len(g1_diag))]
    for target_index, source_index in enumerate(alignment):
        cross[target_index][source_index] = complex(
            math.sqrt(g1_diag[target_index] * g0_diag[source_index]),
            0.0,
        )
    return cross


def validate_unitary(matrix: list[list[complex]], tolerance: float, name: str) -> None:
    validate_square_block(matrix, name)
    gram = matrix_multiply(conjugate_transpose(matrix), matrix)
    for row_index, row in enumerate(gram):
        for col_index, value in enumerate(row):
            expected = 1.0 if row_index == col_index else 0.0
            if abs(value - expected) > tolerance:
                raise ManifestError(f"{name} must be unitary")


def unitary_conjugate(
    unitary: list[list[complex]], matrix: list[list[complex]]
) -> list[list[complex]]:
    return matrix_multiply(matrix_multiply(unitary, matrix), conjugate_transpose(unitary))


def validate_projector_resolution(
    projectors: list[list[list[complex]]], state_size: int, tolerance: float
) -> None:
    resolution = [[0.0 + 0.0j for _col in range(state_size)] for _row in range(state_size)]
    for index, projector in enumerate(projectors):
        validate_projector(projector, state_size, tolerance, f"projectors[{index}]")
        resolution = matrix_add(resolution, projector)
    for row_index, row in enumerate(resolution):
        for col_index, value in enumerate(row):
            expected = 1.0 if row_index == col_index else 0.0
            if abs(value - expected) > tolerance:
                raise ManifestError("projectors must resolve the identity")


def validate_projector(
    projector: list[list[complex]], state_size: int, tolerance: float, name: str
) -> None:
    validate_square_block(projector, name)
    if len(projector) != state_size:
        raise ManifestError(f"{name} size must match state length")
    if not is_hermitian(projector, tolerance):
        raise ManifestError(f"{name} must be Hermitian")
    squared = matrix_multiply(projector, projector)
    for row_index, row in enumerate(squared):
        for col_index, value in enumerate(row):
            if abs(value - projector[row_index][col_index]) > tolerance:
                raise ManifestError(f"{name} must be idempotent")


def matrix_add(left: list[list[complex]], right: list[list[complex]]) -> list[list[complex]]:
    if len(left) != len(right) or len(left[0]) != len(right[0]):
        raise ManifestError("matrix dimensions must match")
    return [
        [left[row][col] + right[row][col] for col in range(len(left[row]))]
        for row in range(len(left))
    ]


def hermitian_inverse_sqrt_small(
    matrix: list[list[complex]], tolerance: float, name: str
) -> list[list[complex]]:
    validate_square_block(matrix, name)
    if len(matrix) > 2:
        raise ManifestError(f"{name} spectral normalization currently supports size 1 or 2")
    if not is_hermitian(matrix, tolerance):
        raise ManifestError(f"{name} must be Hermitian")
    if len(matrix) == 1:
        value = real_diagonal_entry(matrix[0][0], tolerance, f"{name}[0,0]")
        if value <= tolerance:
            raise ManifestError(f"{name} must be positive definite")
        return [[complex(1.0 / math.sqrt(value), 0.0)]]

    a = real_diagonal_entry(matrix[0][0], tolerance, f"{name}[0,0]")
    d = real_diagonal_entry(matrix[1][1], tolerance, f"{name}[1,1]")
    z = matrix[0][1]
    center = (a + d) / 2.0
    radius = math.sqrt((((a - d) / 2.0) ** 2) + (abs(z) ** 2))
    lambda_high = center + radius
    lambda_low = center - radius
    if lambda_low <= tolerance:
        raise ManifestError(f"{name} must be positive definite")
    high_value = 1.0 / math.sqrt(lambda_high)
    low_value = 1.0 / math.sqrt(lambda_low)
    if abs(lambda_high - lambda_low) <= tolerance:
        return [[complex(low_value, 0.0), 0.0 + 0.0j], [0.0 + 0.0j, complex(low_value, 0.0)]]

    scale = (high_value - low_value) / (lambda_high - lambda_low)
    shift = low_value - (scale * lambda_low)
    return [
        [shift + (scale * matrix[0][0]), scale * matrix[0][1]],
        [scale * matrix[1][0], shift + (scale * matrix[1][1])],
    ]


def real_diagonal_entry(value: complex, tolerance: float, field: str) -> float:
    if abs(value.imag) > tolerance:
        raise ManifestError(f"{field} must be real")
    return value.real


def complex_matrix_rank(matrix: list[list[complex]], tolerance: float) -> int:
    if not matrix:
        return 0
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ManifestError("matrix rows must have equal length")
    reduced = [row.copy() for row in matrix]
    row_count = len(reduced)
    rank = 0
    for column in range(width):
        pivot = max(range(rank, row_count), key=lambda row: abs(reduced[row][column]), default=None)
        if pivot is None or abs(reduced[pivot][column]) <= tolerance:
            continue
        reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
        pivot_value = reduced[rank][column]
        reduced[rank] = [value / pivot_value for value in reduced[rank]]
        for row in range(row_count):
            if row == rank:
                continue
            factor = reduced[row][column]
            if abs(factor) <= tolerance:
                continue
            reduced[row] = [
                value - (factor * pivot_row_value)
                for value, pivot_row_value in zip(reduced[row], reduced[rank], strict=True)
            ]
        rank += 1
        if rank == row_count:
            break
    return rank


def compose_block_kernel(
    g0: list[list[complex]], g1: list[list[complex]], cross: list[list[complex]]
) -> list[list[complex]]:
    top_rows: list[list[complex]] = []
    for row_index, g0_row in enumerate(g0):
        top_rows.append([*g0_row, *[cross[col][row_index].conjugate() for col in range(len(g1))]])

    bottom_rows: list[list[complex]] = []
    for row_index, g1_row in enumerate(g1):
        bottom_rows.append([*cross[row_index], *g1_row])
    return [*top_rows, *bottom_rows]


def validate_square_block(block: list[list[complex]], name: str) -> None:
    if not block:
        raise ManifestError(f"{name} must not be empty")
    width = len(block[0])
    if width != len(block):
        raise ManifestError(f"{name} must be square")
    for row in block:
        if len(row) != width:
            raise ManifestError(f"{name} rows must have equal length")


def cycle_phase(cycle: tuple[str, ...], edges: dict[tuple[str, str], float]) -> float:
    phase = 0.0
    for index in range(len(cycle) - 1):
        edge = (cycle[index], cycle[index + 1])
        if edge not in edges:
            raise ManifestError(f"cycle references missing edge {edge[0]}->{edge[1]}")
        phase += edges[edge]
    return wrapped_angle(phase)


def wrapped_angle(angle: float) -> float:
    return (angle + math.pi) % (2.0 * math.pi) - math.pi


def is_hermitian(matrix: list[list[complex]], tolerance: float) -> bool:
    for row_index, row in enumerate(matrix):
        for col_index, value in enumerate(row):
            if abs(value - matrix[col_index][row_index].conjugate()) > tolerance:
                return False
    return True


def conjugate_transpose(matrix: list[list[complex]]) -> list[list[complex]]:
    height = len(matrix)
    width = len(matrix[0])
    return [[matrix[row][col].conjugate() for row in range(height)] for col in range(width)]


def matrix_multiply(left: list[list[complex]], right: list[list[complex]]) -> list[list[complex]]:
    if not left or not right:
        raise ManifestError("cannot multiply empty matrices")
    left_width = len(left[0])
    right_width = len(right[0])
    if left_width != len(right):
        raise ManifestError("matrix dimensions do not compose")
    return [
        [
            sum(left[row][inner] * right[inner][col] for inner in range(left_width))
            for col in range(right_width)
        ]
        for row in range(len(left))
    ]


def scalar_multiply_matrix(scalar: complex, matrix: list[list[complex]]) -> list[list[complex]]:
    return [[scalar * value for value in row] for row in matrix]


def complex_matrix_trace(matrix: list[list[complex]]) -> complex:
    if not matrix:
        raise ManifestError("cannot trace empty matrix")
    width = len(matrix[0])
    if width != len(matrix):
        raise ManifestError("trace requires a square matrix")
    return sum(matrix[index][index] for index in range(width))


def kronecker_product(left: list[list[complex]], right: list[list[complex]]) -> list[list[complex]]:
    if not left or not right:
        raise ManifestError("cannot tensor empty matrices")
    output: list[list[complex]] = []
    for left_row in left:
        rows: list[list[complex]] = [[] for _ in right]
        for left_value in left_row:
            for right_row_index, right_row in enumerate(right):
                rows[right_row_index].extend(left_value * right_value for right_value in right_row)
        output.extend(rows)
    return output


def diagonal_phase_matrix(phases: list[float]) -> list[list[complex]]:
    size = len(phases)
    matrix = zero_matrix(size, size)
    for index, phase in enumerate(phases):
        matrix[index][index] = complex(math.cos(phase), math.sin(phase))
    return matrix


def finite_clock_matrix(size: int) -> list[list[complex]]:
    phase = (2.0 * math.pi) / size
    matrix = zero_matrix(size, size)
    for index in range(size):
        matrix[index][index] = complex(math.cos(phase * index), math.sin(phase * index))
    return matrix


def finite_shift_matrix(size: int) -> list[list[complex]]:
    matrix = zero_matrix(size, size)
    for index in range(size):
        matrix[(index + 1) % size][index] = 1.0
    return matrix


def zero_matrix(rows: int, cols: int) -> list[list[complex]]:
    return [[0.0j for _col in range(cols)] for _row in range(rows)]


def identity_matrix(size: int) -> list[list[complex]]:
    matrix = zero_matrix(size, size)
    for index in range(size):
        matrix[index][index] = 1.0
    return matrix


def matrices_close(left: list[list[complex]], right: list[list[complex]], tolerance: float) -> bool:
    if len(left) != len(right):
        return False
    for row_index, left_row in enumerate(left):
        if len(left_row) != len(right[row_index]):
            return False
        for col_index, value in enumerate(left_row):
            if abs(value - right[row_index][col_index]) > tolerance:
                return False
    return True


def real_lists_close(left: list[float], right: list[float], tolerance: float) -> bool:
    return len(left) == len(right) and all(
        abs(left_value - right[index]) <= tolerance for index, left_value in enumerate(left)
    )


def complex_lists_close(left: list[complex], right: list[complex], tolerance: float) -> bool:
    return len(left) == len(right) and all(
        abs(left_value - right[index]) <= tolerance for index, left_value in enumerate(left)
    )


def max_off_diagonal_abs(matrix: list[list[complex]]) -> float:
    max_value = 0.0
    for row_index, row in enumerate(matrix):
        for col_index, value in enumerate(row):
            if row_index != col_index:
                max_value = max(max_value, abs(value))
    return max_value


def reduced_density_max_offdiag(amplitudes: list[complex], environment_kernel: list[list[complex]]) -> float:
    max_value = 0.0
    for row_index, amplitude in enumerate(amplitudes):
        for col_index in range(row_index + 1, len(amplitudes)):
            coherence = amplitude * amplitudes[col_index].conjugate() * environment_kernel[row_index][col_index]
            max_value = max(max_value, abs(coherence))
    return max_value


def identity_minus(matrix: list[list[complex]]) -> list[list[complex]]:
    if len(matrix) != len(matrix[0]):
        raise ManifestError("matrix must be square")
    return [
        [
            (1.0 if row == col else 0.0) - matrix[row][col]
            for col in range(len(matrix))
        ]
        for row in range(len(matrix))
    ]


def elementwise_product(left: list[list[complex]], right: list[list[complex]]) -> list[list[complex]]:
    return [
        [left[row][col] * right[row][col] for col in range(len(left[row]))]
        for row in range(len(left))
    ]


def nonempty_index_subsets(size: int) -> list[tuple[int, ...]]:
    subsets: list[tuple[int, ...]] = []
    for mask in range(1, 1 << size):
        subset: list[int] = []
        for index in range(size):
            if mask & (1 << index):
                subset.append(index)
        subsets.append(tuple(subset))
    return subsets


def principal_submatrix(matrix: list[list[complex]], subset: tuple[int, ...]) -> list[list[complex]]:
    return [[matrix[row][col] for col in subset] for row in subset]


def determinant(matrix: list[list[complex]]) -> complex:
    size = len(matrix)
    work = [list(row) for row in matrix]
    det = 1.0 + 0.0j
    for pivot_index in range(size):
        pivot_row = max(range(pivot_index, size), key=lambda row_index: abs(work[row_index][pivot_index]))
        if abs(work[pivot_row][pivot_index]) < 1.0e-14:
            return 0.0 + 0.0j
        if pivot_row != pivot_index:
            work[pivot_index], work[pivot_row] = work[pivot_row], work[pivot_index]
            det *= -1.0
        pivot = work[pivot_index][pivot_index]
        det *= pivot
        for row_index in range(pivot_index + 1, size):
            factor = work[row_index][pivot_index] / pivot
            for col_index in range(pivot_index + 1, size):
                work[row_index][col_index] -= factor * work[pivot_index][col_index]
    return det


def validate_events(events: tuple[tuple[int, ...], ...], vector_size: int, matrix_size: int) -> None:
    if vector_size != matrix_size:
        raise ManifestError("weights and gamma size must match")
    for event in events:
        for index in event:
            if index < 0 or index >= vector_size:
                raise ManifestError(f"event index {index} is out of range")


def phase_shifted_weights(weights: list[complex], phase: float) -> list[complex]:
    shifted = list(weights)
    shifted[1] *= complex(math.cos(phase), math.sin(phase))
    return shifted


def matrix_vector_multiply(matrix: list[list[complex]], vector: list[complex]) -> list[complex]:
    if not matrix:
        raise ManifestError("cannot multiply empty matrix by vector")
    width = len(matrix[0])
    if width != len(vector):
        raise ManifestError("matrix and vector dimensions do not compose")
    return [sum(row[index] * vector[index] for index in range(width)) for row in matrix]


def vector_norm_squared(vector: list[complex]) -> float:
    return sum(abs(value) ** 2 for value in vector)


def amplitude_probabilities(amplitudes: list[complex], tolerance: float) -> list[float]:
    total = vector_norm_squared(amplitudes)
    if abs(total - 1.0) > tolerance:
        raise ManifestError("amplitudes must be normalized")
    return [abs(value) ** 2 for value in amplitudes]


def parse_two_state(raw: object, field: str, tolerance: float) -> list[complex]:
    state = parse_vector(raw, field)
    if len(state) != 2:
        raise ManifestError(f"{field} must contain exactly two amplitudes")
    if abs(vector_norm_squared(state) - 1.0) > tolerance:
        raise ManifestError(f"{field} must be normalized")
    return state


def parse_two_state_context(raw: object, field: str, tolerance: float) -> list[list[complex]]:
    context = parse_matrix(raw, field)
    validate_square_block(context, field)
    if len(context) != 2:
        raise ManifestError(f"{field} must be a 2x2 context")
    validate_unitary(context, tolerance, field)
    return context


def parse_two_state_contexts(raw: object, field: str, tolerance: float) -> list[list[list[complex]]]:
    contexts = parse_matrix_list(raw, field)
    for index, context in enumerate(contexts):
        validate_square_block(context, f"{field}[{index}]")
        if len(context) != 2:
            raise ManifestError(f"{field}[{index}] must be a 2x2 context")
        validate_unitary(context, tolerance, f"{field}[{index}]")
    return contexts


def parse_two_probabilities(raw: object, field: str, tolerance: float) -> list[float]:
    probabilities = parse_real_list(raw, field)
    if len(probabilities) != 2:
        raise ManifestError(f"{field} must contain exactly two probabilities")
    for probability in probabilities:
        if probability < -tolerance or probability > 1.0 + tolerance:
            raise ManifestError(f"{field} entries must be probabilities")
    if abs(sum(probabilities) - 1.0) > tolerance:
        raise ManifestError(f"{field} must sum to one")
    return probabilities


def context_basis_state(context: list[list[complex]], outcome: int) -> list[complex]:
    return [value.conjugate() for value in context[outcome]]


def density_matrix_from_state(state: list[complex]) -> list[list[complex]]:
    return [[row_value * col_value.conjugate() for col_value in state] for row_value in state]


def nonselective_context_measurement(
    density: list[list[complex]], context: list[list[complex]], tolerance: float
) -> list[list[complex]]:
    validate_density_shape(density, context, tolerance)
    context_density = unitary_conjugate(context, density)
    dephased = [
        [
            context_density[row][col] if row == col else 0.0 + 0.0j
            for col in range(len(context_density))
        ]
        for row in range(len(context_density))
    ]
    return unitary_conjugate(conjugate_transpose(context), dephased)


def density_context_probabilities(
    density: list[list[complex]], context: list[list[complex]], tolerance: float
) -> list[float]:
    validate_density_shape(density, context, tolerance)
    context_density = unitary_conjugate(context, density)
    probabilities: list[float] = []
    for index, row in enumerate(context_density):
        diagonal = row[index]
        if abs(diagonal.imag) > tolerance:
            raise ManifestError("density readout probability must be real")
        if diagonal.real < -tolerance:
            raise ManifestError("density readout probability must be non-negative")
        probabilities.append(max(0.0, diagonal.real))
    total = sum(probabilities)
    if abs(total - 1.0) > tolerance:
        raise ManifestError("density readout probabilities must sum to one")
    return probabilities


def validate_density_shape(
    density: list[list[complex]], context: list[list[complex]], tolerance: float
) -> None:
    validate_square_block(density, "density")
    if len(density) != len(context):
        raise ManifestError("density and context dimensions must match")
    if len(density) != 2:
        raise ManifestError("two-state density gates require 2x2 density matrices")
    if not is_hermitian(density, tolerance):
        raise ManifestError("density must be Hermitian")


def resonant_two_level_unitary(theta: float) -> list[list[complex]]:
    cosine = math.cos(theta / 2.0)
    sine = math.sin(theta / 2.0)
    return [
        [complex(cosine, 0.0), complex(0.0, -sine)],
        [complex(0.0, -sine), complex(cosine, 0.0)],
    ]


def relative_phase_matrix(phase: float) -> list[list[complex]]:
    return [
        [complex(1.0, 0.0), complex(0.0, 0.0)],
        [complex(0.0, 0.0), complex(math.cos(phase), math.sin(phase))],
    ]


def bell_state_context_correlation(bell_outcome: str, context: str) -> float:
    correlations = {
        "phi_plus": {"zz": 1.0, "xx": 1.0},
        "phi_minus": {"zz": 1.0, "xx": -1.0},
        "psi_plus": {"zz": -1.0, "xx": 1.0},
        "psi_minus": {"zz": -1.0, "xx": -1.0},
    }
    if bell_outcome not in correlations:
        raise ManifestError(f"unknown Bell outcome: {bell_outcome}")
    if context not in correlations[bell_outcome]:
        raise ManifestError(f"unknown Bell correlation context: {context}")
    return correlations[bell_outcome][context]


def teleportation_branch_state(input_state: list[complex], bell_branch: str) -> list[complex]:
    alpha, beta = input_state
    if bell_branch == "phi_plus":
        return [alpha, beta]
    if bell_branch == "phi_minus":
        return [alpha, -beta]
    if bell_branch == "psi_plus":
        return [beta, alpha]
    if bell_branch == "psi_minus":
        return [-beta, alpha]
    raise ManifestError(f"unknown teleportation Bell branch: {bell_branch}")


def teleportation_corrected_state(branch_state: list[complex], bell_branch: str) -> list[complex]:
    first, second = branch_state
    if bell_branch == "phi_plus":
        return [first, second]
    if bell_branch == "phi_minus":
        return [first, -second]
    if bell_branch == "psi_plus":
        return [second, first]
    if bell_branch == "psi_minus":
        return [second, -first]
    raise ManifestError(f"unknown teleportation Bell branch: {bell_branch}")


def hadamard_walk_distribution(steps: int, initial_coin: list[complex]) -> dict[int, float]:
    root_half = 1.0 / math.sqrt(2.0)
    state: dict[tuple[int, int], complex] = {
        (0, 0): initial_coin[0],
        (0, 1): initial_coin[1],
    }
    for _step in range(steps):
        next_state: dict[tuple[int, int], complex] = {}
        for (position, coin), amplitude in state.items():
            if coin == 0:
                left_amplitude = root_half * amplitude
                right_amplitude = root_half * amplitude
            else:
                left_amplitude = root_half * amplitude
                right_amplitude = -root_half * amplitude
            left_key = (position - 1, 0)
            right_key = (position + 1, 1)
            next_state[left_key] = next_state.get(left_key, 0.0 + 0.0j) + left_amplitude
            next_state[right_key] = next_state.get(right_key, 0.0 + 0.0j) + right_amplitude
        state = next_state
    distribution: dict[int, float] = {}
    for (position, _coin), amplitude in state.items():
        distribution[position] = distribution.get(position, 0.0) + (abs(amplitude) ** 2)
    return distribution


def parse_position_distribution(raw: object, field: str) -> dict[int, float]:
    items = require_list(raw, field)
    if not items:
        raise ManifestError(f"{field} must not be empty")
    distribution: dict[int, float] = {}
    for index, item in enumerate(items):
        entry = require_mapping(item, f"{field}[{index}]")
        position = parse_integer(entry.get("position"), f"{field}[{index}].position")
        probability = parse_unit_interval(entry.get("probability"), f"{field}[{index}].probability")
        if position in distribution:
            raise ManifestError(f"{field}[{index}].position duplicates position {position}")
        distribution[position] = probability
    return distribution


def parse_distinguishability_capabilities(raw: object, field: str) -> dict[str, str]:
    mapping = require_mapping(raw, field)
    capabilities: dict[str, str] = {}
    for key, raw_value in mapping.items():
        value = require_string(raw_value, f"{field}.{key}")
        if value not in DISTINGUISHABILITY_GEOMETRY_CAPABILITIES:
            raise ManifestError(f"{field}.{key} has unknown capability {value!r}")
        capabilities[key] = value
    return capabilities


def parse_gpt_separator_capabilities(raw: object, field: str) -> dict[str, str]:
    mapping = require_mapping(raw, field)
    capabilities: dict[str, str] = {}
    for key, raw_value in mapping.items():
        value = require_string(raw_value, f"{field}.{key}")
        if value not in DISTINGUISHABILITY_GEOMETRY_CAPABILITIES:
            raise ManifestError(f"{field}.{key} has unknown capability {value!r}")
        capabilities[key] = value
    return capabilities


def classify_distinguishability_candidate(capabilities: dict[str, str], requirements: tuple[str, ...]) -> str:
    values = [capabilities[requirement] for requirement in requirements]
    if "unsupported" in values:
        return "rejected"
    if "underdetermined" in values:
        return "underdetermined"
    return "survives"


def classify_local_tomography_candidate(local_tomography: str) -> str:
    if local_tomography == "supported":
        return "survives"
    if local_tomography == "unsupported":
        return "rejected"
    if local_tomography == "underdetermined":
        return "underdetermined"
    raise ManifestError(f"unknown local tomography status: {local_tomography}")


def classify_gpt_principle_candidate(capabilities: dict[str, str], principles: tuple[str, ...]) -> str:
    values = [capabilities[principle] for principle in principles]
    if "unsupported" in values:
        return "rejected"
    if "underdetermined" in values:
        return "underdetermined"
    return "survives"


def projective_probabilities(
    state: list[complex], projectors: list[list[list[complex]]], tolerance: float
) -> list[float]:
    return [projective_probability(state, projector, tolerance) for projector in projectors]


def projective_probability(state: list[complex], projector: list[list[complex]], tolerance: float) -> float:
    projected = matrix_vector_multiply(projector, state)
    value = vector_inner_product(state, projected)
    if abs(value.imag) > tolerance:
        raise ManifestError("projective probability must be real")
    if value.real < -tolerance:
        raise ManifestError("projective probability must be non-negative")
    return max(0.0, value.real)


def normalized_projected_state(
    state: list[complex], projector: list[list[complex]], probability: float
) -> list[complex]:
    projected = matrix_vector_multiply(projector, state)
    scale = 1.0 / math.sqrt(probability)
    return [scale * value for value in projected]


def vector_inner_product(left: list[complex], right: list[complex]) -> complex:
    if len(left) != len(right):
        raise ManifestError("vectors must have equal length")
    return sum(left[index].conjugate() * right[index] for index in range(len(left)))


def two_path_output_probability(
    weights: list[complex], gamma: list[list[complex]], phase: float, tolerance: float
) -> float:
    bright_measure = mu_event((0, 1), phase_shifted_weights(weights, phase), gamma)
    dark_measure = mu_event((0, 1), phase_shifted_weights(weights, phase + math.pi), gamma)
    if abs(bright_measure.imag) > tolerance or abs(dark_measure.imag) > tolerance:
        raise ManifestError("two-path readout measures must be real")
    if bright_measure.real < -tolerance or dark_measure.real < -tolerance:
        raise ManifestError("two-path readout measures must be non-negative")
    denominator = bright_measure.real + dark_measure.real
    if denominator <= tolerance:
        raise ManifestError("two-path readout denominator must be positive")
    return bright_measure.real / denominator


def context_probabilities(
    events: list[tuple[int, ...]], weights: list[complex], gamma: list[list[complex]], tolerance: float
) -> list[float]:
    measures = [mu_event(event, weights, gamma) for event in events]
    if any(abs(measure.imag) > tolerance or measure.real < -tolerance for measure in measures):
        raise ManifestError("context measures must be non-negative real values")
    denominator = sum(measure.real for measure in measures)
    if denominator <= tolerance:
        raise ManifestError("context denominator must be positive")
    return [measure.real / denominator for measure in measures]


def probability_context_issue(
    gate_id: str,
    events: list[tuple[int, ...]],
    weights: list[complex],
    gamma: list[list[complex]],
    delta: float,
    tolerance: float,
) -> Issue | None:
    measures = [mu_event(event, weights, gamma) for event in events]
    if any(abs(measure.imag) > tolerance or measure.real <= tolerance for measure in measures):
        return Issue("nonpositive_context_measure", f"{gate_id}: context has non-positive measure")
    denominator = sum(measure.real for measure in measures)
    if denominator <= tolerance:
        return Issue("nonpositive_context_denominator", f"{gate_id}: context denominator is not positive")
    for left_index, left_event in enumerate(events):
        for right_index in range(left_index + 1, len(events)):
            right_event = events[right_index]
            offdiag = actualization(left_event, right_event, weights, gamma)
            bound = delta * math.sqrt(measures[left_index].real * measures[right_index].real)
            if abs(offdiag) > bound + tolerance:
                return Issue(
                    "context_not_probability_admissible",
                    f"{gate_id}: off-diagonal ({left_index},{right_index}) exceeds delta gate",
                )
    return None


def fringe_visibility_phase(
    weights: list[complex], gamma: list[list[complex]], tolerance: float
) -> tuple[float, float]:
    diagonal_measure = mu_event((0,), weights, gamma) + mu_event((1,), weights, gamma)
    if abs(diagonal_measure.imag) > tolerance:
        raise ManifestError("two-path diagonal measure must be real")
    if diagonal_measure.real <= tolerance:
        raise ManifestError("two-path diagonal measure must be positive")
    coherence = weights[0] * weights[1].conjugate() * gamma[0][1]
    visibility = (2.0 * abs(coherence)) / diagonal_measure.real
    if visibility > 1.0 + tolerance:
        raise ManifestError("two-path visibility exceeds one")
    return min(1.0, visibility), math.atan2(coherence.imag, coherence.real)


def second_order_interference(
    event_left: tuple[int, ...],
    event_right: tuple[int, ...],
    weights: list[complex],
    gamma: list[list[complex]],
) -> complex:
    return (
        mu_event(union_event(event_left, event_right), weights, gamma)
        - mu_event(event_left, weights, gamma)
        - mu_event(event_right, weights, gamma)
    )


def bell_no_signalling_issue(
    gate_id: str,
    contexts: dict[tuple[int, int], dict[tuple[int, int], float]],
    tolerance: float,
) -> Issue | None:
    for x_value in {0, 1}:
        for outcome_a in {-1, 1}:
            marginal_y0 = bell_marginal_a(contexts, x_value, 0, outcome_a)
            marginal_y1 = bell_marginal_a(contexts, x_value, 1, outcome_a)
            if abs(marginal_y0 - marginal_y1) > tolerance:
                return Issue("bell_signalling", f"{gate_id}: Alice marginal depends on Bob setting")
    for y_value in {0, 1}:
        for outcome_b in {-1, 1}:
            marginal_x0 = bell_marginal_b(contexts, 0, y_value, outcome_b)
            marginal_x1 = bell_marginal_b(contexts, 1, y_value, outcome_b)
            if abs(marginal_x0 - marginal_x1) > tolerance:
                return Issue("bell_signalling", f"{gate_id}: Bob marginal depends on Alice setting")
    return None


def bell_marginal_a(
    contexts: dict[tuple[int, int], dict[tuple[int, int], float]],
    x_value: int,
    y_value: int,
    outcome_a: int,
) -> float:
    table = contexts.get((x_value, y_value))
    if table is None:
        raise ManifestError("Bell no-signalling check requires all binary contexts")
    return sum(probability for (a_value, _b_value), probability in table.items() if a_value == outcome_a)


def bell_marginal_b(
    contexts: dict[tuple[int, int], dict[tuple[int, int], float]],
    x_value: int,
    y_value: int,
    outcome_b: int,
) -> float:
    table = contexts.get((x_value, y_value))
    if table is None:
        raise ManifestError("Bell no-signalling check requires all binary contexts")
    return sum(probability for (_a_value, b_value), probability in table.items() if b_value == outcome_b)


def bell_correlation(table: dict[tuple[int, int], float]) -> float:
    return sum(float(a_value * b_value) * probability for (a_value, b_value), probability in table.items())


def bell_probabilities_from_amplitudes(
    amplitudes: dict[tuple[int, int], complex], tolerance: float
) -> dict[tuple[int, int], float]:
    total = sum(abs(value) ** 2 for value in amplitudes.values())
    if abs(total - 1.0) > tolerance:
        raise ManifestError("Bell context amplitudes must be normalized")
    return {key: abs(value) ** 2 for key, value in amplitudes.items()}


def singlet_spin_probabilities(angle_delta: float) -> dict[tuple[int, int], float]:
    cosine = math.cos(angle_delta)
    return {
        (1, 1): 0.25 * (1.0 - cosine),
        (1, -1): 0.25 * (1.0 + cosine),
        (-1, 1): 0.25 * (1.0 + cosine),
        (-1, -1): 0.25 * (1.0 - cosine),
    }


def actualization(event_left: tuple[int, ...], event_right: tuple[int, ...], weights: list[complex], gamma: list[list[complex]]) -> complex:
    total = 0.0 + 0.0j
    for left_index in event_left:
        for right_index in event_right:
            total += weights[left_index] * weights[right_index].conjugate() * gamma[left_index][right_index]
    return total


def mu_event(event: tuple[int, ...], weights: list[complex], gamma: list[list[complex]]) -> complex:
    return actualization(event, event, weights, gamma)


def union_event(*events: tuple[int, ...]) -> tuple[int, ...]:
    output: list[int] = []
    for event in events:
        output.extend(event)
    return tuple(output)


def sorkin_i3(
    event_a: tuple[int, ...],
    event_b: tuple[int, ...],
    event_c: tuple[int, ...],
    weights: list[complex],
    gamma: list[list[complex]],
) -> complex:
    return (
        mu_event(union_event(event_a, event_b, event_c), weights, gamma)
        - mu_event(union_event(event_a, event_b), weights, gamma)
        - mu_event(union_event(event_a, event_c), weights, gamma)
        - mu_event(union_event(event_b, event_c), weights, gamma)
        + mu_event(event_a, weights, gamma)
        + mu_event(event_b, weights, gamma)
        + mu_event(event_c, weights, gamma)
    )


FINITE_GATE_CHECKS: dict[str, FiniteGateChecker] = {
    "psd_matrix": check_psd_gate,
    "schur_psd": check_schur_psd_gate,
    "block_psd": check_block_psd_gate,
    "contraction": check_contraction_gate,
    "cycle_holonomy_gauge_invariance": check_cycle_holonomy_gate,
    "cycle_holonomy_class": check_cycle_holonomy_class_gate,
    "actualization_i3_zero": check_actualization_i3_gate,
    "two_path_interference_fringe": check_two_path_interference_fringe_gate,
    "born_context_probability_table": check_born_context_probability_table_gate,
    "unitary_measurement_context": check_unitary_measurement_context_gate,
    "unitary_network_probability": check_unitary_network_probability_gate,
    "projective_measurement_update": check_projective_measurement_update_gate,
    "stern_gerlach_context_readout": check_stern_gerlach_context_readout_gate,
    "sequential_sg_noncommuting_context": check_sequential_sg_noncommuting_context_gate,
    "two_level_update_oscillation": check_two_level_update_oscillation_gate,
    "delayed_context_partition": check_delayed_context_partition_gate,
    "ramsey_clock_phase": check_ramsey_clock_phase_gate,
    "ab_holonomy_phase": check_ab_holonomy_phase_gate,
    "ab_flux_period": check_ab_flux_period_gate,
    "action_frequency_threshold": check_action_frequency_threshold_gate,
    "spectral_anchor_consistency": check_spectral_anchor_consistency_gate,
    "barrier_transmission": check_barrier_transmission_gate,
    "repeated_context_zeno": check_repeated_context_zeno_gate,
    "bosonic_indistinguishability": check_bosonic_indistinguishability_gate,
    "single_quantum_facticity": check_single_quantum_facticity_gate,
    "conditional_inheritance_swap": check_conditional_inheritance_swap_gate,
    "context_transfer_no_cloning": check_context_transfer_no_cloning_gate,
    "no_cloning_context_invariance": check_no_cloning_context_invariance_gate,
    "multipartite_contextuality": check_multipartite_contextuality_gate,
    "ks_contextuality_obstruction": check_ks_contextuality_obstruction_gate,
    "temporal_facticity": check_temporal_facticity_gate,
    "partial_facticity_readout": check_partial_facticity_readout_gate,
    "measurement_facticity_route": check_measurement_facticity_route_gate,
    "unitary_graph_walk": check_unitary_graph_walk_gate,
    "distinguishability_geometry_probe": check_distinguishability_geometry_probe_gate,
    "local_tomography_separator": check_local_tomography_separator_gate,
    "idt_local_tomography_derivation": check_idt_local_tomography_derivation_gate,
    "context_product_exhaustion": check_context_product_exhaustion_gate,
    "rebit_hidden_joint_invariant_separator": check_rebit_hidden_joint_invariant_separator_gate,
    "context_product_local_tomography_theorem": check_context_product_local_tomography_theorem_gate,
    "tomographic_state_effect_duality_theorem": check_tomographic_state_effect_duality_theorem_gate,
    "purification_filtering_recoverable_support_theorem": check_purification_filtering_recoverable_support_theorem_gate,
    "reversible_filter_closure_theorem": check_reversible_filter_closure_theorem_gate,
    "bounded_correlation_screen_theorem": check_bounded_correlation_screen_theorem_gate,
    "noncomplex_jordan_separator_theorem": check_noncomplex_jordan_separator_theorem_gate,
    "generic_gpt_closure_theorem": check_generic_gpt_closure_theorem_gate,
    "broader_generic_gpt_cone_frontier": check_broader_generic_gpt_cone_frontier_gate,
    "nonfinite_gpt_residual_compactness": check_nonfinite_gpt_residual_compactness_gate,
    "nonfinite_gpt_residual_frontier": check_nonfinite_gpt_residual_frontier_gate,
    "no_emergent_joint_only_invariant_route": check_no_emergent_joint_only_invariant_route_gate,
    "idt_purification_filtering": check_idt_purification_filtering_gate,
    "idt_bounded_correlation": check_idt_bounded_correlation_gate,
    "noncomplex_jordan_separator": check_noncomplex_jordan_separator_gate,
    "generic_gpt_closure_separator": check_generic_gpt_closure_separator_gate,
    "born_quadratic_readout_route": check_born_quadratic_readout_route_gate,
    "tensor_composition_route": check_tensor_composition_route_gate,
    "qm_core_recompile_route": check_qm_core_recompile_route_gate,
    "continuum_action_frontier": check_continuum_action_frontier_gate,
    "full_qm_closure_frontier": check_full_qm_closure_frontier_gate,
    "gpt_principle_separator": check_gpt_principle_separator_gate,
    "carrier_selection_frontier": check_carrier_selection_frontier_gate,
    "carrier_quantifier_frontier": check_carrier_quantifier_frontier_gate,
    "route_closed_gpt_subtheory_frontier": check_route_closed_gpt_subtheory_frontier_gate,
    "carrier_selection_proof_route": check_carrier_selection_proof_route_gate,
    "context_product_carrier_lemma_route": check_context_product_carrier_lemma_route_gate,
    "purification_filtering_carrier_lemma_route": check_purification_filtering_carrier_lemma_route_gate,
    "bounded_correlation_carrier_lemma_route": check_bounded_correlation_carrier_lemma_route_gate,
    "noncomplex_jordan_classification_lemma_route": check_noncomplex_jordan_classification_lemma_route_gate,
    "generic_gpt_classification_lemma_route": check_generic_gpt_classification_lemma_route_gate,
    "triple_path_sorkin_parameter": check_triple_path_sorkin_parameter_gate,
    "marker_eraser_visibility": check_marker_eraser_visibility_gate,
    "bell_chsh_table": check_bell_chsh_table_gate,
    "bell_chsh_from_amplitudes": check_bell_chsh_from_amplitudes_gate,
    "spin_bell_angle_model": check_spin_bell_angle_model_gate,
    "unitary_generator_reconstruction": check_unitary_generator_reconstruction_gate,
    "translation_de_broglie_scale": check_translation_de_broglie_scale_gate,
    "finite_weyl_relation": check_finite_weyl_relation_gate,
    "pointer_sector_stability": check_pointer_sector_stability_gate,
    "premeasurement_decoherence": check_premeasurement_decoherence_gate,
    "recoverability_loss": check_recoverability_loss_gate,
    "one_parameter_unitary_flow": check_one_parameter_unitary_flow_gate,
    "strong_continuity_modulus": check_strong_continuity_modulus_gate,
    "generator_difference_convergence": check_generator_difference_convergence_gate,
    "ell0_radar_consistency": check_ell0_radar_consistency_gate,
    "ell0_link_frequency_consistency": check_ell0_link_frequency_consistency_gate,
    "ell0_no_gravity_input": check_ell0_no_gravity_input_gate,
    "clock_vacuum_pole_candidate": check_clock_vacuum_pole_candidate_gate,
    "clock_vacuum_pole_universality": check_clock_vacuum_pole_universality_gate,
    "clock_vacuum_pole_no_calibrated_input": check_clock_vacuum_pole_no_calibrated_input_gate,
    "ell0_candidate_from_clock_pole": check_ell0_candidate_from_clock_pole_gate,
    "ell0_candidate_no_gravity_input": check_ell0_candidate_no_gravity_input_gate,
    "ell0_bound_not_value": check_ell0_bound_not_value_gate,
    "spectral_law_free_parameter_audit": check_spectral_law_free_parameter_audit_gate,
    "spectral_law_no_calibrated_input": check_spectral_law_no_calibrated_input_gate,
    "fixed_point_component_status": check_fixed_point_component_status_gate,
    "non_exact_holonomy_source": check_non_exact_holonomy_source_gate,
    "rho_chi_protocol_invariance": check_rho_chi_protocol_invariance_gate,
    "rho_chi_no_gravity_input": check_rho_chi_no_gravity_input_gate,
    "kappa_omega_consistency": check_kappa_omega_consistency_gate,
    "kappa_omega_no_gravity_input": check_kappa_omega_no_gravity_input_gate,
    "contraction_phase_degeneracy": check_contraction_phase_degeneracy_gate,
    "support_matching_phase_freedom": check_support_matching_phase_freedom_gate,
    "contraction_selection_no_calibrated_input": check_contraction_selection_no_calibrated_input_gate,
    "fixed_point_step_integer_obstruction": check_fixed_point_step_integer_obstruction_gate,
    "fixed_point_step_free_parameter_audit": check_fixed_point_step_free_parameter_audit_gate,
    "fixed_point_step_no_gravity_input": check_fixed_point_step_no_gravity_input_gate,
    "transition_phase_unit_readout": check_transition_phase_unit_readout_gate,
    "cycle_holonomy_composition": check_cycle_holonomy_composition_gate,
    "primitive_transition_phase_no_calibrated_input": check_primitive_transition_phase_no_calibrated_input_gate,
    "holonomy_source_classification": check_holonomy_source_classification_gate,
    "holonomy_selector_class_registry": check_holonomy_selector_class_registry_gate,
    "holonomy_selector_status": check_holonomy_selector_status_gate,
    "holonomy_selector_no_calibrated_input": check_holonomy_selector_no_calibrated_input_gate,
    "winding_selector_homotopy_consistency": check_winding_selector_homotopy_consistency_gate,
    "winding_selector_orientation_reversal": check_winding_selector_orientation_reversal_gate,
    "winding_selector_additivity": check_winding_selector_additivity_gate,
    "winding_selector_no_calibrated_input": check_winding_selector_no_calibrated_input_gate,
    "sector_role_registry": check_sector_role_registry_gate,
    "sector_role_assignment_partition": check_sector_role_assignment_partition_gate,
    "research_graph_contract": check_research_graph_contract_gate,
    "dimensionful_anchor_policy": check_dimensionful_anchor_policy_gate,
    "dimensionless_coupling_policy": check_dimensionless_coupling_policy_gate,
    "bridge_assumption_boundary": check_bridge_assumption_boundary_gate,
    "phase_branch_additivity": check_phase_branch_additivity_gate,
    "phase_branch_no_postfit": check_phase_branch_no_postfit_gate,
    "phase_cost_independence": check_phase_cost_independence_gate,
    "primitive_mass_anchor_inertia_response": check_primitive_mass_anchor_inertia_response_gate,
    "primitive_mass_anchor_no_quantum_gravity_input": check_primitive_mass_anchor_no_quantum_gravity_input_gate,
    "source_response_charge_normalization": check_source_response_charge_normalization_gate,
    "source_response_no_calibrated_input": check_source_response_no_calibrated_input_gate,
    "active_passive_inertial_equality": check_active_passive_inertial_equality_gate,
    "source_response_packet_universality": check_source_response_packet_universality_gate,
    "geometry_response_factor_freeze": check_geometry_response_factor_freeze_gate,
    "geometry_response_no_gravity_anchor": check_geometry_response_no_gravity_anchor_gate,
    "clock_vacuum_stiffness_from_source_response": check_clock_vacuum_stiffness_from_source_response_gate,
    "clock_vacuum_stiffness_universality": check_clock_vacuum_stiffness_universality_gate,
    "clock_vacuum_stiffness_no_calibrated_input": check_clock_vacuum_stiffness_no_calibrated_input_gate,
    "G_symbolic_clock_strain_candidate": check_G_symbolic_clock_strain_candidate_gate,
    "G_candidate_no_calibrated_input": check_G_candidate_no_calibrated_input_gate,
    "photon_dispersion_bound": check_photon_dispersion_bound_gate,
    "matter_wave_bound": check_matter_wave_bound_gate,
    "composite_omega_bound": check_composite_omega_bound_gate,
    "ell0_tick_bound": check_ell0_tick_bound_gate,
    "clock_redshift": check_clock_redshift_gate,
    "combined_clock_rate": check_combined_clock_rate_gate,
    "newtonian_point_mass_clock_field": check_newtonian_point_mass_clock_field_gate,
    "source_flux_gauss": check_source_flux_gauss_gate,
    "ppn_light_bending": check_ppn_light_bending_gate,
    "clock_strain_variational_poisson": check_clock_strain_variational_poisson_gate,
    "source_law_coefficient": check_source_law_coefficient_gate,
    "ppn_gamma_from_potentials": check_ppn_gamma_from_potentials_gate,
    "shapiro_delay": check_shapiro_delay_gate,
    "ppn_perihelion": check_ppn_perihelion_gate,
    "slip_source_poisson": check_slip_source_poisson_gate,
    "zero_stress_boundary_no_slip": check_zero_stress_boundary_no_slip_gate,
    "source_continuity": check_source_continuity_gate,
    "stress_tensor_decomposition": check_stress_tensor_decomposition_gate,
    "anisotropic_stress_norm": check_anisotropic_stress_norm_gate,
    "coarse_grained_anisotropy": check_coarse_grained_anisotropy_gate,
    "slip_source_bound_from_anisotropy": check_slip_source_bound_from_anisotropy_gate,
    "scale_residual_bound": check_scale_residual_bound_gate,
    "scale_residual_activation": check_scale_residual_activation_gate,
    "domain_no_refit": check_domain_no_refit_gate,
    "screened_transition_bound": check_screened_transition_bound_gate,
    "screened_profile_prediction": check_screened_profile_prediction_gate,
    "residual_acceleration_output": check_residual_acceleration_output_gate,
    "residual_light_bending_output": check_residual_light_bending_output_gate,
    "screened_observational_profile": check_screened_observational_profile_gate,
    "sparc_baryonic_residual_point": check_sparc_baryonic_residual_point_gate,
    "sparc_residual_packet": check_sparc_residual_packet_gate,
    "screened_sparc_capacity": check_screened_sparc_capacity_gate,
    "screened_amplitude_lower_bound": check_screened_amplitude_lower_bound_gate,
    "residual_no_postfit_provenance": check_residual_no_postfit_provenance_gate,
    "screened_profile_bound_status": check_screened_profile_bound_status_gate,
    "screened_corridor_feasibility": check_screened_corridor_feasibility_gate,
    "residual_fit_claim_status": check_residual_fit_claim_status_gate,
    "screened_radius_scale_prediction": check_screened_radius_scale_prediction_gate,
    "screened_baryonic_acceleration_map": check_screened_baryonic_acceleration_map_gate,
    "screened_baryonic_exponent_scan": check_screened_baryonic_exponent_scan_gate,
    "screened_baryonic_exponent_transfer": check_screened_baryonic_exponent_transfer_gate,
    "primitive_tick_clock_count": check_primitive_tick_clock_count_gate,
    "primitive_tick_radar_consistency": check_primitive_tick_radar_consistency_gate,
    "primitive_tick_reparam_invariance": check_primitive_tick_reparam_invariance_gate,
    "primitive_tick_clock_universality": check_primitive_tick_clock_universality_gate,
    "primitive_work_balance": check_primitive_work_balance_gate,
    "primitive_work_no_quantum_energy": check_primitive_work_no_quantum_energy_gate,
    "primitive_work_coarse_grain_balance": check_primitive_work_coarse_grain_balance_gate,
    "primitive_work_sector_universality": check_primitive_work_sector_universality_gate,
    "primitive_work_dimensional_obstruction": check_primitive_work_dimensional_obstruction_gate,
    "action_standard_work_time_provenance": check_action_standard_work_time_provenance_gate,
    "action_scale_gauge_obstruction": check_action_scale_gauge_obstruction_gate,
    "tick_scale_lock_status": check_tick_scale_lock_status_gate,
    "work_scale_lock_status": check_work_scale_lock_status_gate,
    "action_anchor_lock_status": check_action_anchor_lock_status_gate,
    "action_standard_provenance": check_action_standard_provenance_gate,
    "phase_action_scale_universality": check_phase_action_scale_universality_gate,
    "action_standard_independence": check_action_standard_independence_gate,
    "hbar_known_gate_holdout": check_hbar_known_gate_holdout_gate,
    "probability_admissible_context": check_probability_admissible_context_gate,
    "relative_phase_cost_family": check_relative_phase_cost_family_gate,
    "relative_phase_cost_from_edges": check_relative_phase_cost_from_edges_gate,
    "relative_phase_cost_from_kernel_edges": check_relative_phase_cost_from_kernel_edges_gate,
    "relative_phase_cost_from_kernel_holonomy": check_relative_phase_cost_from_kernel_holonomy_gate,
    "relative_phase_cost_from_kernel_unit_holonomy": check_relative_phase_cost_from_kernel_unit_holonomy_gate,
    "relative_phase_cost_from_kernel_unit_edges": check_relative_phase_cost_from_kernel_unit_edges_gate,
    "relative_phase_cost_from_kernel_transfer_elements": check_relative_phase_cost_from_kernel_transfer_elements_gate,
    "relative_phase_cost_from_kernel_transfer_blocks": check_relative_phase_cost_from_kernel_transfer_blocks_gate,
    "relative_phase_cost_from_kernel_block_kernels": check_relative_phase_cost_from_kernel_block_kernels_gate,
    "relative_phase_cost_from_kernel_normalized_blocks": check_relative_phase_cost_from_kernel_normalized_blocks_gate,
    "relative_phase_cost_from_kernel_spectral_blocks": check_relative_phase_cost_from_kernel_spectral_blocks_gate,
    "relative_phase_cost_from_spectral_kernel_blocks": check_relative_phase_cost_from_spectral_kernel_blocks_gate,
    "diagonal_kernel_strain_cost": check_diagonal_kernel_strain_cost_gate,
    "spectral_kernel_strain_cost": check_spectral_kernel_strain_cost_gate,
    "spectral_kernel_diagonal_limit": check_spectral_kernel_diagonal_limit_gate,
    "spectral_kernel_readout_covariance": check_spectral_kernel_readout_covariance_gate,
    "cycle_cost_sum": check_cycle_cost_sum_gate,
}
