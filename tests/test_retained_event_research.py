"""Source-level research packets keep immutable, unassessed baselines."""

import hashlib
import unittest

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits
from theory_experiments.source_candidate import parse_source_candidate

PACKS = {
    "primitive_event_origin_inventory.json": ("single_event_origins", {
        "unary_chain_first_passage_detector": "probe_unary_first_passage_detector",
        "reciprocal_petals_with_port_memory": "probe_reciprocal_detector_petals",
        "reversible_marker_detector_sector": "probe_reversible_excitation_detector",
        "driven_context_rate_memory_requirement": "probe_driven_readout_memory",
        "driven_event_trace_memory_witness": "probe_event_memory_witness",
        "second_delft_context_rotor_scope": "probe_delft_second_rotor",
    }),
    "primitive_observer_clock_inventory.json": ("local_observer_clocks", {
        "internal_port_latch_reference_clock": "probe_internal_detector_clocks",
        "matched_detuned_petal_reference": "probe_matched_vernier_petals",
        "externally_stimulated_carry_slip": "probe_trigger_carry_slip",
        "periodic_calendar_contact_alias": "probe_calendar_carry_alias",
        "coprime_raw_signed_encounters": "probe_coprime_signed_encounters",
    }),
    "primitive_particle_contrast_inventory.json": ("particle_observation_contrasts", {
        "polarized_electron_current_assignment": "probe_polarized_z_electron",
        "solar_active_flux_response_degeneracy": "probe_solar_active_flux",
        "reactor_relative_clock_scale_wall": "probe_reactor_relative_clocks",
        "three_arm_late_plate_contact_bound": "probe_three_arm_setting_contacts",
    }),
    "primitive_cell_inference_inventory.json": ("local_cell_inference", {
        "reciprocal_cell_timing_census": "probe_reversible_cell_census",
        "unrestricted_cell_timing_partition": "probe_unrestricted_cell_tables",
        "cell_projection_into_clock_screen": "probe_cell_rule_clock_projection",
        "cell_orientational_fixed_number_exchange": "probe_cell_exchange_intervention",
        "photonic_exchange_phase_countercontrol": "probe_photonic_exchange_reference",
    }),
    "primitive_mobile_load_inventory.json": ("mobile_load_operations", {
        "identical_units_moving_and_parked": "probe_indistinguishable_mobile_load",
        "serial_local_reporting_return_bus": "probe_serial_return_bus",
        "programmed_mobile_complement_contacts": "probe_mobile_cell_complement_mixer",
        "two_mark_marginal_automorphism_wall": "probe_packet_marginal_automorphisms",
        "static_mixer_hardware_census": "probe_static_cell_mixer_search",
        "static_mixer_elapsed_time_and_completion": "probe_static_cell_elapsed_readout",
    }),
    "primitive_stream_cut_inventory.json": ("streaming_memory_cut", {
        "streamed_current_memory_cut": "probe_streaming_observer_cut",
        "five_probability_cut_score": "probe_linear_cut_dimension_witness",
    }),
    "primitive_anonymous_carrier_inventory.json": ("anonymous_carrier_origins", {
        "minimal_local_two_path_reunion": "probe_local_reunion_minimum",
        "anonymous_operations_from_square_opposites": "probe_anonymous_folded_carrier",
        "complement_odd_additive_carrier_charge": "probe_marked_carrier_charge",
        "two_step_observer_mark_atlas": "probe_two_turn_charge_atlas",
        "even_carrier_additive_unit_frontier": "probe_even_carrier_resource_frontier",
        "whole_carrier_wire_orbit_census": "probe_even_mask_wire_orbits",
    }),
    "primitive_anonymous_collision_inventory.json": ("anonymous_collision_preparations", {
        "anonymous_equivariant_port_fusion": "probe_anonymous_port_fusion",
        "unit_only_mixed_load_intervention": "probe_calibrated_unit_pile_comparator",
        "anonymous_collisions_vs_tritter": "probe_anonymous_tritter_control",
    }),
    "primitive_carrier_mode_inventory.json": ("carrier_mode_conservation", {
        "flat_two_state_port_germ": "probe_two_turn_germ_ballots",
        "lowest_binary_association_readout": "probe_minimal_binary_association",
        "binary_frustration_ground_contrast": "probe_binary_frustration_carrier",
        "rooted_parity_walk_mode": "probe_rooted_parity_walk",
        "parity_mode_contact_countermodels": "probe_carrier_mode_countermodels",
        "positive_spring_carrier_resonance": "probe_passive_carrier_resonance",
        "resonant_energy_vs_single_detection": "probe_resonant_energy_and_single_click",
        "native_hop_charge_conservation_wall": "probe_carrier_charge_conservation",
    }),
    "primitive_noisy_cut_inventory.json": ("noisy_binary_cuts", {
        "shared_seed_noisy_binary_overlap": "probe_robust_shared_cut_overlap",
        "randomized_setting_common_target": "probe_randomized_cut_coverage",
        "processor_cut_original_count_control": "probe_processor_cut_data",
    }),
    "primitive_carrier_context_inventory.json": ("carrier_sign_contexts", {
        "central_bit_folded_direction_lifts": "probe_folded_carrier_commutators",
        "compatible_parity_contexts_of_lifts": "probe_folded_carrier_parity_contexts",
        "sequential_context_memory_intervention": "probe_contextual_readout_memory",
    }),
    "primitive_relational_observer_inventory.json": ("relational_observer_covers", {
        "local_reunion_moment_discriminator": "probe_local_reunion_moments",
        "reversible_active_vs_passive_ranging": "probe_reversible_range_alias",
        "exchanged_lift_without_statistics_sign": "probe_collision_free_exchange_paths",
        "closed_three_sheet_reunion_cost": "probe_three_sheet_reunion_cost",
        "abelian_reunion_dimension_intervention": "probe_abelian_reunion_dimensions",
    }),
    "primitive_native_charge_dynamics_inventory.json": ("native_charge_dynamics", {
        "signed_neutral_collision_arity": "probe_charge_collision_invariants",
        "blind_local_collision_invariant": "probe_blind_collision_charge",
        "signed_flag_reflection_geometry": "probe_native_reflection_geometry",
        "even_unimodular_lattice_completion": "probe_even_lattice_completion",
        "trace_normalization_and_pole_control": "probe_charge_trace_and_running",
    }),
    "primitive_ternary_encounter_inventory.json": ("absolute_relative_encounters", {
        "absolute_blank_relative_encounter_intervention": "probe_translated_collision_intervention",
        "absolute_collision_reference_memory": "probe_collision_reference_memory",
    }),
    "primitive_transport_exchange_inventory.json": ("local_transport_exchange", {
        "same_rank_different_return_metrics": "probe_reunion_transport_metric",
        "two_packet_exchange_order_from_paths": "probe_two_packet_exchange_topology",
        "exchange_sector_reciprocal_kinetics": "probe_exchange_sector_kinetics",
        "fermion_exchange_noise_controls": "probe_fermion_exchange_intervention",
    }),
    "primitive_native_frame_readouts_inventory.json": ("native_frame_readout_limits", {
        "native_frames_positive_nonstate": "probe_native_frame_positivity",
        "dense_orbit_discontinuous_readout": "probe_dense_readout_residue_countermodel",
        "rational_four_port_residue_extension": "probe_four_arm_frame_extension",
        "finite_shadow_reciprocal_instruments": "probe_finite_shadow_instruments",
        "three_port_calibration_vs_event_origins": "probe_junction_calibration_and_events",
    }),
    "primitive_particle_count_phase_inventory.json": ("particle_count_and_cp_controls", {
        "massive_offdiagonal_invisible_width": "probe_massive_invisible_channels",
        "two_mass_frequency_and_width_control": "probe_two_flavor_frequency_and_width",
        "conjugate_kaon_double_ratio_vs_partial_rate": "probe_conjugate_decay_rate_contrast",
    }),
    "primitive_spectator_extension_inventory.json": ("spectator_extension_consistency", {
        "six_mode_exclusive_extension_wall": "probe_six_mode_shadow_exclusivity",
        "spectator_circuit_empty_mode_memory": "probe_spectator_circuit_equivalence",
        "five_mode_shared_pair_extension_wall": "probe_five_mode_shadow_boundary",
    }),
    "primitive_square_contact_readouts_inventory.json": ("square_contact_readouts", {
        "anonymous_contact_additive_weight": "probe_anonymous_contact_additive_readout",
        "dyadic_readout_background_preparations": "probe_dyadic_contact_preparations",
        "equal_junction_square_leaf_refinement": "probe_square_leaf_refinement",
        "rational_junction_reflection_compiler": "probe_rational_junction_reflection_compiler",
        "nonlinear_contact_same_square_wall": "probe_nonlinear_junction_discriminator",
    }),
    "primitive_anonymous_cluster_inventory.json": ("anonymous_cluster", {
        "anonymous_relative_quartet_collision": "probe_anonymous_reference_collision",
        "relative_charge_cluster_descent": "probe_local_cluster_charge_descent",
    }),
    "primitive_signed_contact_stream_inventory.json": ("signed_contact_streams", {
        "ordered_signed_contact_rotor": "probe_signed_rotor_junction",
        "permutation_anonymous_signed_bucket": "probe_anonymous_signed_bucket",
        "overlapping_signed_contact_failure": "probe_overlapping_bucket_dynamics",
    }),
    "primitive_single_ticket_transport_inventory.json": ("single_ticket_transport", {
        "equivariant_one_ticket_transport": "probe_equivariant_event_tickets",
        "autonomous_fixed_frame_ticket_clock": "probe_autonomous_ticket_clock",
        "pump_locked_hbt_lag_four": "probe_pump_locked_hbt",
        "irrevocable_fine_event_prefix": "probe_irrevocable_event_prefix",
    }),
    "primitive_relational_signal_channels_inventory.json": ("relational_signal_channels", {
        "relational_return_signal_metric": "probe_relational_signal_metric",
        "relational_cyclic_clock_channel": "probe_relational_clock_modes",
    }),
    "primitive_mobile_refinement_inventory.json": ("mobile_refinement", {
        "moving_ternary_refinement_field": "probe_mobile_refinement_field",
        "anonymous_refinement_relations": "probe_anonymous_refinement_relations",
        "modular_ternary_dark_panel": "probe_modular_contact_nulls",
    }),
    "primitive_particle_label_limits_inventory.json": ("particle_label_limits", {
        "five_flag_global_line_options": "probe_flag_center_blindness",
        "pair_cup_turn_exchange": "probe_pair_cup_exchange",
    }),
    "primitive_clock_memory_contrasts_inventory.json": ("clock_memory_contrasts", {
        "pump_clock_extended_delay_comparisons": "probe_pump_clock_lag_extension",
        "five_depth_stochastic_memory_contrast": "probe_five_depth_memory_contrast",
    }),
    "primitive_vacancy_inertia_inventory.json": ("vacancy_inertia", {
        "unsigned_vacancy_cut_flux": "probe_vacancy_cut_flux",
        "static_current_wave_alias": "probe_static_current_reflection",
        "edge_inertia_scattering": "probe_edge_inertia_scattering",
    }),
    "primitive_readout_design_cost_inventory.json": ("readout_design_cost", {
        "active_fresh_readout_designs": "probe_active_readout_panels",
        "shared_nondisturbing_readout_cost": "probe_shared_prefix_readout_cost",
    }),
    "primitive_exclusive_mark_controls_inventory.json": ("exclusive_mark_controls", {
        "single_mark_mutable_ternary_echo": "probe_single_mark_ternary_echo",
        "single_visit_endpoint_budget": "probe_one_visit_phase_budget",
        "three_equal_field_absorbers": "probe_three_absorber_menus",
    }),
    "primitive_flavor_loop_inventory.json": ("minimal_flavor_loop", {
        "native_minimal_flavor_phase_loop": "probe_minimal_flavor_phase_loop",
    }),
    "primitive_ternary_feedback_windows_inventory.json": ("ternary_feedback_windows", {
        "relational_parallelogram_scatter": "probe_relational_balance_scatter",
        "delayed_ternary_dyadic_feedback": "probe_feedback_ternary_from_pairs",
        "raw_pair_window_reflection": "probe_raw_pair_window_reflection",
        "reversible_pair_retiming_cost": "probe_reversible_pair_retiming",
        "timed_reflection_gain_test": "probe_feedback_pulse_gain_control",
    }),
}


class RetainedEventResearchTests(unittest.TestCase):
    def test_campaign_and_immutable_source_bytes(self):
        for filename, (bundle, ids) in PACKS.items():
            self.assertCountEqual(ids.values(), TOPIC_BUNDLES[bundle])
            specs = inventory_specifications(ROOT / "data" / filename)
            self.assertCountEqual((s["id"] for s in specs), ids)
            for spec in specs:
                row = parse_source_candidate(spec)
                with self.subTest(id=row.id):
                    self.assertEqual({s.path for s in row.sources}, {f"scripts/{ids[row.id]}.py"})
                    for src in row.sources:
                        raw = (ROOT / src.path).read_bytes()
                        self.assertEqual(src.file_sha256, hashlib.sha256(raw).hexdigest())
                        self.assertEqual(src.text.encode(), b"".join(
                            raw.splitlines(keepends=True)[src.first_line-1:src.last_line]))

    def test_pinned_original_reports_and_replay(self):
        archive = History(DEFAULT_HISTORY)
        for filename in PACKS:
            specs = inventory_specifications(ROOT / "data" / filename)
            results = candidate_pipeline.run_batch(specs, fresh=True)
            for spec, outcome in zip(specs, results, strict=True):
                with self.subTest(id=spec["id"]):
                    request = {"schema": SCHEMA, "limits": Limits().specification(), "candidates": [spec]}
                    key = candidate_pipeline.digest(request)
                    self.assertEqual(request, archive.get("submissions", key))
                    stored, = archive.baseline(key)["reports"]
                    for r in (stored, outcome.report):
                        self.assertEqual((r["status"], r["proof_status"], r["empirical_status"]),
                                         ("unsupported", "not_attempted", "not_tested"))
                    self.assertEqual(outcome.report["scope"]["scientific_status"], "unassessed")
                    self.assertEqual(outcome.report["scope"]["adapter_status"], "missing")
                    self.assertEqual(len(outcome.report["checks"]), 1)
                    self.assertEqual(outcome.report["checks"][0]["id"], "primitive_prediction_adapter")
