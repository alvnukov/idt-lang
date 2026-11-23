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
