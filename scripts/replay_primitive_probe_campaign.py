"""Replay allowlisted finite probes from this checkout without updating research records.

Exit status reports process completion, not a scientific verdict or proof.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Literal, TypedDict

ROOT = Path(__file__).resolve().parents[1]
SCOPE = "Process outcomes only; no scientific verdict or claim-status change."

# Historical inventory: commits 14e899f through 9499231, inclusive.
# Also includes the follow-on routing, walk, readout and benchmark probes.
TOPIC_BUNDLES: dict[str, tuple[str, ...]] = {
    "interference": (
        "probe_two_arm_shutters",
        "probe_cyclic_shutter_holdout",
        "probe_eight_label_interferometer",
        "probe_hidden_arm_certificates",
        "probe_native_absorber_memory",
    ),
    "readout": (
        "probe_carrier_resolution",
        "probe_phase_return_walk",
        "probe_cyclic_ballot_preparation",
        "probe_hemisphere_candidate",
        "probe_mid_edge_majority_walk",
        "probe_endpoint_tetra_detector",
        "probe_erased_bit_readouts",
        "probe_positive_square_readout",
        "probe_two_mark_shell",
        "probe_composed_phase_colors",
        "probe_port_stock_origin",
        "probe_rotor_event_stream",
        "probe_spectator_stock_bridge",
        "probe_stock_error_certificates",
    ),
    "composition": (
        "probe_two_particle_capacity",
        "probe_parity_capacity",
        "probe_independent_edge_composition",
        "probe_signed_slot_transfers",
        "probe_five_slot_charge",
    ),
    "routing": (
        "probe_cancellation_event_router",
        "probe_ranked_event_routing",
        "probe_raw_gate_reconstruction",
        "probe_separable_event_stock",
        "probe_routed_pair_bell",
    ),
    "phase": (
        "probe_integer_phase_orbit",
        "probe_paired_rail_encoding",
        "probe_native_recurrence_witness",
        "probe_phase_comparison_links",
        "probe_coset_address_transport",
        "probe_link_phase_harmonics",
    ),
    "walks": (
        "probe_integer_transport_walk",
        "probe_weyl_walk_chirality",
        "probe_universal_clock_rescaling",
        "probe_shared_cone_origin",
    ),
    "benchmarks": (
        "probe_interferometer_benchmark",
        "probe_trigger_alignment",
        "probe_transparency_shutter",
    ),
    "sampling": (
        "probe_exchangeable_event_labels",
        "probe_unread_tick_instruments",
        "probe_two_state_readout_barrier",
    ),
    "sector_words": (
        "probe_echo_gauge_normal_form",
        "probe_native_mixer_sector_density",
        "probe_exact_charge_sector_wall",
        "probe_heralded_sector_phase",
        "probe_projective_repeat_classification",
        "probe_catalytic_sector_phase",
    ),
    "record_order": (
        "probe_alternative_setting_gaps",
        "probe_adic_event_reservoir",
        "probe_hensen_order_controls",
    ),
    "exterior_slots": (
        "probe_collective_pauli_frame",
        "probe_exchange_sign_relator",
        "probe_exterior_slot_minimality",
        "probe_five_slot_quartic_selector",
    ),
    "readout_frames": (
        "probe_native_qutrit_frames",
        "probe_native_row_probability",
        "probe_unread_row_duplication",
        "probe_finite_detector_identity",
    ),
    "family_mixing": (
        "probe_ckm_raw_family_wall",
        "probe_ckm_blank_ports",
    ),
    "phase_network": (
        "probe_balanced_phase_composition",
        "probe_two_source_phase_network",
        "probe_phase_network_game",
        "probe_three_axis_source_parity",
    ),
    "program_memory": (
        "probe_native_markov_spectrum",
        "probe_autonomous_mixer_program",
    ),
    "unsigned_origins": (
        "probe_unsigned_neutral_motifs",
        "probe_uncolored_cycle_carrier",
    ),
    "unsigned_junction": (
        "probe_unsigned_collision_search",
        "probe_complement_collision_mixer",
        "probe_asynchronous_pair_resolver",
        "probe_unsigned_pair_tickets",
        "probe_unsigned_background_readout",
    ),
    "qutrit_extensions": (
        "probe_native_rational_pentagon",
        "probe_qutrit_residue_frames",
    ),
    "packet_observability": (
        "probe_packet_echo_observability",
    ),
    "collision_space": (
        "probe_diamond_collision_walk",
        "probe_routed_diamond_cones",
        "probe_collision_cone_stability",
        "probe_periodic_collision_metric",
        "probe_walk_complex_structure",
        "probe_collision_light_pair",
        "probe_oriented_cell_wave",
        "probe_internal_signal_geometry",
    ),
    "packet_sectors": (
        "probe_six_packet_sectors",
        "probe_packet_hypercharge_reference",
        "probe_packet_exchange_transport",
        "probe_six_packet_matter",
        "probe_packet_chiral_selection",
    ),
    "packet_phase_controls": (
        "probe_packet_phase_program",
        "probe_neutral_phase_controller",
        "probe_three_state_phase_controller",
        "probe_packet_eigenclock",
    ),
    "multiple_photon_exchange": (
        "probe_packet_triad_phase",
        "probe_packet_exchange_cycles",
        "probe_triad_reality_swap",
    ),
    "opposition_origin": (
        "probe_three_opposition_origin",
        "probe_opposition_clock_scatter",
        "probe_opposition_readout",
        "probe_opposition_hidden_carrier",
        "probe_opposition_spin_lift",
        "probe_binary_window_oppositions",
        "probe_tetrahedral_cycle_origin",
    ),
    "opposition_magic_square": (
        "probe_opposition_magic_square",
    ),
    "marked_relays": (
        "probe_flag_local_reunions",
        "probe_minimal_signal_relay",
        "probe_relay_loop_parity",
    ),
    "local_shuttles": (
        "probe_shuttle_local_reunions",
        "probe_boolean_shuttle_origin",
        "probe_joint_relay_phase",
    ),
    "phase_memory": (
        "probe_serial_phase_memory",
        "probe_six_mark_phase_origin",
        "probe_phase_pair_holdout",
        "probe_local_phase_comparator",
        "probe_six_phase_exclusive_packet",
    ),
    "chiral_observations": (
        "probe_occupation_square_signs",
        "probe_packet_charge_pairings",
        "probe_neutron_charge_anchor",
        "probe_flavor_charge_connectivity",
    ),
    "phase_realization": (
        "probe_vacuum_phase_lifts",
        "probe_catalytic_tag_invariants",
        "probe_catalytic_six_phase_words",
        "probe_phase_frame_covariance",
        "probe_transitive_phase_tags",
        "probe_affine_contact_fringe",
        "probe_affine_pulse_holdouts",
        "probe_native_phase_contacts",
        "probe_serial_trial_witness",
        "probe_finite_scalar_channels",
    ),
    "instrument_realization": (
        "probe_alternating_catalyst_clock",
        "probe_affine_contact_record",
        "probe_full_affine_record",
        "probe_affine_preparation_mixtures",
        "probe_affine_operational_library",
        "probe_affine_fourth_axis",
        "probe_affine_unread_instruments",
        "probe_affine_projective_reset",
        "probe_midpoint_spectator_instrument",
        "probe_midpoint_rule_origins",
    ),
    "operational_data": ("probe_mazurek_operational_bridge",),
    "neutral_width_data": ("probe_z_width_data_replay",),
    "primitive_origins_and_composites": (
        "probe_anonymous_midpoint_factory",
        "probe_affine_reset_escape",
        "probe_affine_instrument_witness",
        "probe_hidden_phase_erasure",
        "probe_hexagon_composite_closure",
        "probe_chiral_carrier_holdout",
        "probe_chiral_pencil_signs",
        "probe_anonymous_signal_rulers",
    ),
    "primitive_contacts_and_comparators": (
        "probe_autonomous_midpoint_repair",
        "probe_triangle_exchange_source",
        "probe_heralded_triangle_factory",
        "probe_signed_phase_join",
        "probe_independent_phase_comparator",
        "probe_weighted_chiral_pencil",
        "probe_local_angular_rulers",
    ),
    "reference_transport_and_carriers": (
        "probe_triangle_cycle_phase_axis",
        "probe_triangle_reference_sewing",
        "probe_native_triangle_reference_fanout",
        "probe_prior_triangle_reference",
        "probe_coherent_triangle_pulses",
        "probe_sparse_chiral_supports",
        "probe_anonymous_punctured_carrier",
        "probe_relational_chart_holonomy",
    ),
    "transfer_stock_and_trials": (
        "probe_unsigned_transfer_triangle",
        "probe_bipartite_triangle_origin",
        "probe_triangle_stock_rigidity",
        "probe_triangle_bypass_normalization",
        "probe_native_partial_exchange",
        "probe_reference_sewing_trials",
    ),
    "contacts_and_local_readout": (
        "probe_angular_phase_reference",
        "probe_anonymous_click_addresses",
        "probe_repeatable_triangle_contact",
        "probe_fourth_rail_stock",
        "probe_associative_stock_merge",
        "probe_exclusive_triangle_detector",
        "probe_local_composite_stock",
        "probe_bypass_port_calibration",
    ),
    "operational_identifiability": (
        "probe_boundary_geometry_aliases",
        "probe_three_packet_exchange_sector",
        "probe_connected_contact_tomography",
        "probe_hidden_exchange_colors",
        "probe_partial_hidden_exchange",
        "probe_native_exchange_optimum",
    ),
    "single_event_origins": (
        "probe_unary_first_passage_detector",
        "probe_reciprocal_detector_petals",
        "probe_reversible_excitation_detector",
        "probe_driven_readout_memory",
        "probe_event_memory_witness",
        "probe_delft_second_rotor",
    ),
    "local_observer_clocks": (
        "probe_internal_detector_clocks",
        "probe_matched_vernier_petals",
        "probe_trigger_carry_slip",
        "probe_calendar_carry_alias",
        "probe_coprime_signed_encounters",
    ),
    "particle_observation_contrasts": (
        "probe_polarized_z_electron",
        "probe_solar_active_flux",
        "probe_reactor_relative_clocks",
        "probe_three_arm_setting_contacts",
    ),
    "local_cell_inference": (
        "probe_reversible_cell_census",
        "probe_unrestricted_cell_tables",
        "probe_cell_rule_clock_projection",
        "probe_cell_exchange_intervention",
        "probe_photonic_exchange_reference",
    ),
    "mobile_load_operations": (
        "probe_indistinguishable_mobile_load",
        "probe_serial_return_bus",
        "probe_mobile_cell_complement_mixer",
        "probe_packet_marginal_automorphisms",
        "probe_static_cell_mixer_search",
        "probe_static_cell_elapsed_readout",
    ),
    "streaming_memory_cut": (
        "probe_streaming_observer_cut",
        "probe_linear_cut_dimension_witness",
    ),
    "anonymous_carrier_origins": (
        "probe_local_reunion_minimum",
        "probe_anonymous_folded_carrier",
        "probe_marked_carrier_charge",
        "probe_two_turn_charge_atlas",
        "probe_even_carrier_resource_frontier",
        "probe_even_mask_wire_orbits",
    ),
    "anonymous_collision_preparations": (
        "probe_anonymous_port_fusion",
        "probe_calibrated_unit_pile_comparator",
        "probe_anonymous_tritter_control",
    ),
    "carrier_mode_conservation": (
        "probe_two_turn_germ_ballots",
        "probe_minimal_binary_association",
        "probe_binary_frustration_carrier",
        "probe_rooted_parity_walk",
        "probe_carrier_mode_countermodels",
        "probe_passive_carrier_resonance",
        "probe_resonant_energy_and_single_click",
        "probe_carrier_charge_conservation",
    ),
    "noisy_binary_cuts": (
        "probe_robust_shared_cut_overlap",
        "probe_randomized_cut_coverage",
        "probe_processor_cut_data",
    ),
    "carrier_sign_contexts": (
        "probe_folded_carrier_commutators",
        "probe_folded_carrier_parity_contexts",
        "probe_contextual_readout_memory",
    ),
    "relational_observer_covers": (
        "probe_local_reunion_moments",
        "probe_reversible_range_alias",
        "probe_collision_free_exchange_paths",
        "probe_three_sheet_reunion_cost",
        "probe_abelian_reunion_dimensions",
    ),
    "native_charge_dynamics": (
        "probe_charge_collision_invariants",
        "probe_blind_collision_charge",
        "probe_native_reflection_geometry",
        "probe_even_lattice_completion",
        "probe_charge_trace_and_running",
    ),
    "absolute_relative_encounters": (
        "probe_translated_collision_intervention",
        "probe_collision_reference_memory",
    ),
    "local_transport_exchange": (
        "probe_reunion_transport_metric",
        "probe_two_packet_exchange_topology",
        "probe_exchange_sector_kinetics",
        "probe_fermion_exchange_intervention",
    ),
    "native_frame_readout_limits": (
        "probe_native_frame_positivity",
        "probe_dense_readout_residue_countermodel",
        "probe_four_arm_frame_extension",
        "probe_finite_shadow_instruments",
        "probe_junction_calibration_and_events",
    ),
    "particle_count_and_cp_controls": (
        "probe_massive_invisible_channels",
        "probe_two_flavor_frequency_and_width",
        "probe_conjugate_decay_rate_contrast",
    ),
    "spectator_extension_consistency": (
        "probe_six_mode_shadow_exclusivity",
        "probe_spectator_circuit_equivalence",
        "probe_five_mode_shadow_boundary",
    ),
    "square_contact_readouts": (
        "probe_anonymous_contact_additive_readout",
        "probe_dyadic_contact_preparations",
        "probe_square_leaf_refinement",
        "probe_rational_junction_reflection_compiler",
        "probe_nonlinear_junction_discriminator",
    ),
    "anonymous_cluster": (
        "probe_anonymous_reference_collision",
        "probe_local_cluster_charge_descent",
    ),
    "signed_contact_streams": (
        "probe_signed_rotor_junction",
        "probe_anonymous_signed_bucket",
        "probe_overlapping_bucket_dynamics",
    ),
    "single_ticket_transport": (
        "probe_equivariant_event_tickets",
        "probe_autonomous_ticket_clock",
        "probe_pump_locked_hbt",
        "probe_irrevocable_event_prefix",
    ),
    "relational_signal_channels": (
        "probe_relational_signal_metric",
        "probe_relational_clock_modes",
    ),
    "mobile_refinement": (
        "probe_mobile_refinement_field",
        "probe_anonymous_refinement_relations",
        "probe_modular_contact_nulls",
    ),
    "particle_label_limits": (
        "probe_flag_center_blindness",
        "probe_pair_cup_exchange",
    ),
    "clock_memory_contrasts": (
        "probe_pump_clock_lag_extension",
        "probe_five_depth_memory_contrast",
    ),
    "vacancy_inertia": (
        "probe_vacancy_cut_flux",
        "probe_static_current_reflection",
        "probe_edge_inertia_scattering",
    ),
    "readout_design_cost": (
        "probe_active_readout_panels",
        "probe_shared_prefix_readout_cost",
    ),
    "exclusive_mark_controls": (
        "probe_single_mark_ternary_echo",
        "probe_one_visit_phase_budget",
        "probe_three_absorber_menus",
    ),
    "minimal_flavor_loop": (
        "probe_minimal_flavor_phase_loop",
    ),
    "ternary_feedback_windows": (
        "probe_relational_balance_scatter",
        "probe_feedback_ternary_from_pairs",
        "probe_raw_pair_window_reflection",
        "probe_reversible_pair_retiming",
        "probe_feedback_pulse_gain_control",
    ),
    "bench_contact_composition": (
        "probe_raw_contact_grant_fifo",
        "probe_contact_edge_frames",
        "probe_neighbor_twins_flux",
    ),
    "bench_measured_star_parity": (
        "probe_measured_asi_loop_parity",
        "probe_asi_cut_distance",
    ),
    "bench_packet_phase_words": (
        "probe_packet_matching_order",
        "probe_octagon_three_contexts",
    ),
    "bench_frozen_apamea_transfer": (
        "probe_apamea_fixed_transfer",
    ),
    "bench_anonymous_shell_census": (
        "probe_anonymous_shell_rules",
        "probe_shell_incidence_transfer",
    ),
    "bench_apamea_visible_support": (
        "probe_apamea_vertex_support",
    ),
    "bench_pairwise_quartet_records": (
        "probe_pair_contact_completion",
        "probe_relational_quartet_records",
    ),
    "bench_positive_phase_records": (
        "probe_native_phase_coincidence",
        "probe_raw_packet_phase_quotients",
    ),
    "bench_clean_quartet_compilers": (
        "probe_clean_quartet_compiler",
        "probe_single_relation_quartet",
    ),
    "bench_seam_tracks_and_exchange": (
        "probe_three_mark_tracks",
        "probe_seam_exchange_flux",
    ),
    "bench_one_arm_herald_budget": (
        "probe_single_photon_loss_memory",
    ),
    "bench_embedded_relation_measurement": (
        "probe_embedded_relation_reader",
        "probe_pair_compiled_packet_instruments",
    ),
    "bench_loopless_matching_logic": (
        "probe_loopless_link_quartet",
        "probe_loopless_matching_ports",
    ),
    "bench_setting_and_reversal_controls": (
        "probe_packet_setting_dependence",
        "probe_weak_parity_reversal",
    ),
    "bench_forest_and_localized_packet": (
        "probe_facilitated_forest_signal",
        "probe_localized_shell_packets",
    ),
    "bench_existential_link_comparison": (
        "probe_available_link_logic",
        "probe_link_rule_separation",
    ),
    "bench_packet_clock_and_observation": (
        "probe_shell_shutter_protocols",
        "probe_packet_scheduler_fairness",
        "probe_reversible_packet_return",
    ),
    "bench_directed_shape_motion": (
        "probe_three_link_translation",
        "probe_binary_shape_gait",
        "probe_conserved_bond_gait",
        "probe_native_temporal_reversal",
    ),
    "matching_transport": (
        "probe_matching_transport",
        "probe_pairing_natural_transport",
        "probe_matching_echo_selector",
        "probe_matching_transport_cost",
        "probe_ternary_stock_ambiguity",
    ),
    "clock_gravity": (
        "probe_collision_clock_gravity",
    ),
}
DEFAULT_BUNDLE = "fast"
BUNDLES = {
    "fast": ("probe_cancellation_event_router", "probe_native_recurrence_witness"),
    **TOPIC_BUNDLES,
    "all": tuple(probe for probes in TOPIC_BUNDLES.values() for probe in probes),
}


class ProbeResult(TypedDict):
    probe: str
    status: Literal["replayed", "nonzero_exit", "timeout", "error"]
    returncode: int | None
    stdout: str
    stderr: str
    error: str | None


def decode(output: bytes | None) -> str:
    return (output or b"").decode("utf-8", errors="replace")


def replay(probe: str, timeout: int) -> ProbeResult:
    if probe not in BUNDLES["all"]:
        raise ValueError(f"probe not allowlisted: {probe}")
    result: ProbeResult = {
        "probe": probe,
        "status": "error",
        "returncode": None,
        "stdout": "",
        "stderr": "",
        "error": None,
    }
    # These probes and their local imports use explicit checks, not Python
    # assert statements. -B avoids bytecode writes and -E ignores PYTHONPATH.
    command = [sys.executable, "-B", "-E", "-O", "-m", f"scripts.{probe}"]
    try:
        if not (ROOT / "scripts" / f"{probe}.py").is_file():
            raise FileNotFoundError(f"missing probe source: scripts/{probe}.py")
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            stdin=subprocess.DEVNULL,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        result["status"] = "timeout"
        result["stdout"] = decode(error.stdout)
        result["stderr"] = decode(error.stderr)
        result["error"] = f"exceeded {timeout}s"
    except OSError as error:
        result["error"] = str(error)
    else:
        result["status"] = "replayed" if completed.returncode == 0 else "nonzero_exit"
        result["returncode"] = completed.returncode
        result["stdout"] = decode(completed.stdout)
        result["stderr"] = decode(completed.stderr)
    return result


def positive_seconds(value: str) -> int:
    try:
        seconds = int(value)
    except ValueError:
        seconds = 0
    if seconds <= 0:
        raise argparse.ArgumentTypeError("expected a positive integer number of seconds")
    return seconds


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list bundles without running probes")
    parser.add_argument(
        "--bundle", choices=BUNDLES, help=f"select a bundle (run default: {DEFAULT_BUNDLE})"
    )
    parser.add_argument("--json", action="store_true", help="include captured output in a JSON report")
    parser.add_argument(
        "--timeout", type=positive_seconds, default=120, help="seconds per probe (default: 120)"
    )
    args = parser.parse_args(argv)
    if args.list:
        bundles = {args.bundle: BUNDLES[args.bundle]} if args.bundle else BUNDLES
        if args.json:
            print(json.dumps({"bundles": bundles, "scope": SCOPE}, indent=2))
        else:
            for bundle, probes in bundles.items():
                print(f"{bundle} ({len(probes)}): {', '.join(probes)}")
        return 0

    bundle = args.bundle or DEFAULT_BUNDLE
    results = [replay(probe, args.timeout) for probe in BUNDLES[bundle]]
    ok = all(result["status"] == "replayed" for result in results)
    if args.json:
        print(json.dumps({"bundle": bundle, "scope": SCOPE, "ok": ok, "results": results}, indent=2))
    else:
        print(SCOPE)
        for result in results:
            detail = result["error"] or f"exit {result['returncode']}"
            print(f"{result['probe']}: {result['status']} ({detail})")
            if result["stderr"]:
                print(result["stderr"], end="" if result["stderr"].endswith("\n") else "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
