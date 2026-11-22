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
