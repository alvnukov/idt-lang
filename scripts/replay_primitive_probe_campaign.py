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
