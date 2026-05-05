from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_born_hilbert_bell_primitive_link as primitive_link  # noqa: E402
import scripts.evaluate_schrodinger_logic_attempt as schrodinger_logic  # noqa: E402

Verdict = Literal[
    "EXISTING_QM_LOGIC_CONNECTED_CONDITIONAL",
    "EXISTING_QM_LOGIC_DISCONNECTED",
]
CheckStatus = Literal["PASS", "FAIL"]
CheckLayer = Literal[
    "bell",
    "born",
    "hilbert",
    "schrodinger",
    "shared_anchor",
    "boundary",
    "control",
]


@dataclass(frozen=True)
class ConnectednessCheck:
    name: str
    layer: CheckLayer
    observed: str
    expected: str
    status: CheckStatus
    meaning: str


@dataclass(frozen=True)
class ExistingQMLogicConnectedness:
    verdict: Verdict
    passed: int
    failed: int
    checks: tuple[ConnectednessCheck, ...]
    shared_anchors: tuple[str, ...]
    connected_nodes: tuple[str, ...]
    potential_tensions: tuple[str, ...]
    not_checked_open_obligations: tuple[str, ...]
    forbidden_upgrades: tuple[str, ...]


def check_status(observed: str, expected: str) -> CheckStatus:
    return "PASS" if observed == expected else "FAIL"


def make_check(
    name: str,
    layer: CheckLayer,
    observed: str,
    expected: str,
    meaning: str,
) -> ConnectednessCheck:
    return ConnectednessCheck(
        name=name,
        layer=layer,
        observed=observed,
        expected=expected,
        status=check_status(observed, expected),
        meaning=meaning,
    )


def primitive_check(
    route: primitive_link.PrimitiveLinkPass,
    name: str,
    layer: CheckLayer,
    expected: str,
    meaning: str,
) -> ConnectednessCheck:
    for check in route.checks:
        if check.name == name:
            return make_check(name, layer, check.observed, expected, meaning)
    return make_check(name, layer, "MISSING", expected, meaning)


def schrodinger_route_result() -> schrodinger_logic.RouteResult:
    for route in schrodinger_logic.ROUTES:
        if route.name == "frequency_generator_readout":
            return schrodinger_logic.evaluate_route(route)
    raise ValueError("missing frequency_generator_readout route")


def schrodinger_control_result(route_name: str) -> schrodinger_logic.RouteResult:
    for route in schrodinger_logic.ROUTES:
        if route.name == route_name:
            return schrodinger_logic.evaluate_route(route)
    raise ValueError(f"missing Schrodinger control route: {route_name}")


def schrodinger_test_status(
    route: schrodinger_logic.RouteResult,
    test_name: str,
) -> str:
    for test in route.tests:
        if test.name == test_name:
            return test.verdict
    return "MISSING"


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise ValueError(f"{field} keys must be strings")
        result[key] = item
    return result


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return list(value)


def status_of_symbol(manifest: dict[str, object], symbol_id: str) -> str:
    symbols = require_mapping(manifest.get("symbols"), "symbols")
    symbol = require_mapping(symbols.get(symbol_id), f"symbols.{symbol_id}")
    status = symbol.get("status")
    if not isinstance(status, str):
        raise ValueError(f"symbols.{symbol_id}.status must be a string")
    return status


def finite_gate(manifest: dict[str, object], gate_id: str) -> dict[str, object]:
    for raw_gate in require_list(manifest.get("finite_gates"), "finite_gates"):
        gate = require_mapping(raw_gate, "finite_gates[]")
        if gate.get("id") == gate_id:
            return gate
    raise ValueError(f"missing finite gate {gate_id}")


def bool_gate_field(gate: dict[str, object], field: str) -> str:
    value = gate.get(field)
    if not isinstance(value, bool):
        raise ValueError(f"{gate.get('id')}.{field} must be boolean")
    return "true" if value else "false"


def gate_import_count(gate: dict[str, object]) -> str:
    imports = require_list(gate.get("imports", []), f"{gate.get('id')}.imports")
    return str(len(imports))


def load_manifest(path: Path) -> dict[str, object]:
    return require_mapping(json.loads(path.read_text(encoding="utf-8")), "manifest")


def build_connectedness(manifest_path: Path) -> ExistingQMLogicConnectedness:
    primitive = primitive_link.build_pass()
    schrodinger = schrodinger_route_result()
    schrodinger_import = schrodinger_control_result("imported_schrodinger_equation")
    schrodinger_energy_shortcut = schrodinger_control_result("energy_form_shortcut")
    manifest = load_manifest(manifest_path)
    schrodinger_gate = finite_gate(manifest, "schrodinger_frequency_generator_readout_demo")
    legacy_generator_gate = finite_gate(manifest, "unitary_generator_reconstruction_demo")
    carrier_frontier_gate = finite_gate(manifest, "carrier_selection_frontier_demo")
    legacy_generator_has_hbar = (
        "hbar" in legacy_generator_gate
        or "expected_hamiltonian" in legacy_generator_gate
    )
    legacy_generator_quarantined = (
        not legacy_generator_has_hbar
        or (
            status_of_symbol(manifest, "hbar_I") == "blocked"
            and status_of_symbol(manifest, "qm_generator_translation_closure_I") == "target"
            and status_of_symbol(manifest, "full_QM_I") == "target"
        )
    )

    checks = (
        make_check(
            "primitive_link.route",
            "shared_anchor",
            primitive.verdict,
            "BORN_HILBERT_BELL_PRIMITIVE_LINK_CONDITIONAL_HIT_UNIVERSAL_UNIQUENESS_OPEN",
            "Bell, Born, and Hilbert stay connected by the finite primitive link.",
        ),
        primitive_check(
            primitive,
            "bell.normalized_orientation_overlap",
            "bell",
            "NEW_PRIMITIVE_HIT",
            "Bell angle behavior is connected through normalized orientation overlap.",
        ),
        primitive_check(
            primitive,
            "born.direct_finite_readout",
            "born",
            "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF",
            "Finite Born readout is connected to signed overlap and phase-bundle square.",
        ),
        primitive_check(
            primitive,
            "born.context_probability_readout",
            "born",
            "CONDITIONAL_BORN_ROUTE",
            "Born probability accounting stays downstream of the selected readout weights.",
        ),
        primitive_check(
            primitive,
            "hilbert.phase_bundle_carrier",
            "hilbert",
            "CARRIER_ROUTE_HIT",
            "Hilbert carrier pressure is connected to phase-bundle normalized overlap.",
        ),
        primitive_check(
            primitive,
            "hilbert.representation_route",
            "hilbert",
            "CONDITIONAL_REPRESENTATION_ROUTE",
            "Hilbert representation route is connected to spectrality and reversible symmetry.",
        ),
        primitive_check(
            primitive,
            "separator.real_hilbert_rebit",
            "hilbert",
            "REJECTED",
            "The real-Hilbert/rebit separator remains rejected by hidden joint-only orientation.",
        ),
        make_check(
            "schrodinger.frequency_generator_readout",
            "schrodinger",
            schrodinger.verdict,
            "FREQUENCY_SCHRODINGER_LOGIC_HIT",
            "Schrodinger is connected as action-scale-free generator-readout dynamics.",
        ),
        make_check(
            "schrodinger.phase_orientation",
            "shared_anchor",
            schrodinger_test_status(schrodinger, "phase_orientation"),
            "PASS",
            "Schrodinger uses the same phase-orientation anchor as Born/Hilbert.",
        ),
        make_check(
            "schrodinger.normalized_transition_readout",
            "shared_anchor",
            schrodinger_test_status(schrodinger, "normalized_transition_readout"),
            "PASS",
            "Schrodinger uses normalized transition readout, matching the overlap anchor.",
        ),
        primitive_check(
            primitive,
            "bell.direct_cosine_import_control",
            "control",
            "IMPORTED_HIT",
            "Direct Bell/cosine import remains blocked.",
        ),
        primitive_check(
            primitive,
            "born.import_control",
            "control",
            "IMPORTED_HIT",
            "Direct Born import remains blocked.",
        ),
        primitive_check(
            primitive,
            "hilbert.import_control",
            "control",
            "IMPORTED_HIT",
            "Direct complex-Hilbert import remains blocked.",
        ),
        make_check(
            "schrodinger.import_control",
            "control",
            schrodinger_import.verdict,
            "IMPORTED_HIT",
            "Imported Schrodinger equation remains blocked.",
        ),
        make_check(
            "schrodinger.energy_form_shortcut_control",
            "control",
            "FAIL" if schrodinger_energy_shortcut.failed > 0 else "PASS",
            "FAIL",
            "Energy-form shortcut remains outside the action-scale-free dynamics readout.",
        ),
        make_check(
            "boundary.full_QM_status",
            "boundary",
            status_of_symbol(manifest, "full_QM_I"),
            "target",
            "Existing connectedness must not upgrade full_QM_I.",
        ),
        make_check(
            "boundary.hbar_status",
            "boundary",
            status_of_symbol(manifest, "hbar_I"),
            "blocked",
            "Existing connectedness must not derive the action scale.",
        ),
        make_check(
            "boundary.qm_generator_translation_status",
            "boundary",
            status_of_symbol(manifest, "qm_generator_translation_closure_I"),
            "target",
            "The energy/action generator-translation closure remains outside the current check.",
        ),
        make_check(
            "boundary.universal_carrier_selection_status",
            "boundary",
            str(carrier_frontier_gate.get("expected_frontier_status")),
            "not_derived",
            "Hilbert finite carrier pressure must not be confused with universal carrier selection.",
        ),
        make_check(
            "boundary.schrodinger_gate_action_scale_free",
            "boundary",
            bool_gate_field(schrodinger_gate, "action_scale_free"),
            "true",
            "Manifest Schrodinger gate must remain action-scale-free.",
        ),
        make_check(
            "boundary.schrodinger_gate_imports",
            "boundary",
            gate_import_count(schrodinger_gate),
            "0",
            "Manifest Schrodinger gate must not import the target equation.",
        ),
        make_check(
            "boundary.legacy_hamiltonian_sample_quarantined",
            "boundary",
            "true" if legacy_generator_quarantined else "false",
            "true",
            "Legacy hbar/Hamiltonian sample is allowed only while exact generator translation remains target.",
        ),
    )
    failed = sum(1 for check in checks if check.status == "FAIL")
    verdict: Verdict = (
        "EXISTING_QM_LOGIC_DISCONNECTED"
        if failed
        else "EXISTING_QM_LOGIC_CONNECTED_CONDITIONAL"
    )
    return ExistingQMLogicConnectedness(
        verdict=verdict,
        passed=len(checks) - failed,
        failed=failed,
        checks=checks,
        shared_anchors=(
            "normalized_oriented_distinguishability",
            "phase_orientation",
            "normalized_transition_readout",
            "phase_bundle_square",
        ),
        connected_nodes=(
            "Bell angle/correlation screen",
            "finite Born readout",
            "Hilbert phase-bundle carrier route",
            "Schrodinger frequency-generator dynamics readout",
        ),
        potential_tensions=(
            (
                "unitary_generator_reconstruction_demo contains hbar/Hamiltonian sample; "
                "currently quarantined because hbar_I is blocked and qm_generator_translation_closure_I "
                "remains target"
            ),
        )
        if legacy_generator_has_hbar
        else (),
        not_checked_open_obligations=primitive.remaining_obligations,
        forbidden_upgrades=(
            "does_not_prove_universal_Born",
            "does_not_prove_universal_Hilbert_uniqueness",
            "does_not_prove_exact_fundamental_QM",
            "does_not_check_first_principles_action_scale",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Check logical connectedness of existing Bell/Born/Hilbert/Schrodinger QM nodes."
    )
    parser.add_argument("--manifest", default=str(REPO_ROOT / "theory_verifier_manifest.json"))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_connectedness(Path(args.manifest))
    print(
        f"qm_existing_logic_connectedness={probe.verdict} "
        f"passed={probe.passed} failed={probe.failed}"
    )
    print(f"SHARED_ANCHORS {','.join(probe.shared_anchors)}")
    print(f"CONNECTED_NODES {','.join(probe.connected_nodes)}")
    print(f"POTENTIAL_TENSIONS {','.join(probe.potential_tensions) if probe.potential_tensions else '-'}")
    print(f"NOT_CHECKED_OPEN {','.join(probe.not_checked_open_obligations)}")
    print(f"FORBIDDEN_UPGRADES {','.join(probe.forbidden_upgrades)}")
    if args.show_checks:
        for check in probe.checks:
            print(
                f"{check.status} {check.name}: observed={check.observed} "
                f"expected={check.expected}; layer={check.layer}; meaning={check.meaning}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if probe.verdict == "EXISTING_QM_LOGIC_CONNECTED_CONDITIONAL" else 1


if __name__ == "__main__":
    raise SystemExit(main())
