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

from scripts import evaluate_born_direct_one_pass as born_direct  # noqa: E402
from scripts import evaluate_fpd_projective_derivation as fpd_projective  # noqa: E402
from scripts import evaluate_general_composite_attempt as composite  # noqa: E402
from scripts import evaluate_phase_scale_boundary_attempt as phase_scale  # noqa: E402
from scripts import evaluate_projective_residual_closure as residual  # noqa: E402
from scripts import evaluate_representation_classification_attempt as representation  # noqa: E402
from scripts import evaluate_unitary_dynamics_attempt as dynamics  # noqa: E402
from scripts import verify_finite_qm_route as finite_route  # noqa: E402

Verdict = Literal[
    "DIRECT_FINITE_QM_ROUTE_HIT_UNIVERSAL_QM_OPEN",
    "DIRECT_QM_ROUTE_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]
CheckScope = Literal["finite", "conditional", "control", "boundary"]


@dataclass(frozen=True)
class RouteCheck:
    name: str
    observed: str
    expected: str
    status: CheckStatus
    scope: CheckScope
    obligation: str


@dataclass(frozen=True)
class DirectQMOnePass:
    verdict: Verdict
    checks: list[RouteCheck]
    passed: int
    failed: int
    born_wall_status: str
    remaining_universal_obligations: tuple[str, ...]


def status_for(observed: str, expected: str) -> CheckStatus:
    return "PASS" if observed == expected else "FAIL"


def make_check(name: str, observed: str, expected: str, scope: CheckScope, obligation: str) -> RouteCheck:
    return RouteCheck(
        name=name,
        observed=observed,
        expected=expected,
        status=status_for(observed, expected),
        scope=scope,
        obligation=obligation,
    )


def finite_route_status() -> str:
    checks = finite_route.build_checks()
    if all(check.status == "PASS" for check in checks):
        return "PASS"
    return "FAIL"


def find_representation_route(route_name: str) -> representation.RouteResult:
    for route in representation.ROUTES:
        if route.name == route_name:
            return representation.evaluate_route(route)
    raise ValueError(f"unknown representation route: {route_name}")


def find_dynamics_route(route_name: str) -> dynamics.RouteResult:
    for route in dynamics.ROUTES:
        if route.name == route_name:
            return dynamics.evaluate_route(route)
    raise ValueError(f"unknown dynamics route: {route_name}")


def find_composite_route(route_name: str) -> composite.RouteResult:
    for route in composite.ROUTES:
        if route.name == route_name:
            return composite.evaluate_route(route)
    raise ValueError(f"unknown composite route: {route_name}")


def find_residual_route(route_name: str) -> residual.RouteResult:
    for route in residual.ROUTES:
        if route.name == route_name:
            return residual.evaluate_route(route)
    raise ValueError(f"unknown residual route: {route_name}")


def find_fpd_projective_route(route_name: str) -> fpd_projective.RouteResult:
    for route in fpd_projective.ROUTES:
        if route.name == route_name:
            return fpd_projective.evaluate_route(route)
    raise ValueError(f"unknown FPD/projective route: {route_name}")


def find_phase_scale_route(route_name: str) -> phase_scale.RouteResult:
    for route in phase_scale.ROUTES:
        if route.name == route_name:
            return phase_scale.evaluate_route(route)
    raise ValueError(f"unknown phase-scale route: {route_name}")


def build_checks() -> list[RouteCheck]:
    born_route = born_direct.build_route()
    representation_route = find_representation_route("spectral_symmetry_route")
    representation_import = find_representation_route("imported_complex_hilbert_representation")
    dynamics_route = find_dynamics_route("continuous_generator_route")
    dynamics_import = find_dynamics_route("imported_unitary_dynamics")
    composite_route = find_composite_route("general_projective_composite_route")
    composite_import = find_composite_route("imported_tensor_product")
    residual_route = find_residual_route("fpd_plus_projective_consistency")
    residual_import = find_residual_route("imported_hilbert_completion")
    fpd_route = find_fpd_projective_route("nusd_plus_conservative_projective_gluing")
    fpd_import = find_fpd_projective_route("imported_hilbert_completion")
    scale_route = find_phase_scale_route("calibrated_phase_scale_boundary")
    scale_import = find_phase_scale_route("imported_physical_hbar")

    return [
        make_check(
            "finite_qm_route.gate",
            finite_route_status(),
            "PASS",
            "finite",
            "Existing finite-QM route controls must remain green.",
        ),
        make_check(
            "born.direct_one_pass",
            born_route.verdict,
            "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF",
            "finite",
            "Born must be closed on the direct finite route without target imports.",
        ),
        make_check(
            "representation.spectral_symmetry_route",
            representation_route.verdict,
            "CONDITIONAL_REPRESENTATION_ROUTE",
            "conditional",
            "Derive spectral decomposition and rich reversible symmetry from primitives.",
        ),
        make_check(
            "representation.imported_control",
            representation_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Complex Hilbert representation imports must remain visible as imports.",
        ),
        make_check(
            "dynamics.continuous_generator_route",
            dynamics_route.verdict,
            "CONDITIONAL_DYNAMICS_ROUTE",
            "conditional",
            "Derive continuous reversible inheritance families and generator closure.",
        ),
        make_check(
            "dynamics.imported_control",
            dynamics_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Unitary dynamics imports must remain visible as imports.",
        ),
        make_check(
            "composite.general_projective_route",
            composite_route.verdict,
            "CONDITIONAL_COMPOSITE_ROUTE",
            "conditional",
            "Derive general entanglement and projective-limit composite closure.",
        ),
        make_check(
            "composite.imported_control",
            composite_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Tensor-product imports must remain visible as imports.",
        ),
        make_check(
            "residual.fpd_plus_projective_consistency",
            residual_route.verdict,
            "CONDITIONAL_CLOSURE_HIT",
            "conditional",
            "Derive residual closure from finite projection determinacy and projective consistency.",
        ),
        make_check(
            "residual.imported_control",
            residual_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Hilbert-completion imports must remain visible as imports.",
        ),
        make_check(
            "fpd_projective.nusd_plus_gluing",
            fpd_route.verdict,
            "DERIVATION_CANDIDATE",
            "conditional",
            "Derive NUSD and conservative projective gluing from the primitive base.",
        ),
        make_check(
            "fpd_projective.imported_control",
            fpd_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Imported Hilbert completion must remain visible as an imported closure.",
        ),
        make_check(
            "phase_scale.calibrated_boundary",
            scale_route.verdict,
            "CONDITIONAL_SCALE_BOUNDARY",
            "boundary",
            "Keep physical hbar_I as a calibrated boundary, not a first-principles proof.",
        ),
        make_check(
            "phase_scale.imported_control",
            scale_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Imported hbar derivation must remain rejected as a proof route.",
        ),
    ]


def build_route() -> DirectQMOnePass:
    checks = build_checks()
    failures = [check for check in checks if check.status == "FAIL"]
    verdict: Verdict = "DIRECT_QM_ROUTE_BLOCKED" if failures else "DIRECT_FINITE_QM_ROUTE_HIT_UNIVERSAL_QM_OPEN"
    return DirectQMOnePass(
        verdict=verdict,
        checks=checks,
        passed=len(checks) - len(failures),
        failed=len(failures),
        born_wall_status="finite_route_closed_universal_route_open",
        remaining_universal_obligations=(
            "derive_full_primitive_boundary_package_from_context_first_unknownness",
            "derive_external_randomization_frequency_calibration_for_facticizable_records",
            "derive_signed_expectation_readout_for_normalized_overlap",
            "derive_phase_bundle_double_cover_for_all_admissible_readout_contexts",
            "derive_spectral_decomposition_from_D_cl_and_projective_closure",
            "derive_rich_reversible_symmetry_from_inheritance_automorphisms",
            "derive_continuous_reversible_dynamics_and_generator_closure",
            "derive_general_entanglement_and_projective_limit_composite_closure",
            "derive_NUSD_and_conservative_projective_gluing_from_primitives",
            "keep_physical_hbar_I_as_calibrated_boundary_or_derive_new_scale_principle",
            "generalize_finite_route_to_all_admissible_QM_contexts",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run the direct finite-QM one-pass route gate.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    route = build_route()
    print(f"qm_direct_one_pass={route.verdict} passed={route.passed} failed={route.failed}")
    print(f"BORN {route.born_wall_status}")
    print(f"REMAINING {','.join(route.remaining_universal_obligations)}")
    if args.show_checks:
        for check in route.checks:
            print(
                f"{check.status} {check.name}: observed={check.observed} "
                f"expected={check.expected}; scope={check.scope}; obligation={check.obligation}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(route), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if route.verdict == "DIRECT_FINITE_QM_ROUTE_HIT_UNIVERSAL_QM_OPEN" else 1


if __name__ == "__main__":
    raise SystemExit(main())
