from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal[
    "FREQUENCY_SCHRODINGER_LOGIC_HIT",
    "IMPORTED_HIT",
    "OPEN_WALL",
]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class SchrodingerLogicRoute:
    name: str
    phase_orientation: bool
    normalized_transition_readout: bool
    reversible_dcl_automorphism: bool
    overlap_preserving_projective_action: bool
    continuous_identity_component: bool
    closed_frequency_generator: bool
    no_energy_form_claim: bool
    imports: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class TestResult:
    name: str
    verdict: TestVerdict
    reason: str
    details: dict[str, str | bool]


@dataclass(frozen=True)
class RouteResult:
    route: str
    verdict: Verdict
    passed: int
    failed: int
    open: int
    imports: tuple[str, ...]
    tests: list[TestResult]
    description: str


ROUTES: tuple[SchrodingerLogicRoute, ...] = (
    SchrodingerLogicRoute(
        name="finite_update_gates_only",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=False,
        overlap_preserving_projective_action=False,
        continuous_identity_component=False,
        closed_frequency_generator=False,
        no_energy_form_claim=True,
        imports=(),
        description="finite context updates without a general continuous generator",
    ),
    SchrodingerLogicRoute(
        name="projective_overlap_symmetry_without_continuity",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=False,
        closed_frequency_generator=False,
        no_energy_form_claim=True,
        imports=(),
        description="projective transition-preserving symmetry without a continuous flow",
    ),
    SchrodingerLogicRoute(
        name="continuous_flow_without_generator",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=True,
        closed_frequency_generator=False,
        no_energy_form_claim=True,
        imports=(),
        description="continuous reversible flow without a closed generator theorem",
    ),
    SchrodingerLogicRoute(
        name="generator_without_phase_orientation",
        phase_orientation=False,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=True,
        closed_frequency_generator=True,
        no_energy_form_claim=True,
        imports=(),
        description="closed real generator route without the oriented phase carrier",
    ),
    SchrodingerLogicRoute(
        name="frequency_generator_readout",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=True,
        closed_frequency_generator=True,
        no_energy_form_claim=True,
        imports=(),
        description="action-scale-free generator-readout route for frequency-form dynamics",
    ),
    SchrodingerLogicRoute(
        name="energy_form_shortcut",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=True,
        closed_frequency_generator=True,
        no_energy_form_claim=False,
        imports=(),
        description="premature physical energy-form equation claim",
    ),
    SchrodingerLogicRoute(
        name="imported_schrodinger_equation",
        phase_orientation=True,
        normalized_transition_readout=True,
        reversible_dcl_automorphism=True,
        overlap_preserving_projective_action=True,
        continuous_identity_component=True,
        closed_frequency_generator=True,
        no_energy_form_claim=False,
        imports=("schrodinger_equation_assumed",),
        description="control that imports the target equation",
    ),
)


def pass_or_open(
    name: str,
    condition: bool,
    pass_reason: str,
    open_reason: str,
) -> TestResult:
    if condition:
        return TestResult(name, "PASS", pass_reason, {name: True})
    return TestResult(name, "OPEN", open_reason, {name: False})


def energy_form_boundary_test(route: SchrodingerLogicRoute) -> TestResult:
    if route.no_energy_form_claim:
        return TestResult(
            "no_energy_form_claim",
            "PASS",
            "route stays at frequency-generator dynamics and does not claim physical energy form",
            {"no_energy_form_claim": True},
        )
    return TestResult(
        "no_energy_form_claim",
        "FAIL",
        "route jumps from frequency generator to physical energy form",
        {"no_energy_form_claim": False},
    )


def import_screen(route: SchrodingerLogicRoute) -> TestResult:
    if route.imports:
        return TestResult(
            "import_screen",
            "FAIL",
            "route imports the target equation or target dynamics",
            {"imports": ",".join(route.imports)},
        )
    return TestResult("import_screen", "PASS", "no target equation import", {"imports": "-"})


def evaluate_route(route: SchrodingerLogicRoute) -> RouteResult:
    tests = [
        pass_or_open(
            "phase_orientation",
            route.phase_orientation,
            "phase-bundle orientation is available for the i-form generator readout",
            "closed generator lacks oriented phase carrier",
        ),
        pass_or_open(
            "normalized_transition_readout",
            route.normalized_transition_readout,
            "normalized overlap supplies the transition readout to preserve",
            "no normalized transition readout is available",
        ),
        pass_or_open(
            "reversible_dcl_automorphism",
            route.reversible_dcl_automorphism,
            "dynamics acts as a reversible D_cl automorphism",
            "finite updates do not define a reversible D_cl automorphism",
        ),
        pass_or_open(
            "overlap_preserving_projective_action",
            route.overlap_preserving_projective_action,
            "dynamics preserves transition readout and acts projectively",
            "projective overlap preservation is missing",
        ),
        pass_or_open(
            "continuous_identity_component",
            route.continuous_identity_component,
            "identity-connected reversible flow is present",
            "discrete symmetries alone do not give generator dynamics",
        ),
        pass_or_open(
            "closed_frequency_generator",
            route.closed_frequency_generator,
            "continuous flow has a closed frequency-generator representation",
            "continuous flow lacks a closed generator theorem",
        ),
        energy_form_boundary_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and open_count == 0:
        verdict = "FREQUENCY_SCHRODINGER_LOGIC_HIT"
    else:
        verdict = "OPEN_WALL"
    return RouteResult(
        route=route.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        open=open_count,
        imports=route.imports,
        tests=tests,
        description=route.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Evaluate the action-scale-free Schrodinger generator-readout logic."
    )
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {
        "FREQUENCY_SCHRODINGER_LOGIC_HIT": 3,
        "IMPORTED_HIT": 2,
        "OPEN_WALL": 1,
    }
    results = sorted(
        (evaluate_route(route) for route in ROUTES),
        key=lambda result: (order[result.verdict], result.passed),
        reverse=True,
    )
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} route={result.route} "
            f"passed={result.passed}/8 failed={result.failed} "
            f"open={result.open} imports={imports}"
        )
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
