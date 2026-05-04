from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["PHASE_SCALE_PROVED", "CONDITIONAL_SCALE_BOUNDARY", "IMPORTED_HIT", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class ScaleRoute:
    name: str
    mathematical_qm_scale_free: bool
    calibrated_hbar_anchor: bool
    no_first_principles_hbar_claim: bool
    phase_dimension_consistency: bool
    experimental_anchor_bridge: bool
    independent_action_scale_derivation: bool
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


ROUTES: tuple[ScaleRoute, ...] = (
    ScaleRoute(
        name="mathematical_qm_only",
        mathematical_qm_scale_free=True,
        calibrated_hbar_anchor=False,
        no_first_principles_hbar_claim=True,
        phase_dimension_consistency=True,
        experimental_anchor_bridge=False,
        independent_action_scale_derivation=False,
        imports=(),
        description="scale-free mathematical QM route without physical action-scale anchor",
    ),
    ScaleRoute(
        name="calibrated_phase_scale_boundary",
        mathematical_qm_scale_free=True,
        calibrated_hbar_anchor=True,
        no_first_principles_hbar_claim=True,
        phase_dimension_consistency=True,
        experimental_anchor_bridge=True,
        independent_action_scale_derivation=False,
        imports=(),
        description="honest physical phase-scale boundary using calibrated hbar_I anchor",
    ),
    ScaleRoute(
        name="first_principles_action_scale_route",
        mathematical_qm_scale_free=True,
        calibrated_hbar_anchor=False,
        no_first_principles_hbar_claim=False,
        phase_dimension_consistency=True,
        experimental_anchor_bridge=True,
        independent_action_scale_derivation=True,
        imports=(),
        description="attempted first-principles hbar_I route without calibration boundary",
    ),
    ScaleRoute(
        name="imported_physical_hbar",
        mathematical_qm_scale_free=True,
        calibrated_hbar_anchor=True,
        no_first_principles_hbar_claim=False,
        phase_dimension_consistency=True,
        experimental_anchor_bridge=True,
        independent_action_scale_derivation=True,
        imports=("hbar_value_assumed_as_derived",),
        description="control that imports hbar as a derived primitive",
    ),
)


def mathematical_qm_test(route: ScaleRoute) -> TestResult:
    if route.mathematical_qm_scale_free:
        return TestResult("mathematical_qm_scale_free", "PASS", "the mathematical QM route is formulated up to an external action scale", {"mathematical_qm_scale_free": True})
    return TestResult("mathematical_qm_scale_free", "OPEN", "mathematical QM route depends on an unexplained physical action scale", {"mathematical_qm_scale_free": False})


def calibrated_anchor_test(route: ScaleRoute) -> TestResult:
    if route.calibrated_hbar_anchor:
        return TestResult("calibrated_hbar_anchor", "PASS", "physical phase scale is anchored by explicit calibrated_hbar_I", {"calibrated_hbar_anchor": True})
    return TestResult("calibrated_hbar_anchor", "OPEN", "no explicit calibrated action anchor connects the mathematical route to our universe", {"calibrated_hbar_anchor": False})


def no_stealth_derivation_test(route: ScaleRoute) -> TestResult:
    if route.no_first_principles_hbar_claim:
        return TestResult("no_first_principles_hbar_claim", "PASS", "route does not claim first-principles hbar_I derivation", {"no_first_principles_hbar_claim": True})
    return TestResult("no_first_principles_hbar_claim", "FAIL", "route claims first-principles hbar_I without an accepted proof artifact", {"no_first_principles_hbar_claim": False})


def phase_dimension_test(route: ScaleRoute) -> TestResult:
    if route.phase_dimension_consistency:
        return TestResult("phase_dimension_consistency", "PASS", "action scale converts generator/action to dimensionless phase consistently", {"phase_dimension_consistency": True})
    return TestResult("phase_dimension_consistency", "OPEN", "phase/action dimensions are not consistently bridged", {"phase_dimension_consistency": False})


def experimental_anchor_test(route: ScaleRoute) -> TestResult:
    if route.experimental_anchor_bridge:
        return TestResult("experimental_anchor_bridge", "PASS", "calibrated action scale can be tied to empirical our-universe phase data", {"experimental_anchor_bridge": True})
    return TestResult("experimental_anchor_bridge", "OPEN", "mathematical phase route is not tied to empirical physical scale", {"experimental_anchor_bridge": False})


def action_scale_derivation_test(route: ScaleRoute) -> TestResult:
    if route.independent_action_scale_derivation:
        if route.no_first_principles_hbar_claim:
            return TestResult("independent_action_scale_derivation", "OPEN", "independent action-scale derivation is not claimed in this boundary route", {"independent_action_scale_derivation": False})
        return TestResult("independent_action_scale_derivation", "FAIL", "first-principles hbar_I derivation is outside the accepted proof boundary", {"independent_action_scale_derivation": True})
    return TestResult("independent_action_scale_derivation", "PASS", "route keeps action scale calibrated rather than pretending to derive it", {"independent_action_scale_derivation": False})


def scale_boundary_test(route: ScaleRoute) -> TestResult:
    if (
        route.mathematical_qm_scale_free
        and route.calibrated_hbar_anchor
        and route.no_first_principles_hbar_claim
        and route.phase_dimension_consistency
        and route.experimental_anchor_bridge
        and not route.independent_action_scale_derivation
    ):
        return TestResult("physical_phase_scale_boundary", "PASS", "physical QM is connected by an explicit calibrated action-scale boundary without overclaiming hbar_I", {"physical_phase_scale_boundary": True})
    return TestResult("physical_phase_scale_boundary", "OPEN", "phase-scale bridge is either missing, overclaimed, or not calibrated", {"physical_phase_scale_boundary": False})


def import_screen(route: ScaleRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports or mislabels the physical action scale", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no hidden action-scale import declared", {"imports": "-"})


def evaluate_route(route: ScaleRoute) -> RouteResult:
    tests = [
        mathematical_qm_test(route),
        calibrated_anchor_test(route),
        no_stealth_derivation_test(route),
        phase_dimension_test(route),
        experimental_anchor_test(route),
        action_scale_derivation_test(route),
        scale_boundary_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and route.calibrated_hbar_anchor and route.no_first_principles_hbar_claim and route.experimental_anchor_bridge:
        verdict = "CONDITIONAL_SCALE_BOUNDARY"
    elif failed == 0 and open_count == 0:
        verdict = "PHASE_SCALE_PROVED"
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
    parser = argparse.ArgumentParser(description="Attempt the physical phase-scale boundary theorem.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"PHASE_SCALE_PROVED": 4, "CONDITIONAL_SCALE_BOUNDARY": 3, "IMPORTED_HIT": 2, "OPEN_WALL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} route={result.route} "
            f"passed={result.passed}/8 failed={result.failed} open={result.open} imports={imports}"
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
