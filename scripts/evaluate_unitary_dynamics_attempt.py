from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["UNITARY_DYNAMICS_PROVED", "CONDITIONAL_DYNAMICS_ROUTE", "IMPORTED_HIT", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class DynamicsRoute:
    name: str
    dcl_automorphism: bool
    overlap_preservation: bool
    projective_action: bool
    continuous_one_parameter: bool
    generator_closure: bool
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


ROUTES: tuple[DynamicsRoute, ...] = (
    DynamicsRoute(
        name="finite_unitary_gates_only",
        dcl_automorphism=False,
        overlap_preservation=True,
        projective_action=False,
        continuous_one_parameter=False,
        generator_closure=False,
        imports=(),
        description="existing finite context-map gates without a general dynamics theorem",
    ),
    DynamicsRoute(
        name="dcl_automorphism_only",
        dcl_automorphism=True,
        overlap_preservation=False,
        projective_action=False,
        continuous_one_parameter=False,
        generator_closure=False,
        imports=(),
        description="reversible D_cl automorphism without transition-probability preservation",
    ),
    DynamicsRoute(
        name="wigner_like_symmetry_route",
        dcl_automorphism=True,
        overlap_preservation=True,
        projective_action=True,
        continuous_one_parameter=False,
        generator_closure=False,
        imports=(),
        description="projective transition-probability preserving route; reaches unitary/antiunitary-like symmetry conditionally",
    ),
    DynamicsRoute(
        name="continuous_generator_route",
        dcl_automorphism=True,
        overlap_preservation=True,
        projective_action=True,
        continuous_one_parameter=True,
        generator_closure=True,
        imports=(),
        description="non-imported route from D_cl automorphisms to generator-compatible reversible dynamics",
    ),
    DynamicsRoute(
        name="continuity_without_generator",
        dcl_automorphism=True,
        overlap_preservation=True,
        projective_action=True,
        continuous_one_parameter=True,
        generator_closure=False,
        imports=(),
        description="continuous projective symmetries without a closed generator theorem",
    ),
    DynamicsRoute(
        name="imported_unitary_dynamics",
        dcl_automorphism=True,
        overlap_preservation=True,
        projective_action=True,
        continuous_one_parameter=True,
        generator_closure=True,
        imports=("unitary_evolution_assumed",),
        description="control that assumes the target unitary dynamics",
    ),
)


def dcl_automorphism_test(route: DynamicsRoute) -> TestResult:
    if route.dcl_automorphism:
        return TestResult(
            "dcl_automorphism",
            "PASS",
            "dynamics acts as a reversible automorphism of operationally closed distinguishability",
            {"dcl_automorphism": True},
        )
    return TestResult(
        "dcl_automorphism",
        "OPEN",
        "finite gates do not yet define reversible D_cl automorphisms",
        {"dcl_automorphism": False},
    )


def overlap_preservation_test(route: DynamicsRoute) -> TestResult:
    if route.overlap_preservation:
        return TestResult(
            "overlap_preservation",
            "PASS",
            "transition probabilities / normalized overlap are preserved by the reversible map",
            {"overlap_preservation": True},
        )
    return TestResult(
        "overlap_preservation",
        "OPEN",
        "reversible maps may fail to preserve the normalized-overlap readout",
        {"overlap_preservation": False},
    )


def projective_action_test(route: DynamicsRoute) -> TestResult:
    if route.projective_action:
        return TestResult(
            "projective_action",
            "PASS",
            "maps act on operational rays/classes rather than on arbitrary vector coordinates",
            {"projective_action": True},
        )
    return TestResult(
        "projective_action",
        "OPEN",
        "no projective/ray action theorem is available",
        {"projective_action": False},
    )


def wigner_like_route_test(route: DynamicsRoute) -> TestResult:
    if route.dcl_automorphism and route.overlap_preservation and route.projective_action:
        return TestResult(
            "wigner_like_route",
            "PASS",
            "transition-preserving projective D_cl automorphisms give a Wigner-like representation route",
            {"wigner_like_route": True},
        )
    return TestResult(
        "wigner_like_route",
        "OPEN",
        "Wigner-like representation needs D_cl automorphism, overlap preservation, and projective action",
        {"wigner_like_route": False},
    )


def continuity_test(route: DynamicsRoute) -> TestResult:
    if route.continuous_one_parameter:
        return TestResult(
            "continuous_one_parameter",
            "PASS",
            "dynamics is a continuous one-parameter reversible inheritance family",
            {"continuous_one_parameter": True},
        )
    return TestResult(
        "continuous_one_parameter",
        "OPEN",
        "discrete symmetries may include antiunitary-like maps and do not yield generator dynamics",
        {"continuous_one_parameter": False},
    )


def generator_closure_test(route: DynamicsRoute) -> TestResult:
    if route.generator_closure:
        return TestResult(
            "generator_closure",
            "PASS",
            "continuous reversible dynamics has a closed generator-compatible representation",
            {"generator_closure": True},
        )
    return TestResult(
        "generator_closure",
        "OPEN",
        "continuous reversible dynamics lacks a closed generator theorem",
        {"generator_closure": False},
    )


def dynamics_closure_test(route: DynamicsRoute) -> TestResult:
    requirements = (
        route.dcl_automorphism,
        route.overlap_preservation,
        route.projective_action,
        route.continuous_one_parameter,
        route.generator_closure,
    )
    if all(requirements):
        return TestResult(
            "dynamics_closure",
            "PASS",
            "D_cl automorphism, overlap preservation, projective action, continuity, and generator closure form a dynamics route candidate",
            {"dynamics_closure": True},
        )
    return TestResult(
        "dynamics_closure",
        "OPEN",
        "at least one dynamics-theorem ingredient is missing",
        {"dynamics_closure": False},
    )


def import_screen(route: DynamicsRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports the target unitary dynamics", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no unitary-dynamics import declared", {"imports": "-"})


def evaluate_route(route: DynamicsRoute) -> RouteResult:
    tests = [
        dcl_automorphism_test(route),
        overlap_preservation_test(route),
        projective_action_test(route),
        wigner_like_route_test(route),
        continuity_test(route),
        generator_closure_test(route),
        dynamics_closure_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and all(
        (
            route.dcl_automorphism,
            route.overlap_preservation,
            route.projective_action,
            route.continuous_one_parameter,
            route.generator_closure,
        )
    ):
        verdict = "CONDITIONAL_DYNAMICS_ROUTE"
    elif failed == 0 and open_count == 0:
        verdict = "UNITARY_DYNAMICS_PROVED"
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
    parser = argparse.ArgumentParser(description="Attempt the unitary/generator dynamics theorem.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"UNITARY_DYNAMICS_PROVED": 4, "CONDITIONAL_DYNAMICS_ROUTE": 3, "IMPORTED_HIT": 2, "OPEN_WALL": 1}
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
