from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["REPRESENTATION_PROVED", "CONDITIONAL_REPRESENTATION_ROUTE", "IMPORTED_HIT", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class RepresentationRoute:
    name: str
    finite_route_contract: bool
    fpd_projective_closure: bool
    phase_bundle_j: bool
    normalized_overlap: bool
    local_tomography: bool
    spectral_decomposition: bool
    rich_reversible_symmetry: bool
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


ROUTES: tuple[RepresentationRoute, ...] = (
    RepresentationRoute(
        name="finite_route_only",
        finite_route_contract=True,
        fpd_projective_closure=False,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=False,
        rich_reversible_symmetry=False,
        imports=(),
        description="current finite route without residual closure or representation richness",
    ),
    RepresentationRoute(
        name="fpd_projective_closed_route",
        finite_route_contract=True,
        fpd_projective_closure=True,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=False,
        rich_reversible_symmetry=False,
        imports=(),
        description="finite route plus FPD/projective closure, but no spectral/symmetry theorem",
    ),
    RepresentationRoute(
        name="spectral_without_symmetry",
        finite_route_contract=True,
        fpd_projective_closure=True,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=True,
        rich_reversible_symmetry=False,
        imports=(),
        description="adds spectral decomposition but leaves reversible symmetry underpowered",
    ),
    RepresentationRoute(
        name="symmetry_without_spectral",
        finite_route_contract=True,
        fpd_projective_closure=True,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=False,
        rich_reversible_symmetry=True,
        imports=(),
        description="adds rich reversible symmetries but lacks a spectral decomposition theorem",
    ),
    RepresentationRoute(
        name="spectral_symmetry_route",
        finite_route_contract=True,
        fpd_projective_closure=True,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=True,
        rich_reversible_symmetry=True,
        imports=(),
        description="non-Hilbert representation route candidate using spectrality and D_cl automorphism richness",
    ),
    RepresentationRoute(
        name="imported_complex_hilbert_representation",
        finite_route_contract=True,
        fpd_projective_closure=True,
        phase_bundle_j=True,
        normalized_overlap=True,
        local_tomography=True,
        spectral_decomposition=True,
        rich_reversible_symmetry=True,
        imports=("complex_hilbert_representation_assumed",),
        description="control that assumes the target representation",
    ),
)


def finite_route_contract_test(route: RepresentationRoute) -> TestResult:
    if route.finite_route_contract:
        return TestResult("finite_route_contract", "PASS", "finite route gate and frontier controls are satisfied", {"finite_route_contract": True})
    return TestResult("finite_route_contract", "FAIL", "finite route gate is not satisfied", {"finite_route_contract": False})


def residual_closure_test(route: RepresentationRoute) -> TestResult:
    if route.fpd_projective_closure:
        return TestResult("residual_closure", "PASS", "FPD/projective closure removes route-closed hidden residuals", {"fpd_projective_closure": True})
    return TestResult("residual_closure", "OPEN", "route-closed residual remains possible", {"fpd_projective_closure": False})


def scalar_carrier_test(route: RepresentationRoute) -> TestResult:
    if route.phase_bundle_j and route.normalized_overlap:
        return TestResult("scalar_carrier", "PASS", "phase-bundle J plus normalized overlap supplies the complex-like scalar carrier screen", {"phase_bundle_j": True, "normalized_overlap": True})
    return TestResult("scalar_carrier", "OPEN", "phase-bundle J or normalized overlap is missing", {"phase_bundle_j": route.phase_bundle_j, "normalized_overlap": route.normalized_overlap})


def local_tomography_test(route: RepresentationRoute) -> TestResult:
    if route.local_tomography:
        return TestResult("local_tomography", "PASS", "product contexts separate the finite composite carrier on the current screen", {"local_tomography": True})
    return TestResult("local_tomography", "OPEN", "product-context separation is not established", {"local_tomography": False})


def spectral_decomposition_test(route: RepresentationRoute) -> TestResult:
    if route.spectral_decomposition:
        return TestResult("spectral_decomposition", "PASS", "every finite stable state is assumed/generated by orthogonal exposed contexts", {"spectral_decomposition": True})
    return TestResult("spectral_decomposition", "OPEN", "finite states may lack decomposition into exposed orthogonal context records", {"spectral_decomposition": False})


def reversible_symmetry_test(route: RepresentationRoute) -> TestResult:
    if route.rich_reversible_symmetry:
        return TestResult("rich_reversible_symmetry", "PASS", "D_cl automorphisms are rich enough to connect pure exposed contexts and preserve overlap", {"rich_reversible_symmetry": True})
    return TestResult("rich_reversible_symmetry", "OPEN", "pure-context automorphism richness is not proved", {"rich_reversible_symmetry": False})


def representation_closure_test(route: RepresentationRoute) -> TestResult:
    requirements = (
        route.finite_route_contract,
        route.fpd_projective_closure,
        route.phase_bundle_j,
        route.normalized_overlap,
        route.local_tomography,
        route.spectral_decomposition,
        route.rich_reversible_symmetry,
    )
    if all(requirements):
        return TestResult(
            "representation_closure",
            "PASS",
            "finite route, closure, scalar carrier, spectrality, local tomography, and symmetry form a representation route candidate",
            {"representation_closure": True},
        )
    return TestResult(
        "representation_closure",
        "OPEN",
        "at least one representation-classification ingredient is missing",
        {"representation_closure": False},
    )


def import_screen(route: RepresentationRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports the target representation", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no target representation import declared", {"imports": "-"})


def evaluate_route(route: RepresentationRoute) -> RouteResult:
    tests = [
        finite_route_contract_test(route),
        residual_closure_test(route),
        scalar_carrier_test(route),
        local_tomography_test(route),
        spectral_decomposition_test(route),
        reversible_symmetry_test(route),
        representation_closure_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and route.spectral_decomposition and route.rich_reversible_symmetry and not route.imports:
        verdict = "CONDITIONAL_REPRESENTATION_ROUTE"
    elif failed == 0 and open_count == 0:
        verdict = "REPRESENTATION_PROVED"
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
    parser = argparse.ArgumentParser(description="Attempt the universal complex-Hilbert representation theorem.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"REPRESENTATION_PROVED": 4, "CONDITIONAL_REPRESENTATION_ROUTE": 3, "IMPORTED_HIT": 2, "OPEN_WALL": 1}
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
