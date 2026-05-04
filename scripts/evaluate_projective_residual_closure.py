from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["CONDITIONAL_CLOSURE_HIT", "IMPORTED_HIT", "NEAR_MISS", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class ClosureRoute:
    name: str
    finite_projection_determinacy: bool
    projective_consistency: bool
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


ROUTES: tuple[ClosureRoute, ...] = (
    ClosureRoute(
        name="unclosed_route_residual",
        finite_projection_determinacy=False,
        projective_consistency=False,
        imports=(),
        description="current residual without extra closure principles",
    ),
    ClosureRoute(
        name="finite_projection_determinacy_only",
        finite_projection_determinacy=True,
        projective_consistency=False,
        imports=(),
        description="pointwise finite projection separation without a gluing theorem",
    ),
    ClosureRoute(
        name="projective_consistency_only",
        finite_projection_determinacy=False,
        projective_consistency=True,
        imports=(),
        description="compatible finite-sector gluing without a determinacy theorem",
    ),
    ClosureRoute(
        name="fpd_plus_projective_consistency",
        finite_projection_determinacy=True,
        projective_consistency=True,
        imports=(),
        description="conditional residual closure route using FPD and projective consistency",
    ),
    ClosureRoute(
        name="imported_hilbert_completion",
        finite_projection_determinacy=True,
        projective_consistency=True,
        imports=("complex_hilbert_completion_assumed",),
        description="control that closes the residual by importing the target carrier",
    ),
)


def finite_projection_separation_test(route: ClosureRoute) -> TestResult:
    if route.finite_projection_determinacy:
        return TestResult(
            "finite_projection_separation",
            "PASS",
            "finite projections separate every stable physical distinction",
            {"finite_projection_determinacy": True},
        )
    return TestResult(
        "finite_projection_separation",
        "OPEN",
        "a residual can agree on checked finite routes while remaining stably distinct",
        {"finite_projection_determinacy": False},
    )


def no_hidden_residual_test(route: ClosureRoute) -> TestResult:
    if route.finite_projection_determinacy:
        return TestResult(
            "no_hidden_residual",
            "PASS",
            "a readout-relevant hidden residual must appear in some finite projection or leave physical scope",
            {"hidden_residual_closed": True},
        )
    return TestResult(
        "no_hidden_residual",
        "OPEN",
        "unwitnessed readout-relevant residual is not excluded",
        {"hidden_residual_closed": False},
    )


def compatible_gluing_test(route: ClosureRoute) -> TestResult:
    if route.projective_consistency:
        return TestResult(
            "compatible_gluing",
            "PASS",
            "compatible finite route sectors glue without adding new distinguishability directions",
            {"projective_consistency": True},
        )
    return TestResult(
        "compatible_gluing",
        "OPEN",
        "finite sectors may glue with extra unclassified degrees",
        {"projective_consistency": False},
    )


def structure_preservation_test(route: ClosureRoute) -> TestResult:
    if route.projective_consistency:
        return TestResult(
            "structure_preservation",
            "PASS",
            "projection maps preserve phase-bundle J, normalized overlap, product contexts, and finite readout weights",
            {"preserves_route_structure": True},
        )
    return TestResult(
        "structure_preservation",
        "OPEN",
        "projection maps are not required to preserve the finite route structure",
        {"preserves_route_structure": False},
    )


def import_screen(route: ClosureRoute) -> TestResult:
    if route.imports:
        return TestResult(
            "import_screen",
            "FAIL",
            "route imports the target completion instead of deriving closure",
            {"imports": ",".join(route.imports)},
        )
    return TestResult("import_screen", "PASS", "no target-carrier completion import declared", {"imports": "-"})


def non_circularity_screen(route: ClosureRoute) -> TestResult:
    if route.imports:
        return TestResult(
            "non_circularity",
            "FAIL",
            "closure is circular because the complex-Hilbert completion is assumed",
            {"non_circular": False},
        )
    if route.finite_projection_determinacy and route.projective_consistency:
        return TestResult(
            "non_circularity",
            "PASS",
            "closure uses projection/determinacy obligations rather than naming Hilbert space",
            {"non_circular": True},
        )
    return TestResult(
        "non_circularity",
        "OPEN",
        "route is not circular, but it also does not close the residual",
        {"non_circular": True},
    )


def evaluate_route(route: ClosureRoute) -> RouteResult:
    tests = [
        finite_projection_separation_test(route),
        no_hidden_residual_test(route),
        compatible_gluing_test(route),
        structure_preservation_test(route),
        import_screen(route),
        non_circularity_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and open_count == 0:
        verdict = "CONDITIONAL_CLOSURE_HIT"
    elif passed > 2:
        verdict = "NEAR_MISS"
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
    parser = argparse.ArgumentParser(description="Evaluate conditional closure routes for the finite-sector residual.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"CONDITIONAL_CLOSURE_HIT": 4, "IMPORTED_HIT": 3, "NEAR_MISS": 2, "OPEN_WALL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} route={result.route} "
            f"passed={result.passed}/6 failed={result.failed} open={result.open} imports={imports}"
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
