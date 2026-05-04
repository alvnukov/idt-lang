from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["DERIVATION_CANDIDATE", "IMPORTED_HIT", "PARTIAL_DERIVATION", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class DerivationRoute:
    name: str
    d_cl: bool
    nusd: bool
    finite_context_generation: bool
    structure_preserving_restrictions: bool
    conservative_projective_gluing: bool
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


ROUTES: tuple[DerivationRoute, ...] = (
    DerivationRoute(
        name="b2_core_only",
        d_cl=True,
        nusd=False,
        finite_context_generation=True,
        structure_preserving_restrictions=False,
        conservative_projective_gluing=False,
        imports=(),
        description="D_cl/F/Q/L-style finite route discipline without NUSD or projective gluing conservativity",
    ),
    DerivationRoute(
        name="nusd_finite_generation",
        d_cl=True,
        nusd=True,
        finite_context_generation=True,
        structure_preserving_restrictions=False,
        conservative_projective_gluing=False,
        imports=(),
        description="NUSD plus finite context generation derives finite projection determinacy but not gluing",
    ),
    DerivationRoute(
        name="conservative_projective_gluing_only",
        d_cl=False,
        nusd=False,
        finite_context_generation=False,
        structure_preserving_restrictions=True,
        conservative_projective_gluing=True,
        imports=(),
        description="projective gluing conservativity without finite projection determinacy",
    ),
    DerivationRoute(
        name="nusd_plus_conservative_projective_gluing",
        d_cl=True,
        nusd=True,
        finite_context_generation=True,
        structure_preserving_restrictions=True,
        conservative_projective_gluing=True,
        imports=(),
        description="non-Hilbert derivation candidate for FPD plus projective consistency",
    ),
    DerivationRoute(
        name="declared_projective_consistency",
        d_cl=True,
        nusd=True,
        finite_context_generation=True,
        structure_preserving_restrictions=True,
        conservative_projective_gluing=True,
        imports=("projective_consistency_assumed",),
        description="control that declares projective consistency as the answer",
    ),
    DerivationRoute(
        name="imported_hilbert_completion",
        d_cl=True,
        nusd=True,
        finite_context_generation=True,
        structure_preserving_restrictions=True,
        conservative_projective_gluing=True,
        imports=("complex_hilbert_completion_assumed",),
        description="control that imports the target completion",
    ),
)


def fpd_derivation_test(route: DerivationRoute) -> TestResult:
    if route.d_cl and route.nusd and route.finite_context_generation:
        return TestResult(
            "fpd_derivation",
            "PASS",
            "NUSD plus finite context generation and D_cl gives finite projection determinacy",
            {"d_cl": True, "nusd": True, "finite_context_generation": True},
        )
    return TestResult(
        "fpd_derivation",
        "OPEN",
        "finite route discipline alone does not exclude a stable distinction outside finite projections",
        {
            "d_cl": route.d_cl,
            "nusd": route.nusd,
            "finite_context_generation": route.finite_context_generation,
        },
    )


def no_unwitnessed_difference_test(route: DerivationRoute) -> TestResult:
    if route.nusd and route.d_cl:
        return TestResult(
            "no_unwitnessed_difference",
            "PASS",
            "stable physical distinctions must enter witness or loss-accounting routes",
            {"nusd": True, "d_cl": True},
        )
    return TestResult(
        "no_unwitnessed_difference",
        "OPEN",
        "unwitnessed stable differences remain admissible",
        {"nusd": route.nusd, "d_cl": route.d_cl},
    )


def projective_consistency_derivation_test(route: DerivationRoute) -> TestResult:
    if route.structure_preserving_restrictions and route.conservative_projective_gluing:
        return TestResult(
            "projective_consistency_derivation",
            "PASS",
            "structure-preserving restrictions plus conservative gluing give projective consistency",
            {
                "structure_preserving_restrictions": True,
                "conservative_projective_gluing": True,
            },
        )
    return TestResult(
        "projective_consistency_derivation",
        "OPEN",
        "finite sectors may glue with extra directions or broken route structure",
        {
            "structure_preserving_restrictions": route.structure_preserving_restrictions,
            "conservative_projective_gluing": route.conservative_projective_gluing,
        },
    )


def no_new_gluing_directions_test(route: DerivationRoute) -> TestResult:
    if route.conservative_projective_gluing and route.d_cl:
        return TestResult(
            "no_new_gluing_directions",
            "PASS",
            "compatible gluing cannot introduce a new stable direction unless D_cl supplies a finite witness route",
            {"conservative_projective_gluing": True, "d_cl": True},
        )
    return TestResult(
        "no_new_gluing_directions",
        "OPEN",
        "gluing may add a stable residual not present in finite sectors",
        {"conservative_projective_gluing": route.conservative_projective_gluing, "d_cl": route.d_cl},
    )


def route_structure_preservation_test(route: DerivationRoute) -> TestResult:
    if route.structure_preserving_restrictions:
        return TestResult(
            "route_structure_preservation",
            "PASS",
            "restriction maps preserve J, normalized overlap, product contexts, and readout weights",
            {"structure_preserving_restrictions": True},
        )
    return TestResult(
        "route_structure_preservation",
        "OPEN",
        "finite-sector maps need not preserve the route structure",
        {"structure_preserving_restrictions": False},
    )


def import_screen(route: DerivationRoute) -> TestResult:
    if route.imports:
        return TestResult(
            "import_screen",
            "FAIL",
            "route imports a closure theorem or target completion",
            {"imports": ",".join(route.imports)},
        )
    return TestResult("import_screen", "PASS", "no closure/target import declared", {"imports": "-"})


def evaluate_route(route: DerivationRoute) -> RouteResult:
    tests = [
        fpd_derivation_test(route),
        no_unwitnessed_difference_test(route),
        projective_consistency_derivation_test(route),
        no_new_gluing_directions_test(route),
        route_structure_preservation_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and open_count == 0:
        verdict = "DERIVATION_CANDIDATE"
    elif passed >= 3:
        verdict = "PARTIAL_DERIVATION"
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
    parser = argparse.ArgumentParser(description="Evaluate derivation routes for FPD and projective consistency.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"DERIVATION_CANDIDATE": 4, "IMPORTED_HIT": 3, "PARTIAL_DERIVATION": 2, "OPEN_WALL": 1}
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
