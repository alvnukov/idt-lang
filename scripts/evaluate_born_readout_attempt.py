from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["BORN_RULE_PROVED", "CONDITIONAL_BORN_ROUTE", "IMPORTED_HIT", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class BornRoute:
    name: str
    positive_quadratic_measure: bool
    context_normalization: bool
    exclusivity_additivity: bool
    coarse_graining_consistency: bool
    operational_equivalence: bool
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


ROUTES: tuple[BornRoute, ...] = (
    BornRoute(
        name="finite_overlap_screens_only",
        positive_quadratic_measure=True,
        context_normalization=False,
        exclusivity_additivity=False,
        coarse_graining_consistency=False,
        operational_equivalence=False,
        imports=(),
        description="finite normalized-overlap screens without universal readout obligations",
    ),
    BornRoute(
        name="normalization_only",
        positive_quadratic_measure=True,
        context_normalization=True,
        exclusivity_additivity=False,
        coarse_graining_consistency=False,
        operational_equivalence=False,
        imports=(),
        description="positive quadratic weights plus normalized total context weight",
    ),
    BornRoute(
        name="normalization_exclusivity",
        positive_quadratic_measure=True,
        context_normalization=True,
        exclusivity_additivity=True,
        coarse_graining_consistency=False,
        operational_equivalence=False,
        imports=(),
        description="adds additivity over facticized exclusive alternatives",
    ),
    BornRoute(
        name="normalization_exclusivity_coarse_graining",
        positive_quadratic_measure=True,
        context_normalization=True,
        exclusivity_additivity=True,
        coarse_graining_consistency=True,
        operational_equivalence=False,
        imports=(),
        description="adds stable probabilities under admissible coarse-graining",
    ),
    BornRoute(
        name="quadratic_context_probability_route",
        positive_quadratic_measure=True,
        context_normalization=True,
        exclusivity_additivity=True,
        coarse_graining_consistency=True,
        operational_equivalence=True,
        imports=(),
        description="non-imported route from positive quadratic measure to Born-like context probabilities",
    ),
    BornRoute(
        name="imported_born_rule",
        positive_quadratic_measure=True,
        context_normalization=True,
        exclusivity_additivity=True,
        coarse_graining_consistency=True,
        operational_equivalence=True,
        imports=("born_rule_assumed",),
        description="control that assumes the target probability rule",
    ),
)


def positive_quadratic_measure_test(route: BornRoute) -> TestResult:
    if route.positive_quadratic_measure:
        return TestResult(
            "positive_quadratic_measure",
            "PASS",
            "normalized overlap and positive comparison geometry supply nonnegative quadratic weights",
            {"positive_quadratic_measure": True},
        )
    return TestResult(
        "positive_quadratic_measure",
        "OPEN",
        "readout weights are not known to be positive quadratic measures",
        {"positive_quadratic_measure": False},
    )


def context_normalization_test(route: BornRoute) -> TestResult:
    if route.context_normalization:
        return TestResult(
            "context_normalization",
            "PASS",
            "each admissible finite context has a positive total weight and normalization",
            {"context_normalization": True},
        )
    return TestResult(
        "context_normalization",
        "OPEN",
        "positive weights do not yet define probabilities without stable context normalization",
        {"context_normalization": False},
    )


def exclusivity_additivity_test(route: BornRoute) -> TestResult:
    if route.exclusivity_additivity:
        return TestResult(
            "exclusivity_additivity",
            "PASS",
            "facticized exclusive alternatives add with no unaccounted cross term",
            {"exclusivity_additivity": True},
        )
    return TestResult(
        "exclusivity_additivity",
        "OPEN",
        "exclusive alternatives may retain unaccounted interference/cross terms",
        {"exclusivity_additivity": False},
    )


def coarse_graining_test(route: BornRoute) -> TestResult:
    if route.coarse_graining_consistency:
        return TestResult(
            "coarse_graining_consistency",
            "PASS",
            "admissible coarse-graining preserves normalized context probabilities",
            {"coarse_graining_consistency": True},
        )
    return TestResult(
        "coarse_graining_consistency",
        "OPEN",
        "probability assignments may drift under admissible coarse-graining",
        {"coarse_graining_consistency": False},
    )


def operational_equivalence_test(route: BornRoute) -> TestResult:
    if route.operational_equivalence:
        return TestResult(
            "operational_equivalence",
            "PASS",
            "operationally identical readout events receive identical normalized weights",
            {"operational_equivalence": True},
        )
    return TestResult(
        "operational_equivalence",
        "OPEN",
        "equivalent readout events are not forced to share probabilities",
        {"operational_equivalence": False},
    )


def born_context_probability_test(route: BornRoute) -> TestResult:
    requirements = (
        route.positive_quadratic_measure,
        route.context_normalization,
        route.exclusivity_additivity,
        route.coarse_graining_consistency,
        route.operational_equivalence,
    )
    if all(requirements):
        return TestResult(
            "born_context_probability",
            "PASS",
            "positive quadratic weights become Born-like finite context probabilities",
            {"born_context_probability": True},
        )
    return TestResult(
        "born_context_probability",
        "OPEN",
        "at least one readout obligation is missing before a Born-like context probability theorem follows",
        {"born_context_probability": False},
    )


def import_screen(route: BornRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports the target Born rule", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no Born-rule import declared", {"imports": "-"})


def evaluate_route(route: BornRoute) -> RouteResult:
    tests = [
        positive_quadratic_measure_test(route),
        context_normalization_test(route),
        exclusivity_additivity_test(route),
        coarse_graining_test(route),
        operational_equivalence_test(route),
        born_context_probability_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and all(
        (
            route.positive_quadratic_measure,
            route.context_normalization,
            route.exclusivity_additivity,
            route.coarse_graining_consistency,
            route.operational_equivalence,
        )
    ):
        verdict = "CONDITIONAL_BORN_ROUTE"
    elif failed == 0 and open_count == 0:
        verdict = "BORN_RULE_PROVED"
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
    parser = argparse.ArgumentParser(description="Attempt the universal Born/readout theorem.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"BORN_RULE_PROVED": 4, "CONDITIONAL_BORN_ROUTE": 3, "IMPORTED_HIT": 2, "OPEN_WALL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} route={result.route} "
            f"passed={result.passed}/7 failed={result.failed} open={result.open} imports={imports}"
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
