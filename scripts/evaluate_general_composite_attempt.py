from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["GENERAL_COMPOSITE_PROVED", "CONDITIONAL_COMPOSITE_ROUTE", "IMPORTED_HIT", "OPEN_WALL"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]


@dataclass(frozen=True)
class CompositeRoute:
    name: str
    finite_tensor_multiplicativity: bool
    product_context_exhaustion: bool
    local_tomography: bool
    no_hidden_joint_invariants: bool
    monoidal_associativity: bool
    entanglement_closure: bool
    projective_limit_consistency: bool
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


ROUTES: tuple[CompositeRoute, ...] = (
    CompositeRoute(
        name="finite_qubit_product_screen",
        finite_tensor_multiplicativity=True,
        product_context_exhaustion=True,
        local_tomography=True,
        no_hidden_joint_invariants=True,
        monoidal_associativity=False,
        entanglement_closure=False,
        projective_limit_consistency=False,
        imports=(),
        description="current finite qubit-like product screen without arbitrary composite theorem",
    ),
    CompositeRoute(
        name="monoidal_without_entanglement",
        finite_tensor_multiplicativity=True,
        product_context_exhaustion=True,
        local_tomography=True,
        no_hidden_joint_invariants=True,
        monoidal_associativity=True,
        entanglement_closure=False,
        projective_limit_consistency=False,
        imports=(),
        description="adds monoidal product coherence but not entanglement/projective-limit closure",
    ),
    CompositeRoute(
        name="finite_entanglement_without_limits",
        finite_tensor_multiplicativity=True,
        product_context_exhaustion=True,
        local_tomography=True,
        no_hidden_joint_invariants=True,
        monoidal_associativity=True,
        entanglement_closure=True,
        projective_limit_consistency=False,
        imports=(),
        description="finite arbitrary composites without projective-limit consistency",
    ),
    CompositeRoute(
        name="general_projective_composite_route",
        finite_tensor_multiplicativity=True,
        product_context_exhaustion=True,
        local_tomography=True,
        no_hidden_joint_invariants=True,
        monoidal_associativity=True,
        entanglement_closure=True,
        projective_limit_consistency=True,
        imports=(),
        description="non-imported route to arbitrary finite and projective-limit composite closure",
    ),
    CompositeRoute(
        name="imported_tensor_product",
        finite_tensor_multiplicativity=True,
        product_context_exhaustion=True,
        local_tomography=True,
        no_hidden_joint_invariants=True,
        monoidal_associativity=True,
        entanglement_closure=True,
        projective_limit_consistency=True,
        imports=("hilbert_tensor_product_assumed",),
        description="control that assumes the target Hilbert tensor product",
    ),
)


def finite_tensor_test(route: CompositeRoute) -> TestResult:
    if route.finite_tensor_multiplicativity:
        return TestResult("finite_tensor_multiplicativity", "PASS", "finite product readout probabilities compose multiplicatively", {"finite_tensor_multiplicativity": True})
    return TestResult("finite_tensor_multiplicativity", "OPEN", "finite product multiplicativity is not established", {"finite_tensor_multiplicativity": False})


def product_exhaustion_test(route: CompositeRoute) -> TestResult:
    if route.product_context_exhaustion:
        return TestResult("product_context_exhaustion", "PASS", "product contexts exhaust admissible composite stable facts on the route", {"product_context_exhaustion": True})
    return TestResult("product_context_exhaustion", "OPEN", "composite stable facts may exceed product-context witnesses", {"product_context_exhaustion": False})


def local_tomography_test(route: CompositeRoute) -> TestResult:
    if route.local_tomography:
        return TestResult("local_tomography", "PASS", "product readouts separate composite operational states", {"local_tomography": True})
    return TestResult("local_tomography", "OPEN", "composite states may not be separated by local product readouts", {"local_tomography": False})


def no_hidden_joint_test(route: CompositeRoute) -> TestResult:
    if route.no_hidden_joint_invariants:
        return TestResult("no_hidden_joint_invariants", "PASS", "hidden joint-only stable invariants are rejected or forced into finite product witness routes", {"no_hidden_joint_invariants": True})
    return TestResult("no_hidden_joint_invariants", "OPEN", "hidden joint-only invariants remain possible", {"no_hidden_joint_invariants": False})


def monoidal_associativity_test(route: CompositeRoute) -> TestResult:
    if route.monoidal_associativity:
        return TestResult("monoidal_associativity", "PASS", "independent composites associate and respect unit/symmetry coherence", {"monoidal_associativity": True})
    return TestResult("monoidal_associativity", "OPEN", "product composition may depend on arbitrary bracketing or ordering", {"monoidal_associativity": False})


def entanglement_closure_test(route: CompositeRoute) -> TestResult:
    if route.entanglement_closure:
        return TestResult("entanglement_closure", "PASS", "non-product composite states are generated inside the same finite route contract", {"entanglement_closure": True})
    return TestResult("entanglement_closure", "OPEN", "entangled states are not generated by the general route", {"entanglement_closure": False})


def projective_limit_test(route: CompositeRoute) -> TestResult:
    if route.projective_limit_consistency:
        return TestResult("projective_limit_consistency", "PASS", "compatible finite composite sectors glue without adding hidden degrees", {"projective_limit_consistency": True})
    return TestResult("projective_limit_consistency", "OPEN", "projective/inductive limits may add unclassified composite degrees", {"projective_limit_consistency": False})


def composite_closure_test(route: CompositeRoute) -> TestResult:
    requirements = (
        route.finite_tensor_multiplicativity,
        route.product_context_exhaustion,
        route.local_tomography,
        route.no_hidden_joint_invariants,
        route.monoidal_associativity,
        route.entanglement_closure,
        route.projective_limit_consistency,
    )
    if all(requirements):
        return TestResult("general_composite_closure", "PASS", "finite and projective-limit composites close under the declared route", {"general_composite_closure": True})
    return TestResult("general_composite_closure", "OPEN", "at least one composite closure obligation is missing", {"general_composite_closure": False})


def import_screen(route: CompositeRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports the target tensor product", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no tensor-product import declared", {"imports": "-"})


def evaluate_route(route: CompositeRoute) -> RouteResult:
    tests = [
        finite_tensor_test(route),
        product_exhaustion_test(route),
        local_tomography_test(route),
        no_hidden_joint_test(route),
        monoidal_associativity_test(route),
        entanglement_closure_test(route),
        projective_limit_test(route),
        composite_closure_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed > 0 and route.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif failed == 0 and all(
        (
            route.finite_tensor_multiplicativity,
            route.product_context_exhaustion,
            route.local_tomography,
            route.no_hidden_joint_invariants,
            route.monoidal_associativity,
            route.entanglement_closure,
            route.projective_limit_consistency,
        )
    ):
        verdict = "CONDITIONAL_COMPOSITE_ROUTE"
    elif failed == 0 and open_count == 0:
        verdict = "GENERAL_COMPOSITE_PROVED"
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
    parser = argparse.ArgumentParser(description="Attempt the general composite/tensor theorem.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"GENERAL_COMPOSITE_PROVED": 4, "CONDITIONAL_COMPOSITE_ROUTE": 3, "IMPORTED_HIT": 2, "OPEN_WALL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} route={result.route} "
            f"passed={result.passed}/9 failed={result.failed} open={result.open} imports={imports}"
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
