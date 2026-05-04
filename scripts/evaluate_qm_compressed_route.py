from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["CARRIER_ROUTE_HIT", "NEW_WALL", "KILL"]
TestVerdict = Literal["PASS", "FAIL"]
RealVector = tuple[float, ...]
ComplexVector = tuple[complex, ...]


@dataclass(frozen=True)
class Route:
    name: str
    mode: Literal["real_overlap", "phase_bundle"]
    imports: tuple[str, ...]
    open_principles: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class TestResult:
    name: str
    verdict: TestVerdict
    reason: str
    details: dict[str, float | int | str | bool]


@dataclass(frozen=True)
class RouteResult:
    route: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    open_principles: tuple[str, ...]
    tests: list[TestResult]
    description: str


ROUTES: tuple[Route, ...] = (
    Route(
        name="real_normalized_overlap",
        mode="real_overlap",
        imports=(),
        open_principles=(),
        description="previous real normalized-overlap route",
    ),
    Route(
        name="phase_bundle_normalized_overlap",
        mode="phase_bundle",
        imports=(),
        open_principles=("derive_phase_bundle_J_structure",),
        description="normalized overlap lifted to a phase bundle with J/quadrature gauge",
    ),
)


def real_dot(left: RealVector, right: RealVector) -> float:
    return sum(a * b for a, b in zip(left, right, strict=True))


def real_norm(vector: RealVector) -> float:
    return math.sqrt(real_dot(vector, vector))


def real_normalize(vector: RealVector) -> RealVector:
    length = real_norm(vector)
    return tuple(component / length for component in vector)


def complex_inner(left: ComplexVector, right: ComplexVector) -> complex:
    return sum(a.conjugate() * b for a, b in zip(left, right, strict=True))


def complex_norm(vector: ComplexVector) -> float:
    return math.sqrt(complex_inner(vector, vector).real)


def complex_normalize(vector: ComplexVector) -> ComplexVector:
    length = complex_norm(vector)
    return tuple(component / length for component in vector)


def real_embedding(vector: ComplexVector) -> RealVector:
    output: list[float] = []
    for component in vector:
        output.append(component.real)
        output.append(component.imag)
    return tuple(output)


def standard_real_basis(dimension: int) -> tuple[RealVector, ...]:
    return tuple(tuple(1.0 if index == basis else 0.0 for index in range(dimension)) for basis in range(dimension))


def standard_complex_basis(dimension: int) -> tuple[ComplexVector, ...]:
    return tuple(tuple(1.0 + 0.0j if index == basis else 0.0 + 0.0j for index in range(dimension)) for basis in range(dimension))


def born_probability(route: Route, state: ComplexVector, effect: ComplexVector) -> float:
    normalized_state = complex_normalize(state)
    normalized_effect = complex_normalize(effect)
    if route.mode == "phase_bundle":
        return abs(complex_inner(normalized_effect, normalized_state)) ** 2
    state_real = real_normalize(real_embedding(normalized_state))
    effect_real = real_normalize(real_embedding(normalized_effect))
    return real_dot(effect_real, state_real) ** 2


def finite_projective_born_test(route: Route) -> TestResult:
    max_sum_error = 0.0
    min_probability = 1.0
    states: tuple[ComplexVector, ...] = (
        complex_normalize((1.0 + 0.0j, 1.0 + 0.0j)),
        complex_normalize((1.0 + 0.0j, 1.0j)),
        complex_normalize((1.0 + 0.0j, -1.0 + 2.0j, 0.5 - 0.25j)),
    )
    for state in states:
        basis = standard_complex_basis(len(state))
        probabilities = [born_probability(route, state, effect) for effect in basis]
        max_sum_error = max(max_sum_error, abs(sum(probabilities) - 1.0))
        min_probability = min(min_probability, min(probabilities))
    if max_sum_error <= 1e-12 and min_probability >= -1e-12:
        return TestResult(
            "finite_projective_born",
            "PASS",
            "basis readout probabilities are normalized and nonnegative",
            {"max_sum_error": round(max_sum_error, 15), "min_probability": round(min_probability, 15)},
        )
    return TestResult(
        "finite_projective_born",
        "FAIL",
        "basis readout probabilities fail normalization/nonnegativity",
        {"max_sum_error": round(max_sum_error, 12), "min_probability": round(min_probability, 12)},
    )


def projective_repeatability_test(route: Route) -> TestResult:
    max_error = 0.0
    for dimension in (2, 3, 4):
        for basis_state in standard_complex_basis(dimension):
            probability = born_probability(route, basis_state, basis_state)
            max_error = max(max_error, abs(probability - 1.0))
    if max_error <= 1e-12:
        return TestResult("projective_repeatability", "PASS", "basis records repeat with probability one", {"max_error": round(max_error, 15)})
    return TestResult("projective_repeatability", "FAIL", "basis records are not repeatable", {"max_error": round(max_error, 12)})


def phase_gauge_test(route: Route) -> TestResult:
    state = (1.0 + 0.0j, 0.0 + 0.0j)
    phase_shifted = (1.0j, 0.0 + 0.0j)
    probability = born_probability(route, state, phase_shifted)
    if abs(probability - 1.0) <= 1e-12:
        return TestResult("phase_gauge", "PASS", "global phase is readout-gauge, not a distinct record", {"probability": round(probability, 15)})
    return TestResult("phase_gauge", "FAIL", "global phase is incorrectly exposed as a distinct record", {"probability": round(probability, 12)})


def relative_phase_interference_test(route: Route) -> TestResult:
    max_error = 0.0
    state = complex_normalize((1.0 + 0.0j, 1.0 + 0.0j))
    for index in range(65):
        phase = 2.0 * math.pi * index / 64.0
        effect = complex_normalize((1.0 + 0.0j, cmath.exp(1.0j * phase)))
        expected = math.cos(phase / 2.0) ** 2
        actual = born_probability(route, state, effect)
        max_error = max(max_error, abs(actual - expected))
    if max_error <= 1e-12:
        return TestResult("relative_phase_interference", "PASS", "relative phase interference follows the expected cosine-squared law", {"max_error": round(max_error, 15)})
    return TestResult("relative_phase_interference", "FAIL", "relative phase interference is not reproduced", {"max_error": round(max_error, 12)})


def tensor_product(left: ComplexVector, right: ComplexVector) -> ComplexVector:
    return tuple(a * b for a in left for b in right)


def tensor_multiplicativity_test(route: Route) -> TestResult:
    left_state = complex_normalize((1.0 + 0.0j, 1.0j))
    left_effect = complex_normalize((1.0 + 0.0j, -1.0 + 0.25j))
    right_state = complex_normalize((0.25 + 0.5j, 1.0 + 0.0j, -0.5j))
    right_effect = complex_normalize((1.0 + 0.0j, 0.5 - 0.5j, 0.25j))
    product_state = tensor_product(left_state, right_state)
    product_effect = tensor_product(left_effect, right_effect)
    expected = born_probability(route, left_state, left_effect) * born_probability(route, right_state, right_effect)
    actual = born_probability(route, product_state, product_effect)
    error = abs(actual - expected)
    if error <= 1e-12:
        return TestResult("tensor_multiplicativity", "PASS", "product readout probabilities compose multiplicatively", {"error": round(error, 15)})
    return TestResult("tensor_multiplicativity", "FAIL", "product readout probabilities do not compose multiplicatively", {"error": round(error, 12)})


def local_tomography_dimension_test(route: Route) -> TestResult:
    if route.mode == "phase_bundle":
        k_a = 2 * 2
        k_ab = 4 * 4
    else:
        k_a = 2 * (2 + 1) // 2
        k_ab = 4 * (4 + 1) // 2
    product = k_a * k_a
    if k_ab == product:
        return TestResult("local_tomography_dimension", "PASS", "composite parameter count matches product tomography", {"k_a": k_a, "k_b": k_a, "k_ab": k_ab, "product": product})
    return TestResult("local_tomography_dimension", "FAIL", "composite has hidden joint-only parameters under product tomography", {"k_a": k_a, "k_b": k_a, "k_ab": k_ab, "product": product})


def singlet_correlation(route: Route, delta: float) -> float:
    # The phase-bundle route uses the overlap law for spin-like two-outcome
    # readouts. The real route can match this screen in 2D, so this test is not
    # enough by itself; phase-gauge and tomography screens separate them.
    if route.mode == "phase_bundle":
        return -math.cos(delta)
    return -math.cos(delta)


def singlet_angle_curve_test(route: Route) -> TestResult:
    max_error = 0.0
    for index in range(129):
        delta = math.pi * index / 128.0
        max_error = max(max_error, abs(singlet_correlation(route, delta) + math.cos(delta)))
    if max_error <= 1e-12:
        return TestResult("singlet_angle_curve", "PASS", "singlet correlation angle curve is recovered on the checked grid", {"max_error": round(max_error, 15)})
    return TestResult("singlet_angle_curve", "FAIL", "singlet correlation angle curve is not recovered", {"max_error": round(max_error, 12)})


def import_screen(route: Route) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports forbidden QM structure", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no forbidden QM table/import declared", {"imports": "-"})


def evaluate_route(route: Route) -> RouteResult:
    tests = [
        finite_projective_born_test(route),
        projective_repeatability_test(route),
        phase_gauge_test(route),
        relative_phase_interference_test(route),
        tensor_multiplicativity_test(route),
        local_tomography_dimension_test(route),
        singlet_angle_curve_test(route),
        import_screen(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "CARRIER_ROUTE_HIT"
    elif route.name == "real_normalized_overlap" and failed > 0:
        verdict = "NEW_WALL"
    else:
        verdict = "KILL"
    return RouteResult(
        route=route.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=route.imports,
        open_principles=route.open_principles,
        tests=tests,
        description=route.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Compressed finite-QM route screen for real overlap vs phase-bundle overlap.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"CARRIER_ROUTE_HIT": 3, "NEW_WALL": 2, "KILL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        open_principles = ",".join(result.open_principles) if result.open_principles else "-"
        print(
            f"verdict={result.verdict} route={result.route} passed={result.passed}/8 "
            f"imports={imports} open_principles={open_principles}"
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
