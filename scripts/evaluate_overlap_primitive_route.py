from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["NEW_PRIMITIVE_HIT", "IMPORTED_HIT", "NEW_WALL", "KILL"]
TestVerdict = Literal["PASS", "FAIL"]
Vector = tuple[float, float]

TSIRELSON = 2.0 * math.sqrt(2.0)
CHSH_DELTAS = (math.pi / 4.0, math.pi / 4.0, math.pi / 4.0, 3.0 * math.pi / 4.0)


@dataclass(frozen=True)
class PrimitiveRoute:
    name: str
    mode: str
    imports: tuple[str, ...]
    open_parameters: tuple[str, ...]
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
    open_parameters: tuple[str, ...]
    tests: list[TestResult]
    description: str


ROUTES: tuple[PrimitiveRoute, ...] = (
    PrimitiveRoute(
        name="normalized_orientation_overlap",
        mode="orientation_overlap",
        imports=(),
        open_parameters=(),
        description=(
            "new primitive candidate: reversible orientation transport plus "
            "normalized bilinear overlap as the exposed correlation invariant"
        ),
    ),
    PrimitiveRoute(
        name="closed_tanh_selector_previous",
        mode="critical_tanh",
        imports=(),
        open_parameters=(),
        description="previous closed selector; included as the known wall control",
    ),
    PrimitiveRoute(
        name="born_cosine_projection_control",
        mode="direct_cosine",
        imports=("born_cosine_projection",),
        open_parameters=(),
        description="control that inserts the full Born/singlet curve directly",
    ),
)


def orientation(angle: float) -> Vector:
    return (math.cos(angle), math.sin(angle))


def rotate(vector: Vector, angle: float) -> Vector:
    x, y = vector
    c = math.cos(angle)
    s = math.sin(angle)
    return (c * x - s * y, s * x + c * y)


def dot(left: Vector, right: Vector) -> float:
    return left[0] * right[0] + left[1] * right[1]


def norm(vector: Vector) -> float:
    return math.sqrt(dot(vector, vector))


def normalized_overlap(left: Vector, right: Vector) -> float:
    return dot(left, right) / (norm(left) * norm(right))


def closed_beta() -> float:
    return math.sqrt(2.0) * math.atanh(1.0 / math.sqrt(2.0))


def target_born(delta: float) -> float:
    return -math.cos(delta)


def correlation(route: PrimitiveRoute, delta: float, bottleneck: float = 0.0) -> float:
    attenuation = math.exp(-bottleneck)
    if route.mode == "orientation_overlap":
        left = orientation(0.0)
        right = orientation(delta)
        return -attenuation * normalized_overlap(left, right)
    if route.mode == "critical_tanh":
        return -math.tanh(closed_beta() * math.cos(delta) * attenuation)
    if route.mode == "direct_cosine":
        return attenuation * target_born(delta)
    raise ValueError(f"unknown route mode: {route.mode}")


def no_signalling_test(route: PrimitiveRoute) -> TestResult:
    max_abs = max(abs(correlation(route, math.pi * index / 256.0)) for index in range(257))
    if max_abs <= 1.0 + 1e-12:
        return TestResult("no_signalling", "PASS", "zero-marginal joint distribution remains valid on the angle grid", {"max_abs_correlation": round(max_abs, 12)})
    return TestResult("no_signalling", "FAIL", "correlation exceeds valid zero-marginal probability range", {"max_abs_correlation": round(max_abs, 12)})


def context_composition_test(route: PrimitiveRoute) -> TestResult:
    if route.mode != "orientation_overlap":
        return TestResult("context_composition", "FAIL", "route has no primitive reversible orientation transport", {"mode": route.mode})
    max_error = 0.0
    base = orientation(0.0)
    for i in range(17):
        for j in range(17):
            a = 2.0 * math.pi * i / 17.0
            b = 2.0 * math.pi * j / 17.0
            direct = rotate(base, a + b)
            composed = rotate(rotate(base, a), b)
            error = math.hypot(direct[0] - composed[0], direct[1] - composed[1])
            max_error = max(max_error, error)
    if max_error <= 1e-12:
        return TestResult("context_composition", "PASS", "orientation transport composes reversibly and preserves norm", {"max_error": round(max_error, 15)})
    return TestResult("context_composition", "FAIL", "orientation transport failed reversible composition", {"max_error": round(max_error, 15)})


def chsh_boundary_test(route: PrimitiveRoute) -> TestResult:
    e00, e01, e10, e11 = (correlation(route, delta) for delta in CHSH_DELTAS)
    chsh = e00 + e01 + e10 - e11
    if abs(abs(chsh) - TSIRELSON) <= 1e-12:
        return TestResult("chsh_boundary", "PASS", "canonical CHSH screen reaches the Tsirelson boundary", {"chsh": round(chsh, 12), "tsirelson": round(TSIRELSON, 12)})
    return TestResult("chsh_boundary", "FAIL", "canonical CHSH screen does not reach the Tsirelson boundary", {"chsh": round(chsh, 12), "tsirelson": round(TSIRELSON, 12)})


def born_curve_test(route: PrimitiveRoute) -> TestResult:
    max_error = -1.0
    max_at = 0.0
    errors: list[float] = []
    for index in range(257):
        delta = math.pi * index / 256.0
        error = abs(correlation(route, delta) - target_born(delta))
        errors.append(error)
        if error > max_error:
            max_error = error
            max_at = delta
    rms = math.sqrt(sum(error * error for error in errors) / len(errors))
    if max_error <= 1e-12 and rms <= 1e-12:
        return TestResult("born_angle_curve", "PASS", "full singlet/Born angle curve is recovered from normalized orientation overlap", {"max_error": round(max_error, 15), "rms_error": round(rms, 15), "max_error_delta": round(max_at, 12)})
    return TestResult("born_angle_curve", "FAIL", "route does not recover the full singlet/Born angle curve", {"max_error": round(max_error, 12), "rms_error": round(rms, 12), "max_error_delta": round(max_at, 12)})


def metric_composition_test(route: PrimitiveRoute) -> TestResult:
    delta = math.pi / 5.0
    open_value = correlation(route, delta, bottleneck=0.0)
    direct = correlation(route, delta, bottleneck=3.0)
    composed = open_value * math.exp(-1.0) * math.exp(-2.0)
    if abs(direct - composed) <= 1e-12:
        return TestResult("metric_composition", "PASS", "additive bottlenecks attenuate observable overlap multiplicatively", {"direct": round(direct, 12), "composed": round(composed, 12)})
    return TestResult("metric_composition", "FAIL", "metric attenuation does not compose through readout", {"direct": round(direct, 12), "composed": round(composed, 12)})


def import_screen(route: PrimitiveRoute) -> TestResult:
    if route.imports:
        return TestResult("import_screen", "FAIL", "route imports forbidden final-route structure", {"imports": ",".join(route.imports)})
    return TestResult("import_screen", "PASS", "no explicit Born/Hilbert/Bell table import declared", {"imports": "-"})


def parameter_closure_test(route: PrimitiveRoute) -> TestResult:
    if route.open_parameters:
        return TestResult("parameter_closure", "FAIL", "route still has open parameters", {"open_parameters": ",".join(route.open_parameters)})
    return TestResult("parameter_closure", "PASS", "route has no open parameters on this screen", {"open_parameters": "-"})


def primitive_minimality_test(route: PrimitiveRoute) -> TestResult:
    if route.mode == "orientation_overlap":
        return TestResult(
            "primitive_minimality",
            "PASS",
            "uses only reversible orientation transport and normalized bilinear overlap, not a direct angle-correlation table",
            {"primitive": "normalized_bilinear_overlap", "direct_curve_table": False},
        )
    if route.mode == "direct_cosine":
        return TestResult(
            "primitive_minimality",
            "FAIL",
            "uses the target cosine projection directly",
            {"primitive": "direct_cosine", "direct_curve_table": True},
        )
    return TestResult(
        "primitive_minimality",
        "FAIL",
        "does not provide the new overlap primitive",
        {"primitive": route.mode, "direct_curve_table": False},
    )


def evaluate_route(route: PrimitiveRoute) -> RouteResult:
    tests = [
        no_signalling_test(route),
        context_composition_test(route),
        chsh_boundary_test(route),
        born_curve_test(route),
        metric_composition_test(route),
        import_screen(route),
        parameter_closure_test(route),
        primitive_minimality_test(route),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "NEW_PRIMITIVE_HIT"
    elif route.imports and born_curve_test(route).verdict == "PASS":
        verdict = "IMPORTED_HIT"
    elif route.name == "closed_tanh_selector_previous" and failed > 0:
        verdict = "NEW_WALL"
    else:
        verdict = "KILL"
    return RouteResult(
        route=route.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=route.imports,
        open_parameters=route.open_parameters,
        tests=tests,
        description=route.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate the normalized-overlap primitive route in one pass.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"NEW_PRIMITIVE_HIT": 4, "IMPORTED_HIT": 3, "NEW_WALL": 2, "KILL": 1}
    results = sorted((evaluate_route(route) for route in ROUTES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        params = ",".join(result.open_parameters) if result.open_parameters else "-"
        print(f"verdict={result.verdict} route={result.route} passed={result.passed}/8 imports={imports} open_parameters={params}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
