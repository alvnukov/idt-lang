from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["FINAL_ROUTE_HIT", "IMPORTED_HIT", "NEW_WALL", "KILL"]
TestVerdict = Literal["PASS", "FAIL"]

TSIRELSON = 2.0 * math.sqrt(2.0)
CLOSED_ORIENTATION_BETA = math.sqrt(2.0) * math.atanh(1.0 / math.sqrt(2.0))
CHSH_DELTAS = (math.pi / 4.0, math.pi / 4.0, math.pi / 4.0, 3.0 * math.pi / 4.0)


@dataclass(frozen=True)
class FinalRouteSchema:
    name: str
    correlation_mode: str
    beta: float
    metric_mode: str
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
class FinalRouteResult:
    schema: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    open_parameters: tuple[str, ...]
    tests: list[TestResult]
    description: str


SCHEMAS: tuple[FinalRouteSchema, ...] = (
    FinalRouteSchema(
        name="closed_metric_orientation_consistency",
        correlation_mode="critical_tanh",
        beta=CLOSED_ORIENTATION_BETA,
        metric_mode="exp_bottleneck",
        imports=(),
        open_parameters=(),
        description="closed toy selector from the previous pass",
    ),
    FinalRouteSchema(
        name="cosine_projection_control",
        correlation_mode="cosine",
        beta=0.0,
        metric_mode="exp_bottleneck",
        imports=("born_cosine_projection",),
        open_parameters=(),
        description="control that inserts the full singlet/Born cosine curve",
    ),
    FinalRouteSchema(
        name="local_linear_baseline",
        correlation_mode="local_linear",
        beta=0.0,
        metric_mode="none",
        imports=(),
        open_parameters=(),
        description="closed local hidden-style triangular correlation baseline",
    ),
)


def target_born(delta: float) -> float:
    return -math.cos(delta)


def local_linear(delta: float) -> float:
    folded = abs((delta + math.pi) % (2.0 * math.pi) - math.pi)
    return -1.0 + (2.0 * folded / math.pi)


def correlation(schema: FinalRouteSchema, delta: float, bottleneck: float = 0.0) -> float:
    if schema.correlation_mode == "critical_tanh":
        coupling = schema.beta * math.cos(delta)
        if schema.metric_mode == "exp_bottleneck":
            coupling *= math.exp(-bottleneck)
        return -math.tanh(coupling)
    if schema.correlation_mode == "cosine":
        value = target_born(delta)
        if schema.metric_mode == "exp_bottleneck":
            value *= math.exp(-bottleneck)
        return value
    if schema.correlation_mode == "local_linear":
        return local_linear(delta)
    raise ValueError(f"unknown correlation mode: {schema.correlation_mode}")


def chsh_value(schema: FinalRouteSchema) -> float:
    e00, e01, e10, e11 = (correlation(schema, delta) for delta in CHSH_DELTAS)
    return e00 + e01 + e10 - e11


def no_signalling_test(schema: FinalRouteSchema) -> TestResult:
    # All candidate distributions are defined as P(a,b)=1/4*(1+a*b*E).
    # This has zero local marginals whenever |E| <= 1.
    max_abs = max(abs(correlation(schema, math.pi * index / 64.0)) for index in range(65))
    if max_abs <= 1.0 + 1e-12:
        return TestResult("no_signalling", "PASS", "zero-marginal correlation form is valid on the angle grid", {"max_abs_correlation": round(max_abs, 12)})
    return TestResult("no_signalling", "FAIL", "correlation leaves the valid zero-marginal probability range", {"max_abs_correlation": round(max_abs, 12)})


def chsh_boundary_test(schema: FinalRouteSchema) -> TestResult:
    value = chsh_value(schema)
    if abs(abs(value) - TSIRELSON) <= 0.02:
        return TestResult("chsh_boundary", "PASS", "CHSH reaches the Tsirelson boundary on the canonical screen", {"chsh": round(value, 12), "tsirelson": round(TSIRELSON, 12)})
    return TestResult("chsh_boundary", "FAIL", "CHSH does not reach the Tsirelson boundary on the canonical screen", {"chsh": round(value, 12), "tsirelson": round(TSIRELSON, 12)})


def born_curve_test(schema: FinalRouteSchema) -> TestResult:
    errors: list[float] = []
    max_at = 0.0
    max_error = -1.0
    for index in range(129):
        delta = math.pi * index / 128.0
        error = abs(correlation(schema, delta) - target_born(delta))
        errors.append(error)
        if error > max_error:
            max_error = error
            max_at = delta
    rms = math.sqrt(sum(error * error for error in errors) / len(errors))
    if max_error <= 0.02 and rms <= 0.01:
        return TestResult(
            "born_angle_curve",
            "PASS",
            "correlation matches the singlet/Born cosine curve on the full angle grid",
            {"max_error": round(max_error, 12), "rms_error": round(rms, 12), "max_error_delta": round(max_at, 12)},
        )
    return TestResult(
        "born_angle_curve",
        "FAIL",
        "correlation only matches selected CHSH points, not the full singlet/Born angle curve",
        {"max_error": round(max_error, 12), "rms_error": round(rms, 12), "max_error_delta": round(max_at, 12)},
    )


def import_screen(schema: FinalRouteSchema) -> TestResult:
    if schema.imports:
        return TestResult("import_screen", "FAIL", "schema imports forbidden final-route structure", {"imports": ",".join(schema.imports)})
    return TestResult("import_screen", "PASS", "no explicit Born/Hilbert/Bell table import declared", {"imports": "-"})


def metric_composition_test(schema: FinalRouteSchema) -> TestResult:
    delta = math.pi / 4.0
    open_strength = abs(correlation(schema, delta, bottleneck=0.0))
    one_then_two = abs(correlation(schema, delta, bottleneck=1.0 + 2.0))
    composed = open_strength * math.exp(-1.0) * math.exp(-2.0)
    if schema.metric_mode == "exp_bottleneck" and abs(one_then_two - composed) <= 1e-12:
        return TestResult("metric_composition", "PASS", "bottleneck response composes additively/multiplicatively", {"direct": round(one_then_two, 12), "composed": round(composed, 12)})
    return TestResult("metric_composition", "FAIL", "no closed additive/multiplicative bottleneck law", {"direct": round(one_then_two, 12), "composed": round(composed, 12)})


def parameter_closure_test(schema: FinalRouteSchema) -> TestResult:
    if schema.open_parameters:
        return TestResult("parameter_closure", "FAIL", "schema still has open parameters", {"open_parameters": ",".join(schema.open_parameters)})
    return TestResult("parameter_closure", "PASS", "schema has no open parameters on this screen", {"open_parameters": "-"})


def evaluate_schema(schema: FinalRouteSchema) -> FinalRouteResult:
    tests = [
        no_signalling_test(schema),
        chsh_boundary_test(schema),
        born_curve_test(schema),
        import_screen(schema),
        metric_composition_test(schema),
        parameter_closure_test(schema),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "FINAL_ROUTE_HIT"
    elif born_curve_test(schema).verdict == "PASS" and schema.imports:
        verdict = "IMPORTED_HIT"
    elif schema.name == "closed_metric_orientation_consistency" and failed > 0:
        verdict = "NEW_WALL"
    else:
        verdict = "KILL"
    return FinalRouteResult(
        schema=schema.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=schema.imports,
        open_parameters=schema.open_parameters,
        tests=tests,
        description=schema.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate whether the closed selector reaches the full QM angle-curve route.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"FINAL_ROUTE_HIT": 4, "IMPORTED_HIT": 3, "NEW_WALL": 2, "KILL": 1}
    results = sorted((evaluate_schema(schema) for schema in SCHEMAS), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        params = ",".join(result.open_parameters) if result.open_parameters else "-"
        print(f"verdict={result.verdict} schema={result.schema} passed={result.passed}/6 imports={imports} open_parameters={params}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
