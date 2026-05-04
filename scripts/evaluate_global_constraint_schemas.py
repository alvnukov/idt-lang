from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

Outcome = Literal[-1, 1]
Setting = Literal[0, 1]
Verdict = Literal["VALID_HIT", "PARAMETRIC_HIT", "IMPORTED_HIT", "NEAR_MISS", "KILL"]
TestVerdict = Literal["PASS", "FAIL"]

SETTINGS: tuple[tuple[Setting, Setting], ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
OUTCOMES: tuple[tuple[Outcome, Outcome], ...] = ((-1, -1), (-1, 1), (1, -1), (1, 1))
ANGLES_A: dict[Setting, float] = {0: 0.0, 1: math.pi / 2.0}
ANGLES_B: dict[Setting, float] = {0: math.pi / 4.0, 1: -math.pi / 4.0}
TSIRELSON = 2.0 * math.sqrt(2.0)
CLOSED_ORIENTATION_BETA = math.sqrt(2.0) * math.atanh(1.0 / math.sqrt(2.0))


@dataclass(frozen=True)
class SelectorSchema:
    name: str
    mode: str
    beta: float
    metric_coupling: bool
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
class SchemaResult:
    schema: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    open_parameters: tuple[str, ...]
    tests: list[TestResult]
    correlations: dict[str, float]
    chsh: float
    description: str


SCHEMAS: tuple[SelectorSchema, ...] = (
    SelectorSchema(
        name="local_hidden_orientation_baseline",
        mode="local_hidden",
        beta=0.0,
        metric_coupling=False,
        imports=(),
        open_parameters=(),
        description="uniform hidden orientation with local readout only",
    ),
    SelectorSchema(
        name="direct_pr_parity_control",
        mode="direct_pr",
        beta=0.0,
        metric_coupling=False,
        imports=("bell_parity_table",),
        open_parameters=(),
        description="control that hard-codes the PR parity relation",
    ),
    SelectorSchema(
        name="global_orientation_consistency",
        mode="orientation_consistency",
        beta=1.23,
        metric_coupling=False,
        imports=(),
        open_parameters=("orientation_coupling_beta",),
        description="joint records selected by least orientation-consistency residue",
    ),
    SelectorSchema(
        name="metric_coupled_orientation_consistency",
        mode="orientation_consistency",
        beta=1.23,
        metric_coupling=True,
        imports=(),
        open_parameters=("orientation_coupling_beta", "metric_bottleneck_response"),
        description="orientation-consistency selector whose coupling weakens across bottlenecks",
    ),
    SelectorSchema(
        name="closed_metric_orientation_consistency",
        mode="orientation_consistency",
        beta=CLOSED_ORIENTATION_BETA,
        metric_coupling=True,
        imports=(),
        open_parameters=(),
        description=(
            "orientation selector with beta fixed by the Tsirelson critical boundary "
            "and bottleneck response fixed by additive-to-multiplicative composition"
        ),
    ),
)


def sign(value: float) -> Outcome:
    return 1 if value >= 0 else -1


def local_hidden_distribution(schema: SelectorSchema, a: Setting, b: Setting) -> dict[tuple[Outcome, Outcome], float]:
    samples = 720
    counts = {outcome: 0.0 for outcome in OUTCOMES}
    for index in range(samples):
        theta = (2.0 * math.pi * index) / samples
        left = sign(math.cos(theta - ANGLES_A[a]))
        right = sign(-math.cos(theta - ANGLES_B[b]))
        counts[(left, right)] += 1.0 / samples
    return counts


def direct_pr_distribution(_schema: SelectorSchema, a: Setting, b: Setting) -> dict[tuple[Outcome, Outcome], float]:
    target_product: Outcome = -1 if a == 1 and b == 1 else 1
    output: dict[tuple[Outcome, Outcome], float] = {}
    for left, right in OUTCOMES:
        output[(left, right)] = 0.5 if left * right == target_product else 0.0
    return output


def orientation_distribution(schema: SelectorSchema, a: Setting, b: Setting, bottleneck: float = 0.0) -> dict[tuple[Outcome, Outcome], float]:
    delta = ANGLES_A[a] - ANGLES_B[b]
    coupling = schema.beta * math.cos(delta)
    if schema.metric_coupling:
        coupling *= math.exp(-bottleneck)
    weights: dict[tuple[Outcome, Outcome], float] = {}
    total = 0.0
    for left, right in OUTCOMES:
        # Least-residue orientation consistency: anti-aligned records are favored
        # when the transported context orientations are aligned.
        weight = math.exp(-coupling * left * right)
        weights[(left, right)] = weight
        total += weight
    return {outcome: weight / total for outcome, weight in weights.items()}


def distribution(schema: SelectorSchema, a: Setting, b: Setting, bottleneck: float = 0.0) -> dict[tuple[Outcome, Outcome], float]:
    if schema.mode == "local_hidden":
        return local_hidden_distribution(schema, a, b)
    if schema.mode == "direct_pr":
        return direct_pr_distribution(schema, a, b)
    if schema.mode == "orientation_consistency":
        return orientation_distribution(schema, a, b, bottleneck)
    raise ValueError(f"unknown schema mode: {schema.mode}")


def expectation(dist: dict[tuple[Outcome, Outcome], float]) -> float:
    return sum(left * right * probability for (left, right), probability in dist.items())


def marginal_left(dist: dict[tuple[Outcome, Outcome], float]) -> float:
    return sum(left * probability for (left, _right), probability in dist.items())


def marginal_right(dist: dict[tuple[Outcome, Outcome], float]) -> float:
    return sum(right * probability for (_left, right), probability in dist.items())


def correlations(schema: SelectorSchema, bottleneck: float = 0.0) -> dict[str, float]:
    return {f"e{a}{b}": expectation(distribution(schema, a, b, bottleneck)) for a, b in SETTINGS}


def chsh_value(corr: dict[str, float]) -> float:
    return corr["e00"] + corr["e01"] + corr["e10"] - corr["e11"]


def no_signalling_test(schema: SelectorSchema) -> TestResult:
    worst_delta = 0.0
    for a in (0, 1):
        left_0 = marginal_left(distribution(schema, a, 0))
        left_1 = marginal_left(distribution(schema, a, 1))
        worst_delta = max(worst_delta, abs(left_0 - left_1))
    for b in (0, 1):
        right_0 = marginal_right(distribution(schema, 0, b))
        right_1 = marginal_right(distribution(schema, 1, b))
        worst_delta = max(worst_delta, abs(right_0 - right_1))
    if worst_delta <= 1e-9:
        return TestResult("no_signalling", "PASS", "local marginals are independent of remote settings", {"worst_delta": worst_delta})
    return TestResult("no_signalling", "FAIL", "remote settings alter local marginals", {"worst_delta": worst_delta})


def bell_strength_test(schema: SelectorSchema, corr: dict[str, float], chsh: float) -> TestResult:
    if abs(chsh) > 2.05:
        return TestResult("bell_strength", "PASS", "CHSH screen exceeds local deterministic bound", {"chsh": round(chsh, 9), **corr})
    return TestResult("bell_strength", "FAIL", "CHSH screen stays local/shared-cause compatible", {"chsh": round(chsh, 9), **corr})


def tsirelson_test(chsh: float) -> TestResult:
    excess = abs(chsh) - TSIRELSON
    if excess <= 0.02:
        return TestResult("tsirelson_discipline", "PASS", "CHSH value stays within the quantum-like bound tolerance", {"chsh": round(chsh, 9), "tsirelson": round(TSIRELSON, 9), "excess": round(excess, 9)})
    return TestResult("tsirelson_discipline", "FAIL", "CHSH value is superquantum on this screen", {"chsh": round(chsh, 9), "tsirelson": round(TSIRELSON, 9), "excess": round(excess, 9)})


def import_screen(schema: SelectorSchema) -> TestResult:
    if schema.imports:
        return TestResult("import_screen", "FAIL", "schema imports forbidden structure", {"imports": ",".join(schema.imports)})
    return TestResult("import_screen", "PASS", "no explicit Bell/PR parity import declared", {"imports": "-"})


def metric_bottleneck_test(schema: SelectorSchema) -> TestResult:
    open_corr = correlations(schema, bottleneck=0.0)
    blocked_corr = correlations(schema, bottleneck=1.0)
    open_strength = sum(abs(value) for value in open_corr.values())
    blocked_strength = sum(abs(value) for value in blocked_corr.values())
    response = open_strength - blocked_strength
    if response > 0.25:
        return TestResult("metric_bottleneck_response", "PASS", "correlation strength responds to a bottleneck parameter", {"open_strength": round(open_strength, 9), "blocked_strength": round(blocked_strength, 9), "response": round(response, 9)})
    return TestResult("metric_bottleneck_response", "FAIL", "no effective bottleneck/distance response was recovered", {"open_strength": round(open_strength, 9), "blocked_strength": round(blocked_strength, 9), "response": round(response, 9)})


def parameter_closure_test(schema: SelectorSchema) -> TestResult:
    if schema.open_parameters:
        return TestResult("parameter_closure", "FAIL", "schema still has unexplained fixed parameters", {"open_parameters": ",".join(schema.open_parameters)})
    return TestResult(
        "parameter_closure",
        "PASS",
        "schema has no unexplained numeric or response parameters",
        {
            "open_parameters": "-",
            "beta": round(schema.beta, 12),
            "closed_beta_formula": "sqrt(2)*atanh(1/sqrt(2))" if abs(schema.beta - CLOSED_ORIENTATION_BETA) <= 1e-12 else "-",
            "metric_response": "exp(-bottleneck)" if schema.metric_coupling else "-",
        },
    )


def evaluate_schema(schema: SelectorSchema) -> SchemaResult:
    corr = correlations(schema)
    chsh = chsh_value(corr)
    tests = [
        no_signalling_test(schema),
        bell_strength_test(schema, corr, chsh),
        tsirelson_test(chsh),
        import_screen(schema),
        metric_bottleneck_test(schema),
        parameter_closure_test(schema),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "VALID_HIT"
    elif passed >= 5 and schema.imports:
        verdict = "IMPORTED_HIT"
    elif passed >= 5 and schema.open_parameters:
        verdict = "PARAMETRIC_HIT"
    elif passed >= 4:
        verdict = "NEAR_MISS"
    else:
        verdict = "KILL"
    return SchemaResult(
        schema=schema.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=schema.imports,
        open_parameters=schema.open_parameters,
        tests=tests,
        correlations={key: round(value, 9) for key, value in corr.items()},
        chsh=round(chsh, 9),
        description=schema.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate global-consistency selector schemas in one pass.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    results = [evaluate_schema(schema) for schema in SCHEMAS]
    order = {"VALID_HIT": 4, "PARAMETRIC_HIT": 3, "IMPORTED_HIT": 2, "NEAR_MISS": 1, "KILL": 0}
    results.sort(key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        params = ",".join(result.open_parameters) if result.open_parameters else "-"
        print(
            f"verdict={result.verdict} schema={result.schema} passed={result.passed}/6 "
            f"chsh={result.chsh} imports={imports} open_parameters={params}"
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
