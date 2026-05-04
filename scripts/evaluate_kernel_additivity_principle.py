from __future__ import annotations

import argparse
import json
import math
from collections.abc import Callable, Sequence
from dataclasses import asdict, dataclass
from typing import Literal

CompositionFn = Callable[[float, float], float]
Verdict = Literal["PRINCIPLE_HIT", "IMPORTED_HIT", "AMBIGUOUS", "REJECTED"]
TestVerdict = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class CompositionCandidate:
    name: str
    fn: CompositionFn
    imports: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class TestResult:
    name: str
    verdict: TestVerdict
    reason: str
    details: dict[str, float | int | str | bool]


@dataclass(frozen=True)
class CandidateResult:
    candidate: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    tests: list[TestResult]
    description: str


def additive(left: float, right: float) -> float:
    return left + right


def imported_sum(left: float, right: float) -> float:
    return left + right


def max_compose(left: float, right: float) -> float:
    return max(left, right)


def product_compose(left: float, right: float) -> float:
    return left * right


def p_norm_compose(left: float, right: float) -> float:
    return math.sqrt(left * left + right * right)


def bounded_sum(left: float, right: float) -> float:
    clipped_left = max(-0.999999, min(left, 0.999999))
    clipped_right = max(-0.999999, min(right, 0.999999))
    return math.tanh(math.atanh(clipped_left) + math.atanh(clipped_right))


def saturating_sum(left: float, right: float) -> float:
    return 1.0 - math.exp(-(left + right))


CANDIDATES: tuple[CompositionCandidate, ...] = (
    CompositionCandidate("additive_kernel_composition", additive, (), "direct additive composition of compatible scalar kernels"),
    CompositionCandidate("imported_additive_sum", imported_sum, ("additive_measure_assumed",), "control that declares the target sum as an import"),
    CompositionCandidate("max_composition", max_compose, (), "only strongest compatible constraint matters"),
    CompositionCandidate("product_composition", product_compose, (), "compatible constraints multiply directly at kernel level"),
    CompositionCandidate("p_norm_composition", p_norm_compose, (), "Euclidean magnitude composition of compatible scalar kernels"),
    CompositionCandidate("bounded_tanh_composition", bounded_sum, (), "bounded relativistic-style composition law"),
    CompositionCandidate("saturating_sum_composition", saturating_sum, (), "monotone saturating response to total support"),
)


def samples() -> tuple[float, ...]:
    return (0.0, 0.05, 0.125, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0)


def positive_samples() -> tuple[float, ...]:
    return (0.05, 0.125, 0.25, 0.5, 1.0)


def close(left: float, right: float, tolerance: float = 1e-9) -> bool:
    return abs(left - right) <= tolerance


def algebraic_monoid_test(candidate: CompositionCandidate) -> TestResult:
    max_comm = 0.0
    max_assoc = 0.0
    max_identity = 0.0
    for a in samples():
        max_identity = max(max_identity, abs(candidate.fn(a, 0.0) - a), abs(candidate.fn(0.0, a) - a))
        for b in samples():
            max_comm = max(max_comm, abs(candidate.fn(a, b) - candidate.fn(b, a)))
            for c in samples():
                left = candidate.fn(candidate.fn(a, b), c)
                right = candidate.fn(a, candidate.fn(b, c))
                max_assoc = max(max_assoc, abs(left - right))
    if max_comm <= 1e-9 and max_assoc <= 1e-9 and max_identity <= 1e-9:
        return TestResult(
            "algebraic_monoid",
            "PASS",
            "compatible composition is commutative, associative, and has empty identity",
            {"comm_error": round(max_comm, 12), "assoc_error": round(max_assoc, 12), "identity_error": round(max_identity, 12)},
        )
    return TestResult(
        "algebraic_monoid",
        "FAIL",
        "composition fails commutativity, associativity, or empty identity",
        {"comm_error": round(max_comm, 12), "assoc_error": round(max_assoc, 12), "identity_error": round(max_identity, 12)},
    )


def refinement_invariance_test(candidate: CompositionCandidate) -> TestResult:
    # A compatible constraint split into n equal subconstraints must expose the
    # same scalar kernel as the unsplit constraint. Otherwise readout depends on
    # arbitrary decomposition of the same support.
    max_error = 0.0
    for total in (0.1, 0.25, 0.5, 1.0, 2.0):
        for parts in (2, 3, 4, 5, 8):
            value = 0.0
            piece = total / parts
            for _index in range(parts):
                value = candidate.fn(value, piece)
            max_error = max(max_error, abs(value - total))
    if max_error <= 1e-9:
        return TestResult(
            "refinement_invariance",
            "PASS",
            "readout is invariant under arbitrary splitting of compatible support",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "refinement_invariance",
        "FAIL",
        "readout changes under arbitrary splitting of compatible support",
        {"max_error": round(max_error, 12)},
    )


def cancellation_test(candidate: CompositionCandidate) -> TestResult:
    # Opposite compatible contributions must cancel exactly. This screens out
    # positive-only magnitude laws that cannot represent record/residue balance.
    max_error = 0.0
    for value in positive_samples():
        max_error = max(max_error, abs(candidate.fn(value, -value)))
        max_error = max(max_error, abs(candidate.fn(-value, value)))
    if max_error <= 1e-9:
        return TestResult(
            "cancellation",
            "PASS",
            "opposite compatible contributions cancel to empty kernel",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "cancellation",
        "FAIL",
        "opposite compatible contributions do not cancel to empty kernel",
        {"max_error": round(max_error, 12)},
    )


def monotone_locality_test(candidate: CompositionCandidate) -> TestResult:
    # Adding a positive compatible contribution should not reduce the exposed
    # kernel. This is weaker than additivity and does not decide the result.
    violations = 0
    for a in (0.0, 0.1, 0.3, 0.8, 1.2):
        previous = candidate.fn(a, 0.0)
        for b in (0.05, 0.1, 0.25, 0.5):
            current = candidate.fn(a, b)
            if current + 1e-12 < previous:
                violations += 1
            previous = current
    if violations == 0:
        return TestResult("monotone_locality", "PASS", "positive compatible support does not reduce exposed kernel", {"violations": violations})
    return TestResult("monotone_locality", "FAIL", "positive compatible support can reduce exposed kernel", {"violations": violations})


def infinitesimal_linearity_test(candidate: CompositionCandidate) -> TestResult:
    # Many nonlinear laws can mimic addition for tiny values; the point is to
    # catch laws that cannot even recover the linear tangent at empty support.
    max_error = 0.0
    for epsilon in (1e-6, 1e-5, 1e-4):
        composed = candidate.fn(epsilon, epsilon)
        max_error = max(max_error, abs((composed / epsilon) - 2.0))
    if max_error <= 1e-3:
        return TestResult("infinitesimal_linearity", "PASS", "composition has the correct linear tangent at empty support", {"max_error": round(max_error, 12)})
    return TestResult("infinitesimal_linearity", "FAIL", "composition lacks the correct linear tangent at empty support", {"max_error": round(max_error, 12)})


def finite_cauchy_closure_test(candidate: CompositionCandidate) -> TestResult:
    # If identity, refinement invariance, and associativity hold on the finite
    # grid, repeated compatible composition must match ordinary finite sums.
    max_error = 0.0
    values: Sequence[tuple[float, ...]] = (
        (0.1, 0.2, 0.3),
        (0.05, 0.05, 0.15, 0.25),
        (1.0, -0.25, 0.5, -0.125),
        (0.75, 0.75, -0.5),
    )
    for parts in values:
        value = 0.0
        for part in parts:
            value = candidate.fn(value, part)
        max_error = max(max_error, abs(value - sum(parts)))
    if max_error <= 1e-9:
        return TestResult(
            "finite_cauchy_closure",
            "PASS",
            "finite compatible composition matches ordinary additive closure",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "finite_cauchy_closure",
        "FAIL",
        "finite compatible composition does not match additive closure",
        {"max_error": round(max_error, 12)},
    )


def import_screen(candidate: CompositionCandidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "composition law imports the target additive measure", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no target additive-measure import declared", {"imports": "-"})


def evaluate_candidate(candidate: CompositionCandidate) -> CandidateResult:
    tests = [
        algebraic_monoid_test(candidate),
        refinement_invariance_test(candidate),
        cancellation_test(candidate),
        monotone_locality_test(candidate),
        infinitesimal_linearity_test(candidate),
        finite_cauchy_closure_test(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "PRINCIPLE_HIT"
    elif candidate.imports and passed >= len(tests) - 1:
        verdict = "IMPORTED_HIT"
    elif passed >= 5:
        verdict = "AMBIGUOUS"
    else:
        verdict = "REJECTED"
    return CandidateResult(
        candidate=candidate.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=candidate.imports,
        tests=tests,
        description=candidate.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate compatible-kernel additivity as an IDT composition principle.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"PRINCIPLE_HIT": 4, "IMPORTED_HIT": 3, "AMBIGUOUS": 2, "REJECTED": 1}
    results = sorted((evaluate_candidate(candidate) for candidate in CANDIDATES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(f"verdict={result.verdict} candidate={result.candidate} passed={result.passed}/7 imports={imports}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
