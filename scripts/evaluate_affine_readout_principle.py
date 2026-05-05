from __future__ import annotations

import argparse
import json
import math
from collections.abc import Callable
from dataclasses import asdict, dataclass
from typing import Literal

MixFn = Callable[[float, float, float], float]
Verdict = Literal["AFFINE_READOUT_PRINCIPLE_HIT", "IMPORTED_HIT", "NEAR_MISS", "REJECTED"]
TestVerdict = Literal["PASS", "FAIL"]

PROBABILITIES: tuple[float, ...] = (0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0)
WEIGHTS: tuple[float, ...] = (0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0)
TOLERANCE = 1e-9


@dataclass(frozen=True)
class MixCandidate:
    name: str
    fn: MixFn
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


def affine_mix(weight: float, left: float, right: float) -> float:
    return weight * left + (1.0 - weight) * right


def imported_affine_mix(weight: float, left: float, right: float) -> float:
    return affine_mix(weight, left, right)


def quadratic_mix(weight: float, left: float, right: float) -> float:
    return math.sqrt(weight * left * left + (1.0 - weight) * right * right)


def odds_mix(weight: float, left: float, right: float) -> float:
    epsilon = 1e-9
    clipped_left = min(1.0 - epsilon, max(epsilon, left))
    clipped_right = min(1.0 - epsilon, max(epsilon, right))
    left_logit = math.log(clipped_left / (1.0 - clipped_left))
    right_logit = math.log(clipped_right / (1.0 - clipped_right))
    mixed_logit = weight * left_logit + (1.0 - weight) * right_logit
    return 1.0 / (1.0 + math.exp(-mixed_logit))


def max_mix(_weight: float, left: float, right: float) -> float:
    return max(left, right)


def min_mix(_weight: float, left: float, right: float) -> float:
    return min(left, right)


CANDIDATES: tuple[MixCandidate, ...] = (
    MixCandidate(
        name="operational_frequency_affine_mix",
        fn=affine_mix,
        imports=(),
        description="external randomization of facticizable records mixes observed frequencies linearly",
    ),
    MixCandidate(
        name="imported_convex_probability_control",
        fn=imported_affine_mix,
        imports=("convex_probability_axiom",),
        description="control that imports affine probability rather than deriving it from randomization",
    ),
    MixCandidate(
        name="quadratic_frequency_mix",
        fn=quadratic_mix,
        imports=(),
        description="nonlinear magnitude-style mixture over frequencies",
    ),
    MixCandidate(
        name="odds_logit_mix",
        fn=odds_mix,
        imports=(),
        description="mixture affine in log-odds rather than observed frequencies",
    ),
    MixCandidate(
        name="max_frequency_mix",
        fn=max_mix,
        imports=(),
        description="dominant branch controls mixed readout",
    ),
    MixCandidate(
        name="min_frequency_mix",
        fn=min_mix,
        imports=(),
        description="weakest branch controls mixed readout",
    ),
)


def bounded_test(candidate: MixCandidate) -> TestResult:
    min_value = 1.0
    max_value = 0.0
    for weight in WEIGHTS:
        for left in PROBABILITIES:
            for right in PROBABILITIES:
                value = candidate.fn(weight, left, right)
                min_value = min(min_value, value)
                max_value = max(max_value, value)
    if min_value >= -TOLERANCE and max_value <= 1.0 + TOLERANCE:
        return TestResult("bounded", "PASS", "mixed readout stays inside probability bounds", {"min": round(min_value, 12), "max": round(max_value, 12)})
    return TestResult("bounded", "FAIL", "mixed readout leaves probability bounds", {"min": round(min_value, 12), "max": round(max_value, 12)})


def endpoint_test(candidate: MixCandidate) -> TestResult:
    max_error = 0.0
    for left in PROBABILITIES:
        for right in PROBABILITIES:
            max_error = max(max_error, abs(candidate.fn(1.0, left, right) - left))
            max_error = max(max_error, abs(candidate.fn(0.0, left, right) - right))
    if max_error <= TOLERANCE:
        return TestResult("endpoint", "PASS", "certain randomizer choices recover the selected branch", {"max_error": round(max_error, 12)})
    return TestResult("endpoint", "FAIL", "certain randomizer choices do not recover the selected branch", {"max_error": round(max_error, 12)})


def branch_label_symmetry_test(candidate: MixCandidate) -> TestResult:
    max_error = 0.0
    for weight in WEIGHTS:
        for left in PROBABILITIES:
            for right in PROBABILITIES:
                direct = candidate.fn(weight, left, right)
                swapped = candidate.fn(1.0 - weight, right, left)
                max_error = max(max_error, abs(direct - swapped))
    if max_error <= TOLERANCE:
        return TestResult("branch_label_symmetry", "PASS", "renaming the randomizer branches does not change readout", {"max_error": round(max_error, 12)})
    return TestResult("branch_label_symmetry", "FAIL", "readout depends on branch naming", {"max_error": round(max_error, 12)})


def frequency_calibration_test(candidate: MixCandidate) -> TestResult:
    max_error = 0.0
    for weight in WEIGHTS:
        for left in PROBABILITIES:
            for right in PROBABILITIES:
                observed = weight * left + (1.0 - weight) * right
                max_error = max(max_error, abs(candidate.fn(weight, left, right) - observed))
    if max_error <= TOLERANCE:
        return TestResult(
            "frequency_calibration",
            "PASS",
            "mixed readout matches the observable frequency of externally randomized trials",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "frequency_calibration",
        "FAIL",
        "mixed readout disagrees with externally randomized observed frequencies",
        {"max_error": round(max_error, 12)},
    )


def refinement_associativity_test(candidate: MixCandidate) -> TestResult:
    max_error = 0.0
    for first_weight in (0.2, 0.5, 0.8):
        for second_weight in (0.25, 0.6):
            for first in (0.1, 0.7):
                for second in (0.25, 0.9):
                    for third in (0.4, 1.0):
                        nested = candidate.fn(
                            first_weight,
                            first,
                            candidate.fn(second_weight, second, third),
                        )
                        flattened_second_weight = (1.0 - first_weight) * second_weight
                        flattened_third_weight = (1.0 - first_weight) * (1.0 - second_weight)
                        remaining = flattened_second_weight + flattened_third_weight
                        if remaining <= TOLERANCE:
                            flattened_tail = second
                        else:
                            flattened_tail = candidate.fn(
                                flattened_second_weight / remaining,
                                second,
                                third,
                            )
                        flattened = candidate.fn(first_weight, first, flattened_tail)
                        max_error = max(max_error, abs(nested - flattened))
    if max_error <= TOLERANCE:
        return TestResult(
            "refinement_associativity",
            "PASS",
            "refining the external randomizer tree does not alter readout",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "refinement_associativity",
        "FAIL",
        "readout changes under randomizer-tree refinement",
        {"max_error": round(max_error, 12)},
    )


def import_screen(candidate: MixCandidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "candidate imports a convex probability axiom", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no convex probability axiom import declared", {"imports": "-"})


def evaluate_candidate(candidate: MixCandidate) -> CandidateResult:
    tests = [
        bounded_test(candidate),
        endpoint_test(candidate),
        branch_label_symmetry_test(candidate),
        frequency_calibration_test(candidate),
        refinement_associativity_test(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "AFFINE_READOUT_PRINCIPLE_HIT"
    elif candidate.imports and passed >= len(tests) - 1:
        verdict = "IMPORTED_HIT"
    elif passed >= 4:
        verdict = "NEAR_MISS"
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
    parser = argparse.ArgumentParser(description="Evaluate affine readout as an operational randomization principle below Born.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"AFFINE_READOUT_PRINCIPLE_HIT": 4, "IMPORTED_HIT": 3, "NEAR_MISS": 2, "REJECTED": 1}
    results = sorted(
        (evaluate_candidate(candidate) for candidate in CANDIDATES),
        key=lambda result: (order[result.verdict], result.passed),
        reverse=True,
    )
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(f"verdict={result.verdict} candidate={result.candidate} passed={result.passed}/6 imports={imports}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
