from __future__ import annotations

import argparse
import json
import math
from collections.abc import Callable
from dataclasses import asdict, dataclass
from typing import Literal

Overlap = float
ProbabilityFn = Callable[[Overlap], float]
Verdict = Literal["AFFINE_BORN_SELECTOR_HIT", "IMPORTED_HIT", "NEAR_MISS", "REJECTED"]
TestVerdict = Literal["PASS", "FAIL"]

SAMPLES: tuple[float, ...] = (-1.0, -0.75, -0.5, -0.125, 0.0, 0.25, 0.5, 0.875, 1.0)
MIXTURE_WEIGHTS: tuple[float, ...] = (0.1, 0.25, 0.5, 0.75, 0.9)
TOLERANCE = 1e-9


@dataclass(frozen=True)
class SelectorCandidate:
    name: str
    fn: ProbabilityFn
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


def affine_born_selector(overlap: float) -> float:
    return (1.0 + overlap) / 2.0


def cubic_expectation_selector(overlap: float) -> float:
    return (1.0 + overlap**3) / 2.0


def quintic_expectation_selector(overlap: float) -> float:
    return (1.0 + overlap**5) / 2.0


def tanh_expectation_selector(overlap: float) -> float:
    beta = 1.7
    return (1.0 + math.tanh(beta * overlap) / math.tanh(beta)) / 2.0


def threshold_selector(overlap: float) -> float:
    if overlap > 0.0:
        return 1.0
    if overlap < 0.0:
        return 0.0
    return 0.5


def absolute_overlap_selector(overlap: float) -> float:
    return abs(overlap)


def imported_amplitude_square_selector(overlap: float) -> float:
    return (1.0 + overlap) / 2.0


CANDIDATES: tuple[SelectorCandidate, ...] = (
    SelectorCandidate(
        name="affine_born_from_signed_overlap",
        fn=affine_born_selector,
        imports=(),
        description="binary probability as the affine readout of signed normalized overlap",
    ),
    SelectorCandidate(
        name="cubic_expectation_deformation",
        fn=cubic_expectation_selector,
        imports=(),
        description="odd nonlinear deformation preserving endpoints and complement symmetry",
    ),
    SelectorCandidate(
        name="quintic_expectation_deformation",
        fn=quintic_expectation_selector,
        imports=(),
        description="higher odd nonlinear deformation preserving endpoints",
    ),
    SelectorCandidate(
        name="tanh_expectation_deformation",
        fn=tanh_expectation_selector,
        imports=(),
        description="smooth saturated odd deformation",
    ),
    SelectorCandidate(
        name="threshold_selector",
        fn=threshold_selector,
        imports=(),
        description="deterministic threshold readout over the signed overlap",
    ),
    SelectorCandidate(
        name="absolute_overlap_selector",
        fn=absolute_overlap_selector,
        imports=(),
        description="unsigned overlap readout that loses orientation sign",
    ),
    SelectorCandidate(
        name="imported_amplitude_square_control",
        fn=imported_amplitude_square_selector,
        imports=("born_amplitude_square",),
        description="control with the target formula declared as imported",
    ),
)


def close(left: float, right: float, tolerance: float = TOLERANCE) -> bool:
    return abs(left - right) <= tolerance


def bounded_probability_test(candidate: SelectorCandidate) -> TestResult:
    min_value = 1.0
    max_value = 0.0
    for overlap in SAMPLES:
        value = candidate.fn(overlap)
        min_value = min(min_value, value)
        max_value = max(max_value, value)
    if min_value >= -TOLERANCE and max_value <= 1.0 + TOLERANCE:
        return TestResult(
            "bounded_probability",
            "PASS",
            "selector maps signed overlap into the probability interval",
            {"min": round(min_value, 12), "max": round(max_value, 12)},
        )
    return TestResult(
        "bounded_probability",
        "FAIL",
        "selector leaves the probability interval",
        {"min": round(min_value, 12), "max": round(max_value, 12)},
    )


def repeatability_exclusion_test(candidate: SelectorCandidate) -> TestResult:
    repeat_error = abs(candidate.fn(1.0) - 1.0)
    exclusion_error = abs(candidate.fn(-1.0))
    if repeat_error <= TOLERANCE and exclusion_error <= TOLERANCE:
        return TestResult(
            "repeatability_exclusion",
            "PASS",
            "perfect overlap is certain and opposite overlap is excluded",
            {"repeat_error": round(repeat_error, 12), "exclusion_error": round(exclusion_error, 12)},
        )
    return TestResult(
        "repeatability_exclusion",
        "FAIL",
        "selector fails repeatability or exclusion at signed-overlap endpoints",
        {"repeat_error": round(repeat_error, 12), "exclusion_error": round(exclusion_error, 12)},
    )


def complement_symmetry_test(candidate: SelectorCandidate) -> TestResult:
    max_error = 0.0
    for overlap in SAMPLES:
        max_error = max(max_error, abs(candidate.fn(overlap) + candidate.fn(-overlap) - 1.0))
    if max_error <= TOLERANCE:
        return TestResult("complement_symmetry", "PASS", "opposite binary outcomes are normalized complements", {"max_error": round(max_error, 12)})
    return TestResult("complement_symmetry", "FAIL", "opposite binary outcomes are not normalized complements", {"max_error": round(max_error, 12)})


def unbiased_zero_test(candidate: SelectorCandidate) -> TestResult:
    error = abs(candidate.fn(0.0) - 0.5)
    if error <= TOLERANCE:
        return TestResult("unbiased_zero", "PASS", "zero signed overlap gives unbiased binary readout", {"error": round(error, 12)})
    return TestResult("unbiased_zero", "FAIL", "zero signed overlap is biased", {"error": round(error, 12)})


def affine_mixture_test(candidate: SelectorCandidate) -> TestResult:
    max_error = 0.0
    for left in SAMPLES:
        for right in SAMPLES:
            for weight in MIXTURE_WEIGHTS:
                mixed_overlap = weight * left + (1.0 - weight) * right
                mixed_probability = candidate.fn(mixed_overlap)
                expected = weight * candidate.fn(left) + (1.0 - weight) * candidate.fn(right)
                max_error = max(max_error, abs(mixed_probability - expected))
    if max_error <= TOLERANCE:
        return TestResult(
            "affine_mixture",
            "PASS",
            "probability is affine in the stable signed expectation/overlap",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "affine_mixture",
        "FAIL",
        "probability depends nonlinearly on mixtures of the same signed expectation",
        {"max_error": round(max_error, 12)},
    )


def phase_bundle_square_test(candidate: SelectorCandidate) -> TestResult:
    max_error = 0.0
    for index in range(41):
        amplitude = float(index) / 40.0
        signed_overlap = 2.0 * amplitude * amplitude - 1.0
        max_error = max(max_error, abs(candidate.fn(signed_overlap) - amplitude * amplitude))
    if max_error <= TOLERANCE:
        return TestResult(
            "phase_bundle_square",
            "PASS",
            "with r=2|a|^2-1, affine signed-overlap readout gives |a|^2",
            {"max_error": round(max_error, 12)},
        )
    return TestResult(
        "phase_bundle_square",
        "FAIL",
        "selector does not reduce to amplitude-square readout under the phase-bundle double cover",
        {"max_error": round(max_error, 12)},
    )


def import_screen(candidate: SelectorCandidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "candidate imports the target amplitude-square formula", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no target Born/amplitude-square import declared", {"imports": "-"})


def evaluate_candidate(candidate: SelectorCandidate) -> CandidateResult:
    tests = [
        bounded_probability_test(candidate),
        repeatability_exclusion_test(candidate),
        complement_symmetry_test(candidate),
        unbiased_zero_test(candidate),
        affine_mixture_test(candidate),
        phase_bundle_square_test(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests):
        verdict: Verdict = "AFFINE_BORN_SELECTOR_HIT"
    elif candidate.imports and passed >= len(tests) - 1:
        verdict = "IMPORTED_HIT"
    elif passed >= 5:
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
    parser = argparse.ArgumentParser(description="Evaluate Born readout as affine probability over normalized signed overlap.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"AFFINE_BORN_SELECTOR_HIT": 4, "IMPORTED_HIT": 3, "NEAR_MISS": 2, "REJECTED": 1}
    results = sorted(
        (evaluate_candidate(candidate) for candidate in CANDIDATES),
        key=lambda result: (order[result.verdict], result.passed),
        reverse=True,
    )
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
