from __future__ import annotations

import argparse
import json
import math
from collections.abc import Callable
from dataclasses import asdict, dataclass
from typing import Literal

Vector = tuple[float, float]
TestVerdict = Literal["PASS", "FAIL"]
Verdict = Literal["UNIQUE_HIT", "IMPORTED_HIT", "WEAK_AMBIGUITY", "REJECTED"]
ReadoutFn = Callable[[Vector, Vector], float]


@dataclass(frozen=True)
class Candidate:
    name: str
    fn: ReadoutFn
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


def dot(left: Vector, right: Vector) -> float:
    return left[0] * right[0] + left[1] * right[1]


def norm(vector: Vector) -> float:
    return math.sqrt(dot(vector, vector))


def add(left: Vector, right: Vector) -> Vector:
    return (left[0] + right[0], left[1] + right[1])


def scale(value: float, vector: Vector) -> Vector:
    return (value * vector[0], value * vector[1])


def rotate(vector: Vector, angle: float) -> Vector:
    c = math.cos(angle)
    s = math.sin(angle)
    return (c * vector[0] - s * vector[1], s * vector[0] + c * vector[1])


def normalized_cos(left: Vector, right: Vector) -> float:
    return dot(left, right) / (norm(left) * norm(right))


def normalized_overlap(left: Vector, right: Vector) -> float:
    return normalized_cos(left, right)


def cubic_overlap(left: Vector, right: Vector) -> float:
    return normalized_cos(left, right) ** 3


def tanh_overlap(left: Vector, right: Vector) -> float:
    beta = 1.7
    return math.tanh(beta * normalized_cos(left, right)) / math.tanh(beta)


def local_linear_overlap(left: Vector, right: Vector) -> float:
    cos_value = max(-1.0, min(1.0, normalized_cos(left, right)))
    angle = math.acos(cos_value)
    return 1.0 - 2.0 * angle / math.pi


def absolute_overlap(left: Vector, right: Vector) -> float:
    return abs(normalized_cos(left, right))


def direct_cosine_projection(left: Vector, right: Vector) -> float:
    left_angle = math.atan2(left[1], left[0])
    right_angle = math.atan2(right[1], right[0])
    return math.cos(left_angle - right_angle)


CANDIDATES: tuple[Candidate, ...] = (
    Candidate(
        name="normalized_bilinear_overlap",
        fn=normalized_overlap,
        imports=(),
        description="normalized bilinear overlap induced by the Euclidean scalar kernel",
    ),
    Candidate(
        name="cubic_overlap",
        fn=cubic_overlap,
        imports=(),
        description="nonlinear odd function of normalized overlap",
    ),
    Candidate(
        name="tanh_overlap",
        fn=tanh_overlap,
        imports=(),
        description="nonlinear saturated selector over normalized overlap",
    ),
    Candidate(
        name="local_linear_overlap",
        fn=local_linear_overlap,
        imports=(),
        description="triangular local hidden-style angle readout",
    ),
    Candidate(
        name="absolute_overlap",
        fn=absolute_overlap,
        imports=(),
        description="orientation-invariant magnitude-only readout",
    ),
    Candidate(
        name="direct_cosine_projection",
        fn=direct_cosine_projection,
        imports=("angle_cosine_projection",),
        description="control that computes the cosine curve directly from angles",
    ),
)


def sample_vectors() -> tuple[Vector, ...]:
    return (
        (1.0, 0.0),
        (0.0, 1.0),
        (1.0, 1.0),
        (2.0, -1.0),
        (-1.5, 0.75),
        (0.5, 2.0),
    )


def finite_angles() -> tuple[float, ...]:
    return tuple(2.0 * math.pi * index / 17.0 for index in range(17))


def finite_scales() -> tuple[float, ...]:
    return (0.5, 1.0, 2.0, 3.0)


def kernel(candidate: Candidate, left: Vector, right: Vector) -> float:
    return norm(left) * norm(right) * candidate.fn(left, right)


def transport_invariance_test(candidate: Candidate) -> TestResult:
    max_error = 0.0
    for left in sample_vectors():
        for right in sample_vectors():
            base = candidate.fn(left, right)
            for angle in finite_angles():
                transported = candidate.fn(rotate(left, angle), rotate(right, angle))
                max_error = max(max_error, abs(base - transported))
    if max_error <= 1e-12:
        return TestResult("transport_invariance", "PASS", "simultaneous reversible rotations preserve readout", {"max_error": round(max_error, 15)})
    return TestResult("transport_invariance", "FAIL", "readout changes under simultaneous reversible rotation", {"max_error": round(max_error, 15)})


def scale_gauge_test(candidate: Candidate) -> TestResult:
    max_error = 0.0
    for left in sample_vectors():
        for right in sample_vectors():
            base = candidate.fn(left, right)
            for left_scale in finite_scales():
                for right_scale in finite_scales():
                    scaled = candidate.fn(scale(left_scale, left), scale(right_scale, right))
                    max_error = max(max_error, abs(base - scaled))
    if max_error <= 1e-12:
        return TestResult("scale_gauge", "PASS", "readout ignores arbitrary positive support scale", {"max_error": round(max_error, 15)})
    return TestResult("scale_gauge", "FAIL", "readout depends on arbitrary positive support scale", {"max_error": round(max_error, 15)})


def normalization_test(candidate: Candidate) -> TestResult:
    max_same = 0.0
    max_opposite = 0.0
    for vector in sample_vectors():
        max_same = max(max_same, abs(candidate.fn(vector, vector) - 1.0))
        max_opposite = max(max_opposite, abs(candidate.fn(vector, scale(-1.0, vector)) + 1.0))
    if max_same <= 1e-12 and max_opposite <= 1e-12:
        return TestResult("normalization", "PASS", "same/opposite orientations normalize to +1/-1", {"same_error": round(max_same, 15), "opposite_error": round(max_opposite, 15)})
    return TestResult("normalization", "FAIL", "same/opposite orientation normalization fails", {"same_error": round(max_same, 15), "opposite_error": round(max_opposite, 15)})


def kernel_additivity_test(candidate: Candidate) -> TestResult:
    max_error = 0.0
    vectors = sample_vectors()
    for left_a in vectors:
        for left_b in vectors:
            left_sum = add(left_a, left_b)
            if norm(left_sum) <= 1e-12:
                continue
            for right in vectors:
                expected = kernel(candidate, left_a, right) + kernel(candidate, left_b, right)
                actual = kernel(candidate, left_sum, right)
                max_error = max(max_error, abs(actual - expected))
    for right_a in vectors:
        for right_b in vectors:
            right_sum = add(right_a, right_b)
            if norm(right_sum) <= 1e-12:
                continue
            for left in vectors:
                expected = kernel(candidate, left, right_a) + kernel(candidate, left, right_b)
                actual = kernel(candidate, left, right_sum)
                max_error = max(max_error, abs(actual - expected))
    if max_error <= 1e-12:
        return TestResult(
            "kernel_additivity",
            "PASS",
            "scale-restored readout kernel is additive in each compatible input",
            {"max_error": round(max_error, 15)},
        )
    return TestResult(
        "kernel_additivity",
        "FAIL",
        "scale-restored readout kernel is not additive, so compositional readout fails",
        {"max_error": round(max_error, 12)},
    )


def invariant_kernel_uniqueness_test(candidate: Candidate) -> TestResult:
    e1 = (1.0, 0.0)
    e2 = (0.0, 1.0)
    m11 = kernel(candidate, e1, e1)
    m22 = kernel(candidate, e2, e2)
    m12 = kernel(candidate, e1, e2)
    m21 = kernel(candidate, e2, e1)
    diag_error = abs(m11 - 1.0) + abs(m22 - 1.0)
    offdiag_error = abs(m12) + abs(m21)
    rotation_error = 0.0
    for angle in finite_angles():
        r1 = rotate(e1, angle)
        r2 = rotate(e2, angle)
        rotation_error = max(rotation_error, abs(kernel(candidate, r1, r1) - m11))
        rotation_error = max(rotation_error, abs(kernel(candidate, r2, r2) - m22))
        rotation_error = max(rotation_error, abs(kernel(candidate, r1, r2) - m12))
    dot_error = 0.0
    for left in sample_vectors():
        for right in sample_vectors():
            dot_error = max(dot_error, abs(kernel(candidate, left, right) - dot(left, right)))
    total_error = diag_error + offdiag_error + rotation_error + dot_error
    if total_error <= 1e-12:
        return TestResult(
            "invariant_kernel_uniqueness",
            "PASS",
            "O(2)-invariant additive normalized scalar kernel reduces to the Euclidean dot product",
            {
                "m11": round(m11, 12),
                "m22": round(m22, 12),
                "m12": round(m12, 12),
                "m21": round(m21, 12),
                "dot_error": round(dot_error, 15),
                "total_error": round(total_error, 15),
            },
        )
    return TestResult(
        "invariant_kernel_uniqueness",
        "FAIL",
            "candidate does not reduce to the unique normalized O(2)-invariant additive scalar kernel",
            {
                "m11": round(m11, 12),
                "m22": round(m22, 12),
                "m12": round(m12, 12),
                "m21": round(m21, 12),
                "dot_error": round(dot_error, 12),
                "total_error": round(total_error, 12),
            },
        )


def import_screen(candidate: Candidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "candidate imports a forbidden angle/readout structure", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no direct angle-correlation import declared", {"imports": "-"})


def evaluate_candidate(candidate: Candidate) -> CandidateResult:
    tests = [
        transport_invariance_test(candidate),
        scale_gauge_test(candidate),
        normalization_test(candidate),
        kernel_additivity_test(candidate),
        invariant_kernel_uniqueness_test(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    weak_passed = all(test.verdict == "PASS" for test in tests[:3])
    strong_passed = all(test.verdict == "PASS" for test in tests)
    if strong_passed:
        verdict: Verdict = "UNIQUE_HIT"
    elif candidate.imports and weak_passed:
        verdict = "IMPORTED_HIT"
    elif weak_passed:
        verdict = "WEAK_AMBIGUITY"
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
    parser = argparse.ArgumentParser(description="Evaluate uniqueness of normalized overlap from context/readout axioms.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"UNIQUE_HIT": 4, "IMPORTED_HIT": 3, "WEAK_AMBIGUITY": 2, "REJECTED": 1}
    results = sorted((evaluate_candidate(candidate) for candidate in CANDIDATES), key=lambda result: (order[result.verdict], result.passed), reverse=True)
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
