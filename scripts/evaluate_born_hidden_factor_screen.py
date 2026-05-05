from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

ProbabilityVector = tuple[float, ...]
FactorMode = Literal[
    "baseline",
    "global_context",
    "outcome_bias",
    "product_bias",
    "ternary_residue",
    "declared_qm_unit",
    "imported_born",
]
Verdict = Literal[
    "BORN_BASELINE",
    "DEFORMATION_WALL",
    "GAUGE_EQUIVALENT",
    "I3_WALL",
    "IMPORTED_HIT",
    "SECTOR_FACTOR_OPEN",
]
TestVerdict = Literal["PASS", "FAIL"]

CONTEXTS: tuple[ProbabilityVector, ...] = (
    (0.2, 0.8),
    (0.125, 0.375, 0.5),
    (0.1, 0.2, 0.3, 0.4),
)
EPSILON = 0.17
TOLERANCE = 1e-9


@dataclass(frozen=True)
class HiddenFactorCandidate:
    name: str
    mode: FactorMode
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


CANDIDATES: tuple[HiddenFactorCandidate, ...] = (
    HiddenFactorCandidate(
        name="born_visible_sector_baseline",
        mode="baseline",
        imports=(),
        description="ordinary normalized quadratic readout with no hidden factor",
    ),
    HiddenFactorCandidate(
        name="global_context_unit_factor",
        mode="global_context",
        imports=(),
        description="context-wide factor chi(C), equal for all outcomes and therefore normalized away",
    ),
    HiddenFactorCandidate(
        name="outcome_bias_unit_in_qm",
        mode="outcome_bias",
        imports=(),
        description="outcome-dependent factor that equals one only in the undeformed QM limit",
    ),
    HiddenFactorCandidate(
        name="product_factor_unit_in_qm",
        mode="product_bias",
        imports=(),
        description="factorized product-context hidden factor, unit in the undeformed QM limit",
    ),
    HiddenFactorCandidate(
        name="ternary_residue_unit_in_qm",
        mode="ternary_residue",
        imports=(),
        description="three-alternative residue factor, unit when the ternary channel is frozen",
    ),
    HiddenFactorCandidate(
        name="declared_qm_unit_factor",
        mode="declared_qm_unit",
        imports=(),
        description="factor declared to be one on all current QM fixtures, with no off-fixture law",
    ),
    HiddenFactorCandidate(
        name="born_rule_import_control",
        mode="imported_born",
        imports=("born_rule",),
        description="control that declares the target Born rule rather than deriving the factor",
    ),
)


def close(left: float, right: float, tolerance: float = TOLERANCE) -> bool:
    return abs(left - right) <= tolerance


def normalize(weights: ProbabilityVector) -> ProbabilityVector:
    total = sum(weights)
    if total <= 0.0:
        raise ValueError("weights must have positive total")
    return tuple(weight / total for weight in weights)


def born_probabilities(weights: ProbabilityVector) -> ProbabilityVector:
    return normalize(weights)


def centered_index(index: int, size: int) -> float:
    return float(index) - (float(size) - 1.0) / 2.0


def factors(candidate: HiddenFactorCandidate, context: ProbabilityVector, epsilon: float) -> ProbabilityVector:
    size = len(context)
    if candidate.mode == "baseline":
        return tuple(1.0 for _index in range(size))
    if candidate.mode == "global_context":
        value = math.exp(-epsilon)
        return tuple(value for _index in range(size))
    if candidate.mode == "outcome_bias":
        return tuple(math.exp(epsilon * centered_index(index, size)) for index in range(size))
    if candidate.mode == "product_bias":
        return tuple(math.exp(epsilon * float(index % 2)) for index in range(size))
    if candidate.mode == "ternary_residue":
        if size == 3:
            return (1.0 + epsilon, 1.0 - epsilon, 1.0)
        return tuple(1.0 for _index in range(size))
    if candidate.mode == "declared_qm_unit":
        if close(epsilon, 0.0):
            return tuple(1.0 for _index in range(size))
        return tuple(1.0 + epsilon * 0.0 for _index in range(size))
    if candidate.mode == "imported_born":
        return tuple(1.0 for _index in range(size))
    raise ValueError(f"unknown factor mode: {candidate.mode}")


def deformed_probabilities(
    candidate: HiddenFactorCandidate,
    context: ProbabilityVector,
    epsilon: float,
) -> ProbabilityVector:
    hidden = factors(candidate, context, epsilon)
    weighted = tuple(probability * factor for probability, factor in zip(context, hidden, strict=True))
    return normalize(weighted)


def qm_limit_test(candidate: HiddenFactorCandidate) -> TestResult:
    max_error = 0.0
    for context in CONTEXTS:
        born = born_probabilities(context)
        deformed = deformed_probabilities(candidate, context, 0.0)
        max_error = max(max_error, max(abs(left - right) for left, right in zip(born, deformed, strict=True)))
    if max_error <= TOLERANCE:
        return TestResult("qm_limit", "PASS", "factor reduces to ordinary Born probabilities when chi=1", {"max_error": round(max_error, 12)})
    return TestResult("qm_limit", "FAIL", "factor changes ordinary QM probabilities even in the chi=1 limit", {"max_error": round(max_error, 12)})


def normalization_test(candidate: HiddenFactorCandidate) -> TestResult:
    max_sum_error = 0.0
    min_probability = 1.0
    for context in CONTEXTS:
        deformed = deformed_probabilities(candidate, context, EPSILON)
        max_sum_error = max(max_sum_error, abs(sum(deformed) - 1.0))
        min_probability = min(min_probability, min(deformed))
    if max_sum_error <= TOLERANCE and min_probability >= -TOLERANCE:
        return TestResult(
            "normalization",
            "PASS",
            "deformed factor still gives normalized nonnegative probabilities",
            {"max_sum_error": round(max_sum_error, 12), "min_probability": round(min_probability, 12)},
        )
    return TestResult(
        "normalization",
        "FAIL",
        "deformed factor fails normalization or nonnegativity",
        {"max_sum_error": round(max_sum_error, 12), "min_probability": round(min_probability, 12)},
    )


def repeatability_test(candidate: HiddenFactorCandidate) -> TestResult:
    sharp_contexts: tuple[ProbabilityVector, ...] = ((1.0, 0.0), (0.0, 1.0), (0.0, 1.0, 0.0))
    max_error = 0.0
    for context in sharp_contexts:
        deformed = deformed_probabilities(candidate, context, EPSILON)
        max_error = max(max_error, max(abs(left - right) for left, right in zip(context, deformed, strict=True)))
    if max_error <= TOLERANCE:
        return TestResult("repeatability", "PASS", "sharp projective records remain repeatable", {"max_error": round(max_error, 12)})
    return TestResult("repeatability", "FAIL", "sharp projective records are disturbed", {"max_error": round(max_error, 12)})


def coarse_graining_test(candidate: HiddenFactorCandidate) -> TestResult:
    fine_context = (0.2, 0.3, 0.5)
    fine = deformed_probabilities(candidate, fine_context, EPSILON)
    coarse_from_fine = (fine[0] + fine[1], fine[2])
    coarse_direct = deformed_probabilities(candidate, (0.5, 0.5), EPSILON)
    max_error = max(abs(left - right) for left, right in zip(coarse_from_fine, coarse_direct, strict=True))
    if max_error <= 5e-3:
        return TestResult("coarse_graining", "PASS", "coarse-grained probabilities are stable under refinement", {"max_error": round(max_error, 12)})
    return TestResult("coarse_graining", "FAIL", "factor makes probabilities depend on arbitrary refinement", {"max_error": round(max_error, 12)})


def product_multiplicativity_test(candidate: HiddenFactorCandidate) -> TestResult:
    left_context = (0.3, 0.7)
    right_context = (0.4, 0.6)
    left = deformed_probabilities(candidate, left_context, EPSILON)
    right = deformed_probabilities(candidate, right_context, EPSILON)
    product_from_parts = tuple(left_value * right_value for left_value in left for right_value in right)
    product_context = tuple(left_value * right_value for left_value in left_context for right_value in right_context)
    product_direct = deformed_probabilities(candidate, product_context, EPSILON)
    max_error = max(abs(left_value - right_value) for left_value, right_value in zip(product_from_parts, product_direct, strict=True))
    if max_error <= 5e-3:
        return TestResult("product_multiplicativity", "PASS", "independent product readouts compose multiplicatively", {"max_error": round(max_error, 12)})
    return TestResult("product_multiplicativity", "FAIL", "factor breaks product-readout multiplicativity", {"max_error": round(max_error, 12)})


def hidden_ternary_test(candidate: HiddenFactorCandidate) -> TestResult:
    ternary = factors(candidate, (0.2, 0.3, 0.5), EPSILON)
    binary_left = factors(candidate, (0.5, 0.5), EPSILON)
    ternary_spread = max(ternary) - min(ternary)
    binary_spread = max(binary_left) - min(binary_left)
    hidden_ternary = ternary_spread > 1e-9 and binary_spread <= 1e-9
    if not hidden_ternary:
        return TestResult(
            "no_hidden_ternary_factor",
            "PASS",
            "factor is not active only as a primitive ternary residue",
            {"ternary_spread": round(ternary_spread, 12), "binary_spread": round(binary_spread, 12)},
        )
    return TestResult(
        "no_hidden_ternary_factor",
        "FAIL",
        "factor is a hidden ternary context-only residue",
        {"ternary_spread": round(ternary_spread, 12), "binary_spread": round(binary_spread, 12)},
    )


def physical_nontriviality_test(candidate: HiddenFactorCandidate) -> TestResult:
    max_difference = 0.0
    for context in CONTEXTS:
        born = born_probabilities(context)
        deformed = deformed_probabilities(candidate, context, EPSILON)
        max_difference = max(max_difference, max(abs(left - right) for left, right in zip(born, deformed, strict=True)))
    if max_difference > 1e-6:
        return TestResult("physical_nontriviality", "PASS", "factor would be observable outside the chi=1 sector", {"max_difference": round(max_difference, 12)})
    return TestResult("physical_nontriviality", "FAIL", "factor cancels out of normalized probabilities and is gauge-equivalent here", {"max_difference": round(max_difference, 12)})


def import_screen(candidate: HiddenFactorCandidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "candidate imports the target readout law", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no target Born/Hilbert import declared", {"imports": "-"})


def evaluate_candidate(candidate: HiddenFactorCandidate) -> CandidateResult:
    tests = [
        qm_limit_test(candidate),
        normalization_test(candidate),
        repeatability_test(candidate),
        coarse_graining_test(candidate),
        product_multiplicativity_test(candidate),
        hidden_ternary_test(candidate),
        physical_nontriviality_test(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    failed_names = {test.name for test in tests if test.verdict == "FAIL"}
    if candidate.imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif candidate.mode == "baseline":
        verdict = "BORN_BASELINE"
    elif candidate.mode == "declared_qm_unit":
        verdict = "SECTOR_FACTOR_OPEN"
    elif "physical_nontriviality" in failed_names and passed >= 7:
        verdict = "GAUGE_EQUIVALENT"
    elif "no_hidden_ternary_factor" in failed_names:
        verdict = "I3_WALL"
    else:
        verdict = "DEFORMATION_WALL"
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
    parser = argparse.ArgumentParser(description="Screen hidden unit-factor deformations of Born readout.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {
        "BORN_BASELINE": 6,
        "GAUGE_EQUIVALENT": 5,
        "SECTOR_FACTOR_OPEN": 4,
        "DEFORMATION_WALL": 3,
        "I3_WALL": 2,
        "IMPORTED_HIT": 1,
    }
    results = sorted(
        (evaluate_candidate(candidate) for candidate in CANDIDATES),
        key=lambda result: (order[result.verdict], result.passed),
        reverse=True,
    )
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(f"verdict={result.verdict} candidate={result.candidate} passed={result.passed}/8 imports={imports}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
