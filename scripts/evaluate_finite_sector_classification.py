from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal["FINITE_SECTOR_HIT", "OPEN_RESIDUAL", "REJECTED"]
TestVerdict = Literal["PASS", "FAIL", "OPEN"]

TSIRELSON = 2.0 * math.sqrt(2.0)


@dataclass(frozen=True)
class CarrierCandidate:
    name: str
    kind: Literal[
        "classical",
        "real_hilbert",
        "complex_hilbert",
        "quaternionic_hilbert",
        "boxworld",
        "generic_gpt",
        "route_closed_residual",
    ]
    local_dimension: int
    chsh_capacity: float
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
    open: int
    imports: tuple[str, ...]
    tests: list[TestResult]
    description: str


CANDIDATES: tuple[CarrierCandidate, ...] = (
    CarrierCandidate(
        name="classical_simplex_bit",
        kind="classical",
        local_dimension=2,
        chsh_capacity=2.0,
        imports=(),
        description="finite classical simplex carrier; negative control for contextual/phase capacity",
    ),
    CarrierCandidate(
        name="real_hilbert_rebit",
        kind="real_hilbert",
        local_dimension=2,
        chsh_capacity=TSIRELSON,
        imports=(),
        description="real-Hilbert-like carrier; known hidden joint-orientation separator",
    ),
    CarrierCandidate(
        name="complex_hilbert_qubit_route",
        kind="complex_hilbert",
        local_dimension=2,
        chsh_capacity=TSIRELSON,
        imports=(),
        description="complex-Hilbert-like finite route target, represented through phase-bundle overlap screens",
    ),
    CarrierCandidate(
        name="quaternionic_hilbert_bit",
        kind="quaternionic_hilbert",
        local_dimension=2,
        chsh_capacity=TSIRELSON,
        imports=(),
        description="quaternionic-Hilbert-like finite carrier; local tomography/composition control",
    ),
    CarrierCandidate(
        name="boxworld_pr",
        kind="boxworld",
        local_dimension=2,
        chsh_capacity=4.0,
        imports=("pr_box_table",),
        description="PR/boxworld-like superquantum control",
    ),
    CarrierCandidate(
        name="unconstrained_generic_gpt",
        kind="generic_gpt",
        local_dimension=2,
        chsh_capacity=3.2,
        imports=(),
        description="generic GPT cone without the B2 finite route-closure contract",
    ),
    CarrierCandidate(
        name="finite_route_closed_residual",
        kind="route_closed_residual",
        local_dimension=2,
        chsh_capacity=TSIRELSON,
        imports=(),
        description="abstract residual: passes declared finite screens but lacks a representation classification proof",
    ),
)


def local_parameters(candidate: CarrierCandidate) -> int:
    dimension = candidate.local_dimension
    if candidate.kind == "classical":
        return dimension
    if candidate.kind == "real_hilbert":
        return dimension * (dimension + 1) // 2
    if candidate.kind == "complex_hilbert":
        return dimension * dimension
    if candidate.kind == "quaternionic_hilbert":
        return dimension * (2 * dimension - 1)
    if candidate.kind == "boxworld":
        return 3
    if candidate.kind == "generic_gpt":
        return 5
    if candidate.kind == "route_closed_residual":
        return dimension * dimension
    raise ValueError(f"unknown candidate kind: {candidate.kind}")


def composite_parameters(candidate: CarrierCandidate) -> int:
    dimension = candidate.local_dimension
    composite_dimension = dimension * dimension
    if candidate.kind == "classical":
        return dimension * dimension
    if candidate.kind == "real_hilbert":
        return composite_dimension * (composite_dimension + 1) // 2
    if candidate.kind == "complex_hilbert":
        return composite_dimension * composite_dimension
    if candidate.kind == "quaternionic_hilbert":
        return composite_dimension * (2 * composite_dimension - 1)
    if candidate.kind == "boxworld":
        # Two binary-input/binary-output no-signalling boxes have eight
        # independent correlator/marginal parameters, not K_A*K_B=9.
        return 8
    if candidate.kind == "generic_gpt":
        return 31
    if candidate.kind == "route_closed_residual":
        return composite_dimension * composite_dimension
    raise ValueError(f"unknown candidate kind: {candidate.kind}")


def phase_bundle_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.kind in {"complex_hilbert", "route_closed_residual"}:
        return TestResult("phase_bundle", "PASS", "global phase is gauge and relative phase is readout-relevant", {"phase_bundle": True})
    if candidate.kind == "real_hilbert":
        return TestResult("phase_bundle", "FAIL", "local phase orientation is suppressed and reappears as joint-only orientation", {"phase_bundle": False})
    if candidate.kind == "classical":
        return TestResult("phase_bundle", "FAIL", "classical simplex has no reversible relative-phase interference channel", {"phase_bundle": False})
    if candidate.kind == "quaternionic_hilbert":
        return TestResult("phase_bundle", "FAIL", "noncommutative phase scalars fail the current finite route-composition contract", {"phase_bundle": False})
    if candidate.kind == "boxworld":
        return TestResult("phase_bundle", "FAIL", "boxworld tables provide correlations without a phase-bundle transport screen", {"phase_bundle": False})
    return TestResult("phase_bundle", "FAIL", "generic GPT carrier does not supply the declared phase-bundle route", {"phase_bundle": False})


def local_tomography_screen(candidate: CarrierCandidate) -> TestResult:
    k_a = local_parameters(candidate)
    k_ab = composite_parameters(candidate)
    product = k_a * k_a
    if k_ab == product:
        return TestResult("local_tomography", "PASS", "composite parameter count matches product-context tomography", {"k_a": k_a, "k_b": k_a, "k_ab": k_ab, "product": product})
    return TestResult("local_tomography", "FAIL", "composite parameter count violates product-context tomography", {"k_a": k_a, "k_b": k_a, "k_ab": k_ab, "product": product})


def hidden_joint_invariant_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.kind == "real_hilbert":
        return TestResult("hidden_joint_invariant", "FAIL", "two-rebit Y tensor Y is globally stable but product-context invisible", {"hidden_joint": True})
    if candidate.kind in {"quaternionic_hilbert", "generic_gpt"}:
        return TestResult("hidden_joint_invariant", "FAIL", "candidate admits unclassified composite degrees outside current product witness exhaustion", {"hidden_joint": True})
    if candidate.kind == "route_closed_residual":
        return TestResult("hidden_joint_invariant", "OPEN", "residual declares finite route closure but lacks a proof that all hidden joint degrees are exhausted", {"hidden_joint": "unproved"})
    return TestResult("hidden_joint_invariant", "PASS", "no hidden joint-only invariant appears on this finite screen", {"hidden_joint": False})


def bounded_correlation_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.chsh_capacity > TSIRELSON + 1e-12:
        return TestResult("bounded_correlation", "FAIL", "candidate exceeds the non-superquantum Tsirelson boundary", {"chsh_capacity": round(candidate.chsh_capacity, 12), "tsirelson": round(TSIRELSON, 12)})
    if candidate.chsh_capacity < 2.0 + 1e-12:
        return TestResult("bounded_correlation", "FAIL", "candidate cannot reach Bell-strength contextual correlations", {"chsh_capacity": round(candidate.chsh_capacity, 12), "tsirelson": round(TSIRELSON, 12)})
    return TestResult("bounded_correlation", "PASS", "candidate is inside the finite non-superquantum Bell-strength window", {"chsh_capacity": round(candidate.chsh_capacity, 12), "tsirelson": round(TSIRELSON, 12)})


def finite_route_closure_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.kind in {"complex_hilbert", "route_closed_residual"}:
        return TestResult("finite_route_closure", "PASS", "candidate satisfies the current finite route-closure contract", {"route_closed": True})
    if candidate.kind == "classical":
        return TestResult("finite_route_closure", "FAIL", "candidate misses the phase/interference finite route screens", {"route_closed": False})
    if candidate.kind == "boxworld":
        return TestResult("finite_route_closure", "FAIL", "candidate imports superquantum tables rather than satisfying the route contract", {"route_closed": False})
    return TestResult("finite_route_closure", "FAIL", "candidate fails at least one finite route separator", {"route_closed": False})


def representation_classification_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.kind == "complex_hilbert":
        return TestResult("representation_classification", "PASS", "candidate is the represented finite route target", {"classified": True})
    if candidate.kind == "route_closed_residual":
        return TestResult("representation_classification", "OPEN", "no theorem currently proves this residual equivalent to the complex route", {"classified": False})
    return TestResult("representation_classification", "FAIL", "candidate is rejected before the classification theorem stage", {"classified": False})


def constructive_carrier_witness_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.kind == "complex_hilbert":
        return TestResult(
            "constructive_carrier_witness",
            "PASS",
            "candidate has an explicit phase-bundle finite-route representation witness",
            {"constructive_witness": True},
        )
    if candidate.kind == "route_closed_residual":
        return TestResult(
            "constructive_carrier_witness",
            "FAIL",
            "abstract route-closed residual is not an admissible carrier without a constructive representation witness",
            {"constructive_witness": False},
        )
    return TestResult(
        "constructive_carrier_witness",
        "FAIL",
        "candidate is rejected before it supplies an admissible finite-route representation witness",
        {"constructive_witness": False},
    )


def import_screen(candidate: CarrierCandidate) -> TestResult:
    if candidate.imports:
        return TestResult("import_screen", "FAIL", "candidate declares forbidden imported structure", {"imports": ",".join(candidate.imports)})
    return TestResult("import_screen", "PASS", "no forbidden import declared", {"imports": "-"})


def evaluate_candidate(candidate: CarrierCandidate) -> CandidateResult:
    tests = [
        phase_bundle_screen(candidate),
        local_tomography_screen(candidate),
        hidden_joint_invariant_screen(candidate),
        bounded_correlation_screen(candidate),
        finite_route_closure_screen(candidate),
        representation_classification_screen(candidate),
        constructive_carrier_witness_screen(candidate),
        import_screen(candidate),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = sum(1 for test in tests if test.verdict == "FAIL")
    open_count = sum(1 for test in tests if test.verdict == "OPEN")
    if failed == 0 and open_count == 0:
        verdict: Verdict = "FINITE_SECTOR_HIT"
    elif failed == 0:
        verdict = "OPEN_RESIDUAL"
    else:
        verdict = "REJECTED"
    return CandidateResult(
        candidate=candidate.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        open=open_count,
        imports=candidate.imports,
        tests=tests,
        description=candidate.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate the finite-sector carrier classification frontier.")
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    order = {"FINITE_SECTOR_HIT": 3, "OPEN_RESIDUAL": 2, "REJECTED": 1}
    results = sorted(
        (evaluate_candidate(candidate) for candidate in CANDIDATES),
        key=lambda result: (order[result.verdict], result.passed, -result.open),
        reverse=True,
    )
    for result in results:
        imports = ",".join(result.imports) if result.imports else "-"
        print(
            f"verdict={result.verdict} candidate={result.candidate} "
            f"passed={result.passed}/8 failed={result.failed} open={result.open} imports={imports}"
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
