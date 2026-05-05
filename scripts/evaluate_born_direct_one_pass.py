from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts import evaluate_affine_readout_principle as affine  # noqa: E402
from scripts import evaluate_born_from_overlap_affine_readout as born_overlap  # noqa: E402
from scripts import evaluate_overlap_uniqueness as overlap_unique  # noqa: E402
from scripts import evaluate_phase_bundle_j_derivation as phase_j  # noqa: E402
from scripts import evaluate_primitive_boundary_qm_chain as boundary  # noqa: E402

Verdict = Literal[
    "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF",
    "DIRECT_BORN_ROUTE_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class RouteCheck:
    name: str
    observed: str
    expected: str
    status: CheckStatus
    obligation: str


@dataclass(frozen=True)
class DirectBornOnePass:
    verdict: Verdict
    checks: list[RouteCheck]
    passed: int
    failed: int
    remaining_universal_obligations: tuple[str, ...]


def status_for(observed: str, expected: str) -> CheckStatus:
    return "PASS" if observed == expected else "FAIL"


def make_check(name: str, observed: str, expected: str, obligation: str) -> RouteCheck:
    return RouteCheck(
        name=name,
        observed=observed,
        expected=expected,
        status=status_for(observed, expected),
        obligation=obligation,
    )


def find_boundary_result(candidate_name: str) -> boundary.CandidateResult:
    for candidate in boundary.CANDIDATES:
        if candidate.name == candidate_name:
            return boundary.evaluate_candidate(candidate)
    raise ValueError(f"unknown primitive-boundary candidate: {candidate_name}")


def find_overlap_result(candidate_name: str) -> overlap_unique.CandidateResult:
    for candidate in overlap_unique.CANDIDATES:
        if candidate.name == candidate_name:
            return overlap_unique.evaluate_candidate(candidate)
    raise ValueError(f"unknown overlap candidate: {candidate_name}")


def find_phase_j_result(candidate_name: str) -> phase_j.CandidateResult:
    for candidate in phase_j.CANDIDATES:
        if candidate.name == candidate_name:
            return phase_j.evaluate_candidate(candidate)
    raise ValueError(f"unknown phase-bundle J candidate: {candidate_name}")


def find_affine_result(candidate_name: str) -> affine.CandidateResult:
    for candidate in affine.CANDIDATES:
        if candidate.name == candidate_name:
            return affine.evaluate_candidate(candidate)
    raise ValueError(f"unknown affine readout candidate: {candidate_name}")


def find_born_overlap_result(candidate_name: str) -> born_overlap.CandidateResult:
    for candidate in born_overlap.CANDIDATES:
        if candidate.name == candidate_name:
            return born_overlap.evaluate_candidate(candidate)
    raise ValueError(f"unknown signed-overlap Born candidate: {candidate_name}")


def lean_status() -> str:
    completed = subprocess.run(
        ["lake", "build", "Proofs.QMClosure.PrimitiveBoundaryQMChain"],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return "PASS" if completed.returncode == 0 else "FAIL"


def build_checks() -> list[RouteCheck]:
    primitive_boundary = find_boundary_result("full_primitive_boundary_candidate")
    missing_pairwise = find_boundary_result("missing_pairwise_coverage_control")
    imported_boundary = find_boundary_result("hilbert_born_import_control")
    unique_overlap = find_overlap_result("normalized_bilinear_overlap")
    cubic_overlap = find_overlap_result("cubic_overlap")
    canonical_j = find_phase_j_result("canonical_quadrature_J")
    imported_j = find_phase_j_result("imported_complex_J")
    affine_readout = find_affine_result("operational_frequency_affine_mix")
    imported_affine = find_affine_result("imported_convex_probability_control")
    born_selector = find_born_overlap_result("affine_born_from_signed_overlap")
    imported_born = find_born_overlap_result("imported_amplitude_square_control")

    return [
        make_check(
            "lean.primitive_boundary_chain",
            lean_status(),
            "PASS",
            "Lean dependency-shape artifact must compile.",
        ),
        make_check(
            "boundary.full_candidate",
            primitive_boundary.verdict,
            "PRIMITIVE_BOUNDARY_CANDIDATE",
            "Derive the full primitive-boundary package from context-first unknownness.",
        ),
        make_check(
            "boundary.missing_pairwise_control",
            missing_pairwise.verdict,
            "PARTIAL_BOUNDARY",
            "Pairwise/proper-subcontext coverage remains necessary.",
        ),
        make_check(
            "boundary.imported_control",
            imported_boundary.verdict,
            "IMPORTED_HIT",
            "Hilbert/Born/complex imports must remain rejected as proof routes.",
        ),
        make_check(
            "overlap.unique",
            unique_overlap.verdict,
            "UNIQUE_HIT",
            "Generalize normalized-overlap uniqueness beyond the finite vector screen.",
        ),
        make_check(
            "overlap.cubic_control",
            cubic_overlap.verdict,
            "WEAK_AMBIGUITY",
            "Nonlinear overlap controls must fail additivity/uniqueness before universal upgrade.",
        ),
        make_check(
            "phase_j.canonical",
            canonical_j.verdict,
            "J_DERIVATION_HIT",
            "Derive phase-bundle J and double-cover semantics from primitive-boundary structure.",
        ),
        make_check(
            "phase_j.imported_control",
            imported_j.verdict,
            "IMPORTED_HIT",
            "Imported complex scalar control must remain rejected.",
        ),
        make_check(
            "affine_readout.randomization",
            affine_readout.verdict,
            "AFFINE_READOUT_PRINCIPLE_HIT",
            "Bind external randomization/frequency calibration to primitive facticizable records.",
        ),
        make_check(
            "affine_readout.imported_control",
            imported_affine.verdict,
            "IMPORTED_HIT",
            "Convex probability imports must remain rejected.",
        ),
        make_check(
            "born_selector.signed_overlap",
            born_selector.verdict,
            "AFFINE_BORN_SELECTOR_HIT",
            "Generalize signed-overlap affine readout across all admissible readout contexts.",
        ),
        make_check(
            "born_selector.imported_control",
            imported_born.verdict,
            "IMPORTED_HIT",
            "Direct amplitude-square import must remain rejected.",
        ),
    ]


def build_route() -> DirectBornOnePass:
    checks = build_checks()
    failures = [check for check in checks if check.status == "FAIL"]
    verdict: Verdict = "DIRECT_BORN_ROUTE_BLOCKED" if failures else "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF"
    return DirectBornOnePass(
        verdict=verdict,
        checks=checks,
        passed=len(checks) - len(failures),
        failed=len(failures),
        remaining_universal_obligations=(
            "derive_full_primitive_boundary_package_from_context_first_unknownness",
            "derive_external_randomization_frequency_calibration_for_facticizable_records",
            "derive_signed_expectation_readout_for_normalized_overlap",
            "derive_phase_bundle_double_cover_for_all_admissible_readout_contexts",
            "generalize_from_finite_screens_to_universal_Born_contexts",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run the direct finite Born one-pass route gate.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    route = build_route()
    print(f"born_direct_one_pass={route.verdict} passed={route.passed} failed={route.failed}")
    print(f"REMAINING {','.join(route.remaining_universal_obligations)}")
    if args.show_checks:
        for check in route.checks:
            print(
                f"{check.status} {check.name}: observed={check.observed} "
                f"expected={check.expected}; obligation={check.obligation}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(route), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if route.verdict == "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF" else 1


if __name__ == "__main__":
    raise SystemExit(main())
