from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

Verdict = Literal[
    "BORN_HILBERT_SECTOR_CORRECTION_AUDIT_PASS",
    "BORN_HILBERT_SECTOR_CORRECTION_AUDIT_FAIL",
]
CandidateVerdict = Literal["AUDITED_OPEN_CHANNEL", "REJECTED"]
CheckVerdict = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class CorrectionCandidate:
    name: str
    standard_sector_fixed: bool
    lower_source_declared: bool
    scale_or_context_boundary_declared: bool
    correction_observable_declared: bool
    no_postfit_retuning: bool
    holdout_comparison_required: bool
    no_born_hilbert_redefinition: bool
    reduces_to_standard_sector_inside_boundary: bool
    correction_may_be_zero: bool
    expected: CandidateVerdict
    description: str


@dataclass(frozen=True)
class CheckResult:
    name: str
    verdict: CheckVerdict
    reason: str


@dataclass(frozen=True)
class CandidateResult:
    candidate: str
    verdict: CandidateVerdict
    expected: CandidateVerdict
    passed: int
    failed: int
    checks: list[CheckResult]
    description: str


@dataclass(frozen=True)
class AuditResult:
    verdict: Verdict
    passed_candidates: int
    failed_candidates: int
    results: list[CandidateResult]
    concrete_result: str
    lean_artifacts: tuple[str, ...]


CANDIDATES: tuple[CorrectionCandidate, ...] = (
    CorrectionCandidate(
        name="audited_lower_source_scale_channel",
        standard_sector_fixed=True,
        lower_source_declared=True,
        scale_or_context_boundary_declared=True,
        correction_observable_declared=True,
        no_postfit_retuning=True,
        holdout_comparison_required=True,
        no_born_hilbert_redefinition=True,
        reduces_to_standard_sector_inside_boundary=True,
        correction_may_be_zero=True,
        expected="AUDITED_OPEN_CHANNEL",
        description="allowed open channel: lower source, fixed boundary, fixed observable, no-postfit holdout",
    ),
    CorrectionCandidate(
        name="free_fit_residual",
        standard_sector_fixed=False,
        lower_source_declared=False,
        scale_or_context_boundary_declared=False,
        correction_observable_declared=True,
        no_postfit_retuning=False,
        holdout_comparison_required=False,
        no_born_hilbert_redefinition=False,
        reduces_to_standard_sector_inside_boundary=False,
        correction_may_be_zero=True,
        expected="REJECTED",
        description="rejected: residual term fitted after seeing the target behavior",
    ),
    CorrectionCandidate(
        name="born_rule_redefinition",
        standard_sector_fixed=False,
        lower_source_declared=True,
        scale_or_context_boundary_declared=True,
        correction_observable_declared=True,
        no_postfit_retuning=True,
        holdout_comparison_required=True,
        no_born_hilbert_redefinition=False,
        reduces_to_standard_sector_inside_boundary=False,
        correction_may_be_zero=True,
        expected="REJECTED",
        description="rejected: correction rewrites Born readout instead of leaving the standard sector fixed",
    ),
    CorrectionCandidate(
        name="hilbert_carrier_override",
        standard_sector_fixed=False,
        lower_source_declared=True,
        scale_or_context_boundary_declared=True,
        correction_observable_declared=True,
        no_postfit_retuning=True,
        holdout_comparison_required=True,
        no_born_hilbert_redefinition=False,
        reduces_to_standard_sector_inside_boundary=False,
        correction_may_be_zero=True,
        expected="REJECTED",
        description="rejected: correction replaces the Hilbert-sector carrier rather than auditing a deviation",
    ),
    CorrectionCandidate(
        name="nonzero_inside_standard_boundary",
        standard_sector_fixed=True,
        lower_source_declared=True,
        scale_or_context_boundary_declared=True,
        correction_observable_declared=True,
        no_postfit_retuning=True,
        holdout_comparison_required=True,
        no_born_hilbert_redefinition=True,
        reduces_to_standard_sector_inside_boundary=False,
        correction_may_be_zero=True,
        expected="REJECTED",
        description="rejected: claimed correction does not reduce back to the standard QM sector in its own boundary",
    ),
    CorrectionCandidate(
        name="no_holdout_channel",
        standard_sector_fixed=True,
        lower_source_declared=True,
        scale_or_context_boundary_declared=True,
        correction_observable_declared=True,
        no_postfit_retuning=True,
        holdout_comparison_required=False,
        no_born_hilbert_redefinition=True,
        reduces_to_standard_sector_inside_boundary=True,
        correction_may_be_zero=True,
        expected="REJECTED",
        description="rejected: no held-out comparison is required",
    ),
)


def check_bool(name: str, value: bool, pass_reason: str, fail_reason: str) -> CheckResult:
    if value:
        return CheckResult(name=name, verdict="PASS", reason=pass_reason)
    return CheckResult(name=name, verdict="FAIL", reason=fail_reason)


def evaluate_candidate(candidate: CorrectionCandidate) -> CandidateResult:
    checks = [
        check_bool(
            "standard_sector_fixed",
            candidate.standard_sector_fixed,
            "standard Born/Hilbert sector is held fixed",
            "candidate changes the baseline Born/Hilbert sector",
        ),
        check_bool(
            "lower_source_declared",
            candidate.lower_source_declared,
            "lower primitive source is declared",
            "no lower primitive source is declared",
        ),
        check_bool(
            "scale_or_context_boundary_declared",
            candidate.scale_or_context_boundary_declared,
            "scale/context boundary is fixed before comparison",
            "scale/context boundary is missing",
        ),
        check_bool(
            "correction_observable_declared",
            candidate.correction_observable_declared,
            "observable being tested is declared",
            "observable being tested is missing",
        ),
        check_bool(
            "no_postfit_retuning",
            candidate.no_postfit_retuning,
            "no-postfit discipline is declared",
            "candidate permits post-fit retuning",
        ),
        check_bool(
            "holdout_comparison_required",
            candidate.holdout_comparison_required,
            "held-out comparison is required",
            "held-out comparison is not required",
        ),
        check_bool(
            "no_born_hilbert_redefinition",
            candidate.no_born_hilbert_redefinition,
            "Born/Hilbert readout is not redefined",
            "candidate redefines Born/Hilbert readout",
        ),
        check_bool(
            "reduces_to_standard_sector_inside_boundary",
            candidate.reduces_to_standard_sector_inside_boundary,
            "candidate reduces to the standard sector inside its boundary",
            "candidate does not reduce to the standard sector inside its boundary",
        ),
        check_bool(
            "correction_may_be_zero",
            candidate.correction_may_be_zero,
            "null correction remains admissible",
            "candidate forces nonzero deviation before evidence",
        ),
    ]
    failed = sum(1 for check in checks if check.verdict == "FAIL")
    verdict: CandidateVerdict = "AUDITED_OPEN_CHANNEL" if failed == 0 else "REJECTED"
    return CandidateResult(
        candidate=candidate.name,
        verdict=verdict,
        expected=candidate.expected,
        passed=len(checks) - failed,
        failed=failed,
        checks=checks,
        description=candidate.description,
    )


def build_audit() -> AuditResult:
    results = [evaluate_candidate(candidate) for candidate in CANDIDATES]
    mismatches = [result for result in results if result.verdict != result.expected]
    return AuditResult(
        verdict=(
            "BORN_HILBERT_SECTOR_CORRECTION_AUDIT_FAIL"
            if mismatches
            else "BORN_HILBERT_SECTOR_CORRECTION_AUDIT_PASS"
        ),
        passed_candidates=len(results) - len(mismatches),
        failed_candidates=len(mismatches),
        results=results,
        concrete_result=(
            "Born/Hilbert remain the fixed standard-sector projection; only audited lower-source "
            "correction channels survive, while free-fit, Born-redefinition, Hilbert-override, "
            "inside-boundary, and no-holdout corrections are rejected"
        ),
        lean_artifacts=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::current_beyond_qm_correction_channel_is_audited",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::free_fit_correction_channel_is_rejected",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::current_b2_is_standard_qm_sector_projection_not_final_physics",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Audit Born/Hilbert standard-sector correction candidates.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    audit = build_audit()
    print(
        f"born_hilbert_sector_corrections={audit.verdict} "
        f"passed_candidates={audit.passed_candidates} failed_candidates={audit.failed_candidates}"
    )
    print(f"RESULT {audit.concrete_result}")
    print(f"LEAN {','.join(audit.lean_artifacts)}")
    for result in audit.results:
        print(
            f"{result.verdict} candidate={result.candidate} "
            f"expected={result.expected} passed={result.passed}/9 failed={result.failed}"
        )
        if args.show_checks:
            for check in result.checks:
                print(f"  {check.verdict} {check.name}: {check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(audit), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if audit.verdict == "BORN_HILBERT_SECTOR_CORRECTION_AUDIT_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
