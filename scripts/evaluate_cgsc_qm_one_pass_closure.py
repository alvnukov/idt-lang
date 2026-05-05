from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_cgsc_extension_wall_probe as extension_wall  # noqa: E402
import scripts.evaluate_cgsc_primitive_bridge as primitive_bridge  # noqa: E402
import scripts.evaluate_cgsc_primitive_derivation as primitive_derivation  # noqa: E402
import scripts.evaluate_cgsc_semantic_content_wall as semantic_content_wall  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as full_qm_closure  # noqa: E402
import scripts.evaluate_qm_inevitability_route as qm_inevitability  # noqa: E402
import scripts.verify_finite_qm_route as finite_qm_gate  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCQMOnePassClosureDraft.json"

Verdict = Literal[
    "CGSC_QM_FORMALLY_CLOSED",
    "STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL",
    "STRUCTURAL_ROUTE_BLOCKED",
    "FATAL_IMPORT_WALL",
    "DRAFT_INVALID",
]
PackageStatus = Literal[
    "CANDIDATE_EVIDENCED",
    "CANDIDATE_EVIDENCED_WITH_OPEN_RESIDUAL",
    "BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class EvidenceCheck:
    id: str
    expected: str
    observed: str
    status: CheckStatus


@dataclass(frozen=True)
class PackageCheck:
    id: str
    expected_status: PackageStatus
    status: PackageStatus
    evidence: list[EvidenceCheck]
    open_residuals: tuple[str, ...]


@dataclass(frozen=True)
class GlobalCheck:
    id: str
    expected: str
    observed: str
    status: CheckStatus


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class OnePassClosureProbe:
    verdict: Verdict
    proof_status: str
    draft_path: str
    global_checks_passed: int
    global_checks_failed: int
    packages: int
    package_evidenced: int
    package_open_residual: int
    package_blocked: int
    finite_gate_checks: int
    finite_gate_failures: int
    conditional_artifacts: int
    missing_formal_proof_artifacts: int
    open_residuals: tuple[str, ...]
    global_checks: list[GlobalCheck]
    package_checks: list[PackageCheck]
    draft_checks_passed: int
    draft_checks_failed: int
    draft_checks: list[DraftCheck]
    next_blocker: str


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a string")
    return value


def string_tuple(value: object, field: str) -> tuple[str, ...]:
    return tuple(require_string(item, f"{field}[]") for item in require_list(value, field))


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


def status_for(observed: str, expected: str) -> CheckStatus:
    if observed == expected:
        return "PASS"
    return "FAIL"


def load_draft(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, "draft")


def check_equals(name: str, actual: object, expected: object) -> DraftCheck:
    if actual == expected:
        return DraftCheck(name=name, passed=True, reason=f"{actual!r}")
    return DraftCheck(name=name, passed=False, reason=f"expected {expected!r}, got {actual!r}")


def check_set_equals(name: str, actual: tuple[str, ...], expected: tuple[str, ...]) -> DraftCheck:
    actual_set = set(actual)
    expected_set = set(expected)
    if actual_set == expected_set:
        return DraftCheck(name=name, passed=True, reason=f"count={len(actual_set)}")
    return DraftCheck(
        name=name,
        passed=False,
        reason=f"missing={sorted(expected_set - actual_set)}; extra={sorted(actual_set - expected_set)}",
    )


def existing_dependency_refs(dependencies: tuple[str, ...]) -> DraftCheck:
    missing = tuple(ref for ref in dependencies if not (REPO_ROOT / ref).exists())
    if not missing:
        return DraftCheck(name="dependency_refs_grounded", passed=True, reason=f"count={len(dependencies)}")
    return DraftCheck(name="dependency_refs_grounded", passed=False, reason=f"missing={','.join(missing)}")


def package_status_from_string(value: str, field: str) -> PackageStatus:
    if value == "CANDIDATE_EVIDENCED":
        return "CANDIDATE_EVIDENCED"
    if value == "CANDIDATE_EVIDENCED_WITH_OPEN_RESIDUAL":
        return "CANDIDATE_EVIDENCED_WITH_OPEN_RESIDUAL"
    if value == "BLOCKED":
        return "BLOCKED"
    raise ValueError(f"{field} is invalid: {value!r}")


def finite_gate_evidence() -> tuple[dict[str, finite_qm_gate.GateCheck], int]:
    checks = finite_qm_gate.build_checks()
    failures = sum(1 for check in checks if check.status == "FAIL")
    return {check.name: check for check in checks}, failures


def target_statuses(qm_probe: qm_inevitability.InevitabilityRouteProbe) -> dict[str, str]:
    return {f"qm_target.{check.id}": check.status for check in qm_probe.target_checks}


def evidence_check(evidence_id: str, gate_by_id: dict[str, finite_qm_gate.GateCheck], target_by_id: dict[str, str]) -> EvidenceCheck:
    gate = gate_by_id.get(evidence_id)
    if gate is not None:
        return EvidenceCheck(id=evidence_id, expected=gate.expected, observed=gate.observed, status=gate.status)
    target_status = target_by_id.get(evidence_id)
    if target_status is not None:
        expected = "CONDITIONAL_ROUTE_READY"
        return EvidenceCheck(
            id=evidence_id,
            expected=expected,
            observed=target_status,
            status=status_for(target_status, expected),
        )
    return EvidenceCheck(id=evidence_id, expected="KNOWN_EVIDENCE_REF", observed="MISSING_EVIDENCE_REF", status="FAIL")


def package_from_draft(
    raw_package: object,
    field: str,
    gate_by_id: dict[str, finite_qm_gate.GateCheck],
    target_by_id: dict[str, str],
) -> PackageCheck:
    package = require_mapping(raw_package, field)
    package_id = require_string(package.get("id"), f"{field}.id")
    expected_status = package_status_from_string(
        require_string(package.get("expected_status"), f"{field}.expected_status"),
        f"{field}.expected_status",
    )
    evidence_ids = string_tuple(package.get("evidence"), f"{field}.evidence")
    open_residuals = string_tuple(package.get("open_residuals"), f"{field}.open_residuals")
    evidence = [evidence_check(evidence_id, gate_by_id, target_by_id) for evidence_id in evidence_ids]
    if any(check.status == "FAIL" for check in evidence):
        status: PackageStatus = "BLOCKED"
    elif open_residuals:
        status = "CANDIDATE_EVIDENCED_WITH_OPEN_RESIDUAL"
    else:
        status = "CANDIDATE_EVIDENCED"
    return PackageCheck(
        id=package_id,
        expected_status=expected_status,
        status=status,
        evidence=evidence,
        open_residuals=open_residuals,
    )


def global_requirement_checks(
    attempt: dict[str, object],
    finite_gate_failures: int,
    extension_probe: extension_wall.ExtensionWallProbe,
    primitive_probe: primitive_derivation.PrimitiveDerivationProbe,
    bridge_probe: primitive_bridge.BridgeProbe,
    semantic_probe: semantic_content_wall.SemanticContentWallProbe,
    qm_probe: qm_inevitability.InevitabilityRouteProbe,
    full_probe: full_qm_closure.ClosureAttempt,
) -> list[GlobalCheck]:
    observed_by_id = {
        "finite_qm_route_gate": "PASS" if finite_gate_failures == 0 else "FAIL",
        "extension_wall_probe": extension_probe.verdict,
        "primitive_derivation": primitive_probe.verdict,
        "cgsc_primitive_bridge": bridge_probe.verdict,
        "cgsc_semantic_content_wall": semantic_probe.verdict,
        "qm_inevitability_route": qm_probe.verdict,
        "full_qm_proof_closure": full_probe.verdict,
    }
    checks: list[GlobalCheck] = []
    for index, raw_requirement in enumerate(require_list(attempt.get("global_requirements"), "attempt.global_requirements")):
        requirement = require_mapping(raw_requirement, f"attempt.global_requirements[{index}]")
        requirement_id = require_string(requirement.get("id"), f"attempt.global_requirements[{index}].id")
        expected = require_string(requirement.get("expected"), f"attempt.global_requirements[{index}].expected")
        observed = observed_by_id.get(requirement_id, "MISSING_GLOBAL_REQUIREMENT")
        checks.append(GlobalCheck(id=requirement_id, expected=expected, observed=observed, status=status_for(observed, expected)))
    return checks


def validate_draft(
    draft: dict[str, object],
    attempt: dict[str, object],
    verdict: Verdict,
    package_checks: list[PackageCheck],
    global_checks: list[GlobalCheck],
) -> list[DraftCheck]:
    dependencies = string_tuple(attempt.get("dependencies"), "attempt.dependencies")
    formal_requirements = string_tuple(attempt.get("formal_closure_requirements"), "attempt.formal_closure_requirements")
    forbidden_claims = string_tuple(attempt.get("forbidden_claims"), "attempt.forbidden_claims")
    required_formal_requirements = (
        "CGSC_DERIVED_FROM_PRIMITIVES",
        "FULL_QM_PROVED",
        "machine_checked_proof_artifacts_for_all_qm_obligations",
    )
    required_forbidden = (
        "does_not_claim_CGSC_is_proved",
        "does_not_claim_full_QM_is_proved",
        "does_not_mark_conditional_routes_as_formal_proof",
        "does_not_import_Hilbert_Born_unitary_tensor_or_Stone",
        "does_not_treat_residual_rejection_as_full_QM_proof",
    )
    declared_package_statuses = tuple(f"{check.id}:{check.expected_status}" for check in package_checks)
    observed_package_statuses = tuple(f"{check.id}:{check.status}" for check in package_checks)
    declared_global_checks = tuple(f"{check.id}:{check.expected}" for check in global_checks)
    observed_global_checks = tuple(f"{check.id}:{check.observed}" for check in global_checks)
    return [
        check_equals("artifact_status", draft.get("artifact_status"), "one_pass_closure_attempt_not_formal_proof"),
        check_equals("attempt_id", attempt.get("id"), "cgsc_qm_one_pass_closure"),
        check_equals("expected_verdict", attempt.get("expected_verdict"), verdict),
        existing_dependency_refs(dependencies),
        check_set_equals("package_statuses", observed_package_statuses, declared_package_statuses),
        check_set_equals("global_requirements", observed_global_checks, declared_global_checks),
        check_set_equals("formal_closure_requirements", formal_requirements, required_formal_requirements),
        check_set_equals("forbidden_claims", forbidden_claims, required_forbidden),
    ]


def build_probe(draft_path: Path = DEFAULT_DRAFT) -> OnePassClosureProbe:
    draft = load_draft(draft_path)
    attempt = require_mapping(draft.get("attempt"), "attempt")
    gate_by_id, finite_gate_failures = finite_gate_evidence()
    extension_probe = extension_wall.build_probe()
    primitive_probe = primitive_derivation.build_probe()
    bridge_probe = primitive_bridge.build_probe()
    semantic_probe = semantic_content_wall.build_probe()
    qm_probe = qm_inevitability.build_probe()
    full_probe = full_qm_closure.build_closure_attempt()
    target_by_id = target_statuses(qm_probe)
    package_checks = [
        package_from_draft(raw_package, f"attempt.packages[{index}]", gate_by_id, target_by_id)
        for index, raw_package in enumerate(require_list(attempt.get("packages"), "attempt.packages"))
    ]
    global_checks = global_requirement_checks(
        attempt=attempt,
        finite_gate_failures=finite_gate_failures,
        extension_probe=extension_probe,
        primitive_probe=primitive_probe,
        bridge_probe=bridge_probe,
        semantic_probe=semantic_probe,
        qm_probe=qm_probe,
        full_probe=full_probe,
    )
    global_failures = sum(1 for check in global_checks if check.status == "FAIL")
    package_blocked = sum(1 for check in package_checks if check.status == "BLOCKED")
    open_residuals: set[str] = set()
    for check in package_checks:
        open_residuals.update(check.open_residuals)
    if extension_probe.fatal_imports:
        verdict: Verdict = "FATAL_IMPORT_WALL"
    elif primitive_probe.verdict == "CGSC_DERIVED_FROM_PRIMITIVES" and full_probe.verdict == "FULL_QM_PROVED":
        verdict = "CGSC_QM_FORMALLY_CLOSED"
    elif global_failures == 0 and package_blocked == 0:
        verdict = "STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL"
    else:
        verdict = "STRUCTURAL_ROUTE_BLOCKED"
    draft_checks = validate_draft(draft, attempt, verdict, package_checks, global_checks)
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    if draft_failed > 0:
        verdict = "DRAFT_INVALID"
    package_open_residual = sum(1 for check in package_checks if check.status == "CANDIDATE_EVIDENCED_WITH_OPEN_RESIDUAL")
    return OnePassClosureProbe(
        verdict=verdict,
        proof_status="not_formal_proof" if verdict != "CGSC_QM_FORMALLY_CLOSED" else "formal_proof",
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        global_checks_passed=sum(1 for check in global_checks if check.status == "PASS"),
        global_checks_failed=global_failures,
        packages=len(package_checks),
        package_evidenced=sum(1 for check in package_checks if check.status == "CANDIDATE_EVIDENCED"),
        package_open_residual=package_open_residual,
        package_blocked=package_blocked,
        finite_gate_checks=len(gate_by_id),
        finite_gate_failures=finite_gate_failures,
        conditional_artifacts=full_probe.conditional_artifacts,
        missing_formal_proof_artifacts=full_probe.missing_artifacts + full_probe.sketch_artifacts + full_probe.incomplete_artifacts,
        open_residuals=sorted_tuple(open_residuals),
        global_checks=global_checks,
        package_checks=package_checks,
        draft_checks_passed=sum(1 for check in draft_checks if check.passed),
        draft_checks_failed=draft_failed,
        draft_checks=draft_checks,
        next_blocker=(
            "derive the source kernel directly from primitive-generated admissibility; "
            "the finite-sector residual is rejected by admissibility, not a substitute for full-QM proof"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="One-pass CGSC/QM closure attempt across the current broad route.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-global", action="store_true")
    parser.add_argument("--show-packages", action="store_true")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)))
    print(
        f"cgsc_qm_one_pass_closure={probe.verdict} proof_status={probe.proof_status} "
        f"global_failed={probe.global_checks_failed} packages={probe.packages} "
        f"package_evidenced={probe.package_evidenced} package_open_residual={probe.package_open_residual} "
        f"package_blocked={probe.package_blocked} finite_gate_failures={probe.finite_gate_failures} "
        f"conditional_artifacts={probe.conditional_artifacts} "
        f"missing_formal_proof_artifacts={probe.missing_formal_proof_artifacts} "
        f"open_residuals={len(probe.open_residuals)} draft_checks_failed={probe.draft_checks_failed}"
    )
    if probe.open_residuals:
        print(f"OPEN_RESIDUALS {','.join(probe.open_residuals)}")
    print(f"NEXT {probe.next_blocker}")
    if args.show_global:
        for check in probe.global_checks:
            print(f"{check.status} {check.id}: observed={check.observed} expected={check.expected}")
    if args.show_packages:
        for package in probe.package_checks:
            print(f"{package.status} {package.id}: open_residuals={','.join(package.open_residuals) or '-'}")
            for evidence in package.evidence:
                print(f"  {evidence.status} {evidence.id}: observed={evidence.observed} expected={evidence.expected}")
    if args.show_draft_checks:
        for draft_check in probe.draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("FATAL_IMPORT_WALL", "STRUCTURAL_ROUTE_BLOCKED", "DRAFT_INVALID"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
