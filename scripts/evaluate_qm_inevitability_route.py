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

import scripts.evaluate_born_readout_attempt as born_attempt  # noqa: E402
import scripts.evaluate_cgsc_primitive_derivation as cgsc_primitive  # noqa: E402
import scripts.evaluate_context_generated_stable_closure_route_draft as cgsc_route  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as proof_closure  # noqa: E402
import scripts.evaluate_general_composite_attempt as composite_attempt  # noqa: E402
import scripts.evaluate_representation_classification_attempt as representation_attempt  # noqa: E402
import scripts.evaluate_unitary_dynamics_attempt as dynamics_attempt  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/QMInevitabilityRouteDraft.json"
EXPECTED_ARTIFACT_STATUS = "route_draft_not_formal_proof"
EXPECTED_THEOREM_ID = "hilbert_born_unitary_tensor_follow_from_primitives_route"
EXPECTED_ROUTE_ID = "qm_inevitability_proof_route"
EXPECTED_ROUTE_STATUS = "open"
EXPECTED_PROOF_STATUS = "open"
EXPECTED_TARGET_STATUS = "conditional_route_ready"
TARGET_IDS = ("hilbert_representation", "born_readout", "unitary_dynamics", "tensor_composition")

Verdict = Literal[
    "INEVITABILITY_PROVED",
    "CONDITIONAL_INEVITABILITY_ROUTE_VALIDATED",
    "ROUTE_DRAFT_INVALID",
    "TARGET_ROUTE_NOT_READY",
    "TARGET_IMPORT_REJECTED",
]
ProofStatus = Literal[
    "FORMAL_PROOF",
    "OPEN_PRIMITIVE_CLAUSE_PROOFS_MISSING",
    "OPEN_TARGET_PROOF_ARTIFACTS_MISSING",
    "OPEN_ROUTE_DRAFT_INVALID",
]
TargetStatus = Literal["CONDITIONAL_ROUTE_READY", "OPEN", "FAILED", "IMPORT_REJECTED"]


@dataclass(frozen=True)
class TargetSpec:
    id: str
    structure: str
    expected_live_route: str
    route_script: str
    required_clauses: tuple[str, ...]
    proof_obligations: tuple[str, ...]


@dataclass(frozen=True)
class TargetCheck:
    id: str
    structure: str
    status: TargetStatus
    live_route_verdict: str
    imports: tuple[str, ...]
    missing_clause_proofs: tuple[str, ...]
    missing_proof_artifacts: tuple[str, ...]
    open_gap: str


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class InevitabilityRouteProbe:
    verdict: Verdict
    proof_status: ProofStatus
    draft_path: str
    cgsc_route_draft: str
    cgsc_primitive_derivation: cgsc_primitive.Verdict
    full_qm_closure: proof_closure.ClosureVerdict
    targets: int
    conditional_targets: int
    open_targets: int
    failed_targets: int
    imported_targets: int
    missing_clause_proofs: int
    missing_proof_artifacts: int
    missing_base_extensions: tuple[str, ...]
    draft_checks_passed: int
    draft_checks_failed: int
    target_checks: list[TargetCheck]
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


def find_representation_route(route_name: str) -> representation_attempt.RouteResult:
    for route in representation_attempt.ROUTES:
        if route.name == route_name:
            return representation_attempt.evaluate_route(route)
    raise ValueError(f"unknown representation route {route_name!r}")


def find_born_route(route_name: str) -> born_attempt.RouteResult:
    for route in born_attempt.ROUTES:
        if route.name == route_name:
            return born_attempt.evaluate_route(route)
    raise ValueError(f"unknown Born route {route_name!r}")


def find_dynamics_route(route_name: str) -> dynamics_attempt.RouteResult:
    for route in dynamics_attempt.ROUTES:
        if route.name == route_name:
            return dynamics_attempt.evaluate_route(route)
    raise ValueError(f"unknown dynamics route {route_name!r}")


def find_composite_route(route_name: str) -> composite_attempt.RouteResult:
    for route in composite_attempt.ROUTES:
        if route.name == route_name:
            return composite_attempt.evaluate_route(route)
    raise ValueError(f"unknown composite route {route_name!r}")


def live_route_verdict(target_id: str) -> tuple[str, tuple[str, ...]]:
    if target_id == "hilbert_representation":
        representation_result = find_representation_route("spectral_symmetry_route")
        return representation_result.verdict, representation_result.imports
    if target_id == "born_readout":
        born_result = find_born_route("quadratic_context_probability_route")
        return born_result.verdict, born_result.imports
    if target_id == "unitary_dynamics":
        dynamics_result = find_dynamics_route("continuous_generator_route")
        return dynamics_result.verdict, dynamics_result.imports
    if target_id == "tensor_composition":
        composite_result = find_composite_route("general_projective_composite_route")
        return composite_result.verdict, composite_result.imports
    raise ValueError(f"unknown target id {target_id!r}")


def target_specs_from_draft(proof_route: dict[str, object]) -> list[TargetSpec]:
    targets = require_list(proof_route.get("targets"), "proof_route.targets")
    specs: list[TargetSpec] = []
    for index, raw_target in enumerate(targets):
        target = require_mapping(raw_target, f"proof_route.targets[{index}]")
        specs.append(
            TargetSpec(
                id=require_string(target.get("id"), f"proof_route.targets[{index}].id"),
                structure=require_string(target.get("structure"), f"proof_route.targets[{index}].structure"),
                expected_live_route=require_string(
                    target.get("expected_live_route"),
                    f"proof_route.targets[{index}].expected_live_route",
                ),
                route_script=require_string(target.get("route_script"), f"proof_route.targets[{index}].route_script"),
                required_clauses=string_tuple(
                    target.get("required_clauses"),
                    f"proof_route.targets[{index}].required_clauses",
                ),
                proof_obligations=string_tuple(
                    target.get("proof_obligations"),
                    f"proof_route.targets[{index}].proof_obligations",
                ),
            )
        )
    return specs


def clause_statuses_from_cgsc_route() -> dict[str, str]:
    draft = cgsc_route.load_draft(cgsc_route.DEFAULT_DRAFT)
    proof_route = require_mapping(draft.get("proof_route"), "cgsc.proof_route")
    clauses = require_list(proof_route.get("clauses"), "cgsc.proof_route.clauses")
    statuses: dict[str, str] = {}
    for index, raw_clause in enumerate(clauses):
        clause = require_mapping(raw_clause, f"cgsc.proof_route.clauses[{index}]")
        statuses[require_string(clause.get("id"), "clause.id")] = require_string(clause.get("status"), "clause.status")
    return statuses


def proof_statuses_from_closure(closure: proof_closure.ClosureAttempt) -> dict[str, str]:
    return {check.id: check.status for check in closure.checks}


def check_target(spec: TargetSpec, clause_status_by_id: dict[str, str], proof_status_by_id: dict[str, str]) -> TargetCheck:
    verdict, imports = live_route_verdict(spec.id)
    missing_clause_proofs = tuple(
        clause_id for clause_id in spec.required_clauses if clause_status_by_id.get(clause_id) != "formal_proof"
    )
    missing_artifacts = tuple(
        obligation_id for obligation_id in spec.proof_obligations if proof_status_by_id.get(obligation_id) != "PROVED"
    )
    if imports:
        status: TargetStatus = "IMPORT_REJECTED"
    elif verdict == spec.expected_live_route:
        status = "CONDITIONAL_ROUTE_READY"
    elif verdict.endswith("HIT"):
        status = "FAILED"
    else:
        status = "OPEN"
    if missing_clause_proofs:
        open_gap = "required CGSC clauses are not formal proofs from primitives"
    elif missing_artifacts:
        open_gap = "required full-QM proof artifacts are not registered as PROVED"
    else:
        open_gap = "-"
    return TargetCheck(
        id=spec.id,
        structure=spec.structure,
        status=status,
        live_route_verdict=verdict,
        imports=imports,
        missing_clause_proofs=missing_clause_proofs,
        missing_proof_artifacts=missing_artifacts,
        open_gap=open_gap,
    )


def draft_target_statuses(proof_route: dict[str, object]) -> tuple[str, ...]:
    targets = require_list(proof_route.get("targets"), "proof_route.targets")
    return tuple(
        require_string(require_mapping(target, "proof_route.targets[]").get("expected_status"), "target.expected_status")
        for target in targets
    )


def validate_draft(
    draft: dict[str, object],
    target_specs: list[TargetSpec],
    cgsc_probe: cgsc_route.RouteDraftProbe,
) -> list[DraftCheck]:
    theorem_card = require_mapping(draft.get("theorem_card"), "theorem_card")
    proof_route = require_mapping(draft.get("proof_route"), "proof_route")
    dependencies = string_tuple(theorem_card.get("dependencies"), "theorem_card.dependencies")
    known_failures = string_tuple(theorem_card.get("known_failures"), "theorem_card.known_failures")
    forbidden_claims = string_tuple(theorem_card.get("forbidden_claims"), "theorem_card.forbidden_claims")
    required_failures = (
        "context_generated_stable_closure_clauses_not_proved_from_primitives",
        "cgsc_primitive_derivation_not_closed",
        "full_qm_proof_closure_remains_proof_artifacts_missing",
        "no_machine_checked_formal_proof_for_hilbert_born_unitary_tensor",
        "physical_hbar_I_not_derived",
    )
    required_forbidden = (
        "does_not_prove_full_QM_I",
        "does_not_import_Hilbert_Born_unitary_tensor_or_Stone",
        "does_not_treat_route_draft_as_formal_proof",
    )
    return [
        check_equals("artifact_status", draft.get("artifact_status"), EXPECTED_ARTIFACT_STATUS),
        check_equals("theorem_id", theorem_card.get("id"), EXPECTED_THEOREM_ID),
        check_equals("proof_status", theorem_card.get("proof_status"), EXPECTED_PROOF_STATUS),
        check_equals("verifier", theorem_card.get("verifier"), "scripts/evaluate_qm_inevitability_route.py"),
        existing_dependency_refs(dependencies),
        check_set_equals("known_failures", known_failures, required_failures),
        check_set_equals("required_forbidden_claims", tuple(item for item in forbidden_claims if item in required_forbidden), required_forbidden),
        check_equals("proof_route_id", proof_route.get("id"), EXPECTED_ROUTE_ID),
        check_equals("target_theorem", proof_route.get("target_theorem"), EXPECTED_THEOREM_ID),
        check_equals("expected_route_status", proof_route.get("expected_route_status"), EXPECTED_ROUTE_STATUS),
        check_set_equals("target_ids", tuple(spec.id for spec in target_specs), TARGET_IDS),
        check_set_equals("target_expected_statuses", tuple(set(draft_target_statuses(proof_route))), (EXPECTED_TARGET_STATUS,)),
        check_equals("cgsc_route_draft", cgsc_probe.verdict, "ROUTE_DRAFT_VALIDATED"),
    ]


def build_probe(
    draft_path: Path = DEFAULT_DRAFT,
    manifest_path: Path = proof_closure.DEFAULT_MANIFEST,
) -> InevitabilityRouteProbe:
    draft = load_draft(draft_path)
    proof_route = require_mapping(draft.get("proof_route"), "proof_route")
    target_specs = target_specs_from_draft(proof_route)
    cgsc_probe = cgsc_route.build_probe(cgsc_route.DEFAULT_DRAFT, manifest_path)
    primitive_probe = cgsc_primitive.build_probe()
    closure = proof_closure.build_closure_attempt(manifest_path)
    clause_status_by_id = clause_statuses_from_cgsc_route()
    proof_status_by_id = proof_statuses_from_closure(closure)
    target_checks = [check_target(spec, clause_status_by_id, proof_status_by_id) for spec in target_specs]
    draft_checks = validate_draft(draft, target_specs, cgsc_probe)
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    conditional_targets = sum(1 for check in target_checks if check.status == "CONDITIONAL_ROUTE_READY")
    open_targets = sum(1 for check in target_checks if check.status == "OPEN")
    failed_targets = sum(1 for check in target_checks if check.status == "FAILED")
    imported_targets = sum(1 for check in target_checks if check.status == "IMPORT_REJECTED")
    missing_clause_proofs = sum(len(check.missing_clause_proofs) for check in target_checks)
    missing_proof_artifacts = sum(len(check.missing_proof_artifacts) for check in target_checks)
    if draft_failed > 0:
        verdict: Verdict = "ROUTE_DRAFT_INVALID"
        proof_status: ProofStatus = "OPEN_ROUTE_DRAFT_INVALID"
    elif imported_targets > 0:
        verdict = "TARGET_IMPORT_REJECTED"
        proof_status = "OPEN_TARGET_PROOF_ARTIFACTS_MISSING"
    elif failed_targets > 0 or open_targets > 0:
        verdict = "TARGET_ROUTE_NOT_READY"
        proof_status = "OPEN_TARGET_PROOF_ARTIFACTS_MISSING"
    elif missing_clause_proofs == 0 and missing_proof_artifacts == 0:
        verdict = "INEVITABILITY_PROVED"
        proof_status = "FORMAL_PROOF"
    else:
        verdict = "CONDITIONAL_INEVITABILITY_ROUTE_VALIDATED"
        proof_status = (
            "OPEN_PRIMITIVE_CLAUSE_PROOFS_MISSING"
            if missing_clause_proofs > 0
            else "OPEN_TARGET_PROOF_ARTIFACTS_MISSING"
        )
    return InevitabilityRouteProbe(
        verdict=verdict,
        proof_status=proof_status,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        cgsc_route_draft=cgsc_probe.verdict,
        cgsc_primitive_derivation=primitive_probe.verdict,
        full_qm_closure=closure.verdict,
        targets=len(target_checks),
        conditional_targets=conditional_targets,
        open_targets=open_targets,
        failed_targets=failed_targets,
        imported_targets=imported_targets,
        missing_clause_proofs=missing_clause_proofs,
        missing_proof_artifacts=missing_proof_artifacts,
        missing_base_extensions=primitive_probe.missing_base_extensions,
        draft_checks_passed=sum(1 for check in draft_checks if check.passed),
        draft_checks_failed=draft_failed,
        target_checks=target_checks,
        draft_checks=draft_checks,
        next_blocker=(
            "close CGSC primitive derivation, including missing base extensions, then promote the required "
            "full-QM obligations to machine-checkable proof artifacts"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Validate the broad route that Hilbert/Born/unitary/tensor follow from IDT primitives."
    )
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--manifest", default=str(proof_closure.DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-targets", action="store_true")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)), Path(str(args.manifest)))
    print(
        f"qm_inevitability_route={probe.verdict} proof_status={probe.proof_status} "
        f"draft={probe.draft_path} cgsc_route_draft={probe.cgsc_route_draft} "
        f"cgsc_primitive_derivation={probe.cgsc_primitive_derivation} "
        f"full_qm_closure={probe.full_qm_closure} targets={probe.targets} "
        f"conditional_targets={probe.conditional_targets} open_targets={probe.open_targets} "
        f"failed_targets={probe.failed_targets} imported_targets={probe.imported_targets} "
        f"missing_clause_proofs={probe.missing_clause_proofs} "
        f"missing_proof_artifacts={probe.missing_proof_artifacts} "
        f"missing_base_extensions={len(probe.missing_base_extensions)} "
        f"draft_checks_failed={probe.draft_checks_failed}"
    )
    if probe.missing_base_extensions:
        print(f"MISSING_EXTENSIONS {','.join(probe.missing_base_extensions)}")
    print(f"NEXT {probe.next_blocker}")
    if args.show_targets:
        for target_check in probe.target_checks:
            print(
                f"{target_check.status} {target_check.id}: route={target_check.live_route_verdict} "
                f"missing_clause_proofs={len(target_check.missing_clause_proofs)} "
                f"missing_artifacts={len(target_check.missing_proof_artifacts)} gap={target_check.open_gap}"
            )
    if args.show_draft_checks:
        for draft_check in probe.draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("ROUTE_DRAFT_INVALID", "TARGET_IMPORT_REJECTED", "TARGET_ROUTE_NOT_READY"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
