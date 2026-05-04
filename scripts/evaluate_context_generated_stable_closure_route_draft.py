from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_context_generated_stable_closure as cgsc  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as proof_closure  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/ContextGeneratedStableClosureRouteDraft.json"
EXPECTED_THEOREM_ID = "context_generated_stable_closure_conditionally_covers_qm_structural_walls"
EXPECTED_ROUTE_ID = "context_generated_stable_closure_proof_route"
EXPECTED_ARTIFACT_STATUS = "route_draft_not_formal_proof"
EXPECTED_ROUTE_STATUS = "open"
EXPECTED_CLAUSE_STATUS = "candidate_clause"
EXPECTED_PROOF_STATUS = "open"


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class RouteDraftProbe:
    verdict: str
    draft_path: str
    contract_verdict: cgsc.Verdict
    checks_passed: int
    checks_failed: int
    checks: list[DraftCheck]


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
    missing = sorted(expected_set - actual_set)
    extra = sorted(actual_set - expected_set)
    return DraftCheck(name=name, passed=False, reason=f"missing={missing}; extra={extra}")


def existing_dependency_refs(dependencies: tuple[str, ...]) -> DraftCheck:
    missing = tuple(ref for ref in dependencies if not (REPO_ROOT / ref).exists())
    if not missing:
        return DraftCheck(name="dependency_refs_grounded", passed=True, reason=f"count={len(dependencies)}")
    return DraftCheck(name="dependency_refs_grounded", passed=False, reason=f"missing={','.join(missing)}")


def clause_ids_from_draft(proof_route: dict[str, object]) -> tuple[str, ...]:
    clauses = require_list(proof_route.get("clauses"), "proof_route.clauses")
    return tuple(require_string(require_mapping(clause, "proof_route.clauses[]").get("id"), "clause.id") for clause in clauses)


def clause_statuses_from_draft(proof_route: dict[str, object]) -> tuple[str, ...]:
    clauses = require_list(proof_route.get("clauses"), "proof_route.clauses")
    return tuple(
        require_string(require_mapping(clause, "proof_route.clauses[]").get("status"), "clause.status")
        for clause in clauses
    )


def clause_grounding_refs_from_draft(proof_route: dict[str, object]) -> tuple[str, ...]:
    refs: list[str] = []
    clauses = require_list(proof_route.get("clauses"), "proof_route.clauses")
    for clause in clauses:
        clause_map = require_mapping(clause, "proof_route.clauses[]")
        refs.extend(string_tuple(clause_map.get("primitive_grounding"), "clause.primitive_grounding"))
    return tuple(refs)


def check_clause_grounding(proof_route: dict[str, object], contract_probe: cgsc.CandidateProbe) -> DraftCheck:
    declared_refs = set(clause_grounding_refs_from_draft(proof_route))
    expected_refs: set[str] = set()
    for clause in contract_probe.clauses:
        expected_refs.update(clause.primitive_grounding)
    if expected_refs.issubset(declared_refs):
        return DraftCheck(name="clause_primitive_grounding", passed=True, reason=f"refs={len(declared_refs)}")
    return DraftCheck(
        name="clause_primitive_grounding",
        passed=False,
        reason=f"missing={sorted(expected_refs - declared_refs)}",
    )


def check_forbidden_claims(theorem_card: dict[str, object], contract_probe: cgsc.CandidateProbe) -> DraftCheck:
    declared = set(string_tuple(theorem_card.get("forbidden_claims"), "theorem_card.forbidden_claims"))
    expected = set(contract_probe.forbidden_upgrade)
    if expected.issubset(declared):
        return DraftCheck(name="forbidden_claims", passed=True, reason=f"count={len(declared)}")
    return DraftCheck(name="forbidden_claims", passed=False, reason=f"missing={sorted(expected - declared)}")


def check_known_failures(theorem_card: dict[str, object]) -> DraftCheck:
    failures = set(string_tuple(theorem_card.get("known_failures"), "theorem_card.known_failures"))
    required = {
        "clauses_not_proved_from_primitives",
        "no_machine_checked_formal_proof",
        "full_qm_proof_closure_remains_proof_artifacts_missing",
    }
    if required.issubset(failures):
        return DraftCheck(name="known_failures", passed=True, reason=f"count={len(failures)}")
    return DraftCheck(name="known_failures", passed=False, reason=f"missing={sorted(required - failures)}")


def build_probe(
    draft_path: Path = DEFAULT_DRAFT,
    manifest_path: Path = proof_closure.DEFAULT_MANIFEST,
) -> RouteDraftProbe:
    draft = load_draft(draft_path)
    theorem_card = require_mapping(draft.get("theorem_card"), "theorem_card")
    proof_route = require_mapping(draft.get("proof_route"), "proof_route")
    contract_probe = cgsc.build_probe(manifest_path)
    expected_clause_ids = tuple(clause.id for clause in contract_probe.clauses)
    expected_targets = tuple(check.id for check in contract_probe.target_checks)
    expected_controls = tuple(check.id for check in contract_probe.control_checks)
    dependencies = string_tuple(theorem_card.get("dependencies"), "theorem_card.dependencies")
    checks = [
        check_equals("artifact_status", draft.get("artifact_status"), EXPECTED_ARTIFACT_STATUS),
        check_equals("theorem_id", theorem_card.get("id"), EXPECTED_THEOREM_ID),
        check_equals("proof_status", theorem_card.get("proof_status"), EXPECTED_PROOF_STATUS),
        check_equals("verifier", theorem_card.get("verifier"), "scripts/evaluate_context_generated_stable_closure.py"),
        existing_dependency_refs(dependencies),
        check_forbidden_claims(theorem_card, contract_probe),
        check_known_failures(theorem_card),
        check_equals("proof_route_id", proof_route.get("id"), EXPECTED_ROUTE_ID),
        check_equals("target_theorem", proof_route.get("target_theorem"), EXPECTED_THEOREM_ID),
        check_equals("expected_route_status", proof_route.get("expected_route_status"), EXPECTED_ROUTE_STATUS),
        check_set_equals("clause_ids", clause_ids_from_draft(proof_route), expected_clause_ids),
        check_set_equals(
            "clause_statuses",
            tuple(set(clause_statuses_from_draft(proof_route))),
            (EXPECTED_CLAUSE_STATUS,),
        ),
        check_clause_grounding(proof_route, contract_probe),
        check_set_equals("targets", string_tuple(proof_route.get("targets"), "proof_route.targets"), expected_targets),
        check_set_equals(
            "negative_controls",
            string_tuple(proof_route.get("negative_controls"), "proof_route.negative_controls"),
            expected_controls,
        ),
        check_equals(
            "contract_verdict",
            contract_probe.verdict,
            "CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE",
        ),
    ]
    passed = sum(1 for check in checks if check.passed)
    failed = len(checks) - passed
    verdict = "ROUTE_DRAFT_VALIDATED" if failed == 0 else "ROUTE_DRAFT_INVALID"
    return RouteDraftProbe(
        verdict=verdict,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        contract_verdict=contract_probe.verdict,
        checks_passed=passed,
        checks_failed=failed,
        checks=checks,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate the context-generated stable closure theorem-card/proof-route draft.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--manifest", default=str(proof_closure.DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)), Path(str(args.manifest)))
    print(
        f"context_generated_stable_closure_route_draft={probe.verdict} "
        f"draft={probe.draft_path} contract={probe.contract_verdict} "
        f"checks_passed={probe.checks_passed} checks_failed={probe.checks_failed}"
    )
    if args.show_checks:
        for check in probe.checks:
            status = "PASS" if check.passed else "FAIL"
            print(f"{status} {check.name}: {check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.checks_failed > 0:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
