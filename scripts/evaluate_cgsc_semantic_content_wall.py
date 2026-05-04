from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCSemanticContentWallDraft.json"

Verdict = Literal[
    "SEMANTIC_CONTENT_WALL_DETECTED",
    "LEAN_CHECK_FAILED",
    "WALL_DRAFT_INVALID",
]
CheckStatus = Literal["PASS", "FAIL"]

EXPECTED_EXTENSION_WITNESSES = (
    "coherent_refinement_compactness",
    "complete_exposed_context_partition",
    "generator_bookkeeping_without_stone",
    "no_hidden_joint_only_generation",
    "product_context_generation_closure",
    "reversible_context_automorphism_closure",
)
REQUIRED_FORBIDDEN_CLAIMS = (
    "does_not_prove_CGSC",
    "does_not_prove_full_QM_I",
    "does_not_treat_checked_prop_packaging_as_semantic_content",
    "does_not_mark_vacuous_bridge_as_formal_proof",
    "does_not_claim_extensions_are_proved_from_B0",
)
CHECKER_COMMAND = "lake build Proofs.QMClosure.CGSCSemanticContentWall"


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class SemanticContentWallProbe:
    verdict: Verdict
    draft_path: str
    lean_file: str
    extension_witnesses: int
    draft_checks_failed: int
    lean_check: LeanCheck
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


def run_lean_check(command: str) -> LeanCheck:
    if command != CHECKER_COMMAND:
        return LeanCheck(command=command, returncode=2, status="FAIL")
    completed = subprocess.run(
        shlex.split(command),
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    status: CheckStatus = "PASS" if completed.returncode == 0 else "FAIL"
    return LeanCheck(command=command, returncode=completed.returncode, status=status)


def validate_draft(draft: dict[str, object], wall: dict[str, object]) -> list[DraftCheck]:
    return [
        check_equals("artifact_status", draft.get("artifact_status"), "semantic_content_wall_not_formal_proof"),
        check_equals("wall_id", wall.get("id"), "cgsc_semantic_content_wall"),
        check_equals("expected_verdict", wall.get("expected_verdict"), "SEMANTIC_CONTENT_WALL_DETECTED"),
        check_equals("proof_status", wall.get("proof_status"), "blocked"),
        check_equals("lean_file", wall.get("lean_file"), "Proofs/QMClosure/CGSCSemanticContentWall.lean"),
        check_equals("checker_command", wall.get("checker_command"), CHECKER_COMMAND),
        existing_dependency_refs(string_tuple(wall.get("dependencies"), "wall.dependencies")),
        check_set_equals(
            "extension_witnesses",
            string_tuple(wall.get("extension_witnesses"), "wall.extension_witnesses"),
            EXPECTED_EXTENSION_WITNESSES,
        ),
        check_equals(
            "degenerate_witness",
            wall.get("degenerate_witness"),
            "currentBridgeAdmitsDegenerateExtensionBase",
        ),
        check_equals(
            "required_fix",
            wall.get("required_fix"),
            "replace unconstrained CheckedProp extension fields with typed semantic predicates and no-vacuity obligations before any formal proof upgrade",
        ),
        check_set_equals(
            "forbidden_claims",
            string_tuple(wall.get("forbidden_claims"), "wall.forbidden_claims"),
            REQUIRED_FORBIDDEN_CLAIMS,
        ),
    ]


def build_probe(draft_path: Path = DEFAULT_DRAFT) -> SemanticContentWallProbe:
    draft = load_draft(draft_path)
    wall = require_mapping(draft.get("wall"), "wall")
    draft_checks = validate_draft(draft, wall)
    lean_check = run_lean_check(require_string(wall.get("checker_command"), "wall.checker_command"))
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    if draft_failed > 0:
        verdict: Verdict = "WALL_DRAFT_INVALID"
    elif lean_check.status == "FAIL":
        verdict = "LEAN_CHECK_FAILED"
    else:
        verdict = "SEMANTIC_CONTENT_WALL_DETECTED"
    return SemanticContentWallProbe(
        verdict=verdict,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        lean_file=require_string(wall.get("lean_file"), "wall.lean_file"),
        extension_witnesses=len(string_tuple(wall.get("extension_witnesses"), "wall.extension_witnesses")),
        draft_checks_failed=draft_failed,
        lean_check=lean_check,
        draft_checks=draft_checks,
        next_blocker=(
            "add typed semantic predicates and no-vacuity obligations for the six extension witnesses; "
            "until then the bridge is schematic rather than a primitive proof route"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Detect whether the CGSC primitive bridge still admits vacuous extension witnesses.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)))
    print(
        f"cgsc_semantic_content_wall={probe.verdict} lean={probe.lean_check.status} "
        f"extension_witnesses={probe.extension_witnesses} draft_checks_failed={probe.draft_checks_failed}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.show_draft_checks:
        for draft_check in probe.draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict != "SEMANTIC_CONTENT_WALL_DETECTED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
