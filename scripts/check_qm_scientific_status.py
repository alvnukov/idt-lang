from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts import evaluate_born_direct_one_pass as born_direct  # noqa: E402
from scripts import evaluate_cgsc_qm_one_pass_closure as cgsc_qm_closure  # noqa: E402
from scripts import evaluate_full_qm_proof_closure as full_qm_closure  # noqa: E402
from scripts import evaluate_qm_direct_one_pass as qm_direct  # noqa: E402

DEFAULT_MANIFEST = REPO_ROOT / "theory_verifier_manifest.json"
DEFAULT_README = REPO_ROOT / "README.md"
DEFAULT_WORKFLOW = REPO_ROOT / ".github/workflows/qm-status.yml"

EXPECTED_BORN_VERDICT = "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF"
EXPECTED_QM_VERDICT = "DIRECT_FINITE_QM_ROUTE_HIT_UNIVERSAL_QM_OPEN"
EXPECTED_CGSC_VERDICT = "STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL"
EXPECTED_BADGE_TOKEN = "QM-conditional_structural_route__formalization_wall-yellow"

WORKFLOW_PROBE_SCRIPTS = (
    "scripts/evaluate_born_direct_one_pass.py",
    "scripts/evaluate_qm_direct_one_pass.py",
    "scripts/evaluate_cgsc_qm_one_pass_closure.py",
)
WORKFLOW_GUARD_SCRIPT = "scripts/check_qm_scientific_status.py"

FULL_QM_UPGRADED_SYMBOL_STATUSES = frozenset(
    {
        "derived",
        "derived_conditional",
        "formal_proof",
        "proved",
        "FULL_QM_PROVED",
    }
)
FULL_QM_FORMAL_PROOF_STATUS = "formal_proof"


@dataclass(frozen=True)
class GuardCheck:
    name: str
    passed: bool
    detail: str


def pass_check(name: str, detail: str) -> GuardCheck:
    return GuardCheck(name=name, passed=True, detail=detail)


def fail_check(name: str, detail: str) -> GuardCheck:
    return GuardCheck(name=name, passed=False, detail=detail)


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def optional_string(value: object) -> str | None:
    if isinstance(value, str):
        return value
    return None


def load_manifest(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, "manifest")


def check_expected_verdict(name: str, observed: str, expected: str) -> GuardCheck:
    if observed == expected:
        return pass_check(name, observed)
    return fail_check(name, f"expected {expected}, got {observed}")


def check_readme_badge(readme_text: str) -> GuardCheck:
    if EXPECTED_BADGE_TOKEN in readme_text:
        return pass_check("readme.qm_status_badge", EXPECTED_BADGE_TOKEN)
    return fail_check("readme.qm_status_badge", f"missing {EXPECTED_BADGE_TOKEN}")


def python_script_line(workflow_text: str, script_path: str) -> int | None:
    pattern = re.compile(rf"\bpython3?\s+{re.escape(script_path)}(?:\s|$)")
    for line_number, line in enumerate(workflow_text.splitlines(), start=1):
        stripped = line.strip()
        if stripped.startswith("#"):
            continue
        if pattern.search(stripped):
            return line_number
    return None


def check_workflow_runs_guard(workflow_text: str) -> GuardCheck:
    probe_lines: list[int] = []
    missing: list[str] = []
    for script_path in WORKFLOW_PROBE_SCRIPTS:
        line_number = python_script_line(workflow_text, script_path)
        if line_number is None:
            missing.append(script_path)
        else:
            probe_lines.append(line_number)
    guard_line = python_script_line(workflow_text, WORKFLOW_GUARD_SCRIPT)
    if guard_line is None:
        missing.append(WORKFLOW_GUARD_SCRIPT)
    if missing:
        return fail_check("workflow.qm_status_guard", f"missing commands: {', '.join(missing)}")
    if not probe_lines:
        return fail_check("workflow.qm_status_guard", "missing QM route probes")
    latest_probe_line = max(probe_lines)
    if guard_line is None or guard_line <= latest_probe_line:
        return fail_check(
            "workflow.qm_status_guard",
            f"guard line {guard_line} must be after QM route probe line {latest_probe_line}",
        )
    return pass_check("workflow.qm_status_guard", f"guard line {guard_line}")


def field_string_tuple(mapping: dict[str, object], field: str) -> tuple[str, ...]:
    raw = mapping.get(field, [])
    if not isinstance(raw, list):
        return ()
    return tuple(item for item in raw if isinstance(item, str))


def field_mapping_list_targets_full_qm(mapping: dict[str, object], field: str) -> bool:
    raw = mapping.get(field, [])
    if not isinstance(raw, list):
        return False
    for item in raw:
        if not isinstance(item, dict):
            continue
        target_ref = require_mapping(item, field)
        if target_ref.get("id") == "full_QM_I" or target_ref.get("target") == "full_QM_I":
            return True
    return False


def mapping_targets_full_qm(mapping: dict[str, object]) -> bool:
    direct_fields = (
        "id",
        "target",
        "target_program",
        "claim_ref",
        "conclusion",
    )
    for field in direct_fields:
        if mapping.get(field) == "full_QM_I":
            return True
    for field in ("claim_refs", "conclusions", "targets"):
        if "full_QM_I" in field_string_tuple(mapping, field):
            return True
    if field_mapping_list_targets_full_qm(mapping, "target_refs"):
        return True
    return False


def full_qm_upgrade_markers(manifest: dict[str, object]) -> tuple[str, ...]:
    markers: list[str] = []
    symbols = require_mapping(manifest.get("symbols"), "symbols")
    full_qm = require_mapping(symbols.get("full_QM_I"), "symbols.full_QM_I")
    symbol_status = optional_string(full_qm.get("status"))
    if symbol_status in FULL_QM_UPGRADED_SYMBOL_STATUSES:
        markers.append(f"symbols.full_QM_I.status={symbol_status}")

    for index, raw_card in enumerate(require_list(manifest.get("theorem_cards", []), "theorem_cards")):
        card = require_mapping(raw_card, f"theorem_cards[{index}]")
        proof_status = optional_string(card.get("proof_status"))
        if proof_status == FULL_QM_FORMAL_PROOF_STATUS and mapping_targets_full_qm(card):
            card_id = optional_string(card.get("id")) or f"theorem_cards[{index}]"
            markers.append(f"theorem_cards.{card_id}.proof_status={proof_status}")

    for gate_index, raw_gate in enumerate(require_list(manifest.get("finite_gates", []), "finite_gates")):
        gate = require_mapping(raw_gate, f"finite_gates[{gate_index}]")
        for card_index, raw_card in enumerate(require_list(gate.get("proof_cards", []), "proof_cards")):
            card = require_mapping(raw_card, f"finite_gates[{gate_index}].proof_cards[{card_index}]")
            proof_kind = optional_string(card.get("proof_kind"))
            if proof_kind in full_qm_closure.FORMAL_PROOF_KINDS and mapping_targets_full_qm(card):
                card_id = optional_string(card.get("id")) or f"proof_cards[{card_index}]"
                markers.append(f"proof_cards.{card_id}.proof_kind={proof_kind}")
    return tuple(markers)


def check_full_qm_not_upgraded_without_proof(manifest: dict[str, object], closure_verdict: str) -> GuardCheck:
    markers = full_qm_upgrade_markers(manifest)
    if not markers:
        return pass_check("manifest.full_QM_I_not_upgraded", "no derived/formal full_QM_I marker")
    if closure_verdict == "FULL_QM_PROVED":
        return pass_check("manifest.full_QM_I_not_upgraded", f"allowed by {closure_verdict}")
    return fail_check(
        "manifest.full_QM_I_not_upgraded",
        f"{', '.join(markers)} without FULL_QM_PROVED closure; closure={closure_verdict}",
    )


def build_checks(manifest_path: Path, readme_path: Path, workflow_path: Path) -> list[GuardCheck]:
    born_route = born_direct.build_route()
    qm_route = qm_direct.build_route()
    cgsc_probe = cgsc_qm_closure.build_probe()
    manifest = load_manifest(manifest_path)
    closure = full_qm_closure.build_closure_attempt(manifest_path)
    return [
        check_expected_verdict(
            "route.born_direct_one_pass",
            born_route.verdict,
            EXPECTED_BORN_VERDICT,
        ),
        check_expected_verdict(
            "route.qm_direct_one_pass",
            qm_route.verdict,
            EXPECTED_QM_VERDICT,
        ),
        check_expected_verdict(
            "route.cgsc_qm_one_pass_closure",
            cgsc_probe.verdict,
            EXPECTED_CGSC_VERDICT,
        ),
        check_readme_badge(readme_path.read_text(encoding="utf-8")),
        check_workflow_runs_guard(workflow_path.read_text(encoding="utf-8")),
        check_full_qm_not_upgraded_without_proof(manifest, closure.verdict),
    ]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Guard the public QM scientific status boundary.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--readme", default=str(DEFAULT_README))
    parser.add_argument("--workflow", default=str(DEFAULT_WORKFLOW))
    return parser


def main() -> int:
    args = build_parser().parse_args()
    checks = build_checks(
        manifest_path=Path(str(args.manifest)),
        readme_path=Path(str(args.readme)),
        workflow_path=Path(str(args.workflow)),
    )
    for check in checks:
        status = "PASS" if check.passed else "FAIL"
        print(f"{status} {check.name}: {check.detail}")
    failures = [check for check in checks if not check.passed]
    if failures:
        print(f"qm_scientific_status_guard=FAIL failed={len(failures)}")
        return 1
    print(f"qm_scientific_status_guard=PASS checks={len(checks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
