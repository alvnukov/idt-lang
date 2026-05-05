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
from scripts import evaluate_born_readout_attempt as born_readout  # noqa: E402
from scripts import evaluate_born_wall_separation as born_wall  # noqa: E402
from scripts import evaluate_s2_born_proof_search as s2_search  # noqa: E402

DEFAULT_MANIFEST = REPO_ROOT / "theory_verifier_manifest_v6_0.json"
DEFAULT_WORKFLOW = REPO_ROOT / ".github/workflows/qm-status.yml"

EXPECTED_BORN_DIRECT_VERDICT = "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF"
EXPECTED_BORN_READOUT_VERDICT = "CONDITIONAL_BORN_ROUTE"
EXPECTED_S2_SEARCH_VERDICT = "FINITE_BORN_CHAIN_HIT_UNIVERSAL_S2_OPEN"
EXPECTED_BORN_WALL_VERDICT = "BORN_WALL_REQUIRES_ACTUALIZATION_PRINCIPLE"
EXPECTED_BORN_OBLIGATION_STATUS = "blocked"

WORKFLOW_PROBE_SCRIPTS = (
    "scripts/evaluate_born_direct_one_pass.py",
    "scripts/evaluate_born_readout_attempt.py",
    "scripts/evaluate_s2_born_proof_search.py",
    "scripts/evaluate_born_wall_separation.py",
)
WORKFLOW_GUARD_SCRIPT = "scripts/check_born_scientific_status.py"
UPGRADED_BORN_STATUSES = frozenset({"derived", "derived_conditional", "formal_proof", "proved"})


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


def find_quadratic_context_probability_route() -> born_readout.RouteResult:
    for route in born_readout.ROUTES:
        if route.name == "quadratic_context_probability_route":
            return born_readout.evaluate_route(route)
    raise ValueError("missing quadratic_context_probability_route")


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
        return fail_check("workflow.born_status_guard", f"missing commands: {', '.join(missing)}")
    if not probe_lines:
        return fail_check("workflow.born_status_guard", "missing Born probes")
    latest_probe_line = max(probe_lines)
    if guard_line is None or guard_line <= latest_probe_line:
        return fail_check(
            "workflow.born_status_guard",
            f"guard line {guard_line} must be after Born probe line {latest_probe_line}",
        )
    return pass_check("workflow.born_status_guard", f"guard line {guard_line}")


def field_string_tuple(mapping: dict[str, object], field: str) -> tuple[str, ...]:
    raw = mapping.get(field, [])
    if not isinstance(raw, list):
        return ()
    return tuple(item for item in raw if isinstance(item, str))


def mapping_targets_born_rule(mapping: dict[str, object]) -> bool:
    direct_fields = ("id", "target", "target_program", "claim_ref", "conclusion")
    for field in direct_fields:
        if mapping.get(field) == "born_rule_derivation":
            return True
    for field in ("claim_refs", "conclusions", "targets", "dependencies", "evidence_refs"):
        if "born_rule_derivation" in field_string_tuple(mapping, field):
            return True
    return False


def born_upgrade_markers(manifest: dict[str, object]) -> tuple[str, ...]:
    markers: list[str] = []
    for index, raw_obligation in enumerate(require_list(manifest.get("qm_core_proof_obligations", []), "qm_core_proof_obligations")):
        obligation = require_mapping(raw_obligation, f"qm_core_proof_obligations[{index}]")
        if obligation.get("id") != "born_rule_derivation":
            continue
        status = optional_string(obligation.get("status"))
        if status in UPGRADED_BORN_STATUSES:
            markers.append(f"qm_core_proof_obligations.born_rule_derivation.status={status}")

    for index, raw_card in enumerate(require_list(manifest.get("theorem_cards", []), "theorem_cards")):
        card = require_mapping(raw_card, f"theorem_cards[{index}]")
        proof_status = optional_string(card.get("proof_status"))
        if proof_status == "formal_proof" and mapping_targets_born_rule(card):
            card_id = optional_string(card.get("id")) or f"theorem_cards[{index}]"
            markers.append(f"theorem_cards.{card_id}.proof_status={proof_status}")

    return tuple(markers)


def find_born_obligation(manifest: dict[str, object]) -> dict[str, object] | None:
    for index, raw_obligation in enumerate(require_list(manifest.get("qm_core_proof_obligations", []), "qm_core_proof_obligations")):
        obligation = require_mapping(raw_obligation, f"qm_core_proof_obligations[{index}]")
        if obligation.get("id") == "born_rule_derivation":
            return obligation
    return None


def check_born_obligation_status(manifest: dict[str, object]) -> GuardCheck:
    obligation = find_born_obligation(manifest)
    if obligation is None:
        return fail_check("manifest.born_rule_derivation_status", "missing born_rule_derivation")
    status = optional_string(obligation.get("status"))
    if status != EXPECTED_BORN_OBLIGATION_STATUS:
        return fail_check(
            "manifest.born_rule_derivation_status",
            f"expected {EXPECTED_BORN_OBLIGATION_STATUS}, got {status}",
        )
    markers = born_upgrade_markers(manifest)
    if markers:
        return fail_check("manifest.born_rule_derivation_status", f"unexpected upgrade markers: {', '.join(markers)}")
    return pass_check("manifest.born_rule_derivation_status", status)


def build_checks(manifest_path: Path, workflow_path: Path) -> list[GuardCheck]:
    manifest = load_manifest(manifest_path)
    born_route = born_direct.build_route()
    born_readout_route = find_quadratic_context_probability_route()
    s2_result = s2_search.build_search()
    born_wall_probe = born_wall.build_probe()
    return [
        check_expected_verdict(
            "route.born_direct_one_pass",
            born_route.verdict,
            EXPECTED_BORN_DIRECT_VERDICT,
        ),
        check_expected_verdict(
            "route.born_readout_attempt",
            born_readout_route.verdict,
            EXPECTED_BORN_READOUT_VERDICT,
        ),
        check_expected_verdict(
            "route.s2_born_proof_search",
            s2_result.verdict,
            EXPECTED_S2_SEARCH_VERDICT,
        ),
        check_expected_verdict(
            "route.born_wall_separation",
            born_wall_probe.verdict,
            EXPECTED_BORN_WALL_VERDICT,
        ),
        check_born_obligation_status(manifest),
        check_workflow_runs_guard(workflow_path.read_text(encoding="utf-8")),
    ]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Guard the public Born scientific status boundary.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--workflow", default=str(DEFAULT_WORKFLOW))
    return parser


def main() -> int:
    args = build_parser().parse_args()
    checks = build_checks(
        manifest_path=Path(str(args.manifest)),
        workflow_path=Path(str(args.workflow)),
    )
    for check in checks:
        status = "PASS" if check.passed else "FAIL"
        print(f"{status} {check.name}: {check.detail}")
    failures = [check for check in checks if not check.passed]
    if failures:
        print(f"born_scientific_status_guard=FAIL failed={len(failures)}")
        return 1
    print(f"born_scientific_status_guard=PASS checks={len(checks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
