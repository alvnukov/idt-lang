from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_cgsc_extension_wall_probe as extension_wall  # noqa: E402
import scripts.evaluate_cgsc_primitive_derivation as primitive_derivation  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as full_qm_closure  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCPrimitiveBridgeDraft.json"

Verdict = Literal[
    "CONDITIONAL_EXTENSION_BRIDGE_VALIDATED",
    "UPSTREAM_STATUS_UNEXPECTED",
    "LEAN_CHECK_FAILED",
    "BRIDGE_DRAFT_INVALID",
]
CheckStatus = Literal["PASS", "FAIL"]

EXPECTED_EXTENSIONS = (
    "coherent_refinement_compactness",
    "complete_exposed_context_partition",
    "generator_bookkeeping_without_stone",
    "no_hidden_joint_only_generation",
    "product_context_generation_closure",
    "reversible_context_automorphism_closure",
)
EXPECTED_PACKAGES = (
    "finite_exposed_context_completion",
    "generated_composite_no_hidden_joint_closure",
    "route_automorphism_and_refinement_coherence",
)
EXPECTED_FORBIDDEN_IMPORTS = (
    "born_rule",
    "complex_hilbert_space",
    "generator_assumed",
    "hilbert_tensor_product",
    "spectral_theorem",
    "stone_theorem",
    "unitary_group",
)
REQUIRED_FORBIDDEN_CLAIMS = (
    "does_not_prove_CGSC",
    "does_not_prove_full_QM_I",
    "does_not_claim_extensions_are_proved_from_B0",
    "does_not_mark_conditional_bridge_as_formal_proof",
    "does_not_import_Hilbert_Born_unitary_tensor_or_Stone",
)
CHECKER_COMMAND = "lake build Proofs.QMClosure.CGSCPrimitiveBridge"


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class UpstreamCheck:
    id: str
    expected: str
    observed: str
    status: CheckStatus


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class BridgeProbe:
    verdict: Verdict
    draft_path: str
    lean_file: str
    extensions: int
    packages: int
    obligations: int
    upstream_failed: int
    draft_checks_failed: int
    lean_check: LeanCheck
    upstream_checks: list[UpstreamCheck]
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


def expected_obligations() -> tuple[str, ...]:
    return tuple(obligation.id for obligation in full_qm_closure.OBLIGATIONS)


def extension_ids(bridge: dict[str, object]) -> tuple[str, ...]:
    raw_extensions = require_list(bridge.get("extensions"), "bridge.extensions")
    ids: set[str] = set()
    for index, raw_extension in enumerate(raw_extensions):
        extension = require_mapping(raw_extension, f"bridge.extensions[{index}]")
        ids.add(require_string(extension.get("id"), f"bridge.extensions[{index}].id"))
    return sorted_tuple(ids)


def package_ids_and_obligations(bridge: dict[str, object]) -> tuple[tuple[str, ...], tuple[str, ...]]:
    raw_packages = require_list(bridge.get("package_map"), "bridge.package_map")
    package_ids: set[str] = set()
    obligations: set[str] = set()
    for package_index, raw_package in enumerate(raw_packages):
        package = require_mapping(raw_package, f"bridge.package_map[{package_index}]")
        package_ids.add(require_string(package.get("id"), f"bridge.package_map[{package_index}].id"))
        obligations.update(string_tuple(package.get("obligations"), f"bridge.package_map[{package_index}].obligations"))
    return sorted_tuple(package_ids), sorted_tuple(obligations)


def upstream_checks(bridge: dict[str, object]) -> list[UpstreamCheck]:
    observed_by_id = {
        "extension_wall_probe": extension_wall.build_probe().verdict,
        "primitive_derivation": primitive_derivation.build_probe().verdict,
        "full_qm_proof_closure": full_qm_closure.build_closure_attempt().verdict,
    }
    checks: list[UpstreamCheck] = []
    for index, raw_requirement in enumerate(
        require_list(bridge.get("upstream_requirements"), "bridge.upstream_requirements")
    ):
        requirement = require_mapping(raw_requirement, f"bridge.upstream_requirements[{index}]")
        requirement_id = require_string(requirement.get("id"), f"bridge.upstream_requirements[{index}].id")
        expected = require_string(requirement.get("expected"), f"bridge.upstream_requirements[{index}].expected")
        observed = observed_by_id.get(requirement_id, "MISSING_UPSTREAM_REQUIREMENT")
        status: CheckStatus = "PASS" if observed == expected else "FAIL"
        checks.append(UpstreamCheck(id=requirement_id, expected=expected, observed=observed, status=status))
    return checks


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


def validate_draft(draft: dict[str, object], bridge: dict[str, object]) -> list[DraftCheck]:
    dependencies = string_tuple(bridge.get("dependencies"), "bridge.dependencies")
    package_ids, obligations = package_ids_and_obligations(bridge)
    return [
        check_equals("artifact_status", draft.get("artifact_status"), "conditional_extension_bridge_not_formal_proof"),
        check_equals("bridge_id", bridge.get("id"), "cgsc_primitive_extension_bridge"),
        check_equals("expected_verdict", bridge.get("expected_verdict"), "CONDITIONAL_EXTENSION_BRIDGE_VALIDATED"),
        check_equals("proof_status", bridge.get("proof_status"), "conditional_proof"),
        check_equals("lean_file", bridge.get("lean_file"), "Proofs/QMClosure/CGSCPrimitiveBridge.lean"),
        check_equals("checker_command", bridge.get("checker_command"), CHECKER_COMMAND),
        existing_dependency_refs(dependencies),
        check_set_equals("extensions", extension_ids(bridge), EXPECTED_EXTENSIONS),
        check_set_equals("package_ids", package_ids, EXPECTED_PACKAGES),
        check_set_equals("obligations", obligations, expected_obligations()),
        check_set_equals(
            "forbidden_imports",
            string_tuple(bridge.get("forbidden_imports"), "bridge.forbidden_imports"),
            EXPECTED_FORBIDDEN_IMPORTS,
        ),
        check_set_equals(
            "forbidden_claims",
            string_tuple(bridge.get("forbidden_claims"), "bridge.forbidden_claims"),
            REQUIRED_FORBIDDEN_CLAIMS,
        ),
    ]


def build_probe(draft_path: Path = DEFAULT_DRAFT) -> BridgeProbe:
    draft = load_draft(draft_path)
    bridge = require_mapping(draft.get("bridge"), "bridge")
    draft_checks = validate_draft(draft, bridge)
    upstream = upstream_checks(bridge)
    command = require_string(bridge.get("checker_command"), "bridge.checker_command")
    lean_check = run_lean_check(command)
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    upstream_failed = sum(1 for check in upstream if check.status == "FAIL")
    if draft_failed > 0:
        verdict: Verdict = "BRIDGE_DRAFT_INVALID"
    elif upstream_failed > 0:
        verdict = "UPSTREAM_STATUS_UNEXPECTED"
    elif lean_check.status == "FAIL":
        verdict = "LEAN_CHECK_FAILED"
    else:
        verdict = "CONDITIONAL_EXTENSION_BRIDGE_VALIDATED"
    return BridgeProbe(
        verdict=verdict,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        lean_file=require_string(bridge.get("lean_file"), "bridge.lean_file"),
        extensions=len(extension_ids(bridge)),
        packages=len(package_ids_and_obligations(bridge)[0]),
        obligations=len(package_ids_and_obligations(bridge)[1]),
        upstream_failed=upstream_failed,
        draft_checks_failed=draft_failed,
        lean_check=lean_check,
        upstream_checks=upstream,
        draft_checks=draft_checks,
        next_blocker=(
            "promote the bound successor primitive base or prove its data from B0; "
            "the bridge is conditional and does not prove CGSC or full QM"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate the conditional primitive-extension bridge into CGSC package closure.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-upstream", action="store_true")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)))
    print(
        f"cgsc_primitive_bridge={probe.verdict} lean={probe.lean_check.status} "
        f"extensions={probe.extensions} packages={probe.packages} obligations={probe.obligations} "
        f"upstream_failed={probe.upstream_failed} draft_checks_failed={probe.draft_checks_failed}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.show_upstream:
        for check in probe.upstream_checks:
            print(f"{check.status} {check.id}: observed={check.observed} expected={check.expected}")
    if args.show_draft_checks:
        for draft_check in probe.draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict != "CONDITIONAL_EXTENSION_BRIDGE_VALIDATED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
