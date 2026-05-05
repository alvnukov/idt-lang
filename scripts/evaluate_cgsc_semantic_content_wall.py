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
    "SEMANTIC_GROUNDING_KERNEL_REGISTERED",
    "SEMANTIC_CONTENT_CONTRACT_REGISTERED",
    "SEMANTIC_CONTENT_WALL_DETECTED",
    "LEAN_CHECK_FAILED",
    "TYPED_CONTRACT_CHECK_FAILED",
    "DECORATIVE_WALL_CHECK_FAILED",
    "GROUNDED_KERNEL_CHECK_FAILED",
    "FULL_ASSEMBLY_CHECK_FAILED",
    "GROUNDED_TOY_WALL_CHECK_FAILED",
    "SEMANTIC_GROUNDING_TOY_WALL_REGISTERED",
    "UNIVERSAL_KERNEL_CHECK_FAILED",
    "SEMANTIC_UNIVERSAL_KERNEL_REGISTERED",
    "UNIVERSAL_TOY_WALL_CHECK_FAILED",
    "UNIVERSAL_KERNEL_TOY_WALL_REGISTERED",
    "PRIMITIVE_GENERATED_SOURCE_CHECK_FAILED",
    "PRIMITIVE_GENERATED_SOURCE_KERNEL_REGISTERED",
    "PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_CHECK_FAILED",
    "PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_REGISTERED",
    "BOUND_PRIMITIVE_GENERATED_BASE_CHECK_FAILED",
    "BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED",
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
LEGACY_WALL_COMMAND = "lake build Proofs.QMClosure.CGSCSemanticContentWall"
TYPED_CONTRACT_COMMAND = "lake build Proofs.QMClosure.CGSCTypedSemanticExtensions"
DECORATIVE_WALL_COMMAND = "lake build Proofs.QMClosure.CGSCTypedDecorativeWall"
GROUNDED_KERNEL_COMMAND = "lake build Proofs.QMClosure.CGSCGroundedSemanticExtensions"
FULL_ASSEMBLY_COMMAND = "lake build Proofs.QMClosure.FullQMAssemblyFromGroundedSources"
GROUNDED_TOY_WALL_COMMAND = "lake build Proofs.QMClosure.CGSCGroundedToyWall"
UNIVERSAL_KERNEL_COMMAND = "lake build Proofs.QMClosure.UniversalPrimitiveSourceKernel"
UNIVERSAL_TOY_WALL_COMMAND = "lake build Proofs.QMClosure.UniversalPrimitiveToyWall"
PRIMITIVE_GENERATED_SOURCE_COMMAND = "lake build Proofs.QMClosure.PrimitiveGeneratedSourceKernel"
PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_COMMAND = (
    "lake build Proofs.QMClosure.PrimitiveGeneratedAdmissibilityWall"
)
BOUND_PRIMITIVE_GENERATED_BASE_COMMAND = "lake build Proofs.QMClosure.BoundPrimitiveGeneratedBase"


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
    typed_contract_file: str
    decorative_wall_file: str
    grounded_kernel_file: str
    full_assembly_file: str
    grounded_toy_wall_file: str
    universal_kernel_file: str
    universal_toy_wall_file: str
    primitive_generated_source_file: str
    primitive_generated_admissibility_wall_file: str
    bound_primitive_generated_base_file: str
    extension_witnesses: int
    draft_checks_failed: int
    legacy_wall_check: LeanCheck
    typed_contract_check: LeanCheck
    decorative_wall_check: LeanCheck
    grounded_kernel_check: LeanCheck
    full_assembly_check: LeanCheck
    grounded_toy_wall_check: LeanCheck
    universal_kernel_check: LeanCheck
    universal_toy_wall_check: LeanCheck
    primitive_generated_source_check: LeanCheck
    primitive_generated_admissibility_wall_check: LeanCheck
    bound_primitive_generated_base_check: LeanCheck
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
    allowed_commands = {
        LEGACY_WALL_COMMAND,
        TYPED_CONTRACT_COMMAND,
        DECORATIVE_WALL_COMMAND,
        GROUNDED_KERNEL_COMMAND,
        FULL_ASSEMBLY_COMMAND,
        GROUNDED_TOY_WALL_COMMAND,
        UNIVERSAL_KERNEL_COMMAND,
        UNIVERSAL_TOY_WALL_COMMAND,
        PRIMITIVE_GENERATED_SOURCE_COMMAND,
        PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_COMMAND,
        BOUND_PRIMITIVE_GENERATED_BASE_COMMAND,
    }
    if command not in allowed_commands:
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
        check_equals(
            "expected_verdict",
            wall.get("expected_verdict"),
            "BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED",
        ),
        check_equals("proof_status", wall.get("proof_status"), "blocked"),
        check_equals("lean_file", wall.get("lean_file"), "Proofs/QMClosure/CGSCSemanticContentWall.lean"),
        check_equals("wall_checker_command", wall.get("wall_checker_command"), LEGACY_WALL_COMMAND),
        check_equals(
            "typed_contract_file",
            wall.get("typed_contract_file"),
            "Proofs/QMClosure/CGSCTypedSemanticExtensions.lean",
        ),
        check_equals(
            "typed_contract_checker_command",
            wall.get("typed_contract_checker_command"),
            TYPED_CONTRACT_COMMAND,
        ),
        check_equals(
            "decorative_wall_file",
            wall.get("decorative_wall_file"),
            "Proofs/QMClosure/CGSCTypedDecorativeWall.lean",
        ),
        check_equals(
            "decorative_wall_checker_command",
            wall.get("decorative_wall_checker_command"),
            DECORATIVE_WALL_COMMAND,
        ),
        check_equals(
            "grounded_kernel_file",
            wall.get("grounded_kernel_file"),
            "Proofs/QMClosure/CGSCGroundedSemanticExtensions.lean",
        ),
        check_equals(
            "grounded_kernel_checker_command",
            wall.get("grounded_kernel_checker_command"),
            GROUNDED_KERNEL_COMMAND,
        ),
        check_equals(
            "full_assembly_file",
            wall.get("full_assembly_file"),
            "Proofs/QMClosure/FullQMAssemblyFromGroundedSources.lean",
        ),
        check_equals(
            "full_assembly_checker_command",
            wall.get("full_assembly_checker_command"),
            FULL_ASSEMBLY_COMMAND,
        ),
        check_equals(
            "grounded_toy_wall_file",
            wall.get("grounded_toy_wall_file"),
            "Proofs/QMClosure/CGSCGroundedToyWall.lean",
        ),
        check_equals(
            "grounded_toy_wall_checker_command",
            wall.get("grounded_toy_wall_checker_command"),
            GROUNDED_TOY_WALL_COMMAND,
        ),
        check_equals(
            "universal_kernel_file",
            wall.get("universal_kernel_file"),
            "Proofs/QMClosure/UniversalPrimitiveSourceKernel.lean",
        ),
        check_equals(
            "universal_kernel_checker_command",
            wall.get("universal_kernel_checker_command"),
            UNIVERSAL_KERNEL_COMMAND,
        ),
        check_equals(
            "universal_toy_wall_file",
            wall.get("universal_toy_wall_file"),
            "Proofs/QMClosure/UniversalPrimitiveToyWall.lean",
        ),
        check_equals(
            "universal_toy_wall_checker_command",
            wall.get("universal_toy_wall_checker_command"),
            UNIVERSAL_TOY_WALL_COMMAND,
        ),
        check_equals(
            "primitive_generated_source_file",
            wall.get("primitive_generated_source_file"),
            "Proofs/QMClosure/PrimitiveGeneratedSourceKernel.lean",
        ),
        check_equals(
            "primitive_generated_source_checker_command",
            wall.get("primitive_generated_source_checker_command"),
            PRIMITIVE_GENERATED_SOURCE_COMMAND,
        ),
        check_equals(
            "primitive_generated_admissibility_wall_file",
            wall.get("primitive_generated_admissibility_wall_file"),
            "Proofs/QMClosure/PrimitiveGeneratedAdmissibilityWall.lean",
        ),
        check_equals(
            "primitive_generated_admissibility_wall_checker_command",
            wall.get("primitive_generated_admissibility_wall_checker_command"),
            PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_COMMAND,
        ),
        check_equals(
            "bound_primitive_generated_base_file",
            wall.get("bound_primitive_generated_base_file"),
            "Proofs/QMClosure/BoundPrimitiveGeneratedBase.lean",
        ),
        check_equals(
            "bound_primitive_generated_base_checker_command",
            wall.get("bound_primitive_generated_base_checker_command"),
            BOUND_PRIMITIVE_GENERATED_BASE_COMMAND,
        ),
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
            "typed_contract",
            wall.get("typed_contract"),
            "typed_semantic_extension_base_has_no_vacuity",
        ),
        check_equals(
            "decorative_wall",
            wall.get("decorative_wall"),
            "typed_contract_still_admits_decorative_true_extensions",
        ),
        check_equals(
            "grounded_kernel",
            wall.get("grounded_kernel"),
            "grounded_semantic_extension_base_yields_six_extension_statements",
        ),
        check_equals(
            "full_assembly",
            wall.get("full_assembly"),
            "grounded_semantic_sources_yield_full_qm_obligation_bundle",
        ),
        check_equals(
            "grounded_toy_wall",
            wall.get("grounded_toy_wall"),
            "grounded_kernel_admits_toy_full_qm_obligation_bundle",
        ),
        check_equals(
            "universal_kernel",
            wall.get("universal_kernel"),
            "universal_primitive_source_kernel_yields_full_qm_obligation_bundle",
        ),
        check_equals(
            "universal_kernel_toy_rejection",
            wall.get("universal_kernel_toy_rejection"),
            "toy_grounded_kernel_has_no_universal_exposed_rank",
        ),
        check_equals(
            "universal_toy_wall",
            wall.get("universal_toy_wall"),
            "universal_kernel_admits_three_point_toy_full_qm_obligation_bundle",
        ),
        check_equals(
            "primitive_generated_source_kernel",
            wall.get("primitive_generated_source_kernel"),
            "primitive_generated_admissibility_yields_full_qm_obligation_bundle",
        ),
        check_equals(
            "primitive_generated_atom_universe",
            wall.get("primitive_generated_atom_universe"),
            "primitive_generated_source_slots_share_one_atom_universe",
        ),
        check_equals(
            "primitive_generated_admissibility_wall",
            wall.get("primitive_generated_admissibility_wall"),
            "b0_alone_can_feed_free_primitive_generated_source_kernel",
        ),
        check_equals(
            "bound_primitive_generated_base",
            wall.get("bound_primitive_generated_base"),
            "bound_primitive_generated_base_yields_full_qm_obligation_bundle",
        ),
        check_equals(
            "bound_primitive_generated_roles",
            wall.get("bound_primitive_generated_roles"),
            "bound_admissibility_role_atoms_are_constructor_generated",
        ),
        check_equals(
            "required_fix",
            wall.get("required_fix"),
            "promote the bound successor primitive base or prove its data from B0; free B0 admissibility remains rejected",
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
    legacy_wall_check = run_lean_check(require_string(wall.get("wall_checker_command"), "wall.wall_checker_command"))
    typed_contract_check = run_lean_check(
        require_string(wall.get("typed_contract_checker_command"), "wall.typed_contract_checker_command")
    )
    decorative_wall_check = run_lean_check(
        require_string(wall.get("decorative_wall_checker_command"), "wall.decorative_wall_checker_command")
    )
    grounded_kernel_check = run_lean_check(
        require_string(wall.get("grounded_kernel_checker_command"), "wall.grounded_kernel_checker_command")
    )
    full_assembly_check = run_lean_check(
        require_string(wall.get("full_assembly_checker_command"), "wall.full_assembly_checker_command")
    )
    grounded_toy_wall_check = run_lean_check(
        require_string(wall.get("grounded_toy_wall_checker_command"), "wall.grounded_toy_wall_checker_command")
    )
    universal_kernel_check = run_lean_check(
        require_string(wall.get("universal_kernel_checker_command"), "wall.universal_kernel_checker_command")
    )
    universal_toy_wall_check = run_lean_check(
        require_string(wall.get("universal_toy_wall_checker_command"), "wall.universal_toy_wall_checker_command")
    )
    primitive_generated_source_check = run_lean_check(
        require_string(
            wall.get("primitive_generated_source_checker_command"),
            "wall.primitive_generated_source_checker_command",
        )
    )
    primitive_generated_admissibility_wall_check = run_lean_check(
        require_string(
            wall.get("primitive_generated_admissibility_wall_checker_command"),
            "wall.primitive_generated_admissibility_wall_checker_command",
        )
    )
    bound_primitive_generated_base_check = run_lean_check(
        require_string(
            wall.get("bound_primitive_generated_base_checker_command"),
            "wall.bound_primitive_generated_base_checker_command",
        )
    )
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    if draft_failed > 0:
        verdict: Verdict = "WALL_DRAFT_INVALID"
    elif legacy_wall_check.status == "FAIL":
        verdict = "LEAN_CHECK_FAILED"
    elif typed_contract_check.status == "FAIL":
        verdict = "TYPED_CONTRACT_CHECK_FAILED"
    elif decorative_wall_check.status == "FAIL":
        verdict = "DECORATIVE_WALL_CHECK_FAILED"
    elif grounded_kernel_check.status == "FAIL":
        verdict = "GROUNDED_KERNEL_CHECK_FAILED"
    elif full_assembly_check.status == "FAIL":
        verdict = "FULL_ASSEMBLY_CHECK_FAILED"
    elif grounded_toy_wall_check.status == "FAIL":
        verdict = "GROUNDED_TOY_WALL_CHECK_FAILED"
    elif universal_kernel_check.status == "FAIL":
        verdict = "UNIVERSAL_KERNEL_CHECK_FAILED"
    elif universal_toy_wall_check.status == "FAIL":
        verdict = "UNIVERSAL_TOY_WALL_CHECK_FAILED"
    elif primitive_generated_source_check.status == "FAIL":
        verdict = "PRIMITIVE_GENERATED_SOURCE_CHECK_FAILED"
    elif primitive_generated_admissibility_wall_check.status == "FAIL":
        verdict = "PRIMITIVE_GENERATED_ADMISSIBILITY_WALL_CHECK_FAILED"
    elif bound_primitive_generated_base_check.status == "FAIL":
        verdict = "BOUND_PRIMITIVE_GENERATED_BASE_CHECK_FAILED"
    else:
        verdict = "BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED"
    return SemanticContentWallProbe(
        verdict=verdict,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        lean_file=require_string(wall.get("lean_file"), "wall.lean_file"),
        typed_contract_file=require_string(wall.get("typed_contract_file"), "wall.typed_contract_file"),
        decorative_wall_file=require_string(wall.get("decorative_wall_file"), "wall.decorative_wall_file"),
        grounded_kernel_file=require_string(wall.get("grounded_kernel_file"), "wall.grounded_kernel_file"),
        full_assembly_file=require_string(wall.get("full_assembly_file"), "wall.full_assembly_file"),
        grounded_toy_wall_file=require_string(wall.get("grounded_toy_wall_file"), "wall.grounded_toy_wall_file"),
        universal_kernel_file=require_string(wall.get("universal_kernel_file"), "wall.universal_kernel_file"),
        universal_toy_wall_file=require_string(wall.get("universal_toy_wall_file"), "wall.universal_toy_wall_file"),
        primitive_generated_source_file=require_string(
            wall.get("primitive_generated_source_file"),
            "wall.primitive_generated_source_file",
        ),
        primitive_generated_admissibility_wall_file=require_string(
            wall.get("primitive_generated_admissibility_wall_file"),
            "wall.primitive_generated_admissibility_wall_file",
        ),
        bound_primitive_generated_base_file=require_string(
            wall.get("bound_primitive_generated_base_file"),
            "wall.bound_primitive_generated_base_file",
        ),
        extension_witnesses=len(string_tuple(wall.get("extension_witnesses"), "wall.extension_witnesses")),
        draft_checks_failed=draft_failed,
        legacy_wall_check=legacy_wall_check,
        typed_contract_check=typed_contract_check,
        decorative_wall_check=decorative_wall_check,
        grounded_kernel_check=grounded_kernel_check,
        full_assembly_check=full_assembly_check,
        grounded_toy_wall_check=grounded_toy_wall_check,
        universal_kernel_check=universal_kernel_check,
        universal_toy_wall_check=universal_toy_wall_check,
        primitive_generated_source_check=primitive_generated_source_check,
        primitive_generated_admissibility_wall_check=primitive_generated_admissibility_wall_check,
        bound_primitive_generated_base_check=bound_primitive_generated_base_check,
        draft_checks=draft_checks,
        next_blocker=(
            "promote the bound successor primitive base or prove its data from B0; "
            "free B0 admissibility remains rejected"
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
        f"cgsc_semantic_content_wall={probe.verdict} "
        f"legacy_wall={probe.legacy_wall_check.status} typed_contract={probe.typed_contract_check.status} "
        f"decorative_wall={probe.decorative_wall_check.status} grounded_kernel={probe.grounded_kernel_check.status} "
        f"full_assembly={probe.full_assembly_check.status} grounded_toy_wall={probe.grounded_toy_wall_check.status} "
        f"universal_kernel={probe.universal_kernel_check.status} universal_toy_wall={probe.universal_toy_wall_check.status} "
        f"primitive_generated_source={probe.primitive_generated_source_check.status} "
        f"primitive_generated_admissibility_wall={probe.primitive_generated_admissibility_wall_check.status} "
        f"bound_primitive_generated_base={probe.bound_primitive_generated_base_check.status} "
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
    if probe.verdict != "BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
