from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMAND = "lake build Proofs.QMClosure.CGSCStructuralTargetKernel"
CGSC_ROUTE_DRAFT = REPO_ROOT / "Proofs/QMClosure/ContextGeneratedStableClosureRouteDraft.json"
CGSC_PRIMITIVE_DERIVATION_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCPrimitiveDerivationRouteDraft.json"

Verdict = Literal[
    "CGSC_STRUCTURAL_TARGET_KERNEL_CONDITIONAL",
    "CGSC_STRUCTURAL_TARGET_KERNEL_CHECK_FAILED",
    "CGSC_ROUTE_BLOCKED",
    "CGSC_PRIMITIVE_ROUTE_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]

STRUCTURAL_TARGETS: tuple[str, ...] = (
    "nonunital_stable_distinguishability",
    "spectral_decomposition",
    "rich_d_cl_reversible_symmetry",
    "continuous_inheritance_family",
    "generator_closure",
    "entanglement_closure",
)

CGSC_CLAUSES: tuple[str, ...] = (
    "finite_generation",
    "facticizable_separation",
    "exposed_context_decomposition",
    "reversible_route_closure",
    "coherent_refinement_flow",
    "composite_route_generation",
    "import_boundary",
)

FORBIDDEN_UPGRADES: tuple[str, ...] = (
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_space",
    "does_not_derive_Born_rule",
    "does_not_derive_unitary_dynamics",
    "does_not_derive_tensor_composition",
    "does_not_treat_CGSC_clauses_as_derived_from_primitives",
)


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class CGSCStructuralTargetKernelProbe:
    verdict: Verdict
    lean_check: LeanCheck
    cgsc_route_draft_status: str
    primitive_route_draft_status: str
    structural_targets: tuple[str, ...]
    conditionally_covered_targets: int
    negative_controls: int
    rejected_negative_controls: int
    clauses: tuple[str, ...]
    formal_clause_derivations: int
    unproved_clause_derivations: int
    candidate_supported_clauses: int
    successor_base_bound_clauses: int
    boundary_grounded_clauses: int
    next_blocker: str
    forbidden_upgrades: tuple[str, ...]


def run_lean_check() -> LeanCheck:
    completed = subprocess.run(
        shlex.split(LEAN_COMMAND),
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return LeanCheck(
        command=LEAN_COMMAND,
        returncode=completed.returncode,
        status="PASS" if completed.returncode == 0 else "FAIL",
    )


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


def load_json_object(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, str(path))


def cgsc_route_counts() -> tuple[str, int, int, int]:
    draft = load_json_object(CGSC_ROUTE_DRAFT)
    proof_route = require_mapping(draft.get("proof_route"), "cgsc_route.proof_route")
    status = require_string(draft.get("artifact_status"), "cgsc_route.artifact_status")
    clauses = len(require_list(proof_route.get("clauses"), "cgsc_route.proof_route.clauses"))
    targets = len(require_list(proof_route.get("targets"), "cgsc_route.proof_route.targets"))
    controls = len(
        require_list(
            proof_route.get("negative_controls"),
            "cgsc_route.proof_route.negative_controls",
        )
    )
    return status, clauses, targets, controls


def primitive_route_counts() -> tuple[str, int, int, int, int]:
    draft = load_json_object(CGSC_PRIMITIVE_DERIVATION_DRAFT)
    proof_route = require_mapping(draft.get("proof_route"), "primitive_route.proof_route")
    status = require_string(draft.get("artifact_status"), "primitive_route.artifact_status")
    raw_clauses = require_list(proof_route.get("clauses"), "primitive_route.proof_route.clauses")
    expected_statuses = [
        require_string(
            require_mapping(clause, "primitive_route.proof_route.clauses[]").get("expected_status"),
            "primitive_route.proof_route.clauses[].expected_status",
        )
        for clause in raw_clauses
    ]
    formal = sum(1 for expected_status in expected_statuses if expected_status == "FORMAL_FROM_PRIMITIVES")
    candidate = sum(1 for expected_status in expected_statuses if expected_status == "B0_CANDIDATE_SUPPORTED")
    successor = sum(1 for expected_status in expected_statuses if expected_status == "SUCCESSOR_BASE_BOUND")
    boundary = sum(1 for expected_status in expected_statuses if expected_status == "BOUNDARY_GROUNDED")
    return status, formal, candidate, successor, boundary


def build_probe() -> CGSCStructuralTargetKernelProbe:
    lean_check = run_lean_check()
    route_status, route_clauses, route_targets, route_controls = cgsc_route_counts()
    primitive_status, formal_clause_derivations, candidate_supported, successor_bound, boundary_grounded = (
        primitive_route_counts()
    )
    unproved_clause_derivations = route_clauses - formal_clause_derivations
    if lean_check.status == "FAIL":
        verdict: Verdict = "CGSC_STRUCTURAL_TARGET_KERNEL_CHECK_FAILED"
    elif route_clauses != len(CGSC_CLAUSES) or route_targets != len(STRUCTURAL_TARGETS) or route_controls != 6:
        verdict = "CGSC_ROUTE_BLOCKED"
    elif primitive_status != "primitive_derivation_route_draft_not_formal_proof":
        verdict = "CGSC_PRIMITIVE_ROUTE_BLOCKED"
    else:
        verdict = "CGSC_STRUCTURAL_TARGET_KERNEL_CONDITIONAL"
    return CGSCStructuralTargetKernelProbe(
        verdict=verdict,
        lean_check=lean_check,
        cgsc_route_draft_status=route_status,
        primitive_route_draft_status=primitive_status,
        structural_targets=STRUCTURAL_TARGETS,
        conditionally_covered_targets=route_targets,
        negative_controls=route_controls,
        rejected_negative_controls=route_controls,
        clauses=CGSC_CLAUSES,
        formal_clause_derivations=formal_clause_derivations,
        unproved_clause_derivations=unproved_clause_derivations,
        candidate_supported_clauses=candidate_supported,
        successor_base_bound_clauses=successor_bound,
        boundary_grounded_clauses=boundary_grounded,
        next_blocker=(
            "prove the seven CGSC clauses from B1 or a successor primitive base as machine-checkable "
            "artifacts; the structural target kernel closes the six QM blockers only conditionally"
        ),
        forbidden_upgrades=FORBIDDEN_UPGRADES,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Check the CGSC structural target kernel over the six current full-QM blockers."
    )
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-frontier", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"cgsc_structural_target_kernel={probe.verdict} lean={probe.lean_check.status} "
        f"cgsc_route_draft={probe.cgsc_route_draft_status} "
        f"primitive_route_draft={probe.primitive_route_draft_status} "
        f"structural_targets={len(probe.structural_targets)} conditional_targets={probe.conditionally_covered_targets} "
        f"controls={probe.negative_controls} rejected_controls={probe.rejected_negative_controls} "
        f"clauses={len(probe.clauses)} formal_clauses={probe.formal_clause_derivations} "
        f"unproved_clauses={probe.unproved_clause_derivations}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.show_frontier:
        for target in probe.structural_targets:
            print(f"TARGET {target}")
        for clause in probe.clauses:
            print(f"CLAUSE {clause}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in (
        "CGSC_STRUCTURAL_TARGET_KERNEL_CHECK_FAILED",
        "CGSC_ROUTE_BLOCKED",
        "CGSC_PRIMITIVE_ROUTE_BLOCKED",
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
