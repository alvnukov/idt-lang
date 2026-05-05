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

import scripts.evaluate_context_generated_stable_closure_route_draft as cgsc_route  # noqa: E402
import scripts.evaluate_cgsc_semantic_content_wall as semantic_content_wall  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCPrimitiveDerivationRouteDraft.json"

Verdict = Literal[
    "CGSC_DERIVED_FROM_PRIMITIVES",
    "SUCCESSOR_BASE_DERIVATION_REGISTERED",
    "PRIMITIVE_DERIVATION_NOT_CLOSED",
    "PRIMITIVE_ROUTE_DRAFT_INVALID",
    "TARGET_IMPORT_REJECTED",
]
ClauseStatus = Literal[
    "FORMAL_FROM_PRIMITIVES",
    "SUCCESSOR_BASE_BOUND",
    "B0_CANDIDATE_SUPPORTED",
    "B0_EXTENSION_REQUIRED",
    "BOUNDARY_GROUNDED",
    "IMPORT_REJECTED",
]


@dataclass(frozen=True)
class PrimitiveSupport:
    id: str
    status: str
    role: str


@dataclass(frozen=True)
class ClauseRequirement:
    id: str
    required_b0_primitives: tuple[str, ...]
    required_v6_interfaces: tuple[str, ...]
    required_context_first_principles: tuple[str, ...]
    missing_base_extensions: tuple[str, ...]
    forbidden_imports: tuple[str, ...]
    derivation_obligation: str


@dataclass(frozen=True)
class ClauseCheck:
    id: str
    status: ClauseStatus
    primitive_support: tuple[str, ...]
    interface_support: tuple[str, ...]
    principle_support: tuple[str, ...]
    missing_support: tuple[str, ...]
    forbidden_import_hits: tuple[str, ...]
    derivation_obligation: str


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class PrimitiveDerivationProbe:
    verdict: Verdict
    cgsc_route_draft: str
    route_draft_path: str
    clauses: int
    formal_from_primitives: int
    successor_base_bound: int
    candidate_supported: int
    extension_required: int
    boundary_grounded: int
    import_rejected: int
    route_draft_checks_passed: int
    route_draft_checks_failed: int
    missing_base_extensions: tuple[str, ...]
    checks: list[ClauseCheck]
    route_draft_checks: list[DraftCheck]
    next_blocker: str


V6_INTERFACES: tuple[PrimitiveSupport, ...] = (
    PrimitiveSupport("history_space", "executable_v6_scaffold", "readout-facing history interface"),
    PrimitiveSupport("event_algebra", "executable_v6_scaffold", "readout-facing event interface"),
    PrimitiveSupport("readout_context_family", "executable_v6_scaffold", "readout context interface"),
    PrimitiveSupport("inheritance_act_family", "executable_v6_scaffold", "inheritance act interface"),
)

B0_PRIMITIVES: tuple[PrimitiveSupport, ...] = (
    PrimitiveSupport("admissible_context_cover", "lower_base_candidate", "context cover/category"),
    PrimitiveSupport("local_outcome_event_presheaf", "lower_base_candidate", "local outcome-event presheaf"),
    PrimitiveSupport("inheritance_transition_family", "lower_base_candidate", "context transition family"),
    PrimitiveSupport("facticization_witness_relation", "lower_base_candidate", "readout witness relation"),
    PrimitiveSupport("stable_distinguishability_relation", "lower_base_candidate", "stable distinguishability relation"),
)

CONTEXT_FIRST_PRINCIPLES: tuple[PrimitiveSupport, ...] = (
    PrimitiveSupport("local_facticity", "v7_base_principle_candidate", "facts require local readout witnesses"),
    PrimitiveSupport("no_primitive_global_section", "v7_base_principle_candidate", "global fact tables are not primitive"),
    PrimitiveSupport("overlap_discipline", "v7_base_principle_candidate", "overlap compatibility discipline"),
    PrimitiveSupport("obstruction_physicality", "v7_base_principle_candidate", "obstructions are physical only when witnessed"),
    PrimitiveSupport("finite_witness_discipline", "v7_base_principle_candidate", "finite witnesses control stable claims"),
    PrimitiveSupport("minimal_carrier_selection", "v7_base_principle_candidate", "carriers must be minimal faithful representations"),
    PrimitiveSupport("scale_projection_boundary", "v7_base_principle_candidate", "scale readouts are projection obligations"),
)

FORBIDDEN_IMPORTS: tuple[str, ...] = (
    "born_rule",
    "complex_hilbert_space",
    "hilbert_tensor_product",
    "spectral_theorem",
    "stone_theorem",
    "unitary_group",
    "generator_assumed",
)

CLAUSE_REQUIREMENTS: tuple[ClauseRequirement, ...] = (
    ClauseRequirement(
        id="finite_generation",
        required_b0_primitives=(
            "admissible_context_cover",
            "local_outcome_event_presheaf",
            "inheritance_transition_family",
            "facticization_witness_relation",
        ),
        required_v6_interfaces=("history_space", "event_algebra", "readout_context_family", "inheritance_act_family"),
        required_context_first_principles=("finite_witness_discipline", "local_facticity"),
        missing_base_extensions=(),
        forbidden_imports=("complex_hilbert_space", "born_rule"),
        derivation_obligation="prove finite generation from context cover, local outcome events, inheritance traces, and witness relation",
    ),
    ClauseRequirement(
        id="facticizable_separation",
        required_b0_primitives=("facticization_witness_relation", "stable_distinguishability_relation"),
        required_v6_interfaces=("readout_context_family", "inheritance_act_family"),
        required_context_first_principles=("local_facticity", "finite_witness_discipline"),
        missing_base_extensions=(),
        forbidden_imports=("born_rule", "complex_hilbert_space"),
        derivation_obligation="prove every readout-relevant stable distinction has a finite facticizable witness",
    ),
    ClauseRequirement(
        id="exposed_context_decomposition",
        required_b0_primitives=(
            "admissible_context_cover",
            "local_outcome_event_presheaf",
            "facticization_witness_relation",
            "stable_distinguishability_relation",
        ),
        required_v6_interfaces=("event_algebra", "readout_context_family"),
        required_context_first_principles=("local_facticity", "overlap_discipline"),
        missing_base_extensions=("complete_exposed_context_partition",),
        forbidden_imports=("spectral_theorem", "complex_hilbert_space"),
        derivation_obligation="derive exposed-context decomposition without importing spectral theorem",
    ),
    ClauseRequirement(
        id="reversible_route_closure",
        required_b0_primitives=(
            "inheritance_transition_family",
            "facticization_witness_relation",
            "stable_distinguishability_relation",
        ),
        required_v6_interfaces=("readout_context_family", "inheritance_act_family"),
        required_context_first_principles=("overlap_discipline", "minimal_carrier_selection"),
        missing_base_extensions=("reversible_context_automorphism_closure",),
        forbidden_imports=("unitary_group", "complex_hilbert_space"),
        derivation_obligation="derive reversible route automorphisms preserving D_cl, overlap, and exposed contexts",
    ),
    ClauseRequirement(
        id="coherent_refinement_flow",
        required_b0_primitives=("admissible_context_cover", "inheritance_transition_family"),
        required_v6_interfaces=("history_space", "inheritance_act_family"),
        required_context_first_principles=("finite_witness_discipline", "obstruction_physicality"),
        missing_base_extensions=("coherent_refinement_compactness", "generator_bookkeeping_without_stone"),
        forbidden_imports=("stone_theorem", "unitary_group", "generator_assumed"),
        derivation_obligation="derive coherent finite refinement flow and generator-compatible bookkeeping",
    ),
    ClauseRequirement(
        id="composite_route_generation",
        required_b0_primitives=(
            "admissible_context_cover",
            "local_outcome_event_presheaf",
            "facticization_witness_relation",
            "stable_distinguishability_relation",
        ),
        required_v6_interfaces=("event_algebra", "readout_context_family", "inheritance_act_family"),
        required_context_first_principles=("no_primitive_global_section", "finite_witness_discipline"),
        missing_base_extensions=("product_context_generation_closure", "no_hidden_joint_only_generation"),
        forbidden_imports=("hilbert_tensor_product", "complex_hilbert_space", "born_rule"),
        derivation_obligation="derive composite route generation including non-product facts without hidden joint-only imports",
    ),
    ClauseRequirement(
        id="import_boundary",
        required_b0_primitives=(),
        required_v6_interfaces=(),
        required_context_first_principles=(),
        missing_base_extensions=(),
        forbidden_imports=(),
        derivation_obligation="keep target QM structures outside the primitive base until separately proved",
    ),
)


def support_ids(supports: tuple[PrimitiveSupport, ...]) -> set[str]:
    return {support.id for support in supports}


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


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


def route_clause_ids() -> set[str]:
    draft = cgsc_route.load_draft(cgsc_route.DEFAULT_DRAFT)
    proof_route = cgsc_route.require_mapping(draft.get("proof_route"), "proof_route")
    return set(cgsc_route.clause_ids_from_draft(proof_route))


def check_clause(
    requirement: ClauseRequirement,
    route_clauses: set[str],
    successor_base_bound: bool,
) -> ClauseCheck:
    b0_ids = support_ids(B0_PRIMITIVES)
    v6_ids = support_ids(V6_INTERFACES)
    principle_ids = support_ids(CONTEXT_FIRST_PRINCIPLES)
    missing_support = set()
    if requirement.id not in route_clauses:
        missing_support.add(f"route_clause:{requirement.id}")
    missing_support.update(f"b0:{item}" for item in requirement.required_b0_primitives if item not in b0_ids)
    missing_support.update(f"v6:{item}" for item in requirement.required_v6_interfaces if item not in v6_ids)
    missing_support.update(
        f"context_first_principle:{item}"
        for item in requirement.required_context_first_principles
        if item not in principle_ids
    )
    forbidden_hits = tuple(import_id for import_id in requirement.forbidden_imports if import_id not in FORBIDDEN_IMPORTS)
    if forbidden_hits:
        status: ClauseStatus = "IMPORT_REJECTED"
    elif requirement.id == "import_boundary":
        status = "BOUNDARY_GROUNDED"
    elif missing_support:
        status = "B0_EXTENSION_REQUIRED"
    elif requirement.missing_base_extensions and successor_base_bound:
        status = "SUCCESSOR_BASE_BOUND"
    elif requirement.missing_base_extensions:
        status = "B0_EXTENSION_REQUIRED"
        missing_support.update(requirement.missing_base_extensions)
    else:
        status = "B0_CANDIDATE_SUPPORTED"
    return ClauseCheck(
        id=requirement.id,
        status=status,
        primitive_support=requirement.required_b0_primitives,
        interface_support=requirement.required_v6_interfaces,
        principle_support=requirement.required_context_first_principles,
        missing_support=tuple(sorted(missing_support)),
        forbidden_import_hits=forbidden_hits,
        derivation_obligation=requirement.derivation_obligation,
    )


def extension_missing_support(check: ClauseCheck) -> tuple[str, ...]:
    return tuple(
        item
        for item in check.missing_support
        if not item.startswith(("b0:", "v6:", "context_first_principle:", "route_clause:"))
    )


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


def draft_clause_maps(proof_route: dict[str, object]) -> tuple[dict[str, object], ...]:
    clauses = require_list(proof_route.get("clauses"), "proof_route.clauses")
    return tuple(require_mapping(clause, "proof_route.clauses[]") for clause in clauses)


def validate_route_draft(
    draft_path: Path,
    verdict: Verdict,
    checks: list[ClauseCheck],
    missing_base_extensions: tuple[str, ...],
) -> list[DraftCheck]:
    draft = load_draft(draft_path)
    theorem_card = require_mapping(draft.get("theorem_card"), "theorem_card")
    proof_route = require_mapping(draft.get("proof_route"), "proof_route")
    clause_maps = draft_clause_maps(proof_route)
    status_by_id = {check.id: check.status for check in checks}
    missing_by_id = {check.id: extension_missing_support(check) for check in checks}
    draft_status_by_id = {
        require_string(clause.get("id"), "clause.id"): require_string(clause.get("expected_status"), "clause.expected_status")
        for clause in clause_maps
    }
    draft_missing_by_id = {
        require_string(clause.get("id"), "clause.id"): string_tuple(
            clause.get("missing_base_extensions"),
            "clause.missing_base_extensions",
        )
        for clause in clause_maps
    }
    dependencies = string_tuple(theorem_card.get("dependencies"), "theorem_card.dependencies")
    route_missing_extensions = string_tuple(proof_route.get("missing_base_extensions"), "proof_route.missing_base_extensions")
    draft_checks = [
        check_equals(
            "artifact_status",
            draft.get("artifact_status"),
            "primitive_derivation_route_draft_not_formal_proof",
        ),
        check_equals("theorem_id", theorem_card.get("id"), "context_generated_stable_closure_from_primitives_route"),
        check_equals("proof_status", theorem_card.get("proof_status"), "open"),
        check_equals("verifier", theorem_card.get("verifier"), "scripts/evaluate_cgsc_primitive_derivation.py"),
        existing_dependency_refs(dependencies),
        check_equals("proof_route_id", proof_route.get("id"), "cgsc_primitive_derivation_route"),
        check_equals(
            "target_theorem",
            proof_route.get("target_theorem"),
            "context_generated_stable_closure_from_primitives_route",
        ),
        check_equals("expected_route_status", proof_route.get("expected_route_status"), "open"),
        check_equals("expected_probe_verdict", proof_route.get("expected_probe_verdict"), verdict),
        check_set_equals("clause_ids", tuple(draft_status_by_id), tuple(status_by_id)),
        check_set_equals(
            "clause_statuses",
            tuple(f"{clause_id}:{status}" for clause_id, status in draft_status_by_id.items()),
            tuple(f"{clause_id}:{status}" for clause_id, status in status_by_id.items()),
        ),
        check_set_equals(
            "clause_missing_extensions",
            tuple(f"{clause_id}:{','.join(missing)}" for clause_id, missing in draft_missing_by_id.items()),
            tuple(f"{clause_id}:{','.join(missing)}" for clause_id, missing in missing_by_id.items()),
        ),
        check_set_equals("missing_base_extensions", route_missing_extensions, missing_base_extensions),
    ]
    return draft_checks


def build_probe(draft_path: Path = DEFAULT_DRAFT) -> PrimitiveDerivationProbe:
    route_draft = cgsc_route.build_probe()
    route_clauses = route_clause_ids()
    semantic_probe = semantic_content_wall.build_probe()
    successor_base_bound = semantic_probe.verdict == "BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED"
    checks = [
        check_clause(requirement, route_clauses, successor_base_bound)
        for requirement in CLAUSE_REQUIREMENTS
    ]
    formal = sum(1 for check in checks if check.status == "FORMAL_FROM_PRIMITIVES")
    successor = sum(1 for check in checks if check.status == "SUCCESSOR_BASE_BOUND")
    candidate = sum(1 for check in checks if check.status == "B0_CANDIDATE_SUPPORTED")
    extension = sum(1 for check in checks if check.status == "B0_EXTENSION_REQUIRED")
    boundary = sum(1 for check in checks if check.status == "BOUNDARY_GROUNDED")
    import_rejected = sum(1 for check in checks if check.status == "IMPORT_REJECTED")
    missing_extensions: set[str] = set()
    for check in checks:
        for item in check.missing_support:
            if not item.startswith(("b0:", "v6:", "context_first_principle:", "route_clause:")):
                missing_extensions.add(item)
    if route_draft.verdict != "ROUTE_DRAFT_VALIDATED":
        verdict: Verdict = "PRIMITIVE_ROUTE_DRAFT_INVALID"
    elif import_rejected > 0:
        verdict = "TARGET_IMPORT_REJECTED"
    elif formal == len(checks):
        verdict = "CGSC_DERIVED_FROM_PRIMITIVES"
    elif successor > 0 and extension == 0:
        verdict = "SUCCESSOR_BASE_DERIVATION_REGISTERED"
    else:
        verdict = "PRIMITIVE_DERIVATION_NOT_CLOSED"
    route_draft_checks = validate_route_draft(draft_path, verdict, checks, sorted_tuple(missing_extensions))
    route_draft_checks_failed = sum(1 for check in route_draft_checks if not check.passed)
    if route_draft_checks_failed > 0:
        verdict = "PRIMITIVE_ROUTE_DRAFT_INVALID"
    return PrimitiveDerivationProbe(
        verdict=verdict,
        cgsc_route_draft=route_draft.verdict,
        route_draft_path=str(draft_path.relative_to(REPO_ROOT)),
        clauses=len(checks),
        formal_from_primitives=formal,
        successor_base_bound=successor,
        candidate_supported=candidate,
        extension_required=extension,
        boundary_grounded=boundary,
        import_rejected=import_rejected,
        route_draft_checks_passed=sum(1 for check in route_draft_checks if check.passed),
        route_draft_checks_failed=route_draft_checks_failed,
        missing_base_extensions=sorted_tuple(missing_extensions),
        checks=checks,
        route_draft_checks=route_draft_checks,
        next_blocker=(
            "promote the bound successor primitive base or prove its data from B0, then prove the six "
            "CGSC extensions from that bound base or reject CGSC as insufficient for full QM inevitability"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate whether CGSC clauses are derived from the current primitive base.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-clauses", action="store_true")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)))
    print(
        f"cgsc_primitive_derivation={probe.verdict} cgsc_route_draft={probe.cgsc_route_draft} "
        f"clauses={probe.clauses} formal={probe.formal_from_primitives} "
        f"successor_base_bound={probe.successor_base_bound} "
        f"candidate_supported={probe.candidate_supported} extension_required={probe.extension_required} "
        f"boundary_grounded={probe.boundary_grounded} import_rejected={probe.import_rejected} "
        f"missing_base_extensions={len(probe.missing_base_extensions)} "
        f"route_draft_checks_failed={probe.route_draft_checks_failed}"
    )
    if probe.missing_base_extensions:
        print(f"MISSING_EXTENSIONS {','.join(probe.missing_base_extensions)}")
    print(f"NEXT {probe.next_blocker}")
    if args.show_clauses:
        for check in probe.checks:
            print(f"{check.status} {check.id}: missing={','.join(check.missing_support) or '-'}")
            print(f"  obligation: {check.derivation_obligation}")
    if args.show_draft_checks:
        for draft_check in probe.route_draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("PRIMITIVE_ROUTE_DRAFT_INVALID", "TARGET_IMPORT_REJECTED"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
