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

import scripts.evaluate_full_qm_proof_closure as proof_closure  # noqa: E402
import scripts.evaluate_qm_structural_wall_patterns as wall_patterns  # noqa: E402

Verdict = Literal[
    "CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE",
    "CANDIDATE_INCOMPLETE",
    "TARGET_IMPORT_REJECTED",
    "HARD_WALL_PROBE_FATAL",
]
ClauseId = Literal[
    "finite_generation",
    "facticizable_separation",
    "exposed_context_decomposition",
    "reversible_route_closure",
    "coherent_refinement_flow",
    "composite_route_generation",
    "import_boundary",
]
TargetStatus = Literal["CONDITIONALLY_COVERED", "MISSING_CLAUSE", "IMPORT_REJECTED"]
ControlStatus = Literal["REJECTED", "SURVIVED"]


@dataclass(frozen=True)
class CandidateClause:
    id: ClauseId
    statement: str
    primitive_grounding: tuple[str, ...]
    candidate_imports: tuple[str, ...]


@dataclass(frozen=True)
class ClosureTarget:
    id: str
    requires: tuple[ClauseId, ...]
    forbidden_imports: tuple[str, ...]
    conditional_statement: str


@dataclass(frozen=True)
class NegativeControl:
    id: str
    candidate_imports: tuple[str, ...]
    reason: str


@dataclass(frozen=True)
class TargetCheck:
    id: str
    status: TargetStatus
    missing_clauses: tuple[str, ...]
    import_hits: tuple[str, ...]
    conditional_statement: str


@dataclass(frozen=True)
class ControlCheck:
    id: str
    status: ControlStatus
    import_hits: tuple[str, ...]
    reason: str


@dataclass(frozen=True)
class CandidateProbe:
    verdict: Verdict
    principle_id: str
    candidate_status: str
    pattern_verdict: wall_patterns.PatternVerdict
    targets: int
    conditionally_covered: int
    missing_targets: int
    target_import_rejections: int
    negative_controls: int
    rejected_controls: int
    survived_controls: int
    clauses: list[CandidateClause]
    target_checks: list[TargetCheck]
    control_checks: list[ControlCheck]
    next_formalization_step: str
    forbidden_upgrade: tuple[str, ...]


FORBIDDEN_TARGET_IMPORTS: tuple[str, ...] = wall_patterns.FORBIDDEN_TARGET_IMPORTS

CLAUSES: tuple[CandidateClause, ...] = (
    CandidateClause(
        id="finite_generation",
        statement=(
            "Stable physical structures must have finite context/readout/refinement generation routes "
            "or be outside physical scope."
        ),
        primitive_grounding=("history_space", "event_algebra", "readout_context_family", "inheritance_act_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="facticizable_separation",
        statement=(
            "A stable distinction that can affect a readout must be separated by an admissible finite "
            "facticizable witness."
        ),
        primitive_grounding=("readout_context_family", "inheritance_act_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="exposed_context_decomposition",
        statement=(
            "Finite generated stable states decompose into mutually exclusive exposed context records "
            "when the context family supplies a complete facticizable partition."
        ),
        primitive_grounding=("event_algebra", "readout_context_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="reversible_route_closure",
        statement=(
            "Admissible reversible inheritance acts are route automorphisms preserving D_cl, normalized "
            "overlap, and exposed context records."
        ),
        primitive_grounding=("inheritance_act_family", "readout_context_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="coherent_refinement_flow",
        statement=(
            "Compatible finite refinement families add no new stable directions and admit generator-compatible "
            "bookkeeping without importing a continuum generator."
        ),
        primitive_grounding=("history_space", "inheritance_act_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="composite_route_generation",
        statement=(
            "Composite facts, including non-product facts, must be generated inside admissible product/context "
            "refinement routes rather than by hidden joint-only carrier degrees."
        ),
        primitive_grounding=("event_algebra", "readout_context_family", "inheritance_act_family"),
        candidate_imports=(),
    ),
    CandidateClause(
        id="import_boundary",
        statement="The candidate principle may not cite Hilbert, Born, unitary, tensor, Stone, or spectral theorem imports.",
        primitive_grounding=("sections/01-primitives.md",),
        candidate_imports=(),
    ),
)

CLOSURE_TARGETS: tuple[ClosureTarget, ...] = (
    ClosureTarget(
        id="nonunital_stable_distinguishability",
        requires=("finite_generation", "facticizable_separation", "import_boundary"),
        forbidden_imports=("born_rule", "complex_hilbert_space"),
        conditional_statement="NUSD follows if all readout-relevant stable distinctions require finite facticizable witnesses.",
    ),
    ClosureTarget(
        id="spectral_decomposition",
        requires=("finite_generation", "exposed_context_decomposition", "import_boundary"),
        forbidden_imports=("complex_hilbert_space", "spectral_theorem"),
        conditional_statement="Spectrality follows only as exposed-context decomposition, not as an imported spectral theorem.",
    ),
    ClosureTarget(
        id="rich_d_cl_reversible_symmetry",
        requires=("exposed_context_decomposition", "reversible_route_closure", "import_boundary"),
        forbidden_imports=("complex_hilbert_space", "unitary_group"),
        conditional_statement="Rich symmetry follows if reversible inheritance acts close on exposed-context D_cl routes.",
    ),
    ClosureTarget(
        id="continuous_inheritance_family",
        requires=("reversible_route_closure", "coherent_refinement_flow", "import_boundary"),
        forbidden_imports=("stone_theorem", "unitary_group"),
        conditional_statement="Continuity follows only as coherent finite-refinement flow, not as a supplied Lie group.",
    ),
    ClosureTarget(
        id="generator_closure",
        requires=("coherent_refinement_flow", "import_boundary"),
        forbidden_imports=("generator_assumed", "stone_theorem", "unitary_group"),
        conditional_statement="Generator closure follows only as bookkeeping of coherent refinement, not as Hamiltonian import.",
    ),
    ClosureTarget(
        id="entanglement_closure",
        requires=("finite_generation", "facticizable_separation", "composite_route_generation", "import_boundary"),
        forbidden_imports=("born_rule", "complex_hilbert_space", "hilbert_tensor_product"),
        conditional_statement="Entanglement closure follows only for non-product facts generated inside composite context routes.",
    ),
)

NEGATIVE_CONTROLS: tuple[NegativeControl, ...] = (
    NegativeControl(
        id="hidden_hilbert_carrier_import",
        candidate_imports=("complex_hilbert_space",),
        reason="carrier structure cannot be supplied after the finite generation route",
    ),
    NegativeControl(
        id="born_rule_import",
        candidate_imports=("born_rule",),
        reason="readout probabilities cannot be imported as the target rule",
    ),
    NegativeControl(
        id="unitary_group_import",
        candidate_imports=("unitary_group",),
        reason="reversible symmetry cannot be supplied by naming the unitary group",
    ),
    NegativeControl(
        id="hilbert_tensor_product_import",
        candidate_imports=("hilbert_tensor_product",),
        reason="composite closure cannot be supplied by naming the Hilbert tensor product",
    ),
    NegativeControl(
        id="stone_generator_import",
        candidate_imports=("stone_theorem", "generator_assumed"),
        reason="generator closure cannot be supplied by Stone/Hamiltonian structure",
    ),
    NegativeControl(
        id="spectral_theorem_import",
        candidate_imports=("spectral_theorem",),
        reason="exposed-context decomposition cannot be supplied by the spectral theorem",
    ),
)


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


def clause_ids(clauses: tuple[CandidateClause, ...]) -> set[str]:
    return {clause.id for clause in clauses}


def candidate_imports(clauses: tuple[CandidateClause, ...]) -> set[str]:
    imports: set[str] = set()
    for clause in clauses:
        imports.update(clause.candidate_imports)
    return imports


def check_target(target: ClosureTarget, clauses: tuple[CandidateClause, ...]) -> TargetCheck:
    available_clause_ids = clause_ids(clauses)
    imports = candidate_imports(clauses)
    missing = tuple(clause_id for clause_id in target.requires if clause_id not in available_clause_ids)
    import_hits = tuple(import_id for import_id in target.forbidden_imports if import_id in imports)
    if import_hits:
        status: TargetStatus = "IMPORT_REJECTED"
    elif missing:
        status = "MISSING_CLAUSE"
    else:
        status = "CONDITIONALLY_COVERED"
    return TargetCheck(
        id=target.id,
        status=status,
        missing_clauses=missing,
        import_hits=import_hits,
        conditional_statement=target.conditional_statement,
    )


def check_control(control: NegativeControl) -> ControlCheck:
    import_hits = tuple(import_id for import_id in control.candidate_imports if import_id in FORBIDDEN_TARGET_IMPORTS)
    status: ControlStatus = "REJECTED" if import_hits else "SURVIVED"
    return ControlCheck(
        id=control.id,
        status=status,
        import_hits=import_hits,
        reason=control.reason,
    )


def structural_targets_match_pattern(target_checks: list[TargetCheck], pattern_probe: wall_patterns.StructuralWallPatternProbe) -> bool:
    target_ids = {target.id for target in target_checks}
    return set(pattern_probe.structural_walls).issubset(target_ids)


def build_probe(manifest_path: Path = proof_closure.DEFAULT_MANIFEST) -> CandidateProbe:
    pattern_probe = wall_patterns.build_probe(manifest_path)
    target_checks = [check_target(target, CLAUSES) for target in CLOSURE_TARGETS]
    control_checks = [check_control(control) for control in NEGATIVE_CONTROLS]
    conditional = sum(1 for check in target_checks if check.status == "CONDITIONALLY_COVERED")
    missing = sum(1 for check in target_checks if check.status == "MISSING_CLAUSE")
    target_import_rejections = sum(1 for check in target_checks if check.status == "IMPORT_REJECTED")
    rejected_controls = sum(1 for check in control_checks if check.status == "REJECTED")
    survived_controls = sum(1 for check in control_checks if check.status == "SURVIVED")
    if pattern_probe.verdict == "HARD_WALL_PROBE_FATAL":
        verdict: Verdict = "HARD_WALL_PROBE_FATAL"
    elif target_import_rejections > 0:
        verdict = "TARGET_IMPORT_REJECTED"
    elif missing > 0 or survived_controls > 0 or not structural_targets_match_pattern(target_checks, pattern_probe):
        verdict = "CANDIDATE_INCOMPLETE"
    else:
        verdict = "CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE"
    return CandidateProbe(
        verdict=verdict,
        principle_id="context_generated_stable_closure",
        candidate_status="candidate_principle_not_formal_proof",
        pattern_verdict=pattern_probe.verdict,
        targets=len(target_checks),
        conditionally_covered=conditional,
        missing_targets=missing,
        target_import_rejections=target_import_rejections,
        negative_controls=len(control_checks),
        rejected_controls=rejected_controls,
        survived_controls=survived_controls,
        clauses=list(CLAUSES),
        target_checks=target_checks,
        control_checks=control_checks,
        next_formalization_step=(
            "turn the seven clauses into a theorem-card/proof-route draft and test each clause against "
            "IDT primitives before any proof-status upgrade"
        ),
        forbidden_upgrade=(
            "does_not_prove_full_QM_I",
            "does_not_derive_Hilbert_space",
            "does_not_derive_Born_rule",
            "does_not_derive_unitary_dynamics",
            "does_not_derive_tensor_composition",
            "does_not_treat_candidate_principle_as_formal_proof",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Evaluate the context-generated stable closure candidate against all current QM structural walls."
    )
    parser.add_argument("--manifest", default=str(proof_closure.DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-targets", action="store_true")
    parser.add_argument("--show-controls", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.manifest)))
    print(
        f"context_generated_stable_closure={probe.verdict} principle={probe.principle_id} "
        f"status={probe.candidate_status} pattern={probe.pattern_verdict} "
        f"targets={probe.targets} conditional={probe.conditionally_covered} missing={probe.missing_targets} "
        f"target_import_rejections={probe.target_import_rejections} controls={probe.negative_controls} "
        f"rejected_controls={probe.rejected_controls} survived_controls={probe.survived_controls}"
    )
    print(f"NEXT {probe.next_formalization_step}")
    if args.show_targets:
        for target_check in probe.target_checks:
            print(f"{target_check.status} {target_check.id}: {target_check.conditional_statement}")
    if args.show_controls:
        for control_check in probe.control_checks:
            print(
                f"{control_check.status} {control_check.id}: "
                f"imports={','.join(control_check.import_hits)} reason={control_check.reason}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("HARD_WALL_PROBE_FATAL", "TARGET_IMPORT_REJECTED"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
