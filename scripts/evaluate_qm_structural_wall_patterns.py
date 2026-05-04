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

import scripts.evaluate_qm_hard_wall_probe as hard_wall  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as proof_closure  # noqa: E402

PatternVerdict = Literal[
    "PATTERN_CANDIDATE_FOUND",
    "PATTERN_INCOMPLETE",
    "PATTERN_REJECTED_IMPORT",
    "HARD_WALL_PROBE_FATAL",
]
AxisId = Literal[
    "finite_facticizable_witness_closure",
    "exposed_context_geometry",
    "reversible_context_symmetry",
    "coherent_refinement_flow",
    "generated_composite_closure",
]
AxisStatus = Literal["COVERS_WALLS", "MISSING_WALLS", "IMPORT_REJECTED"]


@dataclass(frozen=True)
class PatternAxis:
    id: AxisId
    statement: str
    covers: tuple[str, ...]
    candidate_imports: tuple[str, ...]
    forbidden_imports: tuple[str, ...]
    open_obligation: str


@dataclass(frozen=True)
class AxisCheck:
    id: AxisId
    status: AxisStatus
    statement: str
    covered_walls: tuple[str, ...]
    missing_walls: tuple[str, ...]
    forbidden_import_hits: tuple[str, ...]
    open_obligation: str


@dataclass(frozen=True)
class StructuralWallPatternProbe:
    verdict: PatternVerdict
    hard_wall_verdict: hard_wall.ProbeVerdict
    structural_walls: tuple[str, ...]
    covered_walls: tuple[str, ...]
    uncovered_walls: tuple[str, ...]
    common_candidate_principle: str
    candidate_status: str
    axis_count: int
    rejected_imports: int
    axes: list[AxisCheck]
    next_decisive_test: str


STRUCTURAL_WALL_IDS: tuple[str, ...] = (
    "nonunital_stable_distinguishability",
    "spectral_decomposition",
    "rich_d_cl_reversible_symmetry",
    "continuous_inheritance_family",
    "generator_closure",
    "entanglement_closure",
)

FORBIDDEN_TARGET_IMPORTS: tuple[str, ...] = (
    "born_rule",
    "complex_hilbert_space",
    "generator_assumed",
    "hilbert_tensor_product",
    "spectral_theorem",
    "stone_theorem",
    "unitary_group",
)

PATTERN_AXES: tuple[PatternAxis, ...] = (
    PatternAxis(
        id="finite_facticizable_witness_closure",
        statement=(
            "Every stable distinction or invariant that can affect a readout must enter a finite "
            "facticizable witness route or be outside physical scope."
        ),
        covers=(
            "nonunital_stable_distinguishability",
            "entanglement_closure",
        ),
        candidate_imports=(),
        forbidden_imports=("born_rule", "complex_hilbert_space", "hilbert_tensor_product"),
        open_obligation="derive NUSD/no-hidden-invariant closure from context-first facticization",
    ),
    PatternAxis(
        id="exposed_context_geometry",
        statement=(
            "Stable finite witness routes must expose enough mutually exclusive context records to decompose "
            "admissible states without assuming a spectral theorem."
        ),
        covers=(
            "spectral_decomposition",
            "rich_d_cl_reversible_symmetry",
        ),
        candidate_imports=(),
        forbidden_imports=("complex_hilbert_space", "spectral_theorem", "unitary_group"),
        open_obligation="derive spectral/exposed-context decomposition from D_cl and finite witness closure",
    ),
    PatternAxis(
        id="reversible_context_symmetry",
        statement=(
            "Admissible reversible inheritance acts must preserve D_cl, normalized overlap, and exposed contexts "
            "strongly enough to generate the symmetry route without naming unitary groups."
        ),
        covers=(
            "rich_d_cl_reversible_symmetry",
            "continuous_inheritance_family",
        ),
        candidate_imports=(),
        forbidden_imports=("complex_hilbert_space", "unitary_group", "stone_theorem"),
        open_obligation="derive rich reversible D_cl symmetry and continuity from inheritance acts",
    ),
    PatternAxis(
        id="coherent_refinement_flow",
        statement=(
            "Compatible finite refinement steps must form coherent families whose limiting behavior has no new "
            "stable directions and admits generator-compatible bookkeeping."
        ),
        covers=(
            "continuous_inheritance_family",
            "generator_closure",
        ),
        candidate_imports=(),
        forbidden_imports=("generator_assumed", "stone_theorem", "unitary_group"),
        open_obligation="derive continuity/generator closure from finite refinement coherence",
    ),
    PatternAxis(
        id="generated_composite_closure",
        statement=(
            "Composite stable facts must be generated inside product/context refinement routes, including "
            "non-product facts, without hidden joint-only carrier imports."
        ),
        covers=(
            "entanglement_closure",
            "nonunital_stable_distinguishability",
        ),
        candidate_imports=(),
        forbidden_imports=("born_rule", "complex_hilbert_space", "hilbert_tensor_product"),
        open_obligation="derive entanglement closure from generated composites plus no hidden joint-only invariants",
    ),
)


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


def structural_wall_ids_from_probe(probe: hard_wall.HardWallProbe) -> tuple[str, ...]:
    return tuple(check.id for check in probe.checks if check.status == "STRUCTURAL_WALL_OPEN")


def check_axis(axis: PatternAxis, structural_walls: tuple[str, ...]) -> AxisCheck:
    structural_wall_set = set(structural_walls)
    covered = tuple(wall_id for wall_id in axis.covers if wall_id in structural_wall_set)
    missing = tuple(wall_id for wall_id in axis.covers if wall_id not in structural_wall_set)
    import_hits = tuple(import_id for import_id in axis.candidate_imports if import_id in FORBIDDEN_TARGET_IMPORTS)
    if import_hits:
        status: AxisStatus = "IMPORT_REJECTED"
    elif missing:
        status = "MISSING_WALLS"
    else:
        status = "COVERS_WALLS"
    return AxisCheck(
        id=axis.id,
        status=status,
        statement=axis.statement,
        covered_walls=covered,
        missing_walls=missing,
        forbidden_import_hits=import_hits,
        open_obligation=axis.open_obligation,
    )


def build_probe(manifest_path: Path = proof_closure.DEFAULT_MANIFEST) -> StructuralWallPatternProbe:
    wall_probe = hard_wall.build_probe(manifest_path)
    structural_walls = structural_wall_ids_from_probe(wall_probe)
    axis_checks = [check_axis(axis, structural_walls) for axis in PATTERN_AXES]
    covered_wall_set: set[str] = set()
    for axis_check in axis_checks:
        covered_wall_set.update(axis_check.covered_walls)
    uncovered = tuple(wall_id for wall_id in structural_walls if wall_id not in covered_wall_set)
    rejected_imports = sum(len(axis.forbidden_import_hits) for axis in axis_checks)
    if wall_probe.fatal_now:
        verdict: PatternVerdict = "HARD_WALL_PROBE_FATAL"
    elif rejected_imports > 0:
        verdict = "PATTERN_REJECTED_IMPORT"
    elif uncovered:
        verdict = "PATTERN_INCOMPLETE"
    else:
        verdict = "PATTERN_CANDIDATE_FOUND"
    return StructuralWallPatternProbe(
        verdict=verdict,
        hard_wall_verdict=wall_probe.verdict,
        structural_walls=structural_walls,
        covered_walls=sorted_tuple(covered_wall_set),
        uncovered_walls=uncovered,
        common_candidate_principle="context_generated_stable_closure",
        candidate_status="candidate_unifying_principle_not_proof",
        axis_count=len(axis_checks),
        rejected_imports=rejected_imports,
        axes=axis_checks,
        next_decisive_test=(
            "formalize context_generated_stable_closure and test whether it derives NUSD, "
            "spectral decomposition, reversible symmetry/continuity, generator closure, and "
            "entanglement closure without Hilbert/Born/unitary/tensor imports"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Search for shared non-imported patterns across the current QM structural walls."
    )
    parser.add_argument("--manifest", default=str(proof_closure.DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-axes", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.manifest)))
    print(
        f"qm_structural_wall_patterns={probe.verdict} hard_wall_verdict={probe.hard_wall_verdict} "
        f"structural_walls={len(probe.structural_walls)} covered={len(probe.covered_walls)} "
        f"uncovered={len(probe.uncovered_walls)} axis_count={probe.axis_count} "
        f"candidate={probe.common_candidate_principle} status={probe.candidate_status} "
        f"rejected_imports={probe.rejected_imports}"
    )
    if probe.uncovered_walls:
        print(f"UNCOVERED {','.join(probe.uncovered_walls)}")
    print(f"NEXT {probe.next_decisive_test}")
    if args.show_axes:
        for axis in probe.axes:
            print(f"{axis.status} {axis.id}: covers={','.join(axis.covered_walls)}")
            print(f"  statement: {axis.statement}")
            print(f"  obligation: {axis.open_obligation}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("HARD_WALL_PROBE_FATAL", "PATTERN_REJECTED_IMPORT"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
