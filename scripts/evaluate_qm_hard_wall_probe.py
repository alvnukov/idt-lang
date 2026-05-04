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

import scripts.evaluate_full_qm_proof_attempt as proof_attempt  # noqa: E402
import scripts.evaluate_full_qm_proof_closure as proof_closure  # noqa: E402

ProbeVerdict = Literal[
    "FATAL_WALL",
    "OPEN_STRUCTURAL_WALL",
    "PROOF_ENGINEERING_GAP",
    "NO_WALL_DETECTED",
]
ProbeStatus = Literal[
    "PROVED",
    "SCAFFOLD_PRESENT",
    "PROOF_ARTIFACT_MISSING",
    "STRUCTURAL_WALL_OPEN",
    "IMPORT_WALL",
]
ProbeClass = Literal[
    "bridge_scaffold",
    "structural_wall",
    "boundary",
]


@dataclass(frozen=True)
class ObligationProbeSpec:
    classification: ProbeClass
    scaffold_refs: tuple[str, ...]
    wall_reason: str
    next_step: str


@dataclass(frozen=True)
class ObligationProbe:
    id: str
    cluster: str
    classification: ProbeClass
    status: ProbeStatus
    reason: str
    next_step: str
    scaffold_refs: tuple[str, ...]
    missing_scaffold_refs: tuple[str, ...]


@dataclass(frozen=True)
class HardWallProbe:
    verdict: ProbeVerdict
    fatal_now: bool
    route_status: proof_attempt.AttemptVerdict
    closure_status: proof_closure.ClosureVerdict
    proved: int
    scaffold_present: int
    proof_artifact_missing: int
    structural_walls: int
    import_walls: int
    checks: list[ObligationProbe]


OBLIGATION_SPECS: dict[str, ObligationProbeSpec] = {
    "finite_projection_determinacy": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("scripts/evaluate_fpd_projective_derivation.py",),
        wall_reason="FPD is conditionally reduced to NUSD plus finite projective gluing.",
        next_step="derive NUSD or explicitly demote the route to a boundary assumption",
    ),
    "projective_consistency": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ProjectionScaffoldsDraft.lean",),
        wall_reason="endomap gluing algebra exists, but IDT projective restrictions are not derived as endomaps",
        next_step="derive projective restriction endomap semantics from IDT projection rules",
    ),
    "nonunital_stable_distinguishability": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="NUSD is a lower-principle candidate, not a derived theorem",
        next_step="try to derive NUSD from context-first facticization, or mark it as an explicit primitive/boundary",
    ),
    "conservative_projective_gluing": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ProjectionScaffoldsDraft.lean",),
        wall_reason="commuting-idempotent gluing is checkable only after the projection semantics is supplied",
        next_step="derive conservative gluing semantics without Hilbert projectors",
    ),
    "spectral_decomposition": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="spectral decomposition is not derivable from the current carrier-neutral primitives",
        next_step="derive exposed-context spectrality from finite distinguishability geometry or add a new audited principle",
    ),
    "rich_d_cl_reversible_symmetry": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="the route needs enough reversible symmetry without importing unitary groups",
        next_step="prove rich D_cl-preserving symmetry from inheritance acts or expose it as an assumption",
    ),
    "context_normalization": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ReadoutScaffoldsDraft.lean",),
        wall_reason="finite positive-weight normalization is checkable only after IDT readout weights are derived",
        next_step="derive finite positive weights from admissible facticization",
    ),
    "exclusivity_additivity": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ReadoutScaffoldsDraft.lean",),
        wall_reason="finite weight arithmetic is present, but additivity over IDT exclusive alternatives is not a proof artifact",
        next_step="connect IDT exclusive alternatives to the finite block-weight model",
    ),
    "coarse_graining_consistency": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ReadoutScaffoldsDraft.lean",),
        wall_reason="explicit finite block coarse-graining is checkable only after admissible coarse-graining is derived",
        next_step="derive admissible coarse-graining as finite block partitions",
    ),
    "operational_equivalence_probability": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ReadoutScaffoldsDraft.lean",),
        wall_reason="equivalence-respecting weights are checkable only when the weight function is derived",
        next_step="derive equivalence-respecting readout weights from operational equivalence",
    ),
    "d_cl_automorphism_dynamics": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/InheritanceScaffoldsDraft.lean",),
        wall_reason="preservation algebra is checkable, but automorphism status is supplied as a predicate",
        next_step="derive D_cl automorphism status for reversible inheritance acts",
    ),
    "overlap_preservation_dynamics": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/InheritanceScaffoldsDraft.lean",),
        wall_reason="overlap preservation is checkable only after the overlap invariant is derived",
        next_step="derive normalized overlap preservation from the inheritance relation",
    ),
    "projective_action": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/InheritanceScaffoldsDraft.lean",),
        wall_reason="projective action is encoded, but admissibility of the action is not derived",
        next_step="derive projective action for admissible reversible inheritance maps",
    ),
    "continuous_inheritance_family": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="continuity is not present in the finite primitive base",
        next_step="derive a continuity principle from finite refinement limits or mark it as a boundary",
    ),
    "generator_closure": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="generator closure would import Stone/Hamiltonian structure unless independently derived",
        next_step="derive generator closure from continuous inheritance without assuming unitary dynamics",
    ),
    "product_context_exhaustion": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=(
            "scripts/evaluate_context_product_encoding_bridge.py",
            "Proofs/QMClosure/CompositeScaffoldsDraft.lean",
        ),
        wall_reason="finite product tables are witnessed, but universal product-context exhaustion is not derived",
        next_step="prove arbitrary admissible context products embed into finite product syntax or a quotient",
    ),
    "local_tomography": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/CompositeScaffoldsDraft.lean",),
        wall_reason="local tomography follows from supplied product-readout separation, not yet from primitives",
        next_step="derive product-readout separation from context-product exhaustion",
    ),
    "monoidal_associativity": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=(
            "scripts/evaluate_context_product_encoding_bridge.py",
            "Proofs/QMClosure/MonoidalAssociativityDraft.lean",
        ),
        wall_reason="append-compatible encoding gives associativity; admissible IDT products are not yet encoded",
        next_step="derive append-compatible finite encoding for admissible context products",
    ),
    "entanglement_closure": ObligationProbeSpec(
        classification="structural_wall",
        scaffold_refs=(),
        wall_reason="non-product composite facts are not closed without importing tensor structure",
        next_step="derive entanglement closure from finite context products plus no hidden joint-only invariants",
    ),
    "projective_limit_consistency": ObligationProbeSpec(
        classification="bridge_scaffold",
        scaffold_refs=("Proofs/QMClosure/ProjectiveLimitScaffoldDraft.lean",),
        wall_reason="compatibility implies consistency only after compatibility is supplied",
        next_step="derive projective-limit compatibility from finite refinement semantics",
    ),
    "physical_phase_scale_boundary": ObligationProbeSpec(
        classification="boundary",
        scaffold_refs=("Proofs/QMClosure/BoundaryScaffoldsDraft.lean",),
        wall_reason="physical hbar remains calibrated, not first-principles derived",
        next_step="keep this as a boundary unless an independent action-scale theorem is found",
    ),
}


def require_spec(obligation_id: str) -> ObligationProbeSpec:
    spec = OBLIGATION_SPECS.get(obligation_id)
    if spec is None:
        raise ValueError(f"missing hard-wall probe spec for obligation {obligation_id}")
    return spec


def missing_scaffold_refs(scaffold_refs: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(ref for ref in scaffold_refs if not (REPO_ROOT / ref).exists())


def status_for_check(check: proof_closure.ObligationCheck, spec: ObligationProbeSpec) -> ProbeStatus:
    if check.status == "PROVED":
        return "PROVED"
    if check.status == "IMPORT_REJECTED":
        return "IMPORT_WALL"
    if spec.classification == "structural_wall":
        return "STRUCTURAL_WALL_OPEN"
    missing_refs = missing_scaffold_refs(spec.scaffold_refs)
    if spec.scaffold_refs and not missing_refs:
        return "SCAFFOLD_PRESENT"
    return "PROOF_ARTIFACT_MISSING"


def reason_for_probe(check: proof_closure.ObligationCheck, spec: ObligationProbeSpec, status: ProbeStatus) -> str:
    if status == "PROVED":
        return check.reason
    if status == "IMPORT_WALL":
        return check.reason
    if status == "SCAFFOLD_PRESENT":
        return f"{check.reason}; bridge scaffold exists: {spec.wall_reason}"
    return f"{check.reason}; {spec.wall_reason}"


def build_probe(manifest_path: Path = proof_closure.DEFAULT_MANIFEST) -> HardWallProbe:
    route = proof_attempt.build_attempt()
    closure = proof_closure.build_closure_attempt(manifest_path)
    checks: list[ObligationProbe] = []
    for check in closure.checks:
        spec = require_spec(check.id)
        missing_refs = missing_scaffold_refs(spec.scaffold_refs)
        probe_status = status_for_check(check, spec)
        checks.append(
            ObligationProbe(
                id=check.id,
                cluster=check.cluster,
                classification=spec.classification,
                status=probe_status,
                reason=reason_for_probe(check, spec, probe_status),
                next_step=spec.next_step,
                scaffold_refs=spec.scaffold_refs,
                missing_scaffold_refs=missing_refs,
            )
        )

    proved = sum(1 for check in checks if check.status == "PROVED")
    scaffold_present = sum(1 for check in checks if check.status == "SCAFFOLD_PRESENT")
    proof_artifact_missing = sum(1 for check in checks if check.status == "PROOF_ARTIFACT_MISSING")
    structural_walls = sum(1 for check in checks if check.status == "STRUCTURAL_WALL_OPEN")
    import_walls = sum(1 for check in checks if check.status == "IMPORT_WALL")
    fatal_now = route.verdict == "BLOCKED" or closure.verdict == "IMPORTED_ASSUMPTION_REJECTED" or import_walls > 0
    if fatal_now:
        verdict: ProbeVerdict = "FATAL_WALL"
    elif structural_walls > 0:
        verdict = "OPEN_STRUCTURAL_WALL"
    elif proof_artifact_missing > 0 or scaffold_present > 0:
        verdict = "PROOF_ENGINEERING_GAP"
    else:
        verdict = "NO_WALL_DETECTED"
    return HardWallProbe(
        verdict=verdict,
        fatal_now=fatal_now,
        route_status=route.verdict,
        closure_status=closure.verdict,
        proved=proved,
        scaffold_present=scaffold_present,
        proof_artifact_missing=proof_artifact_missing,
        structural_walls=structural_walls,
        import_walls=import_walls,
        checks=checks,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Classify current full-QM closure gaps as fatal walls, structural walls, or bridge scaffolds.")
    parser.add_argument("--manifest", default=str(proof_closure.DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-all", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.manifest)))
    print(
        f"qm_hard_wall_probe={probe.verdict} fatal_now={str(probe.fatal_now).lower()} "
        f"route_status={probe.route_status} closure_status={probe.closure_status} "
        f"proved={probe.proved} scaffold_present={probe.scaffold_present} "
        f"proof_artifact_missing={probe.proof_artifact_missing} "
        f"structural_walls={probe.structural_walls} import_walls={probe.import_walls}"
    )
    for check in probe.checks:
        if not args.show_all and check.status not in ("STRUCTURAL_WALL_OPEN", "IMPORT_WALL", "PROOF_ARTIFACT_MISSING"):
            continue
        print(f"{check.status} {check.id} [{check.cluster}]: {check.reason}")
        print(f"  next: {check.next_step}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.fatal_now:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
