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

import scripts.evaluate_born_readout_attempt as born_attempt  # noqa: E402
import scripts.evaluate_b1_cgsc_clause_derivation as b1_clause_derivation  # noqa: E402
import scripts.evaluate_fpd_projective_derivation as fpd_attempt  # noqa: E402
import scripts.evaluate_general_composite_attempt as composite_attempt  # noqa: E402
import scripts.evaluate_phase_scale_boundary_attempt as phase_scale_attempt  # noqa: E402
import scripts.evaluate_representation_classification_attempt as representation_attempt  # noqa: E402
import scripts.evaluate_unitary_dynamics_attempt as dynamics_attempt  # noqa: E402

LEAN_COMMAND = "lake build Proofs.QMClosure.QMSemanticKernelRoute"

Verdict = Literal[
    "SEMANTIC_KERNEL_ROUTE_REGISTERED",
    "SEMANTIC_KERNEL_CHECK_FAILED",
    "SEMANTIC_KERNEL_ROUTE_BLOCKED",
    "SEMANTIC_KERNEL_IMPORT_REJECTED",
]
CheckStatus = Literal["PASS", "FAIL"]
ClusterStatus = Literal["CONDITIONAL_READY", "BLOCKED", "IMPORT_REJECTED"]

B1_CGSC_CLOSED_CORE: tuple[str, ...] = (
    "nonunital_stable_distinguishability",
    "spectral_decomposition",
    "rich_d_cl_reversible_symmetry",
    "continuous_inheritance_family",
    "generator_closure",
    "entanglement_closure",
)


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class KernelCluster:
    id: str
    source_route: str
    verdict: str
    status: ClusterStatus
    covers: tuple[str, ...]
    open_core: tuple[str, ...]
    imports: tuple[str, ...]


@dataclass(frozen=True)
class SemanticKernelRouteProbe:
    verdict: Verdict
    lean_check: LeanCheck
    b1_cgsc_clause_derivation: str
    b1_projection: CheckStatus
    b1_projected_clusters: int
    clusters: int
    conditional_ready: int
    blocked: int
    import_rejected: int
    covered_obligations: int
    b1_closed_core: tuple[str, ...]
    open_core: tuple[str, ...]
    clusters_detail: list[KernelCluster]
    next_blocker: str


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


def find_fpd_route() -> fpd_attempt.RouteResult:
    for route in fpd_attempt.ROUTES:
        if route.name == "nusd_plus_conservative_projective_gluing":
            return fpd_attempt.evaluate_route(route)
    raise ValueError("missing fpd route")


def find_representation_route() -> representation_attempt.RouteResult:
    for route in representation_attempt.ROUTES:
        if route.name == "spectral_symmetry_route":
            return representation_attempt.evaluate_route(route)
    raise ValueError("missing representation route")


def find_born_route() -> born_attempt.RouteResult:
    for route in born_attempt.ROUTES:
        if route.name == "quadratic_context_probability_route":
            return born_attempt.evaluate_route(route)
    raise ValueError("missing Born route")


def find_dynamics_route() -> dynamics_attempt.RouteResult:
    for route in dynamics_attempt.ROUTES:
        if route.name == "continuous_generator_route":
            return dynamics_attempt.evaluate_route(route)
    raise ValueError("missing dynamics route")


def find_composite_route() -> composite_attempt.RouteResult:
    for route in composite_attempt.ROUTES:
        if route.name == "general_projective_composite_route":
            return composite_attempt.evaluate_route(route)
    raise ValueError("missing composite route")


def find_scale_route() -> phase_scale_attempt.RouteResult:
    for route in phase_scale_attempt.ROUTES:
        if route.name == "calibrated_phase_scale_boundary":
            return phase_scale_attempt.evaluate_route(route)
    raise ValueError("missing phase-scale route")


def status_from_route(verdict: str, imports: tuple[str, ...]) -> ClusterStatus:
    if imports:
        return "IMPORT_REJECTED"
    if verdict.startswith("CONDITIONAL") or verdict == "DERIVATION_CANDIDATE":
        return "CONDITIONAL_READY"
    return "BLOCKED"


def build_clusters() -> list[KernelCluster]:
    fpd = find_fpd_route()
    representation = find_representation_route()
    born = find_born_route()
    dynamics = find_dynamics_route()
    composite = find_composite_route()
    scale = find_scale_route()
    return [
        KernelCluster(
            id="residual_projective_kernel",
            source_route=fpd.route,
            verdict=fpd.verdict,
            status=status_from_route(fpd.verdict, fpd.imports),
            covers=(
                "finite_projection_determinacy",
                "projective_consistency",
                "nonunital_stable_distinguishability",
                "conservative_projective_gluing",
            ),
            open_core=("nonunital_stable_distinguishability", "conservative_projective_gluing"),
            imports=fpd.imports,
        ),
        KernelCluster(
            id="representation_kernel",
            source_route=representation.route,
            verdict=representation.verdict,
            status=status_from_route(representation.verdict, representation.imports),
            covers=("spectral_decomposition", "rich_d_cl_reversible_symmetry"),
            open_core=("spectral_decomposition", "rich_d_cl_reversible_symmetry"),
            imports=representation.imports,
        ),
        KernelCluster(
            id="readout_kernel",
            source_route=born.route,
            verdict=born.verdict,
            status=status_from_route(born.verdict, born.imports),
            covers=(
                "context_normalization",
                "exclusivity_additivity",
                "coarse_graining_consistency",
                "operational_equivalence_probability",
            ),
            open_core=("quadratic_context_probability_route",),
            imports=born.imports,
        ),
        KernelCluster(
            id="dynamics_kernel",
            source_route=dynamics.route,
            verdict=dynamics.verdict,
            status=status_from_route(dynamics.verdict, dynamics.imports),
            covers=(
                "d_cl_automorphism_dynamics",
                "overlap_preservation_dynamics",
                "projective_action",
                "continuous_inheritance_family",
                "generator_closure",
            ),
            open_core=("continuous_inheritance_family", "generator_closure"),
            imports=dynamics.imports,
        ),
        KernelCluster(
            id="composite_kernel",
            source_route=composite.route,
            verdict=composite.verdict,
            status=status_from_route(composite.verdict, composite.imports),
            covers=(
                "product_context_exhaustion",
                "local_tomography",
                "monoidal_associativity",
                "entanglement_closure",
                "projective_limit_consistency",
            ),
            open_core=("entanglement_closure", "projective_limit_consistency"),
            imports=composite.imports,
        ),
        KernelCluster(
            id="physical_scale_kernel",
            source_route=scale.route,
            verdict=scale.verdict,
            status=status_from_route(scale.verdict, scale.imports),
            covers=("physical_phase_scale_boundary",),
            open_core=("calibrated_phase_scale_boundary",),
            imports=scale.imports,
        ),
    ]


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


def build_probe() -> SemanticKernelRouteProbe:
    lean_check = run_lean_check()
    b1_clause_probe = b1_clause_derivation.build_probe()
    clusters = build_clusters()
    conditional = sum(1 for cluster in clusters if cluster.status == "CONDITIONAL_READY")
    blocked = sum(1 for cluster in clusters if cluster.status == "BLOCKED")
    imported = sum(1 for cluster in clusters if cluster.status == "IMPORT_REJECTED")
    covered = {obligation for cluster in clusters for obligation in cluster.covers}
    raw_open_core = {item for cluster in clusters for item in cluster.open_core}
    b1_closed_core = (
        B1_CGSC_CLOSED_CORE
        if b1_clause_probe.verdict == "B1_CGSC_CLAUSES_MACHINE_DERIVED"
        else ()
    )
    open_core = sorted_tuple(raw_open_core - set(b1_closed_core))
    if lean_check.status == "FAIL":
        verdict: Verdict = "SEMANTIC_KERNEL_CHECK_FAILED"
    elif imported > 0:
        verdict = "SEMANTIC_KERNEL_IMPORT_REJECTED"
    elif blocked > 0:
        verdict = "SEMANTIC_KERNEL_ROUTE_BLOCKED"
    else:
        verdict = "SEMANTIC_KERNEL_ROUTE_REGISTERED"
    return SemanticKernelRouteProbe(
        verdict=verdict,
        lean_check=lean_check,
        b1_cgsc_clause_derivation=b1_clause_probe.verdict,
        b1_projection=lean_check.status,
        b1_projected_clusters=len(clusters) if lean_check.status == "PASS" else 0,
        clusters=len(clusters),
        conditional_ready=conditional,
        blocked=blocked,
        import_rejected=imported,
        covered_obligations=len(covered),
        b1_closed_core=b1_closed_core,
        open_core=open_core,
        clusters_detail=clusters,
        next_blocker=(
            "prove external semantic adequacy for the remaining open kernel core after B1 CGSC closure; "
            "the B1 package now closes the structural core internally but does not by itself prove "
            "Hilbert/Born/unitary/tensor equivalence or full_QM_I"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Register the broad semantic-kernel route that groups all full-QM obligations."
    )
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-clusters", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"qm_semantic_kernel_route={probe.verdict} lean={probe.lean_check.status} "
        f"b1_projection={probe.b1_projection} b1_projected_clusters={probe.b1_projected_clusters} "
        f"b1_cgsc={probe.b1_cgsc_clause_derivation} b1_closed_core={len(probe.b1_closed_core)} "
        f"clusters={probe.clusters} conditional_ready={probe.conditional_ready} "
        f"blocked={probe.blocked} import_rejected={probe.import_rejected} "
        f"covered_obligations={probe.covered_obligations} open_core={len(probe.open_core)}"
    )
    print(f"NEXT {probe.next_blocker}")
    if probe.open_core:
        print(f"OPEN_CORE {','.join(probe.open_core)}")
    if args.show_clusters:
        for cluster in probe.clusters_detail:
            print(
                f"{cluster.status} {cluster.id}: route={cluster.source_route} "
                f"verdict={cluster.verdict} covers={','.join(cluster.covers)}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict != "SEMANTIC_KERNEL_ROUTE_REGISTERED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
