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

import scripts.evaluate_full_qm_proof_attempt as full_attempt  # noqa: E402

ClosureVerdict = Literal[
    "FULL_QM_PROVED",
    "PROOF_ARTIFACTS_MISSING",
    "IMPORTED_ASSUMPTION_REJECTED",
    "ROUTE_NOT_READY",
]
CheckStatus = Literal["PROVED", "MISSING_ARTIFACT", "INCOMPLETE_ARTIFACT", "IMPORT_REJECTED"]


@dataclass(frozen=True)
class ProofArtifact:
    system: str
    file: str
    theorem: str
    check_command: str
    verified: bool


@dataclass(frozen=True)
class ProofObligation:
    id: str
    cluster: str
    required_statement: str
    forbidden_imports: tuple[str, ...]


@dataclass(frozen=True)
class ObligationCheck:
    id: str
    cluster: str
    status: CheckStatus
    reason: str
    artifact: ProofArtifact | None


@dataclass(frozen=True)
class ClosureAttempt:
    verdict: ClosureVerdict
    route_status: full_attempt.AttemptVerdict
    proved: int
    missing_artifacts: int
    incomplete_artifacts: int
    imported_artifacts: int
    checks: list[ObligationCheck]


OBLIGATIONS: tuple[ProofObligation, ...] = (
    ProofObligation(
        id="finite_projection_determinacy",
        cluster="residual_closure",
        required_statement="Derive finite projection determinacy from IDT primitive rules.",
        forbidden_imports=("hilbert_space", "projector_axiom", "born_rule"),
    ),
    ProofObligation(
        id="projective_consistency",
        cluster="residual_closure",
        required_statement="Derive projective consistency without assuming Hilbert projectors.",
        forbidden_imports=("hilbert_space", "projector_axiom", "born_rule"),
    ),
    ProofObligation(
        id="nonunital_stable_distinguishability",
        cluster="fpd_projective_derivation",
        required_statement="Prove NUSD as an IDT theorem or mark it as an explicit boundary assumption.",
        forbidden_imports=("positive_operator", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="conservative_projective_gluing",
        cluster="fpd_projective_derivation",
        required_statement="Prove conservative projective gluing from finite context/facticization rules.",
        forbidden_imports=("projector_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="spectral_decomposition",
        cluster="representation",
        required_statement="Prove spectral decomposition for admissible carriers from IDT constraints.",
        forbidden_imports=("spectral_theorem_assumed", "hilbert_space", "self_adjoint_operator"),
    ),
    ProofObligation(
        id="rich_d_cl_reversible_symmetry",
        cluster="representation",
        required_statement="Prove enough D_cl-preserving reversible symmetry without importing unitary groups.",
        forbidden_imports=("unitary_group", "wigner_theorem", "hilbert_space"),
    ),
    ProofObligation(
        id="context_normalization",
        cluster="born_readout",
        required_statement="Prove stable normalization for every admissible finite readout context.",
        forbidden_imports=("born_rule", "probability_axiom", "hilbert_space"),
    ),
    ProofObligation(
        id="exclusivity_additivity",
        cluster="born_readout",
        required_statement="Prove additivity over facticized exclusive alternatives.",
        forbidden_imports=("born_rule", "kolmogorov_axioms_assumed", "hilbert_space"),
    ),
    ProofObligation(
        id="coarse_graining_consistency",
        cluster="born_readout",
        required_statement="Prove readout stability under admissible coarse-graining.",
        forbidden_imports=("born_rule", "hilbert_space", "projective_measurement"),
    ),
    ProofObligation(
        id="operational_equivalence_probability",
        cluster="born_readout",
        required_statement="Prove equal probabilities for operationally equivalent readout events.",
        forbidden_imports=("born_rule", "hilbert_space", "trace_rule"),
    ),
    ProofObligation(
        id="d_cl_automorphism_dynamics",
        cluster="dynamics",
        required_statement="Prove reversible inheritance acts as D_cl automorphisms.",
        forbidden_imports=("unitary_evolution", "wigner_theorem", "hilbert_space"),
    ),
    ProofObligation(
        id="overlap_preservation_dynamics",
        cluster="dynamics",
        required_statement="Prove reversible inheritance preserves normalized overlap.",
        forbidden_imports=("unitary_evolution", "inner_product_axiom", "hilbert_space"),
    ),
    ProofObligation(
        id="projective_action",
        cluster="dynamics",
        required_statement="Prove admissible reversible inheritance acts on projective facts.",
        forbidden_imports=("projective_hilbert_space", "wigner_theorem", "unitary_evolution"),
    ),
    ProofObligation(
        id="continuous_inheritance_family",
        cluster="dynamics",
        required_statement="Prove the needed continuous inheritance family or state it as a boundary assumption.",
        forbidden_imports=("stone_theorem", "unitary_group", "schrodinger_equation"),
    ),
    ProofObligation(
        id="generator_closure",
        cluster="dynamics",
        required_statement="Prove generator closure for admissible continuous inheritance.",
        forbidden_imports=("hamiltonian_assumed", "stone_theorem", "unitary_group"),
    ),
    ProofObligation(
        id="product_context_exhaustion",
        cluster="composites",
        required_statement="Prove product-context exhaustion for admissible finite composites.",
        forbidden_imports=("tensor_product_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="local_tomography",
        cluster="composites",
        required_statement="Prove product readouts separate stable composite facts.",
        forbidden_imports=("complex_hilbert_assumed", "tensor_product_axiom", "trace_rule"),
    ),
    ProofObligation(
        id="monoidal_associativity",
        cluster="composites",
        required_statement="Prove associative composition for admissible context products.",
        forbidden_imports=("tensor_category_assumed", "hilbert_space", "quantum_channel"),
    ),
    ProofObligation(
        id="entanglement_closure",
        cluster="composites",
        required_statement="Prove non-product composite stable facts are represented without hidden joint-only imports.",
        forbidden_imports=("tensor_product_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="projective_limit_consistency",
        cluster="composites",
        required_statement="Prove consistency of the finite route under admissible projective limits.",
        forbidden_imports=("infinite_dimensional_hilbert_assumed", "c_star_algebra_assumed", "born_rule"),
    ),
    ProofObligation(
        id="physical_phase_scale_boundary",
        cluster="physical_scale",
        required_statement="Keep hbar_I calibrated or provide an independent action-scale theorem artifact.",
        forbidden_imports=("hbar_derived_by_assumption", "planck_units", "known_quantum_scale"),
    ),
)

ARTIFACTS: dict[str, ProofArtifact] = {}


def artifact_mentions_forbidden_import(artifact: ProofArtifact, obligation: ProofObligation) -> str | None:
    searchable = " ".join((artifact.system, artifact.file, artifact.theorem, artifact.check_command)).lower()
    for forbidden_import in obligation.forbidden_imports:
        if forbidden_import.lower() in searchable:
            return forbidden_import
    return None


def artifact_is_complete(artifact: ProofArtifact) -> bool:
    fields = (artifact.system, artifact.file, artifact.theorem, artifact.check_command)
    return all(field.strip() for field in fields) and artifact.verified


def check_obligation(obligation: ProofObligation) -> ObligationCheck:
    artifact = ARTIFACTS.get(obligation.id)
    if artifact is None:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="MISSING_ARTIFACT",
            reason="no machine-checkable proof artifact is registered",
            artifact=None,
        )
    forbidden_import = artifact_mentions_forbidden_import(artifact, obligation)
    if forbidden_import is not None:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="IMPORT_REJECTED",
            reason=f"artifact mentions forbidden target import: {forbidden_import}",
            artifact=artifact,
        )
    if not artifact_is_complete(artifact):
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="INCOMPLETE_ARTIFACT",
            reason="artifact exists but lacks required fields or verified=true",
            artifact=artifact,
        )
    artifact_path = REPO_ROOT / artifact.file
    if not artifact_path.is_file():
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="INCOMPLETE_ARTIFACT",
            reason="artifact file is not present in the repository",
            artifact=artifact,
        )
    return ObligationCheck(
        id=obligation.id,
        cluster=obligation.cluster,
        status="PROVED",
        reason="registered proof artifact is complete and locally grounded",
        artifact=artifact,
    )


def build_closure_attempt() -> ClosureAttempt:
    route_attempt = full_attempt.build_attempt()
    if route_attempt.verdict not in ("CONDITIONAL_FULL_QM_ROUTE", "FULL_QM_PROVED"):
        return ClosureAttempt(
            verdict="ROUTE_NOT_READY",
            route_status=route_attempt.verdict,
            proved=0,
            missing_artifacts=0,
            incomplete_artifacts=0,
            imported_artifacts=0,
            checks=[],
        )
    checks = [check_obligation(obligation) for obligation in OBLIGATIONS]
    proved = sum(1 for check in checks if check.status == "PROVED")
    missing = sum(1 for check in checks if check.status == "MISSING_ARTIFACT")
    incomplete = sum(1 for check in checks if check.status == "INCOMPLETE_ARTIFACT")
    imported = sum(1 for check in checks if check.status == "IMPORT_REJECTED")
    if imported > 0:
        verdict: ClosureVerdict = "IMPORTED_ASSUMPTION_REJECTED"
    elif missing > 0 or incomplete > 0:
        verdict = "PROOF_ARTIFACTS_MISSING"
    else:
        verdict = "FULL_QM_PROVED"
    return ClosureAttempt(
        verdict=verdict,
        route_status=route_attempt.verdict,
        proved=proved,
        missing_artifacts=missing,
        incomplete_artifacts=incomplete,
        imported_artifacts=imported,
        checks=checks,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Try to close the conditional full-QM route as a proof.")
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    attempt = build_closure_attempt()
    print(
        f"full_qm_proof_closure={attempt.verdict} "
        f"route_status={attempt.route_status} proved={attempt.proved} "
        f"missing_artifacts={attempt.missing_artifacts} "
        f"incomplete_artifacts={attempt.incomplete_artifacts} "
        f"imported_artifacts={attempt.imported_artifacts}"
    )
    for check in attempt.checks:
        print(f"{check.status} {check.id} [{check.cluster}]: {check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(attempt), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if attempt.verdict in ("IMPORTED_ASSUMPTION_REJECTED", "ROUTE_NOT_READY"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
