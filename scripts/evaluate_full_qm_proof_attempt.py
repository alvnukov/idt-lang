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

import scripts.evaluate_fpd_projective_derivation as fpd_projective  # noqa: E402
import scripts.evaluate_projective_residual_closure as residual_closure  # noqa: E402
import scripts.evaluate_representation_classification_attempt as representation_attempt  # noqa: E402
import scripts.verify_finite_qm_route as finite_gate  # noqa: E402

StepStatus = Literal["PASS", "CONDITIONAL", "OPEN", "FAIL"]
AttemptVerdict = Literal["FULL_QM_PROVED", "CONDITIONAL_ROUTE_ADVANCED", "BLOCKED"]


@dataclass(frozen=True)
class ProofStep:
    name: str
    status: StepStatus
    statement: str
    evidence: str
    remaining_obligation: str


@dataclass(frozen=True)
class ProofAttempt:
    verdict: AttemptVerdict
    passed: int
    conditional: int
    open: int
    failed: int
    steps: list[ProofStep]


def build_finite_gate_step() -> ProofStep:
    checks = finite_gate.build_checks()
    failures = [check for check in checks if check.status == "FAIL"]
    if failures:
        failed_names = ",".join(check.name for check in failures)
        return ProofStep(
            name="finite_route_gate",
            status="FAIL",
            statement="The finite QM route dependency gate must pass.",
            evidence=f"failed_checks={failed_names}",
            remaining_obligation="Repair the finite route gate before any full-QM proof attempt.",
        )
    return ProofStep(
        name="finite_route_gate",
        status="PASS",
        statement="The finite dependency route passes all current positive and negative-control checks.",
        evidence=f"checks={len(checks)}",
        remaining_obligation="-",
    )


def find_residual_route(route_name: str) -> residual_closure.RouteResult:
    for route in residual_closure.ROUTES:
        if route.name == route_name:
            return residual_closure.evaluate_route(route)
    raise ValueError(f"unknown residual closure route: {route_name}")


def find_derivation_route(route_name: str) -> fpd_projective.RouteResult:
    for route in fpd_projective.ROUTES:
        if route.name == route_name:
            return fpd_projective.evaluate_route(route)
    raise ValueError(f"unknown FPD/projective route: {route_name}")


def find_representation_route(route_name: str) -> representation_attempt.RouteResult:
    for route in representation_attempt.ROUTES:
        if route.name == route_name:
            return representation_attempt.evaluate_route(route)
    raise ValueError(f"unknown representation route: {route_name}")


def build_residual_closure_step() -> ProofStep:
    route = find_residual_route("fpd_plus_projective_consistency")
    if route.verdict == "CONDITIONAL_CLOSURE_HIT":
        return ProofStep(
            name="finite_route_residual_closure",
            status="CONDITIONAL",
            statement="The route-closed residual is closed if finite projection determinacy and projective consistency hold.",
            evidence=f"verdict={route.verdict}; passed={route.passed}/6; imports={len(route.imports)}",
            remaining_obligation="Prove FPD and projective consistency from primitive IDT principles.",
        )
    return ProofStep(
        name="finite_route_residual_closure",
        status="OPEN",
        statement="The route-closed residual must be eliminated without importing Hilbert space.",
        evidence=f"verdict={route.verdict}; open={route.open}; failed={route.failed}",
        remaining_obligation="Find a non-imported residual closure route.",
    )


def build_fpd_projective_step() -> ProofStep:
    route = find_derivation_route("nusd_plus_conservative_projective_gluing")
    if route.verdict == "DERIVATION_CANDIDATE":
        return ProofStep(
            name="fpd_projective_derivation",
            status="CONDITIONAL",
            statement="NUSD plus conservative projective gluing is a non-Hilbert derivation candidate for FPD and projective consistency.",
            evidence=f"verdict={route.verdict}; passed={route.passed}/6; imports={len(route.imports)}",
            remaining_obligation="Promote NUSD and conservative projective gluing to proof artifacts or explicit boundary assumptions.",
        )
    return ProofStep(
        name="fpd_projective_derivation",
        status="OPEN",
        statement="FPD and projective consistency still lack a non-imported derivation candidate.",
        evidence=f"verdict={route.verdict}; open={route.open}; failed={route.failed}",
        remaining_obligation="Find lower principles that derive FPD and projective consistency.",
    )


def build_universal_representation_step() -> ProofStep:
    route = find_representation_route("spectral_symmetry_route")
    if route.verdict == "CONDITIONAL_REPRESENTATION_ROUTE":
        return ProofStep(
            name="universal_representation_theorem",
            status="CONDITIONAL",
            statement=(
                "A non-imported representation route exists if spectral decomposition and rich D_cl-preserving "
                "reversible symmetry are proved."
            ),
            evidence=f"verdict={route.verdict}; passed={route.passed}/8; imports={len(route.imports)}",
            remaining_obligation=(
                "Prove spectral decomposition and rich reversible symmetry from IDT primitives, then turn the route "
                "into a machine-checkable representation theorem."
            ),
        )
    return ProofStep(
        name="universal_representation_theorem",
        status="OPEN",
        statement=(
            "Every finite-projectively determined carrier satisfying the IDT finite route contract "
            "must be representationally equivalent to a complex-Hilbert-like carrier."
        ),
        evidence="No machine-checkable or finite exhaustive classification theorem is present.",
        remaining_obligation=(
            "Prove a representation/classification theorem from D_cl, NUSD, conservative projective gluing, "
            "phase-bundle J, normalized overlap, product-context exhaustion, and bounded correlations."
        ),
    )


def build_universal_born_step() -> ProofStep:
    return ProofStep(
        name="universal_born_readout_theorem",
        status="OPEN",
        statement="The finite normalized-overlap readout must extend to the universal Born rule for all admissible contexts.",
        evidence="Finite projective Born, relative phase, tensor multiplicativity, and singlet angle screens pass; universal theorem is absent.",
        remaining_obligation=(
            "Prove context normalization, coarse-graining consistency, exclusivity additivity, and quadratic readout "
            "as a universal theorem rather than finite screens."
        ),
    )


def build_dynamics_step() -> ProofStep:
    return ProofStep(
        name="unitary_dynamics_theorem",
        status="OPEN",
        statement="Admissible reversible inheritance dynamics must be represented by unitary/antiunitary or generator-compatible maps.",
        evidence="Finite unitary/context-map gates exist elsewhere in the graph; no full Wigner/Stone-style IDT proof artifact is present here.",
        remaining_obligation=(
            "Derive reversible dynamics from D_cl-preserving inheritance automorphisms without assuming unitary evolution as a primitive."
        ),
    )


def build_general_composite_step() -> ProofStep:
    return ProofStep(
        name="general_composite_theorem",
        status="OPEN",
        statement="Product-context exhaustion and tensor composition must hold for arbitrary admissible finite and projective-limit composites.",
        evidence="The current route checks finite qubit-like carrier and product screens; arbitrary-system theorem is absent.",
        remaining_obligation="Prove general composite closure and entanglement structure from the finite route contract.",
    )


def build_physical_scale_step() -> ProofStep:
    return ProofStep(
        name="physical_phase_scale_boundary",
        status="OPEN",
        statement="The mathematical QM route must connect to physical phase scale without deriving hbar_I by stealth.",
        evidence="Projective finite route can use calibrated anchors; first-principles hbar_I remains blocked by public claim boundary.",
        remaining_obligation="Keep hbar_I as calibrated anchor or prove an independent action-scale theorem.",
    )


def build_attempt() -> ProofAttempt:
    steps = [
        build_finite_gate_step(),
        build_residual_closure_step(),
        build_fpd_projective_step(),
        build_universal_representation_step(),
        build_universal_born_step(),
        build_dynamics_step(),
        build_general_composite_step(),
        build_physical_scale_step(),
    ]
    passed = sum(1 for step in steps if step.status == "PASS")
    conditional = sum(1 for step in steps if step.status == "CONDITIONAL")
    open_count = sum(1 for step in steps if step.status == "OPEN")
    failed = sum(1 for step in steps if step.status == "FAIL")
    if failed > 0:
        verdict: AttemptVerdict = "BLOCKED"
    elif open_count == 0 and conditional == 0:
        verdict = "FULL_QM_PROVED"
    else:
        verdict = "CONDITIONAL_ROUTE_ADVANCED"
    return ProofAttempt(
        verdict=verdict,
        passed=passed,
        conditional=conditional,
        open=open_count,
        failed=failed,
        steps=steps,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run a one-pass full-QM proof attempt over the current IDT theorem stack.")
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    attempt = build_attempt()
    print(
        f"full_qm_proof_attempt={attempt.verdict} "
        f"pass={attempt.passed} conditional={attempt.conditional} open={attempt.open} failed={attempt.failed}"
    )
    for step in attempt.steps:
        print(f"{step.status} {step.name}: {step.statement}")
        print(f"  evidence: {step.evidence}")
        print(f"  obligation: {step.remaining_obligation}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(attempt), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if attempt.failed > 0:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
