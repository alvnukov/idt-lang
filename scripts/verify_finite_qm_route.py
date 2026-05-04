from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts import evaluate_kernel_additivity_principle as kernel  # noqa: E402
from scripts import evaluate_finite_sector_classification as finite_sector  # noqa: E402
from scripts import evaluate_fpd_projective_derivation as fpd_projective  # noqa: E402
from scripts import evaluate_overlap_primitive_route as overlap_route  # noqa: E402
from scripts import evaluate_overlap_uniqueness as overlap_unique  # noqa: E402
from scripts import evaluate_phase_bundle_j_derivation as phase_j  # noqa: E402
from scripts import evaluate_projective_residual_closure as residual_closure  # noqa: E402
from scripts import evaluate_qm_compressed_route as qm_route  # noqa: E402

GateStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class GateCheck:
    name: str
    expected: str
    observed: str
    status: GateStatus


def status_for(observed: str, expected: str) -> GateStatus:
    if observed == expected:
        return "PASS"
    return "FAIL"


def find_kernel_result(candidate_name: str) -> kernel.CandidateResult:
    for candidate in kernel.CANDIDATES:
        if candidate.name == candidate_name:
            return kernel.evaluate_candidate(candidate)
    raise ValueError(f"unknown kernel composition candidate: {candidate_name}")


def find_overlap_unique_result(candidate_name: str) -> overlap_unique.CandidateResult:
    for candidate in overlap_unique.CANDIDATES:
        if candidate.name == candidate_name:
            return overlap_unique.evaluate_candidate(candidate)
    raise ValueError(f"unknown overlap uniqueness candidate: {candidate_name}")


def find_overlap_route_result(route_name: str) -> overlap_route.RouteResult:
    for route in overlap_route.ROUTES:
        if route.name == route_name:
            return overlap_route.evaluate_route(route)
    raise ValueError(f"unknown overlap route: {route_name}")


def find_phase_j_result(candidate_name: str) -> phase_j.CandidateResult:
    for candidate in phase_j.CANDIDATES:
        if candidate.name == candidate_name:
            return phase_j.evaluate_candidate(candidate)
    raise ValueError(f"unknown phase-bundle J candidate: {candidate_name}")


def find_qm_route_result(route_name: str) -> qm_route.RouteResult:
    for route in qm_route.ROUTES:
        if route.name == route_name:
            return qm_route.evaluate_route(route)
    raise ValueError(f"unknown compressed QM route: {route_name}")


def find_finite_sector_result(candidate_name: str) -> finite_sector.CandidateResult:
    for candidate in finite_sector.CANDIDATES:
        if candidate.name == candidate_name:
            return finite_sector.evaluate_candidate(candidate)
    raise ValueError(f"unknown finite-sector candidate: {candidate_name}")


def find_residual_closure_result(route_name: str) -> residual_closure.RouteResult:
    for route in residual_closure.ROUTES:
        if route.name == route_name:
            return residual_closure.evaluate_route(route)
    raise ValueError(f"unknown residual-closure route: {route_name}")


def find_fpd_projective_result(route_name: str) -> fpd_projective.RouteResult:
    for route in fpd_projective.ROUTES:
        if route.name == route_name:
            return fpd_projective.evaluate_route(route)
    raise ValueError(f"unknown FPD/projective derivation route: {route_name}")


def make_check(name: str, observed: str, expected: str) -> GateCheck:
    return GateCheck(name=name, expected=expected, observed=observed, status=status_for(observed, expected))


def build_checks() -> list[GateCheck]:
    additive = find_kernel_result("additive_kernel_composition")
    imported_additive = find_kernel_result("imported_additive_sum")
    overlap = find_overlap_unique_result("normalized_bilinear_overlap")
    cubic = find_overlap_unique_result("cubic_overlap")
    tanh = find_overlap_unique_result("tanh_overlap")
    direct_cosine = find_overlap_unique_result("direct_cosine_projection")
    primitive_route = find_overlap_route_result("normalized_orientation_overlap")
    tanh_wall = find_overlap_route_result("closed_tanh_selector_previous")
    born_control = find_overlap_route_result("born_cosine_projection_control")
    canonical_j = find_phase_j_result("canonical_quadrature_J")
    imported_j = find_phase_j_result("imported_complex_J")
    real_route = find_qm_route_result("real_normalized_overlap")
    phase_route = find_qm_route_result("phase_bundle_normalized_overlap")
    complex_sector = find_finite_sector_result("complex_hilbert_qubit_route")
    residual_sector = find_finite_sector_result("finite_route_closed_residual")
    classical_sector = find_finite_sector_result("classical_simplex_bit")
    real_sector = find_finite_sector_result("real_hilbert_rebit")
    quaternionic_sector = find_finite_sector_result("quaternionic_hilbert_bit")
    boxworld_sector = find_finite_sector_result("boxworld_pr")
    generic_sector = find_finite_sector_result("unconstrained_generic_gpt")
    residual_unclosed = find_residual_closure_result("unclosed_route_residual")
    residual_fpd_only = find_residual_closure_result("finite_projection_determinacy_only")
    residual_projective_only = find_residual_closure_result("projective_consistency_only")
    residual_conditional = find_residual_closure_result("fpd_plus_projective_consistency")
    residual_imported = find_residual_closure_result("imported_hilbert_completion")
    derivation_b2 = find_fpd_projective_result("b2_core_only")
    derivation_nusd = find_fpd_projective_result("nusd_finite_generation")
    derivation_gluing = find_fpd_projective_result("conservative_projective_gluing_only")
    derivation_combined = find_fpd_projective_result("nusd_plus_conservative_projective_gluing")
    derivation_declared = find_fpd_projective_result("declared_projective_consistency")
    derivation_imported = find_fpd_projective_result("imported_hilbert_completion")

    return [
        make_check("kernel.additive", additive.verdict, "PRINCIPLE_HIT"),
        make_check("kernel.imported_control", imported_additive.verdict, "IMPORTED_HIT"),
        make_check("overlap.unique", overlap.verdict, "UNIQUE_HIT"),
        make_check("overlap.cubic_control", cubic.verdict, "WEAK_AMBIGUITY"),
        make_check("overlap.tanh_control", tanh.verdict, "WEAK_AMBIGUITY"),
        make_check("overlap.direct_cosine_control", direct_cosine.verdict, "IMPORTED_HIT"),
        make_check("route.normalized_orientation_overlap", primitive_route.verdict, "NEW_PRIMITIVE_HIT"),
        make_check("route.previous_tanh_wall", tanh_wall.verdict, "NEW_WALL"),
        make_check("route.born_control", born_control.verdict, "IMPORTED_HIT"),
        make_check("phase_j.canonical_quadrature", canonical_j.verdict, "J_DERIVATION_HIT"),
        make_check("phase_j.imported_complex_control", imported_j.verdict, "IMPORTED_HIT"),
        make_check("compressed_qm.real_route", real_route.verdict, "NEW_WALL"),
        make_check("compressed_qm.phase_bundle_route", phase_route.verdict, "CARRIER_ROUTE_HIT"),
        make_check("finite_sector.complex_route", complex_sector.verdict, "FINITE_SECTOR_HIT"),
        make_check("finite_sector.route_closed_residual", residual_sector.verdict, "REJECTED"),
        make_check("finite_sector.classical_control", classical_sector.verdict, "REJECTED"),
        make_check("finite_sector.real_control", real_sector.verdict, "REJECTED"),
        make_check("finite_sector.quaternionic_control", quaternionic_sector.verdict, "REJECTED"),
        make_check("finite_sector.boxworld_control", boxworld_sector.verdict, "REJECTED"),
        make_check("finite_sector.generic_gpt_control", generic_sector.verdict, "REJECTED"),
        make_check("residual_closure.unclosed", residual_unclosed.verdict, "OPEN_WALL"),
        make_check("residual_closure.fpd_only", residual_fpd_only.verdict, "NEAR_MISS"),
        make_check("residual_closure.projective_only", residual_projective_only.verdict, "NEAR_MISS"),
        make_check("residual_closure.fpd_plus_projective_consistency", residual_conditional.verdict, "CONDITIONAL_CLOSURE_HIT"),
        make_check("residual_closure.imported_hilbert_control", residual_imported.verdict, "IMPORTED_HIT"),
        make_check("fpd_projective.b2_core", derivation_b2.verdict, "OPEN_WALL"),
        make_check("fpd_projective.nusd_only", derivation_nusd.verdict, "PARTIAL_DERIVATION"),
        make_check("fpd_projective.gluing_only", derivation_gluing.verdict, "PARTIAL_DERIVATION"),
        make_check("fpd_projective.combined", derivation_combined.verdict, "DERIVATION_CANDIDATE"),
        make_check("fpd_projective.declared_control", derivation_declared.verdict, "IMPORTED_HIT"),
        make_check("fpd_projective.hilbert_import_control", derivation_imported.verdict, "IMPORTED_HIT"),
    ]


def main() -> int:
    checks = build_checks()
    failures = [check for check in checks if check.status == "FAIL"]
    for check in checks:
        print(f"{check.status} {check.name}: observed={check.observed} expected={check.expected}")
    if failures:
        print(f"finite_qm_route_gate=FAIL failed={len(failures)}/{len(checks)}")
        return 1
    print(f"finite_qm_route_gate=PASS checks={len(checks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
