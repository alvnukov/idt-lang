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

from scripts import evaluate_born_direct_one_pass as born_direct  # noqa: E402
from scripts import evaluate_born_readout_attempt as born_readout  # noqa: E402
from scripts import evaluate_finite_sector_classification as finite_sector  # noqa: E402
from scripts import evaluate_overlap_primitive_route as overlap_primitive  # noqa: E402
from scripts import evaluate_qm_compressed_route as compressed_route  # noqa: E402
from scripts import evaluate_representation_classification_attempt as representation  # noqa: E402

Verdict = Literal[
    "BORN_HILBERT_BELL_PRIMITIVE_LINK_CONDITIONAL_HIT_UNIVERSAL_UNIQUENESS_OPEN",
    "BORN_HILBERT_BELL_PRIMITIVE_LINK_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]
CheckLayer = Literal["bell", "born", "hilbert", "separator", "control", "wall"]


@dataclass(frozen=True)
class RouteCheck:
    name: str
    observed: str
    expected: str
    status: CheckStatus
    layer: CheckLayer
    meaning: str


@dataclass(frozen=True)
class PrimitiveLinkPass:
    verdict: Verdict
    checks: list[RouteCheck]
    passed: int
    failed: int
    bell_status: str
    born_status: str
    hilbert_status: str
    primitive_link: str
    readout_derivation: str
    born_constructor_artifact: str
    born_readout_artifact: str
    born_negative_control_artifact: str
    born_blocker: str
    hilbert_pressure: str
    hilbert_blocker: str
    hilbert_representation_artifact: str
    hilbert_negative_controls_artifacts: tuple[str, ...]
    hilbert_finite_frontier_artifact: str
    constructive_sector_artifact: str
    b1_negative_control_artifact: str
    context_first_bridge_artifact: str
    correction_channel_artifact: str
    rejected_free_fit_artifact: str
    concrete_result: str
    remaining_obligations: tuple[str, ...]
    forbidden_upgrade: tuple[str, ...]


def status_for(observed: str, expected: str) -> CheckStatus:
    return "PASS" if observed == expected else "FAIL"


def make_check(
    name: str,
    observed: str,
    expected: str,
    layer: CheckLayer,
    meaning: str,
) -> RouteCheck:
    return RouteCheck(
        name=name,
        observed=observed,
        expected=expected,
        status=status_for(observed, expected),
        layer=layer,
        meaning=meaning,
    )


def find_overlap_route(route_name: str) -> overlap_primitive.RouteResult:
    for route in overlap_primitive.ROUTES:
        if route.name == route_name:
            return overlap_primitive.evaluate_route(route)
    raise ValueError(f"unknown overlap primitive route: {route_name}")


def find_born_readout_route(route_name: str) -> born_readout.RouteResult:
    for route in born_readout.ROUTES:
        if route.name == route_name:
            return born_readout.evaluate_route(route)
    raise ValueError(f"unknown Born readout route: {route_name}")


def find_compressed_route(route_name: str) -> compressed_route.RouteResult:
    for route in compressed_route.ROUTES:
        if route.name == route_name:
            return compressed_route.evaluate_route(route)
    raise ValueError(f"unknown compressed QM route: {route_name}")


def find_representation_route(route_name: str) -> representation.RouteResult:
    for route in representation.ROUTES:
        if route.name == route_name:
            return representation.evaluate_route(route)
    raise ValueError(f"unknown representation route: {route_name}")


def find_finite_sector(candidate_name: str) -> finite_sector.CandidateResult:
    for candidate in finite_sector.CANDIDATES:
        if candidate.name == candidate_name:
            return finite_sector.evaluate_candidate(candidate)
    raise ValueError(f"unknown finite-sector candidate: {candidate_name}")


def build_checks() -> list[RouteCheck]:
    overlap_hit = find_overlap_route("normalized_orientation_overlap")
    direct_cosine_import = find_overlap_route("born_cosine_projection_control")
    tanh_wall = find_overlap_route("closed_tanh_selector_previous")
    direct_born = born_direct.build_route()
    born_context = find_born_readout_route("quadratic_context_probability_route")
    born_import = find_born_readout_route("imported_born_rule")
    phase_bundle = find_compressed_route("phase_bundle_normalized_overlap")
    real_overlap = find_compressed_route("real_normalized_overlap")
    representation_route = find_representation_route("spectral_symmetry_route")
    representation_import = find_representation_route("imported_complex_hilbert_representation")
    complex_sector = find_finite_sector("complex_hilbert_qubit_route")
    real_sector = find_finite_sector("real_hilbert_rebit")
    boxworld_sector = find_finite_sector("boxworld_pr")
    generic_sector = find_finite_sector("unconstrained_generic_gpt")
    residual_sector = find_finite_sector("finite_route_closed_residual")

    return [
        make_check(
            "bell.normalized_orientation_overlap",
            overlap_hit.verdict,
            "NEW_PRIMITIVE_HIT",
            "bell",
            "Bell/Tsirelson angle behavior follows from normalized orientation overlap without a Bell table import.",
        ),
        make_check(
            "bell.direct_cosine_import_control",
            direct_cosine_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Direct Born/Bell cosine projection remains classified as an import.",
        ),
        make_check(
            "bell.previous_tanh_wall",
            tanh_wall.verdict,
            "NEW_WALL",
            "wall",
            "The older closed tanh selector remains a wall, not the active primitive link.",
        ),
        make_check(
            "born.direct_finite_readout",
            direct_born.verdict,
            "DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF",
            "born",
            "Signed overlap plus affine readout and phase-bundle double cover closes the finite Born route.",
        ),
        make_check(
            "born.context_probability_readout",
            born_context.verdict,
            "CONDITIONAL_BORN_ROUTE",
            "born",
            "Quadratic readout becomes context probability only with normalization, exclusivity, coarse-graining, and operational equivalence.",
        ),
        make_check(
            "born.import_control",
            born_import.verdict,
            "IMPORTED_HIT",
            "control",
            "A direct Born-rule assumption remains classified as an import.",
        ),
        make_check(
            "hilbert.phase_bundle_carrier",
            phase_bundle.verdict,
            "CARRIER_ROUTE_HIT",
            "hilbert",
            "Phase-bundle normalized overlap passes finite projective Born, interference, tensor, local tomography, and singlet screens.",
        ),
        make_check(
            "hilbert.real_overlap_wall",
            real_overlap.verdict,
            "NEW_WALL",
            "separator",
            "Real overlap fails phase-gauge/local-tomography screens and exposes the rebit separator pressure.",
        ),
        make_check(
            "hilbert.representation_route",
            representation_route.verdict,
            "CONDITIONAL_REPRESENTATION_ROUTE",
            "hilbert",
            "Spectrality plus rich D_cl reversible symmetry give the current non-imported representation route candidate.",
        ),
        make_check(
            "hilbert.import_control",
            representation_import.verdict,
            "IMPORTED_HIT",
            "control",
            "Direct complex-Hilbert representation remains classified as an import.",
        ),
        make_check(
            "separator.complex_finite_sector",
            complex_sector.verdict,
            "FINITE_SECTOR_HIT",
            "separator",
            "The complex-Hilbert-like finite route is the surviving represented finite sector.",
        ),
        make_check(
            "separator.real_hilbert_rebit",
            real_sector.verdict,
            "REJECTED",
            "separator",
            "Real Hilbert/rebit composition is rejected by hidden joint-only orientation and local-tomography failure.",
        ),
        make_check(
            "separator.boxworld_pr",
            boxworld_sector.verdict,
            "REJECTED",
            "separator",
            "PR/boxworld-like superquantum tables are rejected by the bounded/phase route screens.",
        ),
        make_check(
            "separator.generic_gpt",
            generic_sector.verdict,
            "REJECTED",
            "separator",
            "Unconstrained GPT lacks the finite route-closure and phase-bundle contract.",
        ),
        make_check(
            "separator.route_closed_residual",
            residual_sector.verdict,
            "REJECTED",
            "wall",
            "Route-closed residuals are rejected in the finite graph, but universal classification remains a theorem obligation.",
        ),
    ]


def build_pass() -> PrimitiveLinkPass:
    checks = build_checks()
    failures = [check for check in checks if check.status == "FAIL"]
    verdict: Verdict = (
        "BORN_HILBERT_BELL_PRIMITIVE_LINK_BLOCKED"
        if failures
        else "BORN_HILBERT_BELL_PRIMITIVE_LINK_CONDITIONAL_HIT_UNIVERSAL_UNIQUENESS_OPEN"
    )
    return PrimitiveLinkPass(
        verdict=verdict,
        checks=checks,
        passed=len(checks) - len(failures),
        failed=len(failures),
        bell_status=(
            "finite Bell/CHSH/Tsirelson readout is closed on the current screen by "
            "normalized orientation overlap; direct Bell/cosine tables remain classified as imports"
        ),
        born_status=(
            "finite Born readout is machine-checked for constructor-respecting oriented "
            "facticization: constructor labels force branch preservation, 2*yes=total+signed, "
            "hence P(yes)=(1+r)/2, and phase double-cover gives |a|^2; universal derivation "
            "from primitive unknownness remains open"
        ),
        hilbert_status=(
            "B2-ready inputs now machine-check a Hilbert-like representation route: finite route "
            "closure, phase-bundle scalar carrier, normalized overlap, local tomography, spectral "
            "exposed contexts, rich reversible symmetry, constructive carrier witness, and no hidden "
            "joint-only generation. Universal Hilbert uniqueness remains open."
        ),
        primitive_link=(
            "contextual Bell obstruction, Born readout, and Hilbert carrier pressure "
            "share normalized oriented distinguishability as the finite primitive link"
        ),
        readout_derivation=(
            "oriented two-cover -> constructor-respecting branch labels -> branch-preserving "
            "facticization -> signed binary readout identity -> affine count law -> phase-bundle square"
        ),
        born_constructor_artifact=(
            "Proofs/QMClosure/PrimitiveBoundaryQMChain.lean::"
            "constructor_respecting_oriented_readout_forces_born_count"
        ),
        born_readout_artifact=(
            "Proofs/QMClosure/PrimitiveBoundaryQMChain.lean::"
            "admissible_oriented_born_facticization_forces_affine_signed_count"
        ),
        born_negative_control_artifact=(
            "Proofs/QMClosure/PrimitiveBoundaryQMChain.lean::"
            "total_preservation_alone_does_not_force_born_readout"
        ),
        born_blocker=(
            "derive constructor-respecting oriented branch labels, signed expectation readout, "
            "affine frequency calibration, and phase-bundle double cover from the successor "
            "primitive base for every target readout context; otherwise Born remains a finite "
            "standard-sector law"
        ),
        hilbert_pressure=(
            "phase-bundle/local-tomography/bounded-correlation screens reject real, "
            "boxworld, generic GPT, and finite residual controls; Lean also rejects representation "
            "routes missing spectrality, reversible symmetry, constructive witness, or import guards"
        ),
        hilbert_blocker=(
            "prove carrier-frontier exhaustion: every admissible fundamental carrier must map "
            "to the known finite screen frontier and pass its constructive phase-bundle/local-"
            "tomography/spectral-symmetry screens, or exhibit a concrete non-Hilbert constructive "
            "carrier countermodel"
        ),
        hilbert_representation_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "context_first_witness_completeness_supplies_hilbert_route"
        ),
        hilbert_negative_controls_artifacts=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "current_finite_b2_supplies_hilbert_representation_route",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "current_hilbert_representation_route_still_not_universal",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "missing_spectral_exposed_contexts_blocks_hilbert_representation",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "missing_reversible_symmetry_blocks_hilbert_representation",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "abstract_residual_without_constructive_witness_is_not_hilbert_route",
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "imported_hilbert_representation_is_not_hilbert_route",
        ),
        hilbert_finite_frontier_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "context_first_plus_frontier_exhaustion_closes_hilbert_frontier"
        ),
        constructive_sector_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "current_finite_b2_closes_born_hilbert_finite_routes"
        ),
        b1_negative_control_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "b1_interface_projection_does_not_force_b2_ready"
        ),
        context_first_bridge_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "context_first_witness_completeness_promotes_to_b2_ready"
        ),
        correction_channel_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "current_beyond_qm_correction_channel_is_audited"
        ),
        rejected_free_fit_artifact=(
            "Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean::"
            "free_fit_correction_channel_is_rejected"
        ),
        concrete_result=(
            "B1 is insufficient; context-first constructive witness completeness promotes "
            "to B2; B2 is sufficient for the current finite Born/Hilbert standard-QM "
            "sector projection; with carrier-frontier exhaustion, the Hilbert frontier "
            "closes to complex phase-bundle representation; exact fundamental QM and "
            "audited beyond-QM correction channels remain separate"
        ),
        remaining_obligations=(
            "derive_S2_or_sector_law_from_context_first_unknownness",
            "derive_constructor_respecting_oriented_branch_labels_from_context_first_unknownness",
            "derive_signed_expectation_readout_for_normalized_overlap",
            "derive_affine_frequency_calibration_for_facticizable_records",
            "derive_phase_bundle_double_cover_for_all_admissible_contexts",
            "derive_spectral_decomposition_from_D_cl_exposed_contexts",
            "derive_rich_reversible_symmetry_from_inheritance_transitions",
            "derive_recoverable_oriented_filtering_without_purification_import",
            "prove_carrier_frontier_exhaustion_or_record_non_Hilbert_constructive_countermodel",
        ),
        forbidden_upgrade=(
            "does_not_prove_universal_Born",
            "does_not_prove_complex_Hilbert_uniqueness",
            "does_not_prove_full_QM",
            "does_not_import_Bell_table_Born_rule_or_Hilbert_carrier",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate the joint Born/Hilbert/Bell primitive-link route.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    route = build_pass()
    print(f"born_hilbert_bell_primitive_link={route.verdict} passed={route.passed} failed={route.failed}")
    print(f"BELL_CONTROL {route.bell_status}")
    print(f"BORN_STATUS {route.born_status}")
    print(f"HILBERT_STATUS {route.hilbert_status}")
    print(f"LINK {route.primitive_link}")
    print(f"READOUT {route.readout_derivation}")
    print(f"BORN_CONSTRUCTOR_ARTIFACT {route.born_constructor_artifact}")
    print(f"BORN_READOUT_ARTIFACT {route.born_readout_artifact}")
    print(f"BORN_NEGATIVE_CONTROL {route.born_negative_control_artifact}")
    print(f"BORN_BLOCKER {route.born_blocker}")
    print(f"HILBERT {route.hilbert_pressure}")
    print(f"HILBERT_REPRESENTATION_ARTIFACT {route.hilbert_representation_artifact}")
    print(f"HILBERT_NEGATIVE_CONTROLS {','.join(route.hilbert_negative_controls_artifacts)}")
    print(f"HILBERT_FINITE_FRONTIER {route.hilbert_finite_frontier_artifact}")
    print(f"HILBERT_BLOCKER {route.hilbert_blocker}")
    print(f"CONSTRUCTIVE_SECTOR {route.constructive_sector_artifact}")
    print(f"B1_NEGATIVE_CONTROL {route.b1_negative_control_artifact}")
    print(f"CONTEXT_FIRST_BRIDGE {route.context_first_bridge_artifact}")
    print(f"CORRECTION_CHANNEL {route.correction_channel_artifact}")
    print(f"FREE_FIT_REJECTED {route.rejected_free_fit_artifact}")
    print(f"CONCRETE_RESULT {route.concrete_result}")
    print(f"REMAINING {','.join(route.remaining_obligations)}")
    if args.show_checks:
        for check in route.checks:
            print(
                f"{check.status} {check.name}: observed={check.observed} "
                f"expected={check.expected}; layer={check.layer}; meaning={check.meaning}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(route), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if route.verdict == "BORN_HILBERT_BELL_PRIMITIVE_LINK_CONDITIONAL_HIT_UNIVERSAL_UNIQUENESS_OPEN" else 1


if __name__ == "__main__":
    raise SystemExit(main())
