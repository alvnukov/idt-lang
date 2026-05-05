from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMAND = "lake build Proofs.QMClosure.S2BornProofSearch"

RouteVerdict = Literal[
    "COUNTERMODEL_SURVIVES",
    "CIRCULARITY_RISK",
    "CONDITIONAL_WITH_S2",
    "FINITE_CARRIER_HIT",
    "FINITE_CHAIN_HIT",
    "FINITE_DIRECT_BORN_HIT",
    "FINITE_SELECTOR_HIT",
    "FINITE_EVIDENCE_NOT_PROOF",
    "FINITE_UNIQUENESS_HIT",
    "IMPORT_REJECTED",
    "INSUFFICIENT_CURRENTLY",
    "PRIMITIVE_OR_SECTOR_LAW_REQUIRED",
    "PROMISING_UNPROVED",
    "SECTOR_BOUNDARY_POSSIBLE",
]
SearchVerdict = Literal[
    "BORN_NOT_DERIVED_S2_REQUIRED",
    "BORN_SEARCH_CHECK_FAILED",
    "FINITE_BORN_CHAIN_HIT_UNIVERSAL_S2_OPEN",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class ProofRoute:
    id: str
    verdict: RouteVerdict
    source: str
    decisive_reason: str
    missing_obligation: str
    imports: tuple[str, ...]


@dataclass(frozen=True)
class S2BornProofSearch:
    verdict: SearchVerdict
    lean_check: LeanCheck
    routes_checked: int
    countermodels: int
    conditional_routes: int
    import_rejected: int
    finite_evidence_only: int
    finite_carrier_hits: int
    finite_chain_hits: int
    finite_direct_born_hits: int
    finite_selector_hits: int
    finite_uniqueness_hits: int
    insufficient: int
    primitive_or_sector_law: int
    circularity_risk: int
    promising_unproved: int
    sector_boundary_possible: int
    open_core: tuple[str, ...]
    viable_next_route: str
    routes: list[ProofRoute]


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


def build_routes() -> list[ProofRoute]:
    return [
        ProofRoute(
            id="b1_cgsc_direct_to_born",
            verdict="INSUFFICIENT_CURRENTLY",
            source="Proofs/QMClosure/B1CGSCClauseDerivation.lean",
            decisive_reason=(
                "B1 derives the CGSC structural clauses, but those clauses explicitly preserve "
                "no-Born-import guards and do not select positive quadratic actualization."
            ),
            missing_obligation="derive positive_quadratic_actualization_principle from B1 or successor base",
            imports=(),
        ),
        ProofRoute(
            id="b1_primitive_base_to_finite_chain_inputs",
            verdict="INSUFFICIENT_CURRENTLY",
            source="Proofs/QMClosure/B1PrimitiveBase.lean; sections/01-primitives.md",
            decisive_reason=(
                "B1 binds admissible atoms and roles to constructor-generated witnesses and preserves "
                "no-target-import guards, but it does not yet derive compatible kernel additivity, "
                "normalized overlap uniqueness, phase-bundle J, or proper-subcontext pairwise coverage."
            ),
            missing_obligation=(
                "prove a primitive-boundary theorem from context-first unknownness to the finite-chain "
                "inputs, or expose the missing inputs as audited QM-sector principles"
            ),
            imports=(),
        ),
        ProofRoute(
            id="primitive_boundary_candidate_classifier",
            verdict="PROMISING_UNPROVED",
            source="Proofs/QMClosure/PrimitiveBoundaryQMChain.lean; scripts/evaluate_primitive_boundary_qm_chain.py",
            decisive_reason=(
                "A single primitive-boundary package now identifies the exact non-imported inputs "
                "that would feed the checked finite Born/phase-bundle chain: compatible kernel "
                "additivity, normalized overlap uniqueness, phase-bundle J, proper-subcontext "
                "pairwise coverage, and no hidden ternary context-only fact."
            ),
            missing_obligation=(
                "derive the five principles from context-first primitive unknownness, or declare "
                "the package as an explicit falsifiable QM-sector boundary"
            ),
            imports=(),
        ),
        ProofRoute(
            id="b2_like_dcl_f_q_l_to_s2",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean",
            decisive_reason=(
                "A toy finite core satisfies D_cl/F/Q/L-like accounting while admitting a stable "
                "primitive ternary witness, so second-order facticization is not forced."
            ),
            missing_obligation="add a principle that forbids primitive third-order facticization",
            imports=(),
        ),
        ProofRoute(
            id="finite_i3_zero_to_s2",
            verdict="FINITE_EVIDENCE_NOT_PROOF",
            source="finite gate actualization_demo_i3_zero",
            decisive_reason=(
                "I3=0 gates verify QM-scale finite instances, but a finite gate is not a universal "
                "derivation that forbids every stable third-order facticization witness."
            ),
            missing_obligation="universal no-third-order theorem or explicit QM-sector law",
            imports=(),
        ),
        ProofRoute(
            id="readout_accounting_to_quadratic",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/BornWallSeparation.lean",
            decisive_reason=(
                "Finite readout accounting admits both linear and quadratic stable two-branch "
                "readouts; accounting alone does not select Born."
            ),
            missing_obligation="positive_quadratic_actualization_principle",
            imports=(),
        ),
        ProofRoute(
            id="normalized_probability_layer_to_quadratic_weight",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean",
            decisive_reason=(
                "Normalized context probability accepts supplied linear, quadratic, and cubic positive "
                "weights. Normalization is a readout layer, not a selector for the weight law."
            ),
            missing_obligation="derive the facticization-weight selector below probability",
            imports=(),
        ),
        ProofRoute(
            id="stable_frequency_to_born_weight_law",
            verdict="INSUFFICIENT_CURRENTLY",
            source="sections/175-born-s2-context-only-fact-research-note.md",
            decisive_reason=(
                "Stable frequencies can estimate whatever context probabilities are supplied by the "
                "readout layer; they do not select whether the underlying weight law is linear, "
                "quadratic, or higher-order."
            ),
            missing_obligation="derive why the frequency-stable readout weight is quadratic before normalization",
            imports=(),
        ),
        ProofRoute(
            id="kolmogorov_context_axioms_to_born",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean",
            decisive_reason=(
                "Finite nonnegative normalized weights satisfy context probability accounting for many "
                "weight laws. Kolmogorov-style context axioms do not select the Born exponent."
            ),
            missing_obligation="derive positive quadratic actualization rather than probability axioms",
            imports=(),
        ),
        ProofRoute(
            id="normalized_orientation_overlap_as_weight_selector",
            verdict="FINITE_SELECTOR_HIT",
            source="scripts/evaluate_overlap_primitive_route.py; sections/174-context-bundle-nontriviality-research-note.md#174.211",
            decisive_reason=(
                "Reversible orientation transport plus normalized bilinear overlap passes the finite "
                "Bell/Born-angle selector screen without a direct Born/cosine table import, open "
                "parameters, or probability-layer tuning."
            ),
            missing_obligation=(
                "derive normalized orientation transport/overlap from the primitive base and generalize "
                "from the finite angle screen to arbitrary admissible readout contexts"
            ),
            imports=(),
        ),
        ProofRoute(
            id="signed_overlap_affine_readout_to_born_square",
            verdict="FINITE_SELECTOR_HIT",
            source="scripts/evaluate_born_from_overlap_affine_readout.py; Proofs/QMClosure/PrimitiveBoundaryQMChain.lean",
            decisive_reason=(
                "If normalized overlap is the signed binary expectation and probability readout is "
                "affine under stable mixtures, repeatability, complement symmetry, unbiased zero, "
                "and the phase-bundle double cover force p=(1+r)/2, hence p=|a|^2 for "
                "r=2|a|^2-1. Cubic, quintic, tanh, threshold, and unsigned-overlap controls fail."
            ),
            missing_obligation=(
                "derive signed expectation readout, affine mixture response, and the phase-bundle "
                "double-cover relation from primitive-boundary structure across all admissible contexts"
            ),
            imports=(),
        ),
        ProofRoute(
            id="operational_randomization_to_affine_readout",
            verdict="FINITE_SELECTOR_HIT",
            source="scripts/evaluate_affine_readout_principle.py",
            decisive_reason=(
                "External randomization of already facticizable records forces affine readout if "
                "mixed frequencies must match observable randomized-trial frequencies and remain "
                "invariant under branch relabeling and randomizer-tree refinement. Nonlinear "
                "frequency, log-odds, max, and min controls fail."
            ),
            missing_obligation=(
                "bind external randomization/frequency calibration to the primitive readout language "
                "without importing a convex probability axiom"
            ),
            imports=(),
        ),
        ProofRoute(
            id="direct_finite_born_one_pass_route",
            verdict="FINITE_DIRECT_BORN_HIT",
            source="scripts/evaluate_born_direct_one_pass.py; Proofs/QMClosure/PrimitiveBoundaryQMChain.lean",
            decisive_reason=(
                "The direct one-pass route composes primitive-boundary candidate, normalized-overlap "
                "uniqueness, phase-bundle J, operational affine readout, signed-overlap Born selector, "
                "and imported/negative controls. It closes the finite Born selector route without "
                "target imports, while explicitly preserving the universal-proof boundary."
            ),
            missing_obligation=(
                "derive the primitive-boundary package, external-randomization calibration, signed "
                "expectation semantics, and phase-bundle double cover from primitives for all "
                "admissible contexts"
            ),
            imports=(),
        ),
        ProofRoute(
            id="compatible_kernel_additivity_to_normalized_overlap_uniqueness",
            verdict="FINITE_UNIQUENESS_HIT",
            source="scripts/evaluate_kernel_additivity_principle.py; scripts/evaluate_overlap_uniqueness.py",
            decisive_reason=(
                "The finite uniqueness screen isolates normalized bilinear overlap once compatible "
                "kernel additivity, transport invariance, scale gauge, normalization, and invariant "
                "kernel uniqueness are supplied. Direct cosine is rejected as an import; cubic and "
                "tanh controls fail additivity/uniqueness."
            ),
            missing_obligation=(
                "derive compatible kernel additivity and invariant-kernel premises from primitive "
                "unknownness for the claimed readout sector, not only on the finite vector screen"
            ),
            imports=(),
        ),
        ProofRoute(
            id="phase_bundle_normalized_overlap_to_finite_qm_carrier",
            verdict="FINITE_CARRIER_HIT",
            source="scripts/evaluate_qm_compressed_route.py",
            decisive_reason=(
                "The phase-bundle normalized-overlap carrier passes finite projective Born, "
                "projective repeatability, phase gauge, relative-phase interference, tensor "
                "multiplicativity, local tomography, singlet angle curve, and import screen checks. "
                "The real normalized-overlap control remains a wall."
            ),
            missing_obligation=(
                "derive the phase-bundle J structure and external carrier adequacy from primitives, "
                "then generalize beyond the finite checked carrier screen"
            ),
            imports=(),
        ),
        ProofRoute(
            id="finite_qm_dependency_chain_gate",
            verdict="FINITE_CHAIN_HIT",
            source="scripts/verify_finite_qm_route.py",
            decisive_reason=(
                "The current executable dependency chain passes 31 checks: additive kernel principle, "
                "overlap uniqueness, normalized orientation overlap, canonical quadrature J, "
                "phase-bundle carrier route, finite complex-sector route, and negative controls."
            ),
            missing_obligation=(
                "close the universal residuals: FPD/projective consistency from primitives, external "
                "representation/Born/dynamics/composite adequacy, and the calibrated phase-scale boundary"
            ),
            imports=(),
        ),
        ProofRoute(
            id="normalized_orientation_overlap_to_universal_s2",
            verdict="INSUFFICIENT_CURRENTLY",
            source="scripts/evaluate_overlap_primitive_route.py",
            decisive_reason=(
                "The normalized-overlap route supplies a real pairwise selector on the checked "
                "orientation/Bell screen, but it does not yet prove that all stable facticization "
                "contexts are exhausted by such pairwise overlaps."
            ),
            missing_obligation="prove universal context-family coverage or mark the route as sector-limited",
            imports=(),
        ),
        ProofRoute(
            id="positive_geometry_plus_s2_to_quadratic",
            verdict="CONDITIONAL_WITH_S2",
            source="sections/174-context-bundle-nontriviality-research-note.md#174.90",
            decisive_reason=(
                "Positive comparison geometry plus active S2 gives nonnegative quadratic weights, "
                "but only after S2 is supplied."
            ),
            missing_obligation="derive or declare S2 before using this route",
            imports=(),
        ),
        ProofRoute(
            id="quadratic_measure_with_N_Cg_Ex_to_born_context_probability",
            verdict="CONDITIONAL_WITH_S2",
            source="scripts/evaluate_born_readout_attempt.py",
            decisive_reason=(
                "Quadratic weights plus normalization, exclusivity additivity, coarse-graining, "
                "and operational equivalence give Born-like finite context probability."
            ),
            missing_obligation="supply positive quadratic actualization without Born import",
            imports=(),
        ),
        ProofRoute(
            id="finite_born_quadratic_readout_survivor",
            verdict="FINITE_EVIDENCE_NOT_PROOF",
            source="theorem card finite_born_quadratic_readout_survivor",
            decisive_reason=(
                "The registered finite packet family rejects linear readout and keeps quadratic "
                "readout, but the card is conditional and finite-family scoped."
            ),
            missing_obligation="generalize beyond registered finite packet family",
            imports=(),
        ),
        ProofRoute(
            id="hilbert_back_import_to_born",
            verdict="IMPORT_REJECTED",
            source="qm_core_proof_obligations.born_rule_derivation",
            decisive_reason=(
                "Deriving Born by assuming Hilbert carrier, trace rule, projectors, or Born itself "
                "violates the current public claim boundary."
            ),
            missing_obligation="derive Hilbert carrier and readout rule independently first",
            imports=("hilbert_space", "trace_rule", "born_rule"),
        ),
        ProofRoute(
            id="universal_carrier_selection_to_born",
            verdict="INSUFFICIENT_CURRENTLY",
            source="theorem card universal_carrier_selection_theorem",
            decisive_reason=(
                "Carrier selection is still open over the nonfinite or unwitnessed generic GPT "
                "residual and does not itself supply a Born readout selector."
            ),
            missing_obligation="close universal carrier quantifier and then derive readout rule",
            imports=(),
        ),
        ProofRoute(
            id="hilbert_bell_gravity_common_source_to_born",
            verdict="INSUFFICIENT_CURRENTLY",
            source="sections/174-context-bundle-nontriviality-research-note.md",
            decisive_reason=(
                "The Hilbert/Bell/gravity route supplies pressure for common-source structure, "
                "but no current theorem connects that pressure to second-order actualization."
            ),
            missing_obligation="find a lower common-source principle that forbids third-order readouts",
            imports=(),
        ),
        ProofRoute(
            id="stable_i3_as_hidden_context_only_fact",
            verdict="CIRCULARITY_RISK",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/175-born-s2-context-only-fact-research-note.md",
            decisive_reason=(
                "A stable ternary I3 witness can be represented as a context-only fact: it is visible "
                "only to the whole readout context and not exhausted by pairwise witnesses. If the "
                "theory derives no_hidden_context_only_fact, S2 follows in the checked toy interface. "
                "However, using no_hidden_context_only_fact without an independent source merely "
                "renames the S2 obligation."
            ),
            missing_obligation="derive no_hidden_context_only_fact from primitive unknownness, not by stipulation",
            imports=(),
        ),
        ProofRoute(
            id="coarse_graining_associativity_against_i3",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/175-born-s2-context-only-fact-research-note.md#175.3",
            decisive_reason=(
                "Bracketing equality alone is too weak: a primitive ternary residue can be carried "
                "through both groupings with equal totals. Associativity does not by itself reject I3."
            ),
            missing_obligation="strengthen from grouping equality to proper subcontext witness exhaustion",
            imports=(),
        ),
        ProofRoute(
            id="proper_subcontext_exhaustion_blocks_i3",
            verdict="CIRCULARITY_RISK",
            source="Proofs/QMClosure/S2BornProofSearch.lean",
            decisive_reason=(
                "In the three-alternative toy interface, proper subcontext exhaustion blocks primitive "
                "ternary residue. This is sufficient, but it is not yet independent from S2 unless "
                "derived from a lower witness-generation rule."
            ),
            missing_obligation="derive proper subcontext exhaustion without defining it as no-I3",
            imports=(),
        ),
        ProofRoute(
            id="product_exhaustion_generalized_to_context_exhaustion",
            verdict="CIRCULARITY_RISK",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/175-born-s2-context-only-fact-research-note.md#175.2",
            decisive_reason=(
                "The real-Hilbert hidden joint-only separator and the I3 wall share one pattern: "
                "a stable fact appears only at the whole-context level. Generalizing product-context "
                "exhaustion to arbitrary readout contexts may reject primitive I3, but only if it "
                "independently imposes a proper-subcontext basis rather than restating no-I3."
            ),
            missing_obligation="prove a context-exhaustion theorem, not only the composite product version",
            imports=(),
        ),
        ProofRoute(
            id="current_primitive_base_to_pairwise_basis",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/01-primitives.md",
            decisive_reason=(
                "Constructor generation, no primitive global fact table, local readout witnessing, "
                "and loss accounting still allow a local ternary witness. The witness is not a "
                "global fact table and is not unwitnessed."
            ),
            missing_obligation="add or derive a proper-subcontext/pairwise basis rule",
            imports=(),
        ),
        ProofRoute(
            id="proper_subcontext_basis_to_no_ternary_witness",
            verdict="CIRCULARITY_RISK",
            source="Proofs/QMClosure/S2BornProofSearch.lean",
            decisive_reason=(
                "A proper-subcontext/pairwise basis blocks local ternary witnesses, but this is "
                "only useful if the basis is derived independently from primitive unknownness."
            ),
            missing_obligation="derive the basis without defining it as no ternary witness",
            imports=(),
        ),
        ProofRoute(
            id="pointwise_witnessability_or_nusd_to_s2",
            verdict="COUNTERMODEL_SURVIVES",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/174-context-bundle-nontriviality-research-note.md#174.115",
            decisive_reason=(
                "Pointwise witnessability/NUSD can admit a ternary witness route; it rules out "
                "unwitnessed stable differences, not witnessed third-order facticization."
            ),
            missing_obligation="strengthen witnessability into proper subcontext witness exhaustion",
            imports=(),
        ),
        ProofRoute(
            id="finite_route_compactness_to_s2",
            verdict="COUNTERMODEL_SURVIVES",
            source="sections/174-context-bundle-nontriviality-research-note.md#174.121",
            decisive_reason=(
                "Finite route compactness can bound witness families but still include a compact "
                "ternary route. Compactness is not pairwise exhaustion."
            ),
            missing_obligation="derive pairwise/proper-subcontext basis, not merely finite basis",
            imports=(),
        ),
        ProofRoute(
            id="metricity_of_stable_distinction_to_s2",
            verdict="CIRCULARITY_RISK",
            source="Proofs/QMClosure/S2BornProofSearch.lean; sections/175-born-s2-context-only-fact-research-note.md#175.3",
            decisive_reason=(
                "If stable distinctions are necessarily metric comparison data, then readout is "
                "pairwise and S2 follows. The Lean toy interface checks the conditional implication. "
                "But metricity must be derived independently, or it is another name for pairwise readout."
            ),
            missing_obligation="derive metricity of stable distinguishability from fundamental unknownness",
            imports=(),
        ),
        ProofRoute(
            id="hilbert_bell_metric_common_pattern_to_s2",
            verdict="INSUFFICIENT_CURRENTLY",
            source="sections/173-idt-metalang-research-graph.md#173.13; sections/174-context-bundle-nontriviality-research-note.md#174.132",
            decisive_reason=(
                "Hilbert/Bell/gravity share failed global table, holonomy, witness, and metric-pressure "
                "patterns, but the common pattern is broader than QM and has countermodels without Born."
            ),
            missing_obligation="derive pairwise metric readout rather than only common obstruction shape",
            imports=(),
        ),
        ProofRoute(
            id="higher_order_facticization_as_non_qm_sector",
            verdict="SECTOR_BOUNDARY_POSSIBLE",
            source="sections/175-born-s2-context-only-fact-research-note.md#175.3",
            decisive_reason=(
                "Stable higher-order facticization may be logically possible but outside the QM-scale "
                "sector; then Born is a sector law rather than a universal law of all possible sectors."
            ),
            missing_obligation="decide whether IDT seeks universal S2 or QM-sector S2 only",
            imports=(),
        ),
        ProofRoute(
            id="s2_as_explicit_qm_sector_law",
            verdict="PRIMITIVE_OR_SECTOR_LAW_REQUIRED",
            source="sections/174-context-bundle-nontriviality-research-note.md#174.34",
            decisive_reason=(
                "This is the only route that removes the immediate Born wall without import: "
                "accept S2 as a falsifiable QM-sector law or primitive candidate."
            ),
            missing_obligation="decide whether S2 is primitive, sector-limited, or needs a deeper successor principle",
            imports=(),
        ),
    ]


def count_routes(routes: list[ProofRoute], verdict: RouteVerdict) -> int:
    return sum(1 for route in routes if route.verdict == verdict)


def build_search() -> S2BornProofSearch:
    lean_check = run_lean_check()
    routes = build_routes()
    verdict: SearchVerdict = (
        "FINITE_BORN_CHAIN_HIT_UNIVERSAL_S2_OPEN"
        if lean_check.status == "PASS"
        else "BORN_SEARCH_CHECK_FAILED"
    )
    return S2BornProofSearch(
        verdict=verdict,
        lean_check=lean_check,
        routes_checked=len(routes),
        countermodels=count_routes(routes, "COUNTERMODEL_SURVIVES"),
        conditional_routes=count_routes(routes, "CONDITIONAL_WITH_S2"),
        import_rejected=count_routes(routes, "IMPORT_REJECTED"),
        finite_evidence_only=count_routes(routes, "FINITE_EVIDENCE_NOT_PROOF"),
        finite_carrier_hits=count_routes(routes, "FINITE_CARRIER_HIT"),
        finite_chain_hits=count_routes(routes, "FINITE_CHAIN_HIT"),
        finite_direct_born_hits=count_routes(routes, "FINITE_DIRECT_BORN_HIT"),
        finite_selector_hits=count_routes(routes, "FINITE_SELECTOR_HIT"),
        finite_uniqueness_hits=count_routes(routes, "FINITE_UNIQUENESS_HIT"),
        insufficient=count_routes(routes, "INSUFFICIENT_CURRENTLY"),
        primitive_or_sector_law=count_routes(routes, "PRIMITIVE_OR_SECTOR_LAW_REQUIRED"),
        circularity_risk=count_routes(routes, "CIRCULARITY_RISK"),
        promising_unproved=count_routes(routes, "PROMISING_UNPROVED"),
        sector_boundary_possible=count_routes(routes, "SECTOR_BOUNDARY_POSSIBLE"),
        open_core=(
            "proper_subcontext_pairwise_basis",
            "derive_compatible_kernel_additivity_from_primitives",
            "derive_normalized_overlap_selector_from_primitives",
            "derive_phase_bundle_J_structure_from_primitives",
            "generalize_overlap_selector_to_all_readout_contexts",
            "second_order_facticization",
            "positive_quadratic_actualization_principle",
        ),
        viable_next_route=(
            "Use the finite chain as the target and work below probability: derive compatible "
            "kernel additivity, normalized overlap, phase-bundle J, and proper-subcontext/pairwise "
            "coverage from primitive unknownness. Probability normalization can only read out the "
            "selected weights; it cannot select Born."
        ),
        routes=routes,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run a broad S2/Born proof-search classification over current IDT artifacts."
    )
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-routes", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    search = build_search()
    print(
        f"s2_born_proof_search={search.verdict} lean={search.lean_check.status} "
        f"routes={search.routes_checked} countermodels={search.countermodels} "
        f"conditional={search.conditional_routes} finite_evidence={search.finite_evidence_only} "
        f"finite_uniqueness_hits={search.finite_uniqueness_hits} "
        f"finite_selector_hits={search.finite_selector_hits} "
        f"finite_carrier_hits={search.finite_carrier_hits} "
        f"finite_chain_hits={search.finite_chain_hits} "
        f"finite_direct_born_hits={search.finite_direct_born_hits} "
        f"insufficient={search.insufficient} import_rejected={search.import_rejected} "
        f"primitive_or_sector_law={search.primitive_or_sector_law} "
        f"circularity_risk={search.circularity_risk} "
        f"promising_unproved={search.promising_unproved} "
        f"sector_boundary_possible={search.sector_boundary_possible}"
    )
    print(f"OPEN_CORE {','.join(search.open_core)}")
    print(f"NEXT {search.viable_next_route}")
    if args.show_routes:
        for route in search.routes:
            print(
                f"{route.verdict} {route.id}: missing={route.missing_obligation}; "
                f"source={route.source}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(search), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if search.verdict == "FINITE_BORN_CHAIN_HIT_UNIVERSAL_S2_OPEN" else 1


if __name__ == "__main__":
    raise SystemExit(main())
