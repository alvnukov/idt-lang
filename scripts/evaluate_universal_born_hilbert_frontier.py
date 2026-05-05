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

import scripts.evaluate_born_readout_attempt as born_readout  # noqa: E402
import scripts.evaluate_born_wall_separation as born_wall  # noqa: E402
import scripts.evaluate_finite_sector_classification as finite_sector  # noqa: E402
import scripts.evaluate_representation_classification_attempt as representation  # noqa: E402
import scripts.evaluate_s2_born_proof_search as s2_born  # noqa: E402

LEAN_COMMAND = "lake build Proofs.QMClosure.BornHilbertUniversalClosure"

Verdict = Literal[
    "UNIVERSAL_BORN_HILBERT_FRONTIER_CLOSED_CONDITIONAL",
    "UNIVERSAL_BORN_HILBERT_FRONTIER_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class UniversalBornHilbertFrontierProbe:
    verdict: Verdict
    lean_check: LeanCheck
    born_square_core: str
    pairwise_endpoint_core: str
    primitive_boundary_endpoint_core: str
    context_first_endpoint_core: str
    current_base_coverage: str
    b1_endpoint_data: str
    born_wall_verdict: str
    born_readout_verdict: str
    s2_born_verdict: str
    s2_countermodels: int
    representation_verdict: str
    complex_finite_sector_verdict: str
    conditional_frontier_closed: bool
    exact_from_b0_closed: bool
    closed_result: str
    remaining_obligations: tuple[str, ...]
    forbidden_upgrades: tuple[str, ...]


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


def find_born_readout_route() -> born_readout.RouteResult:
    for route in born_readout.ROUTES:
        if route.name == "quadratic_context_probability_route":
            return born_readout.evaluate_route(route)
    raise ValueError("missing quadratic_context_probability_route")


def find_representation_route() -> representation.RouteResult:
    for route in representation.ROUTES:
        if route.name == "spectral_symmetry_route":
            return representation.evaluate_route(route)
    raise ValueError("missing spectral_symmetry_route")


def find_complex_finite_sector() -> finite_sector.CandidateResult:
    for candidate in finite_sector.CANDIDATES:
        if candidate.name == "complex_hilbert_qubit_route":
            return finite_sector.evaluate_candidate(candidate)
    raise ValueError("missing complex_hilbert_qubit_route")


def build_probe() -> UniversalBornHilbertFrontierProbe:
    lean_check = run_lean_check()
    wall_probe = born_wall.build_probe()
    born_route = find_born_readout_route()
    s2_search = s2_born.build_search()
    representation_route = find_representation_route()
    complex_sector = find_complex_finite_sector()
    conditional_frontier_closed = (
        lean_check.status == "PASS"
        and wall_probe.verdict == "BORN_WALL_REQUIRES_ACTUALIZATION_PRINCIPLE"
        and born_route.verdict == "CONDITIONAL_BORN_ROUTE"
        and not born_route.imports
        and s2_search.verdict == "FINITE_BORN_CHAIN_HIT_UNIVERSAL_S2_OPEN"
        and s2_search.countermodels > 0
        and representation_route.verdict == "CONDITIONAL_REPRESENTATION_ROUTE"
        and not representation_route.imports
        and complex_sector.verdict == "FINITE_SECTOR_HIT"
        and not complex_sector.imports
    )
    verdict: Verdict = (
        "UNIVERSAL_BORN_HILBERT_FRONTIER_CLOSED_CONDITIONAL"
        if conditional_frontier_closed
        else "UNIVERSAL_BORN_HILBERT_FRONTIER_BLOCKED"
    )
    return UniversalBornHilbertFrontierProbe(
        verdict=verdict,
        lean_check=lean_check,
        born_square_core="UNIVERSAL_ORIENTED_CONTEXT_BORN_SQUARE_PROVED" if lean_check.status == "PASS" else "BLOCKED",
        pairwise_endpoint_core="PRIMITIVE_PAIRWISE_ENDPOINT_COVERAGE_TO_BORN_PROVED"
        if lean_check.status == "PASS"
        else "BLOCKED",
        primitive_boundary_endpoint_core="PRIMITIVE_BOUNDARY_ENDPOINT_COVERAGE_TO_BORN_PROVED"
        if lean_check.status == "PASS"
        else "BLOCKED",
        context_first_endpoint_core="CONTEXT_FIRST_ENDPOINT_DATA_TO_BORN_HILBERT_PROVED"
        if lean_check.status == "PASS"
        else "BLOCKED",
        current_base_coverage="CURRENT_BASE_DOES_NOT_FORCE_PAIRWISE_ENDPOINT_COVERAGE"
        if lean_check.status == "PASS"
        else "BLOCKED",
        b1_endpoint_data="B1_INTERFACE_DOES_NOT_FORCE_CONTEXT_FIRST_ENDPOINT_DATA"
        if lean_check.status == "PASS"
        else "BLOCKED",
        born_wall_verdict=wall_probe.verdict,
        born_readout_verdict=born_route.verdict,
        s2_born_verdict=s2_search.verdict,
        s2_countermodels=s2_search.countermodels,
        representation_verdict=representation_route.verdict,
        complex_finite_sector_verdict=complex_sector.verdict,
        conditional_frontier_closed=conditional_frontier_closed,
        exact_from_b0_closed=False,
        closed_result=(
            "context-first universal endpoint data supplies primitive pairwise "
            "endpoint coverage and Born readout; with carrier-frontier exhaustion "
            "it closes frontier-scoped Hilbert representation"
        ),
        remaining_obligations=(
            "derive_context_first_universal_endpoint_data_from_B0_or_successor_base",
            "prove_carrier_frontier_exhaustion_over_all_admissible_carriers",
            "promote_conditional_frontier_closure_to_external_QM_adequacy_theorem",
            "keep_hbar_I_calibrated_or_derive_first_principles_phase_scale_separately",
        ),
        forbidden_upgrades=(
            "does_not_prove_full_QM_I",
            "does_not_prove_universal_Born_from_B0_alone",
            "does_not_prove_universal_Hilbert_uniqueness_from_finite_frontier_alone",
            "does_not_derive_hbar_I",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate the universal Born/Hilbert frontier closure contract.")
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"universal_born_hilbert_frontier={probe.verdict} "
        f"lean={probe.lean_check.status} "
        f"born_square_core={probe.born_square_core} "
        f"pairwise_endpoint_core={probe.pairwise_endpoint_core} "
        f"primitive_boundary_endpoint_core={probe.primitive_boundary_endpoint_core} "
        f"context_first_endpoint_core={probe.context_first_endpoint_core} "
        f"current_base_coverage={probe.current_base_coverage} "
        f"b1_endpoint_data={probe.b1_endpoint_data} "
        f"born_wall={probe.born_wall_verdict} "
        f"born_readout={probe.born_readout_verdict} "
        f"s2_born={probe.s2_born_verdict} "
        f"s2_countermodels={probe.s2_countermodels} "
        f"representation={probe.representation_verdict} "
        f"complex_sector={probe.complex_finite_sector_verdict} "
        f"conditional_frontier_closed={probe.conditional_frontier_closed} "
        f"exact_from_b0_closed={probe.exact_from_b0_closed}"
    )
    print(f"CLOSED_RESULT {probe.closed_result}")
    print(f"REMAINING {','.join(probe.remaining_obligations)}")
    print(f"FORBIDDEN_UPGRADES {','.join(probe.forbidden_upgrades)}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if probe.conditional_frontier_closed else 1


if __name__ == "__main__":
    raise SystemExit(main())
