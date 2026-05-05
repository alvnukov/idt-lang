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

import scripts.evaluate_born_hilbert_bell_primitive_link as primitive_link  # noqa: E402
import scripts.evaluate_full_qm_proof_attempt as full_attempt  # noqa: E402
import scripts.evaluate_qm_inevitability_route as inevitability  # noqa: E402
import scripts.evaluate_schrodinger_logic_attempt as schrodinger_logic  # noqa: E402

LEAN_COMMAND = "lake build Proofs.QMClosure.FullQMSectorClosure"

Verdict = Literal[
    "FULL_FINITE_STANDARD_QM_SECTOR_CLOSED_CONDITIONAL",
    "FULL_QM_PROVED",
    "SECTOR_CLOSURE_BLOCKED",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class FullQMSectorClosureProbe:
    verdict: Verdict
    lean_check: LeanCheck
    primitive_link_verdict: str
    primitive_link_failed: int
    full_qm_attempt_verdict: str
    full_qm_attempt_failed: int
    full_qm_attempt_open: int
    inevitability_verdict: str
    inevitability_proof_status: str
    target_open: int
    target_failed: int
    target_imported: int
    schrodinger_logic_verdict: str
    schrodinger_logic_closed: bool
    finite_sector_closed: bool
    exact_fundamental_qm_closed: bool
    exact_frontier_obligations: int
    external_target_adequacy_obligations: int
    closed_clusters: tuple[str, ...]
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


def build_probe() -> FullQMSectorClosureProbe:
    lean_check = run_lean_check()
    primitive = primitive_link.build_pass()
    attempt = full_attempt.build_attempt()
    route = inevitability.build_probe()
    schrodinger_route = next(
        candidate for candidate in schrodinger_logic.ROUTES if candidate.name == "frequency_generator_readout"
    )
    schrodinger = schrodinger_logic.evaluate_route(schrodinger_route)
    schrodinger_closed = (
        schrodinger.verdict == "FREQUENCY_SCHRODINGER_LOGIC_HIT"
        and schrodinger.failed == 0
        and schrodinger.open == 0
    )
    finite_sector_closed = (
        lean_check.status == "PASS"
        and primitive.failed == 0
        and attempt.failed == 0
        and attempt.open == 0
        and route.open_targets == 0
        and route.failed_targets == 0
        and route.imported_targets == 0
        and schrodinger_closed
    )
    exact_fundamental_qm_closed = finite_sector_closed and route.proof_status == "FORMAL_PROOF"
    if not finite_sector_closed:
        verdict: Verdict = "SECTOR_CLOSURE_BLOCKED"
    elif exact_fundamental_qm_closed:
        verdict = "FULL_QM_PROVED"
    else:
        verdict = "FULL_FINITE_STANDARD_QM_SECTOR_CLOSED_CONDITIONAL"
    return FullQMSectorClosureProbe(
        verdict=verdict,
        lean_check=lean_check,
        primitive_link_verdict=primitive.verdict,
        primitive_link_failed=primitive.failed,
        full_qm_attempt_verdict=attempt.verdict,
        full_qm_attempt_failed=attempt.failed,
        full_qm_attempt_open=attempt.open,
        inevitability_verdict=route.verdict,
        inevitability_proof_status=route.proof_status,
        target_open=route.open_targets,
        target_failed=route.failed_targets,
        target_imported=route.imported_targets,
        schrodinger_logic_verdict=schrodinger.verdict,
        schrodinger_logic_closed=schrodinger_closed,
        finite_sector_closed=finite_sector_closed,
        exact_fundamental_qm_closed=exact_fundamental_qm_closed,
        exact_frontier_obligations=6,
        external_target_adequacy_obligations=4,
        closed_clusters=(
            "born_readout_finite_constructor_respecting_route",
            "hilbert_frontier_under_carrier_exhaustion",
            "semantic_full_qm_obligation_bundle",
            "readout_scaffolds",
            "dynamics_scaffolds",
            "schrodinger_frequency_generator_readout",
            "composite_scaffolds",
            "import_boundaries",
            "exact_qm_frontier_obligation_contract",
            "external_target_adequacy_obligation_contract",
        ),
        remaining_obligations=(
            "derive_B1_or_successor_base_from_lower_B0_without_target_imports",
            "derive_context_first_constructive_witness_completeness_from_lower_base",
            "prove_carrier_frontier_exhaustion_or_record_non_Hilbert_constructive_countermodel",
            "promote_conditional_package_artifacts_to_external_QM_adequacy_theorems",
            "derive_context_first_universal_endpoint_data_for_exact_Born",
            "derive_first_principles_physical_phase_scale_or_keep_calibrated_hbar_boundary",
        ),
        forbidden_upgrades=(
            "does_not_prove_exact_fundamental_QM",
            "does_not_prove_universal_Born_from_B0_alone",
            "does_not_prove_universal_Hilbert_uniqueness_without_frontier_exhaustion",
            "does_not_derive_hbar_I",
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate the wide finite standard-QM sector closure theorem.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-details", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"full_qm_sector_closure={probe.verdict} lean={probe.lean_check.status} "
        f"finite_sector_closed={probe.finite_sector_closed} "
        f"exact_fundamental_qm_closed={probe.exact_fundamental_qm_closed} "
        f"primitive_link={probe.primitive_link_verdict} primitive_failed={probe.primitive_link_failed} "
        f"full_attempt={probe.full_qm_attempt_verdict} open={probe.full_qm_attempt_open} "
        f"failed={probe.full_qm_attempt_failed} inevitability={probe.inevitability_verdict} "
        f"proof_status={probe.inevitability_proof_status} target_open={probe.target_open} "
        f"target_failed={probe.target_failed} target_imported={probe.target_imported} "
        f"schrodinger_logic={probe.schrodinger_logic_verdict} "
        f"schrodinger_closed={probe.schrodinger_logic_closed} "
        f"exact_frontier_obligations={probe.exact_frontier_obligations} "
        f"external_target_adequacy_obligations={probe.external_target_adequacy_obligations}"
    )
    print(f"REMAINING {','.join(probe.remaining_obligations)}")
    print(f"FORBIDDEN_UPGRADES {','.join(probe.forbidden_upgrades)}")
    if args.show_details:
        print(f"LEAN_COMMAND {probe.lean_check.command}")
        print(f"CLOSED_CLUSTERS {','.join(probe.closed_clusters)}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if probe.verdict != "SECTOR_CLOSURE_BLOCKED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
