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
import scripts.evaluate_phase_scale_boundary_attempt as phase_scale_attempt  # noqa: E402

LEAN_COMMAND = "lake build Proofs.QMClosure.BornWallSeparation"

Verdict = Literal[
    "BORN_WALL_REQUIRES_ACTUALIZATION_PRINCIPLE",
    "BORN_WALL_CHECK_FAILED",
    "BORN_WALL_IMPORT_REJECTED",
]
CheckStatus = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class BornWallSeparationProbe:
    verdict: Verdict
    lean_check: LeanCheck
    conditional_born_route: str
    phase_scale_boundary: str
    accounting_countermodel: CheckStatus
    conditional_h11: CheckStatus
    calibrated_scale_boundary: CheckStatus
    missing_principle: str
    next_blocker: str
    forbidden_upgrades: tuple[str, ...]


FORBIDDEN_UPGRADES: tuple[str, ...] = (
    "does_not_prove_universal_Born_rule",
    "does_not_prove_full_QM_I",
    "does_not_derive_hbar_I",
    "does_not_treat_linear_countermodel_as_physical_QM",
    "does_not_treat_accounting_scaffold_as_quadratic_selection",
)


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


def find_born_route() -> born_attempt.RouteResult:
    for route in born_attempt.ROUTES:
        if route.name == "quadratic_context_probability_route":
            return born_attempt.evaluate_route(route)
    raise ValueError("missing quadratic_context_probability_route")


def find_phase_scale_route() -> phase_scale_attempt.RouteResult:
    for route in phase_scale_attempt.ROUTES:
        if route.name == "calibrated_phase_scale_boundary":
            return phase_scale_attempt.evaluate_route(route)
    raise ValueError("missing calibrated_phase_scale_boundary")


def build_probe() -> BornWallSeparationProbe:
    lean_check = run_lean_check()
    born_route = find_born_route()
    phase_route = find_phase_scale_route()
    imported = bool(born_route.imports) or bool(phase_route.imports)
    if lean_check.status == "FAIL":
        verdict: Verdict = "BORN_WALL_CHECK_FAILED"
    elif imported:
        verdict = "BORN_WALL_IMPORT_REJECTED"
    else:
        verdict = "BORN_WALL_REQUIRES_ACTUALIZATION_PRINCIPLE"
    return BornWallSeparationProbe(
        verdict=verdict,
        lean_check=lean_check,
        conditional_born_route=born_route.verdict,
        phase_scale_boundary=phase_route.verdict,
        accounting_countermodel=lean_check.status,
        conditional_h11=lean_check.status,
        calibrated_scale_boundary=lean_check.status,
        missing_principle="positive_quadratic_actualization_principle",
        next_blocker=(
            "prove positive_quadratic_actualization_principle from B1 or a successor primitive base, "
            "or declare it as an explicit new primitive/boundary assumption; the current accounting "
            "scaffold admits a non-quadratic stable readout and therefore does not select Born by itself"
        ),
        forbidden_upgrades=FORBIDDEN_UPGRADES,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Diagnose whether the Born wall is derived or requires an actualization principle."
    )
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"born_wall_separation={probe.verdict} lean={probe.lean_check.status} "
        f"born_route={probe.conditional_born_route} phase_scale={probe.phase_scale_boundary} "
        f"countermodel={probe.accounting_countermodel} h11={probe.conditional_h11} "
        f"missing={probe.missing_principle}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("BORN_WALL_CHECK_FAILED", "BORN_WALL_IMPORT_REJECTED"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
