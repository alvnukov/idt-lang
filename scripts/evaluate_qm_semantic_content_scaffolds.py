from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]

LEAN_COMMAND = "lake build Proofs.QMClosure.QMSemanticContentScaffoldBundle"

Verdict = Literal["SCAFFOLD_BUNDLE_CHECKED", "SCAFFOLD_BUNDLE_CHECK_FAILED"]
CheckStatus = Literal["PASS", "FAIL"]

MACHINE_CHECKED_SCAFFOLDS = (
    "conservative_projective_gluing_scaffold",
    "readout_probability_scaffold",
    "inheritance_action_scaffold",
    "product_local_tomography_scaffold",
    "monoidal_associativity_scaffold",
    "projective_limit_consistency_scaffold",
    "calibrated_scale_boundary_scaffold",
)

STRUCTURAL_TARGET_BLOCKERS = (
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
class SemanticContentScaffoldProbe:
    verdict: Verdict
    lean_check: LeanCheck
    machine_checked_scaffolds: tuple[str, ...]
    structural_target_blockers: tuple[str, ...]
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


def build_probe() -> SemanticContentScaffoldProbe:
    lean_check = run_lean_check()
    verdict: Verdict = "SCAFFOLD_BUNDLE_CHECKED" if lean_check.status == "PASS" else "SCAFFOLD_BUNDLE_CHECK_FAILED"
    return SemanticContentScaffoldProbe(
        verdict=verdict,
        lean_check=lean_check,
        machine_checked_scaffolds=MACHINE_CHECKED_SCAFFOLDS,
        structural_target_blockers=STRUCTURAL_TARGET_BLOCKERS,
        next_blocker=(
            "combine the finite scaffold bundle with B1 CGSC closure, then prove external "
            "Hilbert/Born/unitary/tensor adequacy; the scaffold bundle is machine-checked "
            "but is not itself a full-QM proof"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Check the finite semantic-content scaffold bundle for the current QM proof route."
    )
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-blockers", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"qm_semantic_content_scaffolds={probe.verdict} lean={probe.lean_check.status} "
        f"machine_checked_scaffolds={len(probe.machine_checked_scaffolds)} "
        f"structural_target_blockers={len(probe.structural_target_blockers)}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.show_blockers:
        for blocker in probe.structural_target_blockers:
            print(f"BLOCKER {blocker}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict != "SCAFFOLD_BUNDLE_CHECKED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
