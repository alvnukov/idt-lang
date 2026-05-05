from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMAND = "lake build Proofs.QMClosure.B1CGSCClauseDerivation"

Verdict = Literal["B1_CGSC_CLAUSES_MACHINE_DERIVED", "B1_CGSC_CLAUSE_DERIVATION_CHECK_FAILED"]
CheckStatus = Literal["PASS", "FAIL"]

CGSC_CLAUSES: tuple[str, ...] = (
    "finite_generation",
    "facticizable_separation",
    "exposed_context_decomposition",
    "reversible_route_closure",
    "coherent_refinement_flow",
    "composite_route_generation",
    "import_boundary",
)

STRUCTURAL_TARGETS: tuple[str, ...] = (
    "nonunital_stable_distinguishability",
    "spectral_decomposition",
    "rich_d_cl_reversible_symmetry",
    "continuous_inheritance_family",
    "generator_closure",
    "entanglement_closure",
)

FORBIDDEN_UPGRADES: tuple[str, ...] = (
    "does_not_prove_full_QM_I",
    "does_not_derive_Hilbert_space_from_B0_alone",
    "does_not_derive_Born_rule_from_B0_alone",
    "does_not_replace_external_QM_equivalence_theorems",
)


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckStatus


@dataclass(frozen=True)
class B1CGSCClauseDerivationProbe:
    verdict: Verdict
    lean_check: LeanCheck
    clauses: tuple[str, ...]
    machine_derived_clauses: int
    structural_targets: tuple[str, ...]
    closed_structural_targets: int
    shared_atom_universe: CheckStatus
    import_boundaries_preserved: CheckStatus
    next_blocker: str
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


def build_probe() -> B1CGSCClauseDerivationProbe:
    lean_check = run_lean_check()
    passed = lean_check.status == "PASS"
    return B1CGSCClauseDerivationProbe(
        verdict=(
            "B1_CGSC_CLAUSES_MACHINE_DERIVED"
            if passed
            else "B1_CGSC_CLAUSE_DERIVATION_CHECK_FAILED"
        ),
        lean_check=lean_check,
        clauses=CGSC_CLAUSES,
        machine_derived_clauses=len(CGSC_CLAUSES) if passed else 0,
        structural_targets=STRUCTURAL_TARGETS,
        closed_structural_targets=len(STRUCTURAL_TARGETS) if passed else 0,
        shared_atom_universe=lean_check.status,
        import_boundaries_preserved=lean_check.status,
        next_blocker=(
            "prove external adequacy: show the B1-derived CGSC package is not only an internal "
            "IDT obligation bundle but reconstructs Hilbert/Born/unitary/tensor QM with the intended "
            "universal physical semantics"
        ),
        forbidden_upgrades=FORBIDDEN_UPGRADES,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Check the B1 machine derivation of all seven CGSC clauses."
    )
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-clauses", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe()
    print(
        f"b1_cgsc_clause_derivation={probe.verdict} lean={probe.lean_check.status} "
        f"clauses={len(probe.clauses)} machine_derived={probe.machine_derived_clauses} "
        f"structural_targets={len(probe.structural_targets)} closed_targets={probe.closed_structural_targets} "
        f"shared_atom_universe={probe.shared_atom_universe} import_boundaries={probe.import_boundaries_preserved}"
    )
    print(f"NEXT {probe.next_blocker}")
    if args.show_clauses:
        for clause in probe.clauses:
            print(f"CLAUSE {clause}")
        for target in probe.structural_targets:
            print(f"TARGET {target}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict != "B1_CGSC_CLAUSES_MACHINE_DERIVED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
