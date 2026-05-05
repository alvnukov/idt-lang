from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMAND = "lake build Proofs.QMClosure.PrimitiveBoundaryQMChain"

Verdict = Literal[
    "BOUND_INTERFACE_ONLY",
    "IMPORTED_HIT",
    "PARTIAL_BOUNDARY",
    "PRIMITIVE_BOUNDARY_CANDIDATE",
    "REJECTED",
    "SECTOR_LAW_CANDIDATE",
]
GateVerdict = Literal[
    "PRIMITIVE_BOUNDARY_CANDIDATE_IDENTIFIED_NOT_DERIVED",
    "PRIMITIVE_BOUNDARY_CHECK_FAILED",
]
CheckVerdict = Literal["PASS", "FAIL"]


@dataclass(frozen=True)
class LeanCheck:
    command: str
    returncode: int
    status: CheckVerdict


@dataclass(frozen=True)
class BoundaryCandidate:
    name: str
    b1_bound_interface: bool
    no_target_imports: bool
    compatible_kernel_additivity: bool
    normalized_overlap_uniqueness: bool
    phase_bundle_j: bool
    proper_subcontext_pairwise_coverage: bool
    no_hidden_ternary_fact: bool
    sector_limited: bool
    imports: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class CandidateCheck:
    name: str
    verdict: CheckVerdict
    reason: str
    details: dict[str, bool | int | str]


@dataclass(frozen=True)
class CandidateResult:
    candidate: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    checks: list[CandidateCheck]
    missing: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class PrimitiveBoundaryGate:
    verdict: GateVerdict
    lean_check: LeanCheck
    candidates_checked: int
    primitive_boundary_candidates: int
    sector_law_candidates: int
    partial_boundaries: int
    bound_interface_only: int
    imported_hits: int
    rejected: int
    required_principles: tuple[str, ...]
    current_wall: str
    results: list[CandidateResult]


CANDIDATES: tuple[BoundaryCandidate, ...] = (
    BoundaryCandidate(
        name="b1_bound_interface_only",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=False,
        normalized_overlap_uniqueness=False,
        phase_bundle_j=False,
        proper_subcontext_pairwise_coverage=False,
        no_hidden_ternary_fact=False,
        sector_limited=False,
        imports=(),
        description="current B1-style constructor-bound primitive interface and import guards",
    ),
    BoundaryCandidate(
        name="b1_plus_compatible_kernel_only",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=False,
        phase_bundle_j=False,
        proper_subcontext_pairwise_coverage=False,
        no_hidden_ternary_fact=False,
        sector_limited=False,
        imports=(),
        description="B1 plus additive compatible-kernel composition, without overlap/J/pairwise coverage",
    ),
    BoundaryCandidate(
        name="b1_plus_kernel_overlap_j_without_pairwise_coverage",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=False,
        no_hidden_ternary_fact=False,
        sector_limited=False,
        imports=(),
        description="finite-chain inputs except the rule that blocks hidden ternary context-only facts",
    ),
    BoundaryCandidate(
        name="full_primitive_boundary_candidate",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=(),
        description="universal primitive-boundary target needed to close the finite Born chain from primitives",
    ),
    BoundaryCandidate(
        name="qm_sector_overlap_boundary",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=True,
        imports=(),
        description="same package declared as a falsifiable QM-sector boundary rather than a universal primitive theorem",
    ),
    BoundaryCandidate(
        name="missing_kernel_additivity_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=False,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=(),
        description="drop-one control: all boundary inputs except compatible kernel additivity",
    ),
    BoundaryCandidate(
        name="missing_overlap_uniqueness_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=False,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=(),
        description="drop-one control: all boundary inputs except normalized overlap uniqueness",
    ),
    BoundaryCandidate(
        name="missing_phase_bundle_j_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=False,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=(),
        description="drop-one control: all boundary inputs except phase-bundle J",
    ),
    BoundaryCandidate(
        name="missing_pairwise_coverage_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=False,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=(),
        description="drop-one control: all boundary inputs except proper-subcontext/pairwise coverage",
    ),
    BoundaryCandidate(
        name="missing_no_hidden_ternary_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=False,
        sector_limited=False,
        imports=(),
        description="drop-one control: all boundary inputs except no-hidden-ternary fact discipline",
    ),
    BoundaryCandidate(
        name="hilbert_born_import_control",
        b1_bound_interface=True,
        no_target_imports=False,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=True,
        no_hidden_ternary_fact=True,
        sector_limited=False,
        imports=("hilbert_space", "born_rule", "complex_scalar"),
        description="control that closes the target by importing Hilbert/Born/complex structure",
    ),
    BoundaryCandidate(
        name="hidden_ternary_context_control",
        b1_bound_interface=True,
        no_target_imports=True,
        compatible_kernel_additivity=True,
        normalized_overlap_uniqueness=True,
        phase_bundle_j=True,
        proper_subcontext_pairwise_coverage=False,
        no_hidden_ternary_fact=False,
        sector_limited=False,
        imports=(),
        description="control with a stable hidden ternary context-only fact still admitted",
    ),
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


def make_check(name: str, passed: bool, reason: str, details: dict[str, bool | int | str]) -> CandidateCheck:
    return CandidateCheck(name=name, verdict="PASS" if passed else "FAIL", reason=reason, details=details)


def check_candidate(candidate: BoundaryCandidate) -> list[CandidateCheck]:
    chain_inputs = (
        candidate.compatible_kernel_additivity
        and candidate.normalized_overlap_uniqueness
        and candidate.phase_bundle_j
    )
    pairwise_closure = candidate.proper_subcontext_pairwise_coverage and candidate.no_hidden_ternary_fact
    finite_chain_projection = (
        candidate.b1_bound_interface
        and candidate.no_target_imports
        and chain_inputs
        and pairwise_closure
    )
    return [
        make_check(
            "bound_interface",
            candidate.b1_bound_interface,
            "candidate is tied to the B1/context-first bound primitive interface",
            {"b1_bound_interface": candidate.b1_bound_interface},
        ),
        make_check(
            "import_screen",
            candidate.no_target_imports and not candidate.imports,
            "candidate does not import Hilbert, Born, complex scalars, unitary, or tensor structure",
            {"no_target_imports": candidate.no_target_imports, "imports": ",".join(candidate.imports) or "-"},
        ),
        make_check(
            "finite_chain_inputs",
            chain_inputs,
            "candidate supplies compatible kernel additivity, normalized overlap uniqueness, and phase-bundle J",
            {
                "compatible_kernel_additivity": candidate.compatible_kernel_additivity,
                "normalized_overlap_uniqueness": candidate.normalized_overlap_uniqueness,
                "phase_bundle_j": candidate.phase_bundle_j,
            },
        ),
        make_check(
            "pairwise_coverage",
            pairwise_closure,
            "candidate blocks hidden ternary facts through proper-subcontext/pairwise coverage",
            {
                "proper_subcontext_pairwise_coverage": candidate.proper_subcontext_pairwise_coverage,
                "no_hidden_ternary_fact": candidate.no_hidden_ternary_fact,
            },
        ),
        make_check(
            "finite_chain_projection",
            finite_chain_projection,
            "candidate can feed the checked finite Born/phase-bundle chain without target imports",
            {"finite_chain_projection": finite_chain_projection},
        ),
    ]


def missing_obligations(candidate: BoundaryCandidate) -> tuple[str, ...]:
    missing: list[str] = []
    if not candidate.b1_bound_interface:
        missing.append("bind_to_context_first_B1_interface")
    if not candidate.no_target_imports or candidate.imports:
        missing.append("remove_target_imports")
    if not candidate.compatible_kernel_additivity:
        missing.append("compatible_kernel_additivity")
    if not candidate.normalized_overlap_uniqueness:
        missing.append("normalized_overlap_uniqueness")
    if not candidate.phase_bundle_j:
        missing.append("phase_bundle_J")
    if not candidate.proper_subcontext_pairwise_coverage:
        missing.append("proper_subcontext_pairwise_coverage")
    if not candidate.no_hidden_ternary_fact:
        missing.append("no_hidden_ternary_context_fact")
    return tuple(missing)


def evaluate_candidate(candidate: BoundaryCandidate) -> CandidateResult:
    checks = check_candidate(candidate)
    passed = sum(1 for check in checks if check.verdict == "PASS")
    failed = len(checks) - passed
    missing = missing_obligations(candidate)
    if candidate.imports or not candidate.no_target_imports:
        verdict: Verdict = "IMPORTED_HIT"
    elif passed == len(checks) and candidate.sector_limited:
        verdict = "SECTOR_LAW_CANDIDATE"
    elif passed == len(checks):
        verdict = "PRIMITIVE_BOUNDARY_CANDIDATE"
    elif candidate.b1_bound_interface and candidate.no_target_imports and passed <= 2:
        verdict = "BOUND_INTERFACE_ONLY"
    elif candidate.b1_bound_interface and candidate.no_target_imports and passed >= 3:
        verdict = "PARTIAL_BOUNDARY"
    else:
        verdict = "REJECTED"
    return CandidateResult(
        candidate=candidate.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=candidate.imports,
        checks=checks,
        missing=missing,
        description=candidate.description,
    )


def count(results: list[CandidateResult], verdict: Verdict) -> int:
    return sum(1 for result in results if result.verdict == verdict)


def build_gate() -> PrimitiveBoundaryGate:
    lean_check = run_lean_check()
    results = [evaluate_candidate(candidate) for candidate in CANDIDATES]
    gate_verdict: GateVerdict = (
        "PRIMITIVE_BOUNDARY_CANDIDATE_IDENTIFIED_NOT_DERIVED"
        if lean_check.status == "PASS" and count(results, "PRIMITIVE_BOUNDARY_CANDIDATE") == 1
        else "PRIMITIVE_BOUNDARY_CHECK_FAILED"
    )
    return PrimitiveBoundaryGate(
        verdict=gate_verdict,
        lean_check=lean_check,
        candidates_checked=len(results),
        primitive_boundary_candidates=count(results, "PRIMITIVE_BOUNDARY_CANDIDATE"),
        sector_law_candidates=count(results, "SECTOR_LAW_CANDIDATE"),
        partial_boundaries=count(results, "PARTIAL_BOUNDARY"),
        bound_interface_only=count(results, "BOUND_INTERFACE_ONLY"),
        imported_hits=count(results, "IMPORTED_HIT"),
        rejected=count(results, "REJECTED"),
        required_principles=(
            "compatible_kernel_additivity",
            "normalized_overlap_uniqueness",
            "phase_bundle_J",
            "proper_subcontext_pairwise_coverage",
            "no_hidden_ternary_context_fact",
        ),
        current_wall=(
            "B1 gives constructor binding and import guards, but a full primitive-boundary theorem "
            "must still derive the five required principles or mark them as an audited QM-sector law."
        ),
        results=results,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Classify primitive-boundary candidates for the finite QM chain.")
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-candidates", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    gate = build_gate()
    print(
        f"primitive_boundary_qm_chain={gate.verdict} lean={gate.lean_check.status} "
        f"candidates={gate.candidates_checked} primitive_boundary={gate.primitive_boundary_candidates} "
        f"sector_law={gate.sector_law_candidates} partial={gate.partial_boundaries} "
        f"bound_only={gate.bound_interface_only} imported={gate.imported_hits} rejected={gate.rejected}"
    )
    print(f"REQUIRED {','.join(gate.required_principles)}")
    print(f"WALL {gate.current_wall}")
    if args.show_candidates:
        for result in gate.results:
            missing = ",".join(result.missing) if result.missing else "-"
            imports = ",".join(result.imports) if result.imports else "-"
            print(
                f"{result.verdict} {result.candidate}: passed={result.passed}/5 "
                f"missing={missing} imports={imports}"
            )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(gate), handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if gate.verdict == "PRIMITIVE_BOUNDARY_CANDIDATE_IDENTIFIED_NOT_DERIVED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
