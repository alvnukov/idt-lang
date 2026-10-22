"""Read-only finite pair benchmark coverage; absent native adapters never reject a base."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_pipeline import (
    LOADED_SOURCE_HASHES,
    parse_hypothesis,
    provenance,
    run_batch,
)
from theory_experiments.identical_particles import IdenticalPairAmplitudes
from theory_experiments.primitive_screen import bounded_int, canonical_json, load_json


def evidence(specifications: list[object]) -> dict[str, object]:
    bounded_int(len(specifications), 1, 64)
    before = provenance()
    if before["source_sha256"] != LOADED_SOURCE_HASHES:
        raise ValueError("sources changed since import; restart the interpreter")
    reports: list[dict[str, object]] = []
    for specification in specifications:
        candidate = parse_hypothesis(specification)
        row: dict[str, object] = {
            "candidate": candidate.specification(), "candidate_verdict": "unchanged",
            "scientific_status": "unassessed", "empirical_status": "not_tested",
            "proof_status": "not_attempted",
        }
        if isinstance(candidate, IdenticalPairAmplitudes):
            report = run_batch([specification], fresh=True)[0].report
            row.update({"status": report["status"], "scope": report["scope"], "checks": report["checks"]})
        else:
            row.update({"status": "unsupported", "adapter_status": "missing",
                        "requirement_applicability": {"pauli_same_complete_mode": "unassessed",
                                                      "exchange_symmetry": "unassessed"},
                        "reason": "no_reviewed_native_identical_pair_prediction_adapter"})
        reports.append(row)
    if provenance() != before:
        raise ValueError("sources changed during audit; rerun from a stable checkout")
    return {"schema": "idt-identical-pair-coverage/1", "reports": reports, "provenance": before,
            "meaning": "supplied_finite_benchmark_or_missing_adapter_not_native_prediction_or_rejection"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch-file", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        specifications = load_json(args.batch_file)
        if not isinstance(specifications, list):
            raise TypeError("candidate batch must be an array")
        result = evidence(specifications)
        print(canonical_json(result))
        rows = result["reports"]
        assert isinstance(rows, list)
        statuses = [row["status"] for row in rows]
        if "counterexample" in statuses:
            return 1
        return 3 if any(status in ("unsupported", "inconclusive") for status in statuses) else 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"identical_particles: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
