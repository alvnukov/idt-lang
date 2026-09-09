"""Check a proposed scalar projection without changing candidate verdicts or history."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_pipeline import LOADED_SOURCE_HASHES, provenance
from theory_experiments.native_observability import (
    LOADED_MODULE_SHA256,
    analyze_projection,
)
from theory_experiments.primitive_screen import (
    bounded_int,
    canonical_json,
    load_json,
    object_fields,
)

EXTRA_SOURCES = (
    "theory_experiments/native_observability.py", "scripts/check_native_observability.py",
    "Proofs/QMClosure/NativeAmplitudeObservability.lean",
)


def _extra_source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in EXTRA_SOURCES}


LOADED_PROVENANCE = provenance()
LOADED_EXTRA_HASHES = _extra_source_hashes()


def evidence(specifications: list[object]) -> dict[str, object]:
    bounded_int(len(specifications), 1, 64)
    before = provenance()
    hashes = _extra_source_hashes()
    if (before != LOADED_PROVENANCE or hashes != LOADED_EXTRA_HASHES
            or before["source_sha256"] != LOADED_SOURCE_HASHES
            or hashes["theory_experiments/native_observability.py"] != LOADED_MODULE_SHA256):
        raise ValueError("sources changed since import; restart the interpreter")
    reports = [analyze_projection(spec) for spec in specifications]
    after = _extra_source_hashes()
    if before != provenance() or hashes != after:
        raise ValueError("source changed during analysis; rerun from a stable checkout")
    return {"schema": "idt-native-observability/1", "candidates": specifications,
            "reports": reports, "provenance": before, "additional_source_sha256": hashes,
            "meaning": "projection_analysis_not_candidate_confirmation_or_rejection"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch-file", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        specifications = load_json(args.batch_file)
        if not isinstance(specifications, list):
            raise TypeError("candidate batch must be an array")
        report = evidence(specifications)
        print(canonical_json(report))
        # A failed projection is a completed analysis, not candidate rejection.
        rows = report["reports"]
        assert isinstance(rows, list)
        return 3 if any(object_fields(row)["status"] == "unsupported" for row in rows) else 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"native_observability: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
