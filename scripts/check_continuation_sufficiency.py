"""Check a declared finite model; exit 0 for analysis, 2 for unaccepted input.

This command writes no files and never changes a candidate verdict or history.
Unaccepted certificates may be invalid or outside schema/resource limits; this
does not establish that their evidence is false.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.continuation_sufficiency import (
    LOADED_HELPER_SHA256,
    LOADED_MODULE_SHA256,
    SCOPE,
    analyze,
    demo_models,
    normalize_model,
    verify_certificate,
)
from theory_experiments.primitive_screen import canonical_json, load_json

SOURCE_PATHS = ("theory_experiments/continuation_sufficiency.py",
                "scripts/check_continuation_sufficiency.py",
                "theory_experiments/primitive_screen.py")


def _source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


LOADED_SOURCE_HASHES = _source_hashes()


def evidence(models: dict[str, object], certificate: object | None = None) -> dict[str, object]:
    before = _source_hashes()
    if (before != LOADED_SOURCE_HASHES
            or before[SOURCE_PATHS[0]] != LOADED_MODULE_SHA256
            or before[SOURCE_PATHS[2]] != LOADED_HELPER_SHA256):
        raise ValueError("sources changed since import; restart the interpreter")
    normalized = {name: normalize_model(value) for name, value in models.items()}
    if certificate is None:
        reports = {name: analyze(value) for name, value in normalized.items()}
    else:
        if len(normalized) != 1 or not verify_certificate(next(iter(normalized.values())), certificate):
            raise ValueError("certificate not accepted (invalid or outside supported limits), not candidate rejection")
        reports = {"supplied": {"certificate_valid": True, "candidate_verdict": "unchanged",
                                "proof_status": "concrete_certificate_not_lean_checked",
                                "empirical_status": "not_tested", "scope": SCOPE,
                                "certificate": certificate}}
    if before != _source_hashes():
        raise ValueError("sources changed during analysis; rerun from a stable checkout")
    return {"schema": "idt-continuation-audit/1", "models": normalized,
            "reports": reports, "source_sha256": before,
            "meaning": "declared_model_analysis_not_candidate_confirmation_or_rejection"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--model-file", type=Path)
    inputs.add_argument("--demo", action="store_true")
    parser.add_argument("--certificate-file", type=Path)
    args = parser.parse_args(argv)
    if args.certificate_file is not None and args.model_file is None:
        parser.error("--certificate-file requires --model-file")
    try:
        models = demo_models() if args.demo else {"supplied": load_json(args.model_file)}
        certificate = None if args.certificate_file is None else load_json(args.certificate_file)
        if args.certificate_file is not None and certificate is None:
            raise ValueError("certificate must not be null")
        print(canonical_json(evidence(models, certificate)))
        return 0  # An observable mismatch is completed analysis, not candidate rejection.
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"continuation_sufficiency: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
