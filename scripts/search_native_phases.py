"""Run the fixed 52-law exploratory campaign; no writes unless explicitly requested.

Hits are exact finite traces, not empirical support, global norm preservation or
QM derivation. No-hit means only the selected integer box/filter/readout. The
unit-weight filter strongly favors Gaussian roots; it is not physical selection.
"""

from __future__ import annotations

import argparse
import gzip
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_history import History
from theory_experiments.native_phase_search import DEFAULT_CONFIG, campaign, load_config
from theory_experiments.primitive_screen import canonical_json


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG,
                        help="fixed reviewed configuration (no tuning parameters)")
    parser.add_argument("--output", type=Path,
                        help="write full exact phase evidence to a NEW file; .gz uses deterministic gzip; refuse replacement")
    parser.add_argument("--record-history", action="store_true",
                        help="explicitly archive all 52 input laws and bounded screen reports")
    parser.add_argument("--history-dir", type=Path,
                        help="optional archive location; requires --record-history")
    args = parser.parse_args(argv)
    if args.history_dir is not None and not args.record_history:
        parser.error("--history-dir requires --record-history")
    if args.record_history and args.output is None:
        parser.error("--record-history requires --output to preserve phase evidence too")
    if args.output is not None and args.output.exists():
        parser.error("--output must name a new file; nothing will be overwritten")
    try:
        archive = (History() if args.history_dir is None else History(args.history_dir)) if args.record_history else None
        report = campaign(load_config(args.config), history=archive)
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            raw = canonical_json(report).encode("utf-8") + b"\n"
            if args.output.suffix == ".gz":
                raw = gzip.compress(raw, mtime=0)
            with args.output.open("xb") as destination:
                destination.write(raw)
        print(canonical_json({"summary": report["summary"], "report_sha256": report["report_sha256"],
                              "output": None if args.output is None else str(args.output),
                              "archival": report["archival"], "candidate_verdict": "unchanged"}))
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"native_phase_search: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
