"""Replay Mazurek et al. (2016) primary coincidence rates offline."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from xml.etree.ElementTree import ParseError
from zipfile import BadZipFile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.mazurek_primary import (
    FIXTURE,
    extract_workbooks,
    load_counts,
    summarize,
    write_counts,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--fixture", type=Path, help="read an alternative copy of the pinned gzip fixture")
    parser.add_argument("--aggregate-workbook", type=Path, help="publisher source file 1462")
    parser.add_argument("--run-workbook", type=Path, help="publisher source file 1463")
    parser.add_argument("--output", type=Path, help="create a new .json.gz fixture from both workbooks")
    args = parser.parse_args(argv)
    if (args.aggregate_workbook is None) != (args.run_workbook is None):
        parser.error("both source workbooks are required together")
    if args.aggregate_workbook is not None and args.fixture is not None:
        parser.error("choose either a fixture or both workbooks")
    if args.output is not None and args.aggregate_workbook is None:
        parser.error("--output requires both original workbooks")
    try:
        if args.aggregate_workbook is None:
            counts = load_counts(args.fixture if args.fixture is not None else FIXTURE)
            input_mode = "pinned_offline_fixture"
        else:
            counts = extract_workbooks(args.aggregate_workbook, args.run_workbook)
            input_mode = "both_sha256_verified_publisher_workbooks"
        receipt = {**summarize(counts), "input_mode": input_mode, "fixture_written": args.output is not None}
        if args.output is not None:
            write_counts(args.output, counts)
        print(json.dumps(receipt, sort_keys=True, indent=2, allow_nan=False))
        return 0
    except (OSError, ValueError, KeyError, RecursionError, BadZipFile, ParseError) as error:
        print(f"replay_mazurek_primary: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
