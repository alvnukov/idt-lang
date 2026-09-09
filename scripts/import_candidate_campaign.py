"""Preserve an existing finite-search campaign without rerunning or rewriting its evidence."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_history import DEFAULT_HISTORY, History
from theory_experiments.candidate_pipeline import CACHE_SCHEMA, digest
from theory_experiments.primitive_screen import (
    canonical_json,
    load_json,
    object_fields,
    parse_limits,
)


def import_campaign(source: Path, history: History, *, baseline: bool = False) -> dict[str, object]:
    protocol = object_fields(load_json(source / "protocol.json"))
    if protocol.get("schema") != "idt-finite-search-campaign/1":
        raise ValueError("unsupported campaign protocol")
    limits = parse_limits(protocol["limits"])
    reports: dict[str, dict[str, object]] = {}
    for path in sorted((source / "evidence").glob("*.json")):
        envelope = object_fields(load_json(path))
        report = object_fields(envelope["report"])
        request = object_fields(report["request"])
        name = object_fields(request["candidate"])["id"]
        if (envelope["schema"] != CACHE_SCHEMA or envelope["key"] != digest(request)
                or envelope["report_sha256"] != digest(report)
                or not isinstance(name, str) or name in reports):
            raise ValueError("invalid or duplicate original campaign evidence")
        reports[name] = report
    batches: list[list[object]] = []
    names: list[str] = []
    for path in sorted(source.glob("candidates-*.json")):
        raw = load_json(path)
        if not isinstance(raw, list) or not 1 <= len(raw) <= 64:
            raise ValueError("invalid original candidate batch")
        specs: list[object] = list(raw)
        for spec in specs:
            name = object_fields(spec)["id"]
            if not isinstance(name, str) or name in names or name not in reports:
                raise ValueError("missing or duplicated original candidate")
            request = object_fields(reports[name]["request"])
            if (canonical_json(request["candidate"]) != canonical_json(spec)
                    or canonical_json(request["limits"]) != canonical_json(limits.specification())):
                raise ValueError("original campaign input/bounds mismatch")
            names.append(name)
        batches.append(specs)
    if not batches or set(names) != set(reports):
        raise ValueError("campaign import would lose candidates or evidence")
    offset = 0
    records: list[dict[str, str]] = []
    for specs in batches:
        submission = history.submit(specs, limits)
        selected: list[object] = [reports[name] for name in names[offset:offset + len(specs)]]
        observation = history.observe(submission, selected)
        if baseline:
            history.pin_initial(submission, observation)
        records.append({"submission": submission, "observation": observation})
        offset += len(specs)
    return {"candidates": len(names), "checker_commit": protocol.get("checker_commit"),
            "records": records, "baseline_initialization_requested": baseline,
            "meaning": "preserved_computations_not_new_physical_evidence"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--history-dir", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--initial-baseline", action="store_true",
                        help="initialize absent comparison pins; never overwrite an existing pin")
    args = parser.parse_args(argv)
    try:
        print(canonical_json(import_campaign(args.source, History(args.history_dir),
                                             baseline=args.initial_baseline)))
        return 0
    except (ValueError, TypeError, OSError, KeyError, RecursionError) as error:
        print(f"import_candidate_campaign: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
