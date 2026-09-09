"""Retain reviewed repository proposals without inventing a physical prediction adapter."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_history import DEFAULT_HISTORY, History, record_batch
from theory_experiments.primitive_screen import (
    bounded_int,
    canonical_json,
    load_json,
    object_fields,
)
from theory_experiments.source_candidate import (
    SourceSnapshot,
    parse_source_candidate,
    source_digest,
    source_path,
)

INVENTORY = ROOT / "data/existing_primitive_inventory.json"


def snapshot_source(value: object, root: Path) -> dict[str, object]:
    row = object_fields(value, {"path", "first_line", "last_line", "file_sha256"})
    relative = source_path(row["path"])
    path = root / relative
    if path.is_symlink() or not path.resolve(strict=True).is_relative_to(root.resolve()):
        raise ValueError("snapshot source must remain inside the repository")
    if not path.is_file() or path.stat().st_size > 2 * 1024 * 1024:
        raise ValueError("snapshot source is not a bounded regular file")
    raw = path.read_bytes()
    expected = source_digest(row["file_sha256"])
    if hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError(f"source changed: review inventory spans before recapturing {relative}")
    lines = raw.decode("utf-8").splitlines(keepends=True)
    first = bounded_int(row["first_line"], 1, len(lines))
    last = bounded_int(row["last_line"], first, min(len(lines), first + 1000))
    snapshot = SourceSnapshot(relative, first, last, expected, "".join(lines[first - 1:last]))
    return snapshot.specification()


def inventory_specifications(inventory: Path = INVENTORY, root: Path = ROOT) -> list[object]:
    manifest = object_fields(load_json(inventory), {"schema", "candidates"})
    entries = manifest["candidates"]
    if manifest["schema"] != "idt-existing-primitive-inventory/1" or not isinstance(entries, list) or not entries:
        raise ValueError("invalid existing-primitive inventory")
    specifications: list[object] = []
    identifiers: set[str] = set()
    for entry in entries:
        row = object_fields(entry, {"id", "role", "components", "declared_status", "missing_bridges", "sources"})
        sources = row["sources"]
        if not isinstance(sources, list):
            raise TypeError("inventory sources must be an array")
        candidate = parse_source_candidate({**row, "family": "source_theory",
            "sources": [snapshot_source(source, root) for source in sources]})
        if candidate.id in identifiers:
            raise ValueError("duplicate existing-primitive candidate id")
        identifiers.add(candidate.id)
        spec = candidate.specification()
        if len(canonical_json([spec]).encode("utf-8")) > 131072:
            raise ValueError("source candidate exceeds the history submission limit")
        specifications.append(spec)
    return specifications


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history-dir", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--inventory", type=Path, default=INVENTORY)
    args = parser.parse_args(argv)
    try:
        # Read/validate the complete inventory before publishing any of its records.
        specs = inventory_specifications(args.inventory)
        records: list[dict[str, object]] = []
        changed = False
        for spec in specs:
            run = record_batch([spec], history=History(args.history_dir), fresh=True)
            changed = changed or bool(run.changes)
            records.append({"id": object_fields(spec)["id"], "submission": run.submission,
                "observation": run.observation, "status": run.results[0].report["status"]})
        print(canonical_json({"archived": len(records), "records": records,
                              "meaning": "retained_with_missing_prediction_adapters_not_physically_tested"}))
        return 4 if changed else 0
    except (ValueError, TypeError, OSError, KeyError, RecursionError) as error:
        print(f"archive_existing_primitives: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
