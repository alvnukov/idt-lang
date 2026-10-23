"""Replay pinned Hensen2015 event candidates; opt-in pinned download, no fitting."""

from __future__ import annotations

import argparse
import hashlib
import io
import os
import stat
import sys
import urllib.request
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.bell_trial_test import (
    RAW_SHA256,
    RAW_SIZE,
    assert_loaded_sources,
    read_pinned_raw,
    replay,
)
from theory_experiments.primitive_screen import canonical_json, object_fields

ARCHIVE_SIZE = 152913
ARCHIVE_SHA256 = "c28eb0f075759aef620a0b2e00a70fd675ce712bc8214d11c103f5a3d29492c0"
MIRROR_URL = ("https://raw.githubusercontent.com/DenBraun/onto2d/"
              "c737171a38313566feb15c346837229ee1914bb4/references/canonical/data/hensen2015-data.zip")


def fetch_release(destination: Path) -> None:
    """Opt-in fixed mirror, bounded pinned archive/member; never execute author code."""
    assert_loaded_sources()
    if destination.exists() or destination.is_symlink():
        read_pinned_raw(destination)
        return
    with urllib.request.urlopen(MIRROR_URL, timeout=30) as response:
        packed = response.read(ARCHIVE_SIZE+1)
    if len(packed) != ARCHIVE_SIZE or hashlib.sha256(packed).hexdigest() != ARCHIVE_SHA256:
        raise ValueError("downloaded archive size/digest mismatch")
    with zipfile.ZipFile(io.BytesIO(packed)) as archive:
        if archive.namelist().count("bell_open_data.txt") != 1:
            raise ValueError("archive member missing or duplicated")
        if archive.getinfo("bell_open_data.txt").file_size != RAW_SIZE:
            raise ValueError("archive member size mismatch")
        with archive.open("bell_open_data.txt") as member:
            raw = member.read(RAW_SIZE+1)
    if len(raw) != RAW_SIZE or hashlib.sha256(raw).hexdigest() != RAW_SHA256:
        raise ValueError("archive member digest/size mismatch")
    assert_loaded_sources()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("xb") as output:
        output.write(raw)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-file", type=Path, required=True)
    parser.add_argument("--fetch", action="store_true", help="opt-in fixed checksum-pinned mirror download")
    parser.add_argument("--output", type=Path, default=ROOT / "dist/hensen2015-trial-replay-v1.json")
    args = parser.parse_args(argv)
    try:
        if args.fetch:
            fetch_release(args.raw_file)
        report = replay(args.raw_file)
        rendered = canonical_json(report) + "\n"
        args.output.parent.mkdir(parents=True, exist_ok=True)
        try:
            with args.output.open("x", encoding="utf-8") as stream:
                stream.write(rendered)
        except FileExistsError:
            expected = rendered.encode("utf-8")
            descriptor = os.open(args.output, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(descriptor, "rb") as existing:
                regular = stat.S_ISREG(os.fstat(existing.fileno()).st_mode)
                identical = regular and existing.read(len(expected)+1) == expected
            if not identical:
                raise ValueError("output exists with different contents; choose a new output path") from None
        assessment = object_fields(report["assessment"])
        print(canonical_json({"execution_status": "complete", "report": str(args.output),
              "N": assessment["N"], "K": assessment["K"],
              "tail_decimal_display": object_fields(assessment["tail"])["decimal_display"],
              "status": assessment["status"], "unconditional_verdict": "not_established"}))
        return 0
    except (OSError, ValueError, TypeError, KeyError, UnicodeError, zipfile.BadZipFile) as error:
        print(f"replay_hensen2015: input/data/operational error (not physics rejection): {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
