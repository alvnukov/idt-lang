"""Replay both pinned Gstir2021 detector-voltage runs; no candidate assessment."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.raw_signal_replay import canonical_json, replay


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-directory", type=Path, required=True,
                        help="directory containing the two fixed registry filenames; never downloaded")
    parser.add_argument("--output", type=Path, default=ROOT / "dist/gstir2021-raw-replay.json",
                        help="full deterministic JSON; refuses to overwrite different existing contents")
    args = parser.parse_args(argv)
    try:
        report = replay(args.raw_directory)
        rendered = canonical_json(report) + "\n"
        args.output.parent.mkdir(parents=True, exist_ok=True)
        try:
            with args.output.open("x", encoding="utf-8") as stream:
                stream.write(rendered)
        except FileExistsError:
            if args.output.is_symlink() or args.output.read_text() != rendered:
                raise ValueError("output exists with different contents; select a new output path") from None
        runs = cast(list[dict[str, object]], report["runs"])
        print(canonical_json({"execution_status": "complete", "candidate_verdict": "not_assessed",
                              "report": str(args.output), "primary_all_cycles": [
                                  run["primary_all_cycles"] for run in runs]}))
        return 0
    except (OSError, ValueError, TypeError, KeyError, ImportError) as error:
        print(f"replay_gstir2021: input/data/operational error (not primitive counterexample): {error}",
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
