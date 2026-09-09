"""Fresh cross-version candidate-history regression; never refresh baselines automatically."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    History,
    recheck_history,
)
from theory_experiments.primitive_screen import canonical_json


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history-dir", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--record", action="store_true", help="append current observations, never update baselines")
    args = parser.parse_args(argv)
    try:
        result = recheck_history(History(args.history_dir), record=args.record)
        print(canonical_json(result))
        return 0 if result["status"] == "unchanged" else 4
    except (ValueError, TypeError, OSError, KeyError, RecursionError, EOFError) as error:
        print(f"check_candidate_history: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
