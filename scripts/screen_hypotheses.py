"""Batch finite primitive/QM/SM screens. Cache reuse never upgrades scientific status."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.candidate_pipeline import (
    Result,
    controls,
    digest,
    exit_code,
    replay_artifact,
    run_batch,
)
from theory_experiments.primitive_screen import Limits, canonical_json, load_json


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--builtin", nargs="+", choices=tuple(controls()))
    source.add_argument("--batch-file", type=Path, help="JSON array of candidate specifications")
    source.add_argument("--replay", type=Path, help="recompute one complete cache artifact")
    parser.add_argument("--show-candidates", action="store_true")
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--no-cache", action="store_true")
    parser.add_argument("--fresh", action="store_true", help="recompute; compare any existing entry")
    parser.add_argument("--max-cases", type=int)
    parser.add_argument("--reference-radius", type=int)
    parser.add_argument("--coefficient-radius", type=int)
    parser.add_argument("--max-copies", type=int)
    parser.add_argument("--json", action="store_true", help="full reports instead of compact cards")
    args = parser.parse_args(argv)
    try:
        results: tuple[Result, ...]
        bounds = (args.max_cases, args.coefficient_radius, args.reference_radius, args.max_copies)
        if args.no_cache and args.cache_dir is not None:
            raise ValueError("--no-cache conflicts with --cache-dir")
        if args.replay:
            if (any(x is not None for x in bounds) or args.fresh or args.no_cache
                    or args.cache_dir is not None or args.show_candidates):
                raise ValueError("replay uses recorded scope and bypasses cache execution")
            report = replay_artifact(args.replay)
            results = (Result(report, digest(report["request"]), False, args.replay.resolve()),)
        else:
            specifications: list[object]
            if args.batch_file:
                value = load_json(args.batch_file)
                if not isinstance(value, list):
                    raise ValueError("batch file must contain a JSON array")
                specifications = list(value)
            else:
                specifications = [controls()[name].specification() for name in args.builtin]
            if args.show_candidates:
                if any(x is not None for x in bounds) or args.fresh:
                    raise ValueError("show-candidates cannot execute a search")
                print(canonical_json(specifications))
                return 0
            defaults = Limits()
            limits = Limits(args.max_cases if args.max_cases is not None else defaults.max_cases,
                            args.coefficient_radius if args.coefficient_radius is not None else defaults.coefficient_radius,
                            args.reference_radius if args.reference_radius is not None else defaults.reference_radius,
                            args.max_copies if args.max_copies is not None else defaults.max_copies)
            cache = None if args.no_cache else (args.cache_dir or ROOT / "dist/primitive-screen-cache")
            results = run_batch(specifications, limits, cache, fresh=args.fresh)
        for result in results:
            print(canonical_json(result.report if args.json else result.card()))
        return exit_code(results)
    except (ValueError, TypeError, OSError, RecursionError) as error:
        print(f"screen_hypotheses: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
