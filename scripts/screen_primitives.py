"""Run a bounded primitive-candidate screen without launching Lean."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.primitive_screen import (
    Limits,
    builtin_candidates,
    load_json,
    parse_candidate,
    replay,
    screen,
    summary,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--builtin", choices=tuple(builtin_candidates()))
    source.add_argument("--candidate-file", type=Path)
    source.add_argument("--replay", type=Path)
    parser.add_argument("--max-cases", type=int, default=None)
    parser.add_argument("--coefficient-radius", type=int, default=None)
    parser.add_argument("--reference-radius", type=int, default=None)
    parser.add_argument("--max-copies", type=int, default=None)
    parser.add_argument("--json", action="store_true", help="print the complete deterministic report")
    parser.add_argument("--output", type=Path, help="save report; refuses to overwrite an existing file")
    parser.add_argument("--show-candidate", action="store_true", help="print an editable candidate specification")
    args = parser.parse_args(argv)
    try:
        bounds = (args.max_cases, args.coefficient_radius, args.reference_radius, args.max_copies)
        if args.replay is not None:
            if any(x is not None for x in bounds) or args.show_candidate:
                raise ValueError("replay uses recorded bounds and cannot show a candidate only")
            report = replay(load_json(args.replay))
        else:
            candidate = (parse_candidate(load_json(args.candidate_file))
                         if args.candidate_file is not None
                         else builtin_candidates()[args.builtin or "square"])
            if args.show_candidate:
                if args.output is not None or any(x is not None for x in bounds):
                    raise ValueError("show-candidate does not accept output or search bounds")
                print(json.dumps(candidate.specification(), indent=2, sort_keys=True))
                return 0
            defaults = Limits()
            limits = Limits(
                args.max_cases if args.max_cases is not None else defaults.max_cases,
                args.coefficient_radius if args.coefficient_radius is not None else defaults.coefficient_radius,
                args.reference_radius if args.reference_radius is not None else defaults.reference_radius,
                args.max_copies if args.max_copies is not None else defaults.max_copies,
            )
            report = screen(candidate, limits)
        encoded = json.dumps(report, indent=2, sort_keys=True, allow_nan=False) + "\n"
        if args.output is not None:
            with args.output.open("x", encoding="utf-8") as output:
                output.write(encoded)
        print(encoded if args.json else summary(report), end="" if args.json else "\n")
        return 1 if report["status"] == "counterexample" else 0 if report["status"] == "no_counterexample_within_bounds" else 3
    except (TypeError, ValueError, OSError, RecursionError) as error:
        print(f"screen_primitives: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
