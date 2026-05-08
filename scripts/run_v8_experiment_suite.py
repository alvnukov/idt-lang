from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.v8_runner import (  # noqa: E402
    DEFAULT_OUTPUT,
    DEFAULT_REPORT,
    ExperimentRunnerError,
    load_registry_from_lean,
    load_registry_from_path,
    run_experiment_suite,
    stats_json_text,
    validate_stats_payload,
    write_outputs,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Lean-sourced IDT v8 experiment telemetry fixtures.")
    parser.add_argument("--protocol-json", type=Path, default=None)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--experiment", action="append", default=[])
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument("--validate-only", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    repo_root = ROOT
    try:
        registry = (
            load_registry_from_path(args.protocol_json)
            if args.protocol_json is not None
            else load_registry_from_lean(repo_root)
        )
        payload = run_experiment_suite(
            registry=registry,
            repo_root=repo_root,
            experiment_filters=args.experiment,
        )
        validate_stats_payload(payload)
        if args.validate_only:
            experiments = payload.get("experiments")
            if not isinstance(experiments, list):
                raise ExperimentRunnerError("experiments must be an array")
            print(stats_json_text({"ok": True, "experiments": len(experiments)}, pretty=args.pretty), end="")
            return 0
        write_outputs(payload, args.output, args.report, args.pretty)
        return 0
    except ExperimentRunnerError as error:
        parser.exit(2, f"run_v8_experiment_suite: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
