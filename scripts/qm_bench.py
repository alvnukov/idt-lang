from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def main(argv: Sequence[str] | None = None) -> int:
    from theory_verifier.core import load_manifest, verify_manifest
    from theory_verifier.qm_bench import compile_qm_bench

    parser = argparse.ArgumentParser(description="Compile the QM universal-pattern bench.")
    parser.add_argument(
        "manifest",
        nargs="?",
        default="theory_verifier_manifest_v6_0.json",
        help="Path to a JSON verifier manifest.",
    )
    parser.add_argument("--json", action="store_true", help="Print machine-readable bench report.")
    args = parser.parse_args(argv)

    manifest = load_manifest(Path(args.manifest))
    verifier_report = verify_manifest(manifest)
    if not verifier_report.ok:
        if args.json:
            print(json.dumps({"ok": False, "issues": verifier_report.to_jsonable()["issues"]}, indent=2))
        else:
            print("ok: false")
            for issue in verifier_report.issues:
                print(f"- [{issue.code}] {issue.message}")
        return 1

    bench = compile_qm_bench(manifest)
    if args.json:
        print(json.dumps(bench.to_jsonable(), indent=2, sort_keys=True))
    else:
        print("ok: true")
        print(f"kernels: {len(bench.kernels)}")
        print(f"experiments: {bench.experiment_count}")
        print(f"finite gate refs: {bench.finite_gate_reference_count}")
        for kernel in bench.kernels:
            print(
                f"- {kernel.compiler_target}: "
                f"{len(kernel.experiment_ids)} experiments, {len(kernel.finite_gate_ids)} gate refs"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
