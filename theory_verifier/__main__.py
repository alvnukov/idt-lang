from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from theory_verifier.core import load_manifest, verify_manifest


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify IDT theory logic manifest.")
    parser.add_argument(
        "manifest",
        nargs="?",
        default="theory_verifier_manifest_v6_0.json",
        help="Path to a JSON verifier manifest.",
    )
    parser.add_argument("--json", action="store_true", help="Print machine-readable report.")
    args = parser.parse_args(argv)

    manifest = load_manifest(Path(args.manifest))
    report = verify_manifest(manifest)

    if args.json:
        print(json.dumps(report.to_jsonable(), indent=2, sort_keys=True))
    else:
        print(f"ok: {report.ok}")
        print(f"checks: {len(report.checks)}")
        if report.issues:
            print("issues:")
            for issue in report.issues:
                print(f"- [{issue.code}] {issue.message}")

    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
