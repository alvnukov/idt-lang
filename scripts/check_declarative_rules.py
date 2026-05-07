from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def main(argv: Sequence[str] | None = None) -> int:
    from theory_verifier.declarative import (
        load_json_file,
        load_rule_documents,
        verify_declarative_rule_documents,
    )

    parser = argparse.ArgumentParser(description="Verify IDT v8 declarative rules.")
    parser.add_argument(
        "--manifest",
        default="theory_verifier_manifest.json",
        help="Path to the IDT verifier manifest.",
    )
    parser.add_argument(
        "--rules",
        default="rules/v8",
        help="Path to one .idtl.json file or a directory of v8 rule files.",
    )
    parser.add_argument("--json", action="store_true", help="Print machine-readable report.")
    args = parser.parse_args(argv)

    manifest_path = ROOT / args.manifest
    rules_path = ROOT / args.rules
    manifest = load_json_file(manifest_path)
    rules = load_rule_documents(rules_path)
    report = verify_declarative_rule_documents(manifest, rules, ROOT)

    if args.json:
        print(json.dumps(report.to_jsonable(), indent=2, sort_keys=True))
    else:
        print(f"ok: {report.ok}")
        print(f"specification_documents: {len(report.specification_documents)}")
        print(f"verification_rules_checked: {report.verification_rules_checked}")
        if report.issues:
            print("issues:")
            for item in report.issues:
                print(f"- [{item.code}] {item.message}")
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
