from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

BridgeVerdict = Literal["FINITE_CARTESIAN_ENCODING_WITNESS", "BRIDGE_WITNESS_FAILED", "GATE_MISSING"]
CheckStatus = Literal["PASS", "FAIL"]

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "theory_verifier_manifest_v6_0.json"
TARGET_GATE_ID = "context_product_exhaustion_demo"


@dataclass(frozen=True)
class EncodingCheck:
    candidate_id: str
    status: CheckStatus
    reason: str
    left_contexts: int
    right_contexts: int
    declared_products: int
    expected_products: int


@dataclass(frozen=True)
class EncodingBridgeAttempt:
    verdict: BridgeVerdict
    gate_id: str
    passed: int
    failed: int
    checks: list[EncodingCheck]


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{field} must be a non-empty string")
    return value


def require_string_tuple(value: object, field: str) -> tuple[str, ...]:
    return tuple(require_string(item, f"{field}[]") for item in require_list(value, field))


def load_manifest(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, "manifest")


def find_gate(manifest: dict[str, object], gate_id: str) -> dict[str, object] | None:
    for index, raw_gate in enumerate(require_list(manifest.get("finite_gates", []), "finite_gates")):
        gate = require_mapping(raw_gate, f"finite_gates[{index}]")
        if gate.get("id") == gate_id:
            return gate
    return None


def product_pair_set(raw_products: list[object], field: str) -> set[tuple[str, str]]:
    pairs: set[tuple[str, str]] = set()
    for index, raw_product in enumerate(raw_products):
        product = require_mapping(raw_product, f"{field}[{index}]")
        left = require_string(product.get("left"), f"{field}[{index}].left")
        right = require_string(product.get("right"), f"{field}[{index}].right")
        pairs.add((left, right))
    return pairs


def evaluate_candidate(raw_candidate: object, index: int) -> EncodingCheck:
    candidate = require_mapping(raw_candidate, f"candidates[{index}]")
    candidate_id = require_string(candidate.get("id"), f"candidates[{index}].id")
    left_contexts = require_string_tuple(candidate.get("left_contexts", []), f"{candidate_id}.left_contexts")
    right_contexts = require_string_tuple(candidate.get("right_contexts", []), f"{candidate_id}.right_contexts")
    raw_products = require_list(candidate.get("product_contexts", []), f"{candidate_id}.product_contexts")
    expected_pairs = {(left, right) for left in left_contexts for right in right_contexts}
    declared_pairs = product_pair_set(raw_products, f"{candidate_id}.product_contexts")
    unknown_pairs = {
        (left, right)
        for left, right in declared_pairs
        if left not in set(left_contexts) or right not in set(right_contexts)
    }
    if unknown_pairs:
        return EncodingCheck(
            candidate_id=candidate_id,
            status="FAIL",
            reason="declared product references an unknown local context",
            left_contexts=len(left_contexts),
            right_contexts=len(right_contexts),
            declared_products=len(declared_pairs),
            expected_products=len(expected_pairs),
        )
    if declared_pairs != expected_pairs:
        return EncodingCheck(
            candidate_id=candidate_id,
            status="FAIL",
            reason="declared product contexts do not close the Cartesian table",
            left_contexts=len(left_contexts),
            right_contexts=len(right_contexts),
            declared_products=len(declared_pairs),
            expected_products=len(expected_pairs),
        )
    return EncodingCheck(
        candidate_id=candidate_id,
        status="PASS",
        reason="declared product contexts admit finite pair/list encoding over the Cartesian table",
        left_contexts=len(left_contexts),
        right_contexts=len(right_contexts),
        declared_products=len(declared_pairs),
        expected_products=len(expected_pairs),
    )


def build_attempt(manifest_path: Path = DEFAULT_MANIFEST) -> EncodingBridgeAttempt:
    manifest = load_manifest(manifest_path)
    gate = find_gate(manifest, TARGET_GATE_ID)
    if gate is None:
        return EncodingBridgeAttempt(
            verdict="GATE_MISSING",
            gate_id=TARGET_GATE_ID,
            passed=0,
            failed=0,
            checks=[],
        )
    candidates = require_list(gate.get("candidates", []), f"{TARGET_GATE_ID}.candidates")
    checks = [evaluate_candidate(candidate, index) for index, candidate in enumerate(candidates)]
    passed = sum(1 for check in checks if check.status == "PASS")
    failed = sum(1 for check in checks if check.status == "FAIL")
    verdict: BridgeVerdict = "FINITE_CARTESIAN_ENCODING_WITNESS" if failed == 0 and checks else "BRIDGE_WITNESS_FAILED"
    return EncodingBridgeAttempt(
        verdict=verdict,
        gate_id=TARGET_GATE_ID,
        passed=passed,
        failed=failed,
        checks=checks,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate finite context-product encoding witnesses.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    attempt = build_attempt(Path(str(args.manifest)))
    print(
        f"context_product_encoding_bridge={attempt.verdict} "
        f"gate={attempt.gate_id} passed={attempt.passed} failed={attempt.failed}"
    )
    for check in attempt.checks:
        print(
            f"{check.status} {check.candidate_id}: {check.reason} "
            f"left={check.left_contexts} right={check.right_contexts} "
            f"declared={check.declared_products} expected={check.expected_products}"
        )
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(attempt), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if attempt.verdict == "BRIDGE_WITNESS_FAILED":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
