from __future__ import annotations

import json
import shlex
import subprocess
import sys
from pathlib import Path
from typing import TypedDict


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "theory_verifier_manifest_v6_0.json"


class ProofCommandResult(TypedDict):
    command: str
    returncode: int


def load_manifest() -> dict[str, object]:
    raw: object = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("manifest root must be an object")
    return raw


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{field} must be a non-empty string")
    return value


def require_string_list(value: object, field: str) -> list[str]:
    items = require_list(value, field)
    output: list[str] = []
    for index, item in enumerate(items):
        output.append(require_string(item, f"{field}[{index}]"))
    return output


def iter_checker_commands(manifest: dict[str, object]) -> list[str]:
    commands: list[str] = []
    finite_gates = require_list(manifest.get("finite_gates", []), "finite_gates")
    for gate_index, raw_gate in enumerate(finite_gates):
        gate = require_mapping(raw_gate, f"finite_gates[{gate_index}]")
        if gate.get("type") != "formal_proof_ledger_audit":
            continue
        proof_cards = require_list(gate.get("proof_cards", []), f"finite_gates[{gate_index}].proof_cards")
        for card_index, raw_card in enumerate(proof_cards):
            card = require_mapping(raw_card, f"finite_gates[{gate_index}].proof_cards[{card_index}]")
            commands.extend(
                require_string_list(
                    card.get("checker_commands", []),
                    f"finite_gates[{gate_index}].proof_cards[{card_index}].checker_commands",
                )
            )
    return commands


def run_command(command: str) -> ProofCommandResult:
    completed = subprocess.run(
        shlex.split(command),
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if completed.stdout:
        sys.stdout.write(completed.stdout)
    return {"command": command, "returncode": completed.returncode}


def main() -> int:
    manifest = load_manifest()
    commands = iter_checker_commands(manifest)
    if not commands:
        print(json.dumps({"ok": True, "commands": []}, indent=2))
        return 0

    results: list[ProofCommandResult] = []
    for command in commands:
        result = run_command(command)
        results.append(result)
        if result["returncode"] != 0:
            print(json.dumps({"ok": False, "failed": result, "commands": results}, indent=2))
            return result["returncode"]
    print(json.dumps({"ok": True, "commands": results}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
