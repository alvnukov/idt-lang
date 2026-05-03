from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import sys
import tempfile
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO

import fcntl


DEFAULT_MANIFEST = Path("theory_verifier_manifest_v6_0.json")

SAFE_EDIT_FIELDS: dict[str, frozenset[str]] = {
    "symbols": frozenset({"status"}),
    "derivations": frozenset({"status"}),
    "qm_core_proof_obligations": frozenset({"status", "open_gap", "claim_boundary"}),
    "theorem_cards": frozenset({"proof_status", "physical_scope"}),
}

STATUS_VALUES = frozenset(
    {
        "primitive",
        "definition",
        "derived",
        "derived_conditional",
        "bridge_assumption",
        "experimental_gate",
        "open",
        "blocked",
        "gate",
        "target",
        "formula",
    }
)

PROOF_STATUS_VALUES = frozenset(
    {
        "formal_proof",
        "finite_verifier_pass",
        "numerical_evidence",
        "calibrated_match",
        "open",
        "blocked",
    }
)


@dataclass(frozen=True)
class GraphObject:
    collection: str
    identifier: str
    value: object


class GraphQueryError(ValueError):
    pass


def load_json(path: Path) -> dict[str, object]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise GraphQueryError("manifest root must be an object")
    return raw


def manifest_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def graph_summary(path: Path) -> dict[str, object]:
    manifest = load_json(path)
    return {
        "path": str(path),
        "sha256": manifest_sha256(path),
        "counts": {
            "symbols": len(require_mapping(manifest.get("symbols"), "symbols")),
            "equations": len(require_list(manifest.get("equations"), "equations")),
            "derivations": len(require_list(manifest.get("derivations"), "derivations")),
            "forbidden_paths": len(require_list(manifest.get("forbidden_paths"), "forbidden_paths")),
            "qm_experiments": len(require_list(manifest.get("qm_experiments"), "qm_experiments")),
            "qm_universal_patterns": len(require_list(manifest.get("qm_universal_patterns"), "qm_universal_patterns")),
            "qm_core_proof_obligations": len(
                require_list(manifest.get("qm_core_proof_obligations"), "qm_core_proof_obligations")
            ),
            "theorem_cards": len(require_list(manifest.get("theorem_cards"), "theorem_cards")),
            "finite_gates": len(require_list(manifest.get("finite_gates"), "finite_gates")),
        },
    }


def find_object(path: Path, identifier: str, collection: str | None = None) -> list[GraphObject]:
    manifest = load_json(path)
    return [
        graph_object
        for graph_object in iter_graph_objects(manifest)
        if graph_object.identifier == identifier and (collection is None or graph_object.collection == collection)
    ]


def incoming_refs(path: Path, identifier: str) -> list[dict[str, str]]:
    manifest = load_json(path)
    refs: list[dict[str, str]] = []
    for graph_object in iter_graph_objects(manifest):
        if graph_object.identifier == identifier:
            continue
        for field_path in object_string_refs(graph_object.value, identifier):
            refs.append(
                {
                    "collection": graph_object.collection,
                    "id": graph_object.identifier,
                    "path": field_path,
                }
            )
    return refs


def edit_field(path: Path, collection: str, identifier: str, field: str, value: str, expect_sha: str) -> str:
    if field not in SAFE_EDIT_FIELDS.get(collection, frozenset()):
        raise GraphQueryError(f"{collection}.{field} is not an allowed edit field")
    validate_edit_value(field, value)
    with manifest_lock(path):
        before_sha = manifest_sha256(path)
        if before_sha != expect_sha:
            raise GraphQueryError(f"manifest sha mismatch: expected {expect_sha}, got {before_sha}")
        manifest = load_json(path)
        graph_objects = [
            item
            for item in iter_graph_objects(manifest)
            if item.collection == collection and item.identifier == identifier
        ]
        if len(graph_objects) != 1:
            raise GraphQueryError(f"expected exactly one {collection} object with id {identifier!r}")
        item = require_mapping(graph_objects[0].value, f"{collection}.{identifier}")
        old_value = item.get(field)
        if not isinstance(old_value, str):
            raise GraphQueryError(f"{collection}.{identifier}.{field} must be an existing string field")
        text = path.read_text(encoding="utf-8")
        start, end = find_object_line_range(text.splitlines(), collection, identifier)
        updated = replace_string_field(text, start, end, field, old_value, value)
        atomic_write_text(path, updated)
        return manifest_sha256(path)


def iter_graph_objects(manifest: dict[str, object]) -> Iterator[GraphObject]:
    symbols = require_mapping(manifest.get("symbols"), "symbols")
    for symbol_id, value in symbols.items():
        yield GraphObject("symbols", symbol_id, value)
    for collection in (
        "equations",
        "derivations",
        "forbidden_paths",
        "qm_experiments",
        "qm_universal_patterns",
        "qm_core_proof_obligations",
        "theorem_cards",
        "finite_gates",
    ):
        for index, item in enumerate(require_list(manifest.get(collection), collection)):
            item_map = require_mapping(item, f"{collection}[{index}]")
            item_id = item_map.get("id")
            target = item_map.get("target")
            if isinstance(item_id, str):
                yield GraphObject(collection, item_id, item_map)
            elif collection == "forbidden_paths" and isinstance(target, str):
                yield GraphObject(collection, target, item_map)


def object_string_refs(raw: object, needle: str, prefix: str = "") -> Iterator[str]:
    if isinstance(raw, str):
        if raw == needle:
            yield prefix or "."
        return
    if isinstance(raw, list):
        for index, item in enumerate(raw):
            yield from object_string_refs(item, needle, f"{prefix}[{index}]")
        return
    if isinstance(raw, dict):
        for key, item in raw.items():
            if not isinstance(key, str):
                continue
            child_prefix = f"{prefix}.{key}" if prefix else key
            yield from object_string_refs(item, needle, child_prefix)


def validate_edit_value(field: str, value: str) -> None:
    if field == "status" and value not in STATUS_VALUES:
        raise GraphQueryError(f"unknown status value {value!r}")
    if field == "proof_status" and value not in PROOF_STATUS_VALUES:
        raise GraphQueryError(f"unknown proof_status value {value!r}")
    if not value.strip():
        raise GraphQueryError(f"{field} must not be empty")


def find_object_line_range(lines: Sequence[str], collection: str, identifier: str) -> tuple[int, int]:
    collection_start = find_collection_start(lines, collection)
    if collection == "symbols":
        return find_named_object_range(lines, collection_start + 1, identifier)
    return find_list_object_range(lines, collection_start + 1, identifier)


def find_collection_start(lines: Sequence[str], collection: str) -> int:
    pattern = re.compile(rf'^\s*"{re.escape(collection)}"\s*:\s*[\[{{]')
    for index, line in enumerate(lines):
        if pattern.match(line):
            return index
    raise GraphQueryError(f"collection {collection!r} not found")


def find_named_object_range(lines: Sequence[str], start_index: int, identifier: str) -> tuple[int, int]:
    pattern = re.compile(rf'^\s*"{re.escape(identifier)}"\s*:\s*{{')
    for index in range(start_index, len(lines)):
        if pattern.match(lines[index]):
            return index, find_matching_brace_line(lines, index)
    raise GraphQueryError(f"object {identifier!r} not found")


def find_list_object_range(lines: Sequence[str], start_index: int, identifier: str) -> tuple[int, int]:
    for index in range(start_index, len(lines)):
        if not re.match(r"^\s*{", lines[index]):
            continue
        end_index = find_matching_brace_line(lines, index)
        block = "\n".join(lines[index : end_index + 1])
        if re.search(rf'"id"\s*:\s*{re.escape(json.dumps(identifier))}', block):
            return index, end_index
    raise GraphQueryError(f"object {identifier!r} not found")


def find_matching_brace_line(lines: Sequence[str], start_index: int) -> int:
    depth = 0
    in_string = False
    escape = False
    started = False
    for index in range(start_index, len(lines)):
        for char in lines[index]:
            if escape:
                escape = False
                continue
            if char == "\\" and in_string:
                escape = True
                continue
            if char == '"':
                in_string = not in_string
                continue
            if in_string:
                continue
            if char == "{":
                depth += 1
                started = True
            elif char == "}":
                depth -= 1
                if started and depth == 0:
                    return index
    raise GraphQueryError("unterminated JSON object")


def replace_string_field(text: str, start: int, end: int, field: str, old_value: str, new_value: str) -> str:
    lines = text.splitlines(keepends=True)
    field_pattern = re.compile(rf'^(\s*"{re.escape(field)}"\s*:\s*)({re.escape(json.dumps(old_value))})(,?\s*)$')
    matches: list[int] = []
    for index in range(start, end + 1):
        if field_pattern.match(lines[index].rstrip("\n")):
            matches.append(index)
    if len(matches) != 1:
        raise GraphQueryError(f"expected exactly one editable {field!r} line in object")
    line_index = matches[0]
    line = lines[line_index]
    newline = "\n" if line.endswith("\n") else ""
    stripped = line.rstrip("\n")
    match = field_pattern.match(stripped)
    if match is None:
        raise GraphQueryError(f"could not replace {field!r}")
    lines[line_index] = f"{match.group(1)}{json.dumps(new_value)}{match.group(3)}{newline}"
    return "".join(lines)


@contextlib.contextmanager
def manifest_lock(path: Path) -> Iterator[None]:
    lock_name = "idt-lang-" + hashlib.sha256(str(path.resolve()).encode("utf-8")).hexdigest()[:16] + ".lock"
    lock_path = Path(tempfile.gettempdir()) / lock_name
    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def atomic_write_text(path: Path, text: str) -> None:
    directory = path.parent
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=directory, delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(text)
        temp_file.flush()
        os.fsync(temp_file.fileno())
    os.replace(temp_path, path)


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise GraphQueryError(f"{field} must be an object")
    output: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise GraphQueryError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise GraphQueryError(f"{field} must be a list")
    return list(value)


def print_json(value: object, output: TextIO) -> None:
    output.write(json.dumps(value, indent=2, sort_keys=True))
    output.write("\n")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Query and cautiously edit the IDT research graph manifest.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("summary", help="Print manifest counts and sha256.")

    show_parser = subparsers.add_parser("show", help="Show graph objects with the given id.")
    show_parser.add_argument("identifier")
    show_parser.add_argument("--collection")

    refs_parser = subparsers.add_parser("refs", help="Show incoming references to a graph id.")
    refs_parser.add_argument("identifier")

    edit_parser = subparsers.add_parser("set-field", help="Safely edit one allowed string field.")
    edit_parser.add_argument("--collection", required=True)
    edit_parser.add_argument("--id", required=True)
    edit_parser.add_argument("--field", required=True)
    edit_parser.add_argument("--value", required=True)
    edit_parser.add_argument("--expect-sha", required=True)
    return parser


def main(argv: Sequence[str] | None = None, output: TextIO | None = None) -> int:
    stream = output if output is not None else sys.stdout
    parser = build_parser()
    args = parser.parse_args(argv)
    manifest_path = Path(args.manifest)
    try:
        if args.command == "summary":
            print_json(graph_summary(manifest_path), stream)
        elif args.command == "show":
            results = [
                {"collection": item.collection, "id": item.identifier, "value": item.value}
                for item in find_object(manifest_path, args.identifier, args.collection)
            ]
            print_json(results, stream)
        elif args.command == "refs":
            print_json(incoming_refs(manifest_path, args.identifier), stream)
        elif args.command == "set-field":
            new_sha = edit_field(
                manifest_path,
                args.collection,
                args.id,
                args.field,
                args.value,
                args.expect_sha,
            )
            print_json({"ok": True, "sha256": new_sha}, stream)
        else:
            parser.error(f"unknown command {args.command!r}")
    except GraphQueryError as error:
        parser.exit(2, f"graph_query: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
