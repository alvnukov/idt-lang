from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import re
import sys
from collections import deque
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_verifier.ai_theory_graph import (  # noqa: E402
    SCHEMA,
    GraphEdge as Edge,
    GraphNode as Node,
    JsonObject,
    graph_json_text,
    validate_graph_payload,
)

DEFAULT_MANIFEST = Path("theory_verifier_manifest.json")
DEFAULT_RULE_DIR = Path("rules/v8")
DEFAULT_OUTPUT = Path("dist/idt-v8-ai-theory-graph.json")
DEFAULT_SOURCE_GLOBS = (
    "README.md",
    "PUBLIC_CLAIM_SHEET.md",
    "PROTOLANGUAGE.md",
    "sections/*.md",
    "Proofs/**/*.lean",
    "Experiments/**/*.lean",
    "rules/v8/*.idtl.json",
)

MANIFEST_COLLECTIONS = (
    "symbols",
    "equations",
    "derivations",
    "forbidden_paths",
    "finite_gates",
    "qm_experiments",
    "qm_universal_patterns",
    "qm_core_proof_obligations",
    "theorem_cards",
)

TEXT_FIELDS = frozenset(
    {
        "assumptions[]",
        "claim_boundary",
        "definition",
        "domain",
        "forbidden_claims[]",
        "known_failures[]",
        "mechanism",
        "open_gap",
        "physical_scope",
        "stable_invariant",
        "standard_result",
        "statement",
        "status",
        "term",
        "title",
        "type",
    }
)

RELATION_FIELDS: dict[str, str] = {
    "dependencies[]": "depends_on",
    "depends_on[]": "depends_on",
    "evidence_refs[]": "evidence",
    "experiments[]": "covers_experiment",
    "finite_gates[]": "uses_gate",
    "lhs": "defines",
    "proposed_gates[]": "proposes_gate",
    "route_gates[]": "uses_gate",
    "target": "targets",
    "verifier": "verified_by",
}

DECLARATION_RE = re.compile(
    r"^(?:private\s+|partial\s+|noncomputable\s+)?"
    r"(theorem|def|structure|inductive|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)"
)
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.'/-]+)$")


class V8GraphError(ValueError):
    pass


@dataclass(frozen=True)
class SourceFile:
    path: Path
    relative_path: str
    node_id: str
    module_id: str
    digest: str
    title: str
    byte_count: int


@dataclass(frozen=True)
class ManifestObject:
    collection: str
    identifier: str
    payload: JsonObject


def build_v8_ai_theory_graph(
    repo_root: Path = Path("."),
    manifest_path: Path = DEFAULT_MANIFEST,
    rule_dir: Path = DEFAULT_RULE_DIR,
    source_globs: Sequence[str] = DEFAULT_SOURCE_GLOBS,
    include_manifest_residuals: bool = True,
    include_sources: bool = True,
    max_label_chars: int = 140,
    focus: str | None = None,
    depth: int = 1,
) -> dict[str, object]:
    root = repo_root.resolve()
    manifest = load_json_object(resolve_path(root, manifest_path))
    nodes: list[Node] = []
    edges: list[Edge] = []
    aliases: dict[str, set[str]] = {}

    add_collection_nodes(nodes)
    if include_manifest_residuals:
        manifest_nodes, manifest_edges, manifest_aliases = build_manifest_residual_layer(
            manifest,
            resolve_path(root, manifest_path),
            max_label_chars,
        )
        nodes.extend(manifest_nodes)
        edges.extend(manifest_edges)
        merge_aliases(aliases, manifest_aliases)

    rule_nodes, rule_edges, rule_aliases = build_idtl_rule_layer(root, resolve_path(root, rule_dir), max_label_chars)
    nodes.extend(rule_nodes)
    edges.extend(rule_edges)
    merge_aliases(aliases, rule_aliases)

    if include_sources:
        source_nodes, source_edges, source_aliases = build_source_layer(root, source_globs, max_label_chars)
        nodes.extend(source_nodes)
        edges.extend(source_edges)
        merge_aliases(aliases, source_aliases)

    nodes = sorted(unique_nodes(nodes), key=lambda node: node.identifier)
    edges = sorted(unique_edges(edges), key=lambda edge: (edge.source, edge.relation, edge.target, edge.evidence))
    if focus is not None:
        focus_ids = resolve_focus(focus, aliases, {node.identifier for node in nodes})
        nodes, edges = focus_subgraph(nodes, edges, focus_ids, depth)

    graph: JsonObject = {
        "schema": SCHEMA,
        "contract": {
            "purpose": "compressed_source_grounded_context_for_ai_agents",
            "proof_authority": "lean_only",
            "manifest_role": "residual_input_not_proof_truth",
            "claim_upgrade_policy": "no_artifact_no_upgrade",
            "full_text_policy": "use source paths and sha16 digests to fetch exact repository files",
        },
        "legend": {
            "node": ["id", "kind", "status", "label", "source", "sha16"],
            "edge": ["source", "relation", "target", "evidence"],
            "kinds": [
                "collection",
                "idtl.doc",
                "idtl.rule",
                "idtl.term",
                "lean.decl",
                "manifest.residual",
                "source.file",
            ],
        },
        "meta": {
            "theory_version": string_field(manifest, "theory_version"),
            "schema_version": string_field(manifest, "schema_version"),
            "repo_root": str(root),
            "manifest": relative_or_absolute(root, resolve_path(root, manifest_path)),
            "manifest_sha256": file_sha256(resolve_path(root, manifest_path)),
            "rule_dir": relative_or_absolute(root, resolve_path(root, rule_dir)),
            "source_mode": "included" if include_sources else "disabled",
            "manifest_residuals": include_manifest_residuals,
            "max_label_chars": max_label_chars,
            "focus": focus or "",
            "depth": depth if focus else 0,
        },
        "coverage": {
            "manifest_counts": manifest_counts(manifest),
            "nodes": len(nodes),
            "edges": len(edges),
            "duplicate_aliases": duplicate_aliases(aliases),
        },
        "nodes": [node.row() for node in nodes],
        "edges": [edge.row() for edge in edges],
    }
    validate_graph_payload(graph)
    return graph


def add_collection_nodes(nodes: list[Node]) -> None:
    for collection in MANIFEST_COLLECTIONS:
        nodes.append(
            Node(
                identifier=collection_node_id(collection),
                kind="collection",
                status="",
                label=collection,
                source="v8_manifest_collection_contract",
                digest=short_digest(collection),
            )
        )


def build_manifest_residual_layer(
    manifest: Mapping[str, object],
    manifest_path: Path,
    max_label_chars: int,
) -> tuple[list[Node], list[Edge], dict[str, set[str]]]:
    objects = list(iter_manifest_objects(manifest))
    raw_index = manifest_alias_index(objects)
    nodes: list[Node] = []
    edges: list[Edge] = []
    aliases: dict[str, set[str]] = {}
    for item in objects:
        node_id = residual_node_id(item.collection, item.identifier)
        aliases.setdefault(item.identifier, set()).add(node_id)
        nodes.append(
            Node(
                identifier=node_id,
                kind="manifest.residual",
                status=object_status(item.payload),
                label=compact_text(object_label(item), max_label_chars),
                source=f"{manifest_path.name}#{item.collection}.{item.identifier}",
                digest=short_digest(stable_json(item.payload)),
            )
        )
        edges.append(Edge(node_id, "in_collection", collection_node_id(item.collection), item.collection))
        edges.extend(manifest_object_edges(node_id, item.payload, raw_index))
    return nodes, edges, aliases


def iter_manifest_objects(manifest: Mapping[str, object]) -> Iterator[ManifestObject]:
    symbols = require_object(manifest.get("symbols"), "symbols")
    for identifier, payload in symbols.items():
        yield ManifestObject("symbols", identifier, require_object(payload, f"symbols.{identifier}"))
    for collection in MANIFEST_COLLECTIONS:
        if collection == "symbols":
            continue
        for index, raw_item in enumerate(require_array(manifest.get(collection), collection)):
            payload = require_object(raw_item, f"{collection}[{index}]")
            raw_identifier = payload.get("id")
            if not isinstance(raw_identifier, str) and collection == "forbidden_paths":
                raw_identifier = payload.get("target")
            if isinstance(raw_identifier, str) and raw_identifier.strip():
                yield ManifestObject(collection, raw_identifier, payload)


def manifest_alias_index(objects: Sequence[ManifestObject]) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    for item in objects:
        index.setdefault(item.identifier, []).append(residual_node_id(item.collection, item.identifier))
    return index


def manifest_object_edges(
    source_node: str,
    payload: Mapping[str, object],
    raw_index: Mapping[str, Sequence[str]],
) -> list[Edge]:
    edges: list[Edge] = []
    for field_path, value in iter_string_fields(payload):
        if field_path in TEXT_FIELDS:
            continue
        target_nodes = raw_index.get(value, ())
        relation = relation_for_field(field_path)
        if relation == "refs" and not target_nodes:
            continue
        for target_node in target_nodes:
            if target_node != source_node:
                edges.append(Edge(source_node, relation, target_node, field_path))
    return edges


def relation_for_field(field_path: str) -> str:
    for suffix, relation in RELATION_FIELDS.items():
        if field_path == suffix or field_path.endswith(f".{suffix}"):
            return relation
    return "refs"


def build_idtl_rule_layer(
    repo_root: Path,
    rule_dir: Path,
    max_label_chars: int,
) -> tuple[list[Node], list[Edge], dict[str, set[str]]]:
    nodes: list[Node] = []
    edges: list[Edge] = []
    aliases: dict[str, set[str]] = {}
    for path in sorted(rule_dir.glob("*.idtl.json")):
        document = load_json_object(path)
        doc_id = require_string(document.get("id"), f"{path}.id")
        doc_node = f"idtl:{doc_id}"
        aliases.setdefault(doc_id, set()).add(doc_node)
        nodes.append(
            Node(
                identifier=doc_node,
                kind="idtl.doc",
                status=string_field(document, "language_version"),
                label=doc_id,
                source=relative_or_absolute(repo_root, path),
                digest=file_sha256(path)[:16],
            )
        )
        for index, raw_term in enumerate(require_array(document.get("controlled_vocabulary"), f"{doc_id}.controlled_vocabulary")):
            term = require_object(raw_term, f"{doc_id}.controlled_vocabulary[{index}]")
            term_text = require_string(term.get("term"), f"{doc_id}.controlled_vocabulary[{index}].term")
            term_node = f"term:{doc_id}:{slug(term_text)}"
            nodes.append(
                Node(
                    identifier=term_node,
                    kind="idtl.term",
                    status=string_field(term, "status"),
                    label=compact_text(term_text, max_label_chars),
                    source=relative_or_absolute(repo_root, path),
                    digest=short_digest(stable_json(term)),
                )
            )
            edges.append(Edge(doc_node, "defines_term", term_node, f"controlled_vocabulary[{index}]"))
        for index, raw_rule in enumerate(require_array(document.get("verification_rules"), f"{doc_id}.verification_rules")):
            rule = require_object(raw_rule, f"{doc_id}.verification_rules[{index}]")
            rule_id = require_string(rule.get("id"), f"{doc_id}.verification_rules[{index}].id")
            rule_node = f"rule:{doc_id}:{rule_id}"
            aliases.setdefault(rule_id, set()).add(rule_node)
            nodes.append(
                Node(
                    identifier=rule_node,
                    kind="idtl.rule",
                    status="",
                    label=compact_text(rule_id, max_label_chars),
                    source=relative_or_absolute(repo_root, path),
                    digest=short_digest(stable_json(rule)),
                )
            )
            edges.append(Edge(doc_node, "has_rule", rule_node, f"verification_rules[{index}]"))
            collection = rule_target_collection(rule)
            if collection:
                edges.append(Edge(rule_node, "targets_collection", collection_node_id(collection), "applies_to.collection"))
    return nodes, edges, aliases


def rule_target_collection(rule: Mapping[str, object]) -> str:
    applies_to = rule.get("applies_to")
    if not isinstance(applies_to, dict):
        return ""
    collection = applies_to.get("collection")
    if isinstance(collection, str):
        return collection
    return ""


def build_source_layer(
    repo_root: Path,
    source_globs: Sequence[str],
    max_label_chars: int,
) -> tuple[list[Node], list[Edge], dict[str, set[str]]]:
    files = discover_source_files(repo_root, source_globs)
    nodes: list[Node] = []
    edges: list[Edge] = []
    aliases: dict[str, set[str]] = {}
    module_index = {source.module_id: source.node_id for source in files if source.module_id}
    for source in files:
        nodes.append(
            Node(
                identifier=source.node_id,
                kind="source.file",
                status=file_kind(source.relative_path),
                label=compact_text(source.title, max_label_chars),
                source=source.relative_path,
                digest=source.digest,
            )
        )
        if source.module_id:
            aliases.setdefault(source.module_id, set()).add(source.node_id)
            source_nodes, source_edges, source_aliases = lean_declaration_nodes(source, max_label_chars)
            nodes.extend(source_nodes)
            edges.extend(source_edges)
            merge_aliases(aliases, source_aliases)
            edges.extend(lean_import_edges(source, module_index))
    return nodes, edges, aliases


def discover_source_files(repo_root: Path, source_globs: Sequence[str]) -> list[SourceFile]:
    files: list[SourceFile] = []
    for path in sorted(repo_root.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(repo_root).as_posix()
        if source_path_ignored(relative):
            continue
        if not any(fnmatch.fnmatch(relative, pattern) for pattern in source_globs):
            continue
        raw = path.read_bytes()
        text = raw.decode("utf-8", errors="replace")
        module_id = lean_module_id(relative) if relative.endswith(".lean") else ""
        files.append(
            SourceFile(
                path=path,
                relative_path=relative,
                node_id=f"src:{relative}",
                module_id=module_id,
                digest=hashlib.sha256(raw).hexdigest()[:16],
                title=source_title(relative, text),
                byte_count=len(raw),
            )
        )
    return files


def source_path_ignored(relative: str) -> bool:
    return relative.startswith(".git/") or relative.startswith(".lake/") or relative.startswith("archive/")


def file_kind(relative: str) -> str:
    if relative.endswith(".lean"):
        return "lean"
    if relative.endswith(".idtl.json"):
        return "idtl"
    if relative.endswith(".md"):
        return "markdown"
    return "source"


def source_title(relative: str, text: str) -> str:
    if relative.endswith(".md"):
        for line in text.splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    if relative.endswith(".lean"):
        return lean_module_id(relative)
    return relative


def lean_module_id(relative: str) -> str:
    return relative.removesuffix(".lean").replace("/", ".")


def lean_declaration_nodes(
    source: SourceFile,
    max_label_chars: int,
) -> tuple[list[Node], list[Edge], dict[str, set[str]]]:
    nodes: list[Node] = []
    edges: list[Edge] = []
    aliases: dict[str, set[str]] = {}
    text = source.path.read_text(encoding="utf-8")
    for line_number, line in enumerate(text.splitlines(), start=1):
        match = DECLARATION_RE.match(line.strip())
        if match is None:
            continue
        decl_kind, decl_name = match.groups()
        decl_node = f"decl:{source.module_id}.{decl_name}"
        aliases.setdefault(decl_name, set()).add(decl_node)
        aliases.setdefault(f"{source.module_id}.{decl_name}", set()).add(decl_node)
        nodes.append(
            Node(
                identifier=decl_node,
                kind="lean.decl",
                status=decl_kind,
                label=compact_text(decl_name, max_label_chars),
                source=f"{source.relative_path}:{line_number}",
                digest=short_digest(line.strip()),
            )
        )
        edges.append(Edge(source.node_id, "declares", decl_node, f"line:{line_number}"))
    return nodes, edges, aliases


def lean_import_edges(source: SourceFile, module_index: Mapping[str, str]) -> list[Edge]:
    edges: list[Edge] = []
    text = source.path.read_text(encoding="utf-8")
    for line_number, line in enumerate(text.splitlines(), start=1):
        match = IMPORT_RE.match(line.strip())
        if match is None:
            continue
        target = module_index.get(match.group(1))
        if target is not None:
            edges.append(Edge(source.node_id, "imports", target, f"line:{line_number}"))
    return edges


def focus_subgraph(
    nodes: Sequence[Node],
    edges: Sequence[Edge],
    focus_ids: Sequence[str],
    depth: int,
) -> tuple[list[Node], list[Edge]]:
    node_map = {node.identifier: node for node in nodes}
    neighbors: dict[str, set[str]] = {node.identifier: set() for node in nodes}
    for edge in edges:
        neighbors.setdefault(edge.source, set()).add(edge.target)
        neighbors.setdefault(edge.target, set()).add(edge.source)
    selected: set[str] = set()
    queue: deque[tuple[str, int]] = deque()
    for node_id in focus_ids:
        if node_id in node_map:
            selected.add(node_id)
            queue.append((node_id, 0))
    while queue:
        current, distance = queue.popleft()
        if distance >= depth:
            continue
        for neighbor in sorted(neighbors.get(current, set())):
            if neighbor in selected:
                continue
            selected.add(neighbor)
            queue.append((neighbor, distance + 1))
    return (
        sorted((node_map[node_id] for node_id in selected), key=lambda node: node.identifier),
        [edge for edge in edges if edge.source in selected and edge.target in selected],
    )


def resolve_focus(focus: str, aliases: Mapping[str, set[str]], node_ids: set[str]) -> list[str]:
    if focus in node_ids:
        return [focus]
    matches = sorted(aliases.get(focus, set()))
    if matches:
        return matches
    raise V8GraphError(f"focus {focus!r} is not a v8 node id or alias")


def iter_string_fields(raw: object, prefix: str = "") -> Iterator[tuple[str, str]]:
    if isinstance(raw, str):
        yield prefix, raw
        return
    if isinstance(raw, list):
        for item in raw:
            child_prefix = f"{prefix}[]" if prefix else "[]"
            yield from iter_string_fields(item, child_prefix)
        return
    if isinstance(raw, dict):
        for key, value in raw.items():
            if isinstance(key, str):
                child_prefix = f"{prefix}.{key}" if prefix else key
                yield from iter_string_fields(value, child_prefix)


def object_status(payload: Mapping[str, object]) -> str:
    for field in ("proof_status", "status", "role"):
        value = payload.get(field)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def object_label(item: ManifestObject) -> str:
    if item.collection == "symbols":
        return item.identifier
    for field in ("title", "statement", "lhs", "target", "type", "role"):
        value = item.payload.get(field)
        if isinstance(value, str) and value.strip():
            return value
    return item.identifier


def residual_node_id(collection: str, identifier: str) -> str:
    return f"res:{collection}:{identifier}"


def collection_node_id(collection: str) -> str:
    return f"col:{collection}"


def unique_nodes(nodes: Iterable[Node]) -> list[Node]:
    output: dict[str, Node] = {}
    for node in nodes:
        output.setdefault(node.identifier, node)
    return list(output.values())


def unique_edges(edges: Iterable[Edge]) -> list[Edge]:
    output: dict[tuple[str, str, str, str], Edge] = {}
    for edge in edges:
        output.setdefault((edge.source, edge.relation, edge.target, edge.evidence), edge)
    return list(output.values())


def merge_aliases(target: dict[str, set[str]], source: Mapping[str, set[str]]) -> None:
    for alias, node_ids in source.items():
        target.setdefault(alias, set()).update(node_ids)


def duplicate_aliases(aliases: Mapping[str, set[str]]) -> list[str]:
    return sorted(alias for alias, node_ids in aliases.items() if len(node_ids) > 1)


def manifest_counts(manifest: Mapping[str, object]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for collection in MANIFEST_COLLECTIONS:
        if collection == "symbols":
            counts[collection] = len(require_object(manifest.get(collection), collection))
        else:
            counts[collection] = len(require_array(manifest.get(collection), collection))
    return counts


def load_json_object(path: Path) -> JsonObject:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_object(raw, str(path))


def require_object(value: object, field: str) -> JsonObject:
    if not isinstance(value, dict):
        raise V8GraphError(f"{field} must be an object")
    output: JsonObject = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise V8GraphError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_array(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise V8GraphError(f"{field} must be an array")
    return list(value)


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise V8GraphError(f"{field} must be a non-empty string")
    return value


def string_field(payload: Mapping[str, object], field: str) -> str:
    value = payload.get(field)
    if isinstance(value, str):
        return value
    return ""


def stable_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def compact_text(value: str, max_chars: int) -> str:
    compact = " ".join(value.split())
    if len(compact) <= max_chars:
        return compact
    return compact[: max_chars - 1].rstrip() + "…"


def short_digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()[:16]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def slug(value: str) -> str:
    lowered = value.lower()
    compact = re.sub(r"[^a-z0-9]+", "_", lowered).strip("_")
    return compact or short_digest(value)


def resolve_path(repo_root: Path, path: Path) -> Path:
    if path.is_absolute():
        return path
    return repo_root / path


def relative_or_absolute(repo_root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return str(path)


def write_graph(path: Path, graph: Mapping[str, object], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(graph_json_text(graph, pretty) + "\n", encoding="utf-8")


def print_graph(graph: Mapping[str, object], output: TextIO, pretty: bool) -> None:
    output.write(graph_json_text(graph, pretty))
    output.write("\n")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Build a compact v8 source-grounded theory graph for AI agents."
    )
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--rule-dir", type=Path, default=DEFAULT_RULE_DIR)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument("--no-sources", action="store_true")
    parser.add_argument("--no-manifest-residuals", action="store_true")
    parser.add_argument("--focus")
    parser.add_argument("--depth", type=int, default=1)
    parser.add_argument("--max-label-chars", type=int, default=140)
    parser.add_argument("--source-glob", action="append", dest="source_globs")
    return parser


def main(argv: Sequence[str] | None = None, output: TextIO | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.depth < 0:
        parser.error("--depth must be >= 0")
    if args.max_label_chars < 32:
        parser.error("--max-label-chars must be >= 32")
    source_globs = tuple(args.source_globs) if args.source_globs is not None else DEFAULT_SOURCE_GLOBS
    try:
        graph = build_v8_ai_theory_graph(
            repo_root=Path(args.repo_root),
            manifest_path=Path(args.manifest),
            rule_dir=Path(args.rule_dir),
            source_globs=source_globs,
            include_manifest_residuals=not bool(args.no_manifest_residuals),
            include_sources=not bool(args.no_sources),
            max_label_chars=int(args.max_label_chars),
            focus=args.focus,
            depth=int(args.depth),
        )
    except V8GraphError as error:
        parser.exit(2, f"build_ai_theory_graph: {error}\n")
    if args.stdout:
        print_graph(graph, output if output is not None else sys.stdout, bool(args.pretty))
    else:
        write_graph(Path(args.output), graph, bool(args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
