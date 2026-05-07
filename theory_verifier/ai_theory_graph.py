from __future__ import annotations

import hashlib
import json
import re
from collections import deque
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "idt-v8-ai-theory-graph/1"
DEFAULT_GRAPH = Path("dist/idt-v8-ai-theory-graph.json")
JsonObject = dict[str, object]
SHA16_RE = re.compile(r"^[0-9a-f]{16}$")
EXPECTED_CONTRACT: dict[str, str] = {
    "proof_authority": "lean_only",
    "manifest_role": "residual_input_not_proof_truth",
    "claim_upgrade_policy": "no_artifact_no_upgrade",
    "full_text_policy": "use source paths and sha16 digests to fetch exact repository files",
}


class V8GraphQueryError(ValueError):
    pass


@dataclass(frozen=True)
class GraphNode:
    identifier: str
    kind: str
    status: str
    label: str
    source: str
    digest: str

    def row(self) -> list[str]:
        return [
            self.identifier,
            self.kind,
            self.status,
            self.label,
            self.source,
            self.digest,
        ]


@dataclass(frozen=True)
class GraphEdge:
    source: str
    relation: str
    target: str
    evidence: str

    def row(self) -> list[str]:
        return [self.source, self.relation, self.target, self.evidence]


@dataclass(frozen=True)
class TheoryGraph:
    schema: str
    contract: JsonObject
    coverage: JsonObject
    nodes: tuple[GraphNode, ...]
    edges: tuple[GraphEdge, ...]

    @property
    def node_index(self) -> dict[str, GraphNode]:
        return {node.identifier: node for node in self.nodes}


def load_theory_graph(path: Path) -> TheoryGraph:
    try:
        raw_text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise V8GraphQueryError(f"cannot read graph {path}: {error}") from error
    try:
        raw = require_object(json.loads(raw_text), str(path))
    except json.JSONDecodeError as error:
        raise V8GraphQueryError(f"invalid graph JSON {path}: {error}") from error
    return theory_graph_from_payload(raw)


def theory_graph_from_payload(raw: Mapping[str, object]) -> TheoryGraph:
    schema = require_string(raw.get("schema"), "schema")
    if schema != SCHEMA:
        raise V8GraphQueryError(f"unsupported graph schema {schema!r}; expected {SCHEMA!r}")
    graph = TheoryGraph(
        schema=schema,
        contract=require_object(raw.get("contract"), "contract"),
        coverage=require_object(raw.get("coverage"), "coverage"),
        nodes=tuple(parse_nodes(raw.get("nodes"))),
        edges=tuple(parse_edges(raw.get("edges"))),
    )
    validate_theory_graph(graph)
    return graph


def validate_graph_payload(raw: Mapping[str, object]) -> None:
    theory_graph_from_payload(raw)


def validate_theory_graph(graph: TheoryGraph) -> None:
    validate_contract(graph.contract)
    validate_nodes(graph.nodes)
    validate_edges(graph.nodes, graph.edges)
    validate_coverage(graph.coverage, graph.nodes, graph.edges)


def validate_source_file_hashes(graph: TheoryGraph, repo_root: Path) -> None:
    root = repo_root.resolve()
    for node in graph.nodes:
        if node.kind != "source.file":
            continue
        if Path(node.source).is_absolute():
            raise V8GraphQueryError(f"source node {node.identifier!r} uses absolute source path")
        source_path = (root / node.source).resolve()
        try:
            source_path.relative_to(root)
        except ValueError as error:
            raise V8GraphQueryError(
                f"source node {node.identifier!r} escapes repo root"
            ) from error
        try:
            actual = hashlib.sha256(source_path.read_bytes()).hexdigest()[:16]
        except OSError as error:
            raise V8GraphQueryError(
                f"cannot read source for node {node.identifier!r}: {node.source}: {error}"
            ) from error
        if actual != node.digest:
            raise V8GraphQueryError(
                f"source hash mismatch for node {node.identifier!r}: "
                f"graph={node.digest} actual={actual}"
            )


def validate_contract(contract: Mapping[str, object]) -> None:
    for field, expected in EXPECTED_CONTRACT.items():
        actual = require_string(contract.get(field), f"contract.{field}")
        if actual != expected:
            raise V8GraphQueryError(
                f"contract.{field} must be {expected!r}, got {actual!r}"
            )


def validate_nodes(nodes: Sequence[GraphNode]) -> None:
    node_ids = [node.identifier for node in nodes]
    if node_ids != sorted(node_ids):
        raise V8GraphQueryError("nodes must be sorted by id")
    seen: set[str] = set()
    for node in nodes:
        if not node.identifier:
            raise V8GraphQueryError("node id must be non-empty")
        if node.identifier in seen:
            raise V8GraphQueryError(f"duplicate node id {node.identifier!r}")
        seen.add(node.identifier)
        if not node.kind:
            raise V8GraphQueryError(f"node {node.identifier!r} has empty kind")
        if not node.source:
            raise V8GraphQueryError(f"node {node.identifier!r} has empty source")
        if SHA16_RE.fullmatch(node.digest) is None:
            raise V8GraphQueryError(f"node {node.identifier!r} has invalid sha16 digest")


def validate_edges(nodes: Sequence[GraphNode], edges: Sequence[GraphEdge]) -> None:
    node_ids = {node.identifier for node in nodes}
    edge_keys = [(edge.source, edge.relation, edge.target, edge.evidence) for edge in edges]
    if edge_keys != sorted(edge_keys):
        raise V8GraphQueryError("edges must be sorted by source/relation/target/evidence")
    seen: set[tuple[str, str, str, str]] = set()
    for edge in edges:
        row = (edge.source, edge.relation, edge.target, edge.evidence)
        if row in seen:
            raise V8GraphQueryError(f"duplicate edge {row!r}")
        seen.add(row)
        if edge.source not in node_ids:
            raise V8GraphQueryError(f"edge source {edge.source!r} is not a graph node")
        if edge.target not in node_ids:
            raise V8GraphQueryError(f"edge target {edge.target!r} is not a graph node")
        if not edge.relation:
            raise V8GraphQueryError(f"edge {row!r} has empty relation")
        if not edge.evidence:
            raise V8GraphQueryError(f"edge {row!r} has empty evidence")


def validate_coverage(
    coverage: Mapping[str, object],
    nodes: Sequence[GraphNode],
    edges: Sequence[GraphEdge],
) -> None:
    expected_nodes = require_int(coverage.get("nodes"), "coverage.nodes")
    expected_edges = require_int(coverage.get("edges"), "coverage.edges")
    if expected_nodes != len(nodes):
        raise V8GraphQueryError(
            f"coverage.nodes={expected_nodes} does not match actual node count {len(nodes)}"
        )
    if expected_edges != len(edges):
        raise V8GraphQueryError(
            f"coverage.edges={expected_edges} does not match actual edge count {len(edges)}"
        )


def graph_summary(graph: TheoryGraph) -> JsonObject:
    return {
        "schema": graph.schema,
        "contract": graph.contract,
        "coverage": graph.coverage,
        "node_kinds": count_by(node.kind for node in graph.nodes),
        "node_statuses": count_by(node.status for node in graph.nodes if node.status),
        "edge_relations": count_by(edge.relation for edge in graph.edges),
    }


def show_node(graph: TheoryGraph, query: str) -> JsonObject:
    node_id = resolve_node_id(graph, query)
    node = graph.node_index[node_id]
    outgoing = sorted(
        (edge for edge in graph.edges if edge.source == node_id),
        key=lambda edge: (edge.relation, edge.target, edge.evidence),
    )
    incoming = sorted(
        (edge for edge in graph.edges if edge.target == node_id),
        key=lambda edge: (edge.source, edge.relation, edge.evidence),
    )
    return {
        "query": query,
        "resolved": node_id,
        "node": node.row(),
        "incoming": [edge.row() for edge in incoming],
        "outgoing": [edge.row() for edge in outgoing],
    }


def incoming_refs(graph: TheoryGraph, query: str) -> JsonObject:
    node_id = resolve_node_id(graph, query)
    incoming = sorted(
        (edge for edge in graph.edges if edge.target == node_id),
        key=lambda edge: (edge.source, edge.relation, edge.evidence),
    )
    return {
        "query": query,
        "resolved": node_id,
        "incoming": [edge.row() for edge in incoming],
    }


def neighbor_subgraph(graph: TheoryGraph, query: str, depth: int) -> JsonObject:
    if depth < 0:
        raise V8GraphQueryError("depth must be >= 0")
    focus = resolve_node_id(graph, query)
    selected = neighborhood_ids(graph, focus, depth)
    nodes = sorted(
        (node for node in graph.nodes if node.identifier in selected),
        key=lambda node: node.identifier,
    )
    edges = sorted(
        (
            edge
            for edge in graph.edges
            if edge.source in selected and edge.target in selected
        ),
        key=lambda edge: (edge.source, edge.relation, edge.target, edge.evidence),
    )
    return {
        "query": query,
        "resolved": focus,
        "depth": depth,
        "nodes": [node.row() for node in nodes],
        "edges": [edge.row() for edge in edges],
    }


def source_pointers(graph: TheoryGraph, query: str, depth: int) -> JsonObject:
    subgraph = neighbor_subgraph(graph, query, depth)
    rows = require_rows(subgraph["nodes"], "nodes", 6)
    sources = sorted({(row[0], row[4], row[5]) for row in rows if row[4]})
    return {
        "query": query,
        "resolved": require_string(subgraph["resolved"], "resolved"),
        "depth": depth,
        "sources": [[node_id, source, digest] for node_id, source, digest in sources],
    }


def neighborhood_ids(graph: TheoryGraph, focus: str, depth: int) -> set[str]:
    neighbors: dict[str, set[str]] = {node.identifier: set() for node in graph.nodes}
    for edge in graph.edges:
        neighbors.setdefault(edge.source, set()).add(edge.target)
        neighbors.setdefault(edge.target, set()).add(edge.source)
    selected = {focus}
    queue: deque[tuple[str, int]] = deque([(focus, 0)])
    while queue:
        current, distance = queue.popleft()
        if distance >= depth:
            continue
        for neighbor in sorted(neighbors.get(current, set())):
            if neighbor in selected:
                continue
            selected.add(neighbor)
            queue.append((neighbor, distance + 1))
    return selected


def resolve_node_id(graph: TheoryGraph, query: str) -> str:
    node_ids = {node.identifier for node in graph.nodes}
    if query in node_ids:
        return query
    for matches in (
        suffix_matches(graph, query),
        source_or_decl_matches(graph, query),
        label_matches(graph, query),
    ):
        if len(matches) == 1:
            return matches[0]
        if len(matches) > 1:
            preview = ", ".join(matches[:8])
            suffix = "" if len(matches) <= 8 else f", ... ({len(matches)} matches)"
            raise V8GraphQueryError(f"ambiguous graph alias {query!r}: {preview}{suffix}")
    raise V8GraphQueryError(f"unknown graph node id or alias {query!r}")


def suffix_matches(graph: TheoryGraph, query: str) -> list[str]:
    return sorted(
        node.identifier
        for node in graph.nodes
        if node.identifier.endswith(f":{query}")
    )


def source_or_decl_matches(graph: TheoryGraph, query: str) -> list[str]:
    return sorted(
        node.identifier
        for node in graph.nodes
        if source_or_decl_matches_query(node.identifier, query)
    )


def label_matches(graph: TheoryGraph, query: str) -> list[str]:
    return sorted(node.identifier for node in graph.nodes if node.label == query)


def source_or_decl_matches_query(identifier: str, query: str) -> bool:
    if identifier.startswith("src:") and identifier.removeprefix("src:") == query:
        return True
    if identifier.startswith("decl:") and identifier.removeprefix("decl:").endswith(f".{query}"):
        return True
    return False


def parse_nodes(value: object) -> list[GraphNode]:
    return [
        GraphNode(row[0], row[1], row[2], row[3], row[4], row[5])
        for row in require_rows(value, "nodes", 6)
    ]


def parse_edges(value: object) -> list[GraphEdge]:
    return [
        GraphEdge(row[0], row[1], row[2], row[3])
        for row in require_rows(value, "edges", 4)
    ]


def require_rows(value: object, field: str, width: int) -> list[list[str]]:
    if not isinstance(value, list):
        raise V8GraphQueryError(f"{field} must be an array")
    rows: list[list[str]] = []
    for index, item in enumerate(value):
        if not isinstance(item, list) or len(item) != width:
            raise V8GraphQueryError(f"{field}[{index}] must be a {width}-column row")
        row: list[str] = []
        for column, raw in enumerate(item):
            if not isinstance(raw, str):
                raise V8GraphQueryError(f"{field}[{index}][{column}] must be a string")
            row.append(raw)
        rows.append(row)
    return rows


def require_object(value: object, field: str) -> JsonObject:
    if not isinstance(value, dict):
        raise V8GraphQueryError(f"{field} must be an object")
    output: JsonObject = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise V8GraphQueryError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise V8GraphQueryError(f"{field} must be a non-empty string")
    return value


def require_int(value: object, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise V8GraphQueryError(f"{field} must be an integer")
    return value


def count_by(values: Iterable[str]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def graph_json_text(graph: Mapping[str, object], pretty: bool) -> str:
    if pretty:
        return json.dumps(graph, ensure_ascii=False, indent=2, sort_keys=True)
    return json.dumps(graph, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
