from __future__ import annotations

import argparse
import json
import sys
from collections import deque
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO


DEFAULT_GRAPH = Path("dist/idt-v8-ai-theory-graph.json")
SCHEMA = "idt-v8-ai-theory-graph/1"
JsonObject = dict[str, object]


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
    raw = require_object(json.loads(path.read_text(encoding="utf-8")), str(path))
    schema = require_string(raw.get("schema"), "schema")
    if schema != SCHEMA:
        raise V8GraphQueryError(f"unsupported graph schema {schema!r}; expected {SCHEMA!r}")
    return TheoryGraph(
        schema=schema,
        contract=require_object(raw.get("contract"), "contract"),
        coverage=require_object(raw.get("coverage"), "coverage"),
        nodes=tuple(parse_nodes(raw.get("nodes"))),
        edges=tuple(parse_edges(raw.get("edges"))),
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


def count_by(values: Iterable[str]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def write_json(value: Mapping[str, object], output: TextIO, pretty: bool) -> None:
    text = (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
        if pretty
        else json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    )
    output.write(text)
    output.write("\n")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Query a compact IDT v8 AI theory graph.")
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    parser.add_argument("--pretty", action="store_true")
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("summary", help="Show graph contract, coverage, and compact counts.")
    show_parser = subparsers.add_parser("show", help="Show one node plus incoming/outgoing edges.")
    show_parser.add_argument("query")
    refs_parser = subparsers.add_parser("refs", help="Show incoming edges for one node.")
    refs_parser.add_argument("query")
    neighbors_parser = subparsers.add_parser("neighbors", help="Show a local undirected neighborhood.")
    neighbors_parser.add_argument("query")
    neighbors_parser.add_argument("--depth", type=int, default=1)
    sources_parser = subparsers.add_parser("sources", help="Show source pointers for a local neighborhood.")
    sources_parser.add_argument("query")
    sources_parser.add_argument("--depth", type=int, default=1)
    return parser


def run_command(graph: TheoryGraph, command: str, query: str, depth: int) -> JsonObject:
    if command == "summary":
        return graph_summary(graph)
    if command == "show":
        return show_node(graph, query)
    if command == "refs":
        return incoming_refs(graph, query)
    if command == "neighbors":
        return neighbor_subgraph(graph, query, depth)
    if command == "sources":
        return source_pointers(graph, query, depth)
    raise V8GraphQueryError(f"unsupported command {command!r}")


def main(argv: Sequence[str] | None = None, output: TextIO | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    raw_query = getattr(args, "query", "")
    query = raw_query if isinstance(raw_query, str) else ""
    raw_depth = getattr(args, "depth", 1)
    depth = raw_depth if isinstance(raw_depth, int) else 1
    try:
        graph = load_theory_graph(Path(args.graph))
        result = run_command(graph, str(args.command), query, depth)
    except V8GraphQueryError as error:
        parser.exit(2, f"query_ai_theory_graph: {error}\n")
    write_json(result, output if output is not None else sys.stdout, bool(args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
