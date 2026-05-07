from __future__ import annotations

import argparse
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TextIO

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_verifier.ai_theory_graph import (  # noqa: E402
    DEFAULT_GRAPH,
    JsonObject,
    TheoryGraph,
    V8GraphQueryError,
    graph_json_text,
    graph_summary,
    incoming_refs,
    load_theory_graph,
    neighbor_subgraph,
    show_node,
    source_pointers,
)


def write_json(value: Mapping[str, object], output: TextIO, pretty: bool) -> None:
    output.write(graph_json_text(value, pretty))
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
