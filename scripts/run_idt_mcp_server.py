from __future__ import annotations

import argparse
import sys
from collections.abc import Sequence
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_verifier.ai_theory_graph import DEFAULT_GRAPH, V8GraphQueryError  # noqa: E402
from theory_verifier.idt_mcp_server import load_server, serve  # noqa: E402
from theory_verifier.idt_rag import IdtRagError  # noqa: E402


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run the source-grounded IDT v8 development MCP server over stdio."
    )
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        server = load_server(Path(args.repo_root), Path(args.graph))
    except (IdtRagError, V8GraphQueryError) as error:
        parser.exit(2, f"run_idt_mcp_server: {error}\n")
    return serve(server, sys.stdin, sys.stdout)


if __name__ == "__main__":
    raise SystemExit(main())
