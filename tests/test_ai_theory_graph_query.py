from __future__ import annotations

import io
import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_ai_theory_graph import build_v8_ai_theory_graph, write_graph
from scripts.query_ai_theory_graph import main
from theory_verifier.ai_theory_graph import (
    graph_summary,
    incoming_refs,
    load_theory_graph,
    neighbor_subgraph,
    show_node,
    source_pointers,
)


class AiTheoryGraphQueryTests(unittest.TestCase):
    def test_summary_reports_v8_contract_counts(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            graph_path = write_sample_graph(Path(raw_dir), include_sources=False)

            summary = graph_summary(load_theory_graph(graph_path))

            self.assertEqual("idt-v8-ai-theory-graph/1", summary["schema"])
            contract = require_mapping(summary["contract"])
            self.assertEqual("lean_only", contract["proof_authority"])
            node_kinds = require_mapping(summary["node_kinds"])
            manifest_residual_count = node_kinds["manifest.residual"]
            if not isinstance(manifest_residual_count, int):
                raise AssertionError("expected integer manifest.residual count")
            self.assertGreater(manifest_residual_count, 0)

    def test_show_resolves_manifest_alias(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            graph_path = write_sample_graph(Path(raw_dir), include_sources=False)

            result = show_node(load_theory_graph(graph_path), "born_card")

            self.assertEqual("res:theorem_cards:born_card", result["resolved"])
            outgoing = {tuple(edge) for edge in require_rows(result["outgoing"])}
            self.assertIn(
                (
                    "res:theorem_cards:born_card",
                    "depends_on",
                    "res:finite_gates:born_gate",
                    "dependencies[]",
                ),
                outgoing,
            )

    def test_refs_returns_incoming_edges(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            graph_path = write_sample_graph(Path(raw_dir), include_sources=False)

            result = incoming_refs(load_theory_graph(graph_path), "born_gate")

            incoming = {tuple(edge) for edge in require_rows(result["incoming"])}
            self.assertIn(
                (
                    "res:theorem_cards:born_card",
                    "verified_by",
                    "res:finite_gates:born_gate",
                    "verifier",
                ),
                incoming,
            )

    def test_neighbors_returns_local_subgraph_only(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            graph_path = write_sample_graph(Path(raw_dir), include_sources=False)

            result = neighbor_subgraph(load_theory_graph(graph_path), "born_card", depth=1)

            nodes = rows_by_id(result["nodes"])
            self.assertIn("res:theorem_cards:born_card", nodes)
            self.assertIn("res:finite_gates:born_gate", nodes)
            self.assertNotIn("res:symbols:unrelated_symbol", nodes)

    def test_sources_reports_source_pointers_for_neighborhood(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            proof_dir = root / "Proofs" / "MetaLang"
            proof_dir.mkdir(parents=True)
            (proof_dir / "A.lean").write_text("def alpha := 1\n", encoding="utf-8")
            graph_path = write_sample_graph(root, include_sources=True)

            result = source_pointers(load_theory_graph(graph_path), "alpha", depth=1)

            sources = require_rows(result["sources"])
            self.assertTrue(
                any(
                    row[0] == "decl:Proofs.MetaLang.A.alpha"
                    and row[1] == "Proofs/MetaLang/A.lean:1"
                    for row in sources
                )
            )
            self.assertTrue(all(len(row[2]) == 16 for row in sources))

    def test_cli_outputs_compact_json(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            graph_path = write_sample_graph(Path(raw_dir), include_sources=False)
            output = io.StringIO()

            exit_code = main(["--graph", str(graph_path), "show", "born_card"], output)

            self.assertEqual(0, exit_code)
            raw = output.getvalue()
            self.assertNotIn("\n  ", raw)
            parsed = json.loads(raw)
            self.assertEqual("res:theorem_cards:born_card", parsed["resolved"])


def write_sample_graph(root: Path, include_sources: bool) -> Path:
    manifest_path = write_sample_manifest(root)
    graph = build_v8_ai_theory_graph(
        repo_root=root,
        manifest_path=manifest_path,
        include_sources=include_sources,
    )
    graph_path = root / "graph.json"
    write_graph(graph_path, graph, pretty=False)
    return graph_path


def write_sample_manifest(root: Path) -> Path:
    manifest = {
        "schema_version": "test",
        "theory_version": "v8.0.0",
        "symbols": {
            "born_readout_I": {"status": "target", "dimension": {}},
            "unrelated_symbol": {"status": "open", "dimension": {}},
        },
        "equations": [],
        "derivations": [],
        "forbidden_paths": [],
        "finite_gates": [
            {
                "id": "born_gate",
                "type": "demo",
                "status": "derived_conditional",
            }
        ],
        "qm_experiments": [],
        "qm_universal_patterns": [],
        "qm_core_proof_obligations": [],
        "theorem_cards": [
            {
                "id": "born_card",
                "statement": "Born card.",
                "role": "theorem",
                "assumptions": [],
                "dependencies": ["born_gate"],
                "proof_status": "conditional_proof",
                "verifier": "born_gate",
                "known_failures": [],
                "physical_scope": "test",
                "forbidden_claims": ["does_not_prove_full_QM_I"],
            }
        ],
    }
    manifest_path = root / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest_path


def require_mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise AssertionError("expected mapping")
    return value


def require_rows(value: object) -> list[list[str]]:
    if not isinstance(value, list):
        raise AssertionError("expected list")
    rows: list[list[str]] = []
    for item in value:
        if not isinstance(item, list) or not all(isinstance(part, str) for part in item):
            raise AssertionError("expected string row")
        rows.append(item)
    return rows


def rows_by_id(value: object) -> dict[str, list[str]]:
    return {row[0]: row for row in require_rows(value)}


if __name__ == "__main__":
    unittest.main()
