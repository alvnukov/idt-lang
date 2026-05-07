from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_ai_theory_graph import build_v8_ai_theory_graph, main


class AiTheoryGraphTests(unittest.TestCase):
    def test_manifest_residual_graph_preserves_theorem_edges(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)

            graph = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
            )

            self.assertEqual("idt-v8-ai-theory-graph/1", graph["schema"])
            coverage = require_mapping(graph["coverage"])
            self.assertEqual(1, require_mapping(coverage["manifest_counts"])["theorem_cards"])
            nodes = rows_by_id(graph["nodes"])
            self.assertIn("res:theorem_cards:born_card", nodes)
            self.assertEqual("conditional_proof", nodes["res:theorem_cards:born_card"][2])
            edges = {tuple(edge) for edge in require_rows(graph["edges"])}
            self.assertIn(
                (
                    "res:theorem_cards:born_card",
                    "depends_on",
                    "res:finite_gates:born_gate",
                    "dependencies[]",
                ),
                edges,
            )
            self.assertIn(
                (
                    "res:theorem_cards:born_card",
                    "verified_by",
                    "res:finite_gates:born_gate",
                    "verifier",
                ),
                edges,
            )

    def test_focus_outputs_neighborhood_only(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)

            graph = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
                focus="born_card",
                depth=1,
            )

            nodes = rows_by_id(graph["nodes"])
            self.assertIn("res:theorem_cards:born_card", nodes)
            self.assertIn("res:finite_gates:born_gate", nodes)
            self.assertIn("col:theorem_cards", nodes)
            self.assertNotIn("res:symbols:unrelated_symbol", nodes)

    def test_source_graph_indexes_files_and_lean_imports(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)
            proof_dir = root / "Proofs" / "MetaLang"
            proof_dir.mkdir(parents=True)
            (proof_dir / "A.lean").write_text("def alpha := 1\n", encoding="utf-8")
            (proof_dir / "B.lean").write_text("import Proofs.MetaLang.A\n", encoding="utf-8")
            sections_dir = root / "sections"
            sections_dir.mkdir()
            (sections_dir / "001-test.md").write_text("# Test Section\nBody\n", encoding="utf-8")

            graph = build_v8_ai_theory_graph(repo_root=root, manifest_path=manifest_path)

            nodes = rows_by_id(graph["nodes"])
            self.assertIn("src:Proofs/MetaLang/A.lean", nodes)
            self.assertIn("src:sections/001-test.md", nodes)
            self.assertIn("decl:Proofs.MetaLang.A.alpha", nodes)
            self.assertEqual("Test Section", nodes["src:sections/001-test.md"][3])
            edges = {tuple(edge) for edge in require_rows(graph["edges"])}
            self.assertIn(
                (
                    "src:Proofs/MetaLang/B.lean",
                    "imports",
                    "src:Proofs/MetaLang/A.lean",
                    "line:1",
                ),
                edges,
            )

    def test_cli_writes_compact_json(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)
            output_path = root / "graph.json"

            exit_code = main(
                [
                    "--manifest",
                    str(manifest_path),
                    "--repo-root",
                    str(root),
                    "--no-sources",
                    "--output",
                    str(output_path),
                ]
            )

            self.assertEqual(0, exit_code)
            raw = output_path.read_text(encoding="utf-8")
            self.assertNotIn("\n  ", raw)
            parsed = json.loads(raw)
            self.assertEqual("disabled", parsed["meta"]["source_mode"])

    def test_graph_declares_lean_only_proof_contract(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)

            graph = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
            )

            contract = require_mapping(graph["contract"])
            self.assertEqual("lean_only", contract["proof_authority"])
            self.assertEqual("residual_input_not_proof_truth", contract["manifest_role"])


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
