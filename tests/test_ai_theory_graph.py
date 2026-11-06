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
            (proof_dir / "B.lean").write_text(
                "import Proofs.MetaLang.A\n"
                "theorem beta : alpha = alpha := by rfl\n"
                "def gamma := 2 -- beta alpha\n",
                encoding="utf-8",
            )
            sections_dir = root / "sections"
            sections_dir.mkdir()
            (sections_dir / "001-test.md").write_text("# Test Section\nBody\n", encoding="utf-8")
            (root / "AI_AGENT_GUIDE.md").write_text("# AI Agent Guide\nBody\n", encoding="utf-8")

            graph = build_v8_ai_theory_graph(repo_root=root, manifest_path=manifest_path)

            nodes = rows_by_id(graph["nodes"])
            self.assertIn("src:Proofs/MetaLang/A.lean", nodes)
            self.assertIn("src:sections/001-test.md", nodes)
            self.assertIn("src:AI_AGENT_GUIDE.md", nodes)
            self.assertIn("decl:Proofs.MetaLang.A.alpha", nodes)
            self.assertIn("decl:Proofs.MetaLang.B.beta", nodes)
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
            self.assertIn(
                (
                    "decl:Proofs.MetaLang.B.beta",
                    "refs",
                    "decl:Proofs.MetaLang.A.alpha",
                    "line:2",
                ),
                edges,
            )
            self.assertNotIn(
                (
                    "decl:Proofs.MetaLang.B.gamma",
                    "refs",
                    "decl:Proofs.MetaLang.A.alpha",
                    "line:3",
                ),
                edges,
            )

    def test_unicode_lean_names_keep_distinct_nodes_anchors_and_refs(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)
            proof_dir = root / "Proofs" / "MetaLang"
            proof_dir.mkdir(parents=True)
            declarations = {
                "numerator₁": (2, "def numerator₁ := 1"),
                "numerator₂": (3, "def numerator₂ := 2"),
                "output₁": (4, "def output₁ := Mixer.numerator₁"),
                "output₂": (5, "def output₂ := Mixer.numerator₂"),
                "numerator_twice₁": (6, "theorem numerator_twice₁ : output₁ = numerator₁ := rfl"),
                "numerator_twice₂": (7, "theorem numerator_twice₂ : output₂ = numerator₂ := rfl"),
            }
            (proof_dir / "Mixer.lean").write_text(
                "namespace Mixer\n"
                + "\n".join(line for _, line in declarations.values())
                + "\nend Mixer\n",
                encoding="utf-8",
            )

            graph = build_v8_ai_theory_graph(repo_root=root, manifest_path=manifest_path)

            prefix = "decl:Proofs.MetaLang.Mixer."
            nodes = rows_by_id(graph["nodes"])
            self.assertEqual(
                {prefix + name for name in declarations},
                {node_id for node_id in nodes if node_id.startswith(prefix)},
            )
            edges = {tuple(edge) for edge in require_rows(graph["edges"])}
            for name, (line_number, _) in declarations.items():
                with self.subTest(name=name):
                    self.assertEqual(name, nodes[prefix + name][3])
                    self.assertEqual(
                        f"Proofs/MetaLang/Mixer.lean:{line_number}", nodes[prefix + name][4]
                    )
                    self.assertIn(
                        ("src:Proofs/MetaLang/Mixer.lean", "declares", prefix + name, f"line:{line_number}"),
                        edges,
                    )
            for suffix, line_number in (("₁", 4), ("₂", 5)):
                self.assertEqual(
                    {(prefix + "output" + suffix, "refs", prefix + "numerator" + suffix,
                      f"line:{line_number}")},
                    {edge for edge in edges
                     if edge[0] == prefix + "output" + suffix and edge[1] == "refs"},
                )
                self.assertIn(
                    (prefix + "numerator_twice" + suffix, "refs", prefix + "numerator" + suffix,
                     f"line:{line_number + 2}"),
                    edges,
                )

    def test_lean_identifier_characters_do_not_absorb_operators(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)
            proof_dir = root / "Proofs" / "MetaLang"
            proof_dir.mkdir(parents=True)
            names = ["ascii", "ascii'", "ascii!", "ascii?", "α₁", "ℝ₁", "𝒜₁",
                     "café", "subsₐ", "subsᵢ", "subsⱼ"]
            lines = [f"def {name} := 1" for name in names]
            lines.extend(["def total := " + "+".join(names), "def × := 1", "def λ := 1"])
            (proof_dir / "Names.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")

            graph = build_v8_ai_theory_graph(repo_root=root, manifest_path=manifest_path)

            prefix = "decl:Proofs.MetaLang.Names."
            nodes = rows_by_id(graph["nodes"])
            self.assertEqual(
                {prefix + name for name in [*names, "total"]},
                {node_id for node_id in nodes if node_id.startswith(prefix)},
            )
            edges = {tuple(edge) for edge in require_rows(graph["edges"])}
            self.assertEqual(
                {(prefix + "total", "refs", prefix + name, f"line:{len(names) + 1}")
                 for name in names},
                {edge for edge in edges if edge[0] == prefix + "total" and edge[1] == "refs"},
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

    def test_graph_build_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)

            first = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
            )
            second = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
            )

            self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))

    def test_graph_can_exclude_manifest_residuals(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            manifest_path = write_sample_manifest(root)

            graph = build_v8_ai_theory_graph(
                repo_root=root,
                manifest_path=manifest_path,
                include_sources=False,
                include_manifest_residuals=False,
            )

            nodes = rows_by_id(graph["nodes"])
            self.assertIn("col:theorem_cards", nodes)
            self.assertNotIn("res:theorem_cards:born_card", nodes)


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
