from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from theory_verifier.ai_theory_graph import (
    TheoryGraph,
    V8GraphQueryError,
    graph_json_text,
    load_theory_graph,
    validate_graph_payload,
    validate_source_file_hashes,
)


class AiTheoryGraphValidationTests(unittest.TestCase):
    def test_valid_payload_loads(self) -> None:
        graph = load_from_payload(valid_payload())

        self.assertEqual("idt-v8-ai-theory-graph/1", graph.schema)
        self.assertEqual(2, len(graph.nodes))
        self.assertEqual(1, len(graph.edges))

    def test_rejects_non_lean_proof_authority(self) -> None:
        payload = valid_payload(
            contract={
                "proof_authority": "manifest",
                "manifest_role": "residual_input_not_proof_truth",
                "claim_upgrade_policy": "no_artifact_no_upgrade",
                "full_text_policy": "use source paths and sha16 digests to fetch exact repository files",
            }
        )

        with self.assertRaisesRegex(V8GraphQueryError, "contract.proof_authority"):
            validate_graph_payload(payload)

    def test_rejects_unknown_schema(self) -> None:
        payload = valid_payload()
        payload["schema"] = "other"

        with self.assertRaisesRegex(V8GraphQueryError, "unsupported graph schema"):
            validate_graph_payload(payload)

    def test_rejects_bad_node_row_width(self) -> None:
        payload = valid_payload(nodes=[["n:a", "kind"]], edges=[], coverage={"nodes": 1, "edges": 0})

        with self.assertRaisesRegex(V8GraphQueryError, "nodes\\[0\\]"):
            validate_graph_payload(payload)

    def test_rejects_non_string_node_cell(self) -> None:
        payload = valid_payload(
            nodes=[
                ["n:a", "kind", "", "A", "source:a", 123],
                ["n:b", "kind", "", "B", "source:b", "fedcba9876543210"],
            ]
        )

        with self.assertRaisesRegex(V8GraphQueryError, "nodes\\[0\\]\\[5\\]"):
            validate_graph_payload(payload)

    def test_rejects_duplicate_node_ids(self) -> None:
        payload = valid_payload(
            nodes=[
                ["n:a", "kind", "", "A", "source:a", "0123456789abcdef"],
                ["n:a", "kind", "", "A copy", "source:a", "0123456789abcdee"],
            ],
            edges=[],
            coverage={"nodes": 2, "edges": 0},
        )

        with self.assertRaisesRegex(V8GraphQueryError, "duplicate node id"):
            validate_graph_payload(payload)

    def test_rejects_unsorted_nodes(self) -> None:
        payload = valid_payload(
            nodes=[
                ["n:b", "kind", "", "B", "source:b", "fedcba9876543210"],
                ["n:a", "kind", "", "A", "source:a", "0123456789abcdef"],
            ],
            edges=[],
            coverage={"nodes": 2, "edges": 0},
        )

        with self.assertRaisesRegex(V8GraphQueryError, "nodes must be sorted"):
            validate_graph_payload(payload)

    def test_rejects_dangling_edge_target(self) -> None:
        payload = valid_payload(
            edges=[["n:a", "depends_on", "n:missing", "fixture"]],
        )

        with self.assertRaisesRegex(V8GraphQueryError, "edge target"):
            validate_graph_payload(payload)

    def test_rejects_unsorted_edges(self) -> None:
        payload = valid_payload(
            nodes=[
                ["n:a", "kind", "", "A", "source:a", "0123456789abcdef"],
                ["n:b", "kind", "", "B", "source:b", "fedcba9876543210"],
            ],
            edges=[
                ["n:b", "depends_on", "n:a", "fixture"],
                ["n:a", "depends_on", "n:b", "fixture"],
            ],
            coverage={"nodes": 2, "edges": 2},
        )

        with self.assertRaisesRegex(V8GraphQueryError, "edges must be sorted"):
            validate_graph_payload(payload)

    def test_rejects_duplicate_edges(self) -> None:
        payload = valid_payload(
            edges=[
                ["n:a", "depends_on", "n:b", "fixture"],
                ["n:a", "depends_on", "n:b", "fixture"],
            ],
            coverage={"nodes": 2, "edges": 2},
        )

        with self.assertRaisesRegex(V8GraphQueryError, "duplicate edge"):
            validate_graph_payload(payload)

    def test_rejects_invalid_sha16_digest(self) -> None:
        payload = valid_payload(
            nodes=[
                ["n:a", "kind", "", "A", "source:a", "not-a-sha16"],
                ["n:b", "kind", "", "B", "source:b", "fedcba9876543210"],
            ]
        )

        with self.assertRaisesRegex(V8GraphQueryError, "invalid sha16"):
            validate_graph_payload(payload)

    def test_rejects_coverage_mismatch(self) -> None:
        payload = valid_payload(coverage={"nodes": 99, "edges": 1})

        with self.assertRaisesRegex(V8GraphQueryError, "coverage.nodes"):
            validate_graph_payload(payload)

    def test_rejects_boolean_coverage_count(self) -> None:
        payload = valid_payload(coverage={"nodes": True, "edges": 1})

        with self.assertRaisesRegex(V8GraphQueryError, "coverage.nodes"):
            validate_graph_payload(payload)

    def test_rejects_invalid_json_file(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "bad.json"
            path.write_text("{", encoding="utf-8")

            with self.assertRaisesRegex(V8GraphQueryError, "invalid graph JSON"):
                load_theory_graph(path)

    def test_rejects_missing_graph_file(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "missing.json"

            with self.assertRaisesRegex(V8GraphQueryError, "cannot read graph"):
                load_theory_graph(path)

    def test_compact_json_is_deterministic(self) -> None:
        payload = valid_payload()

        self.assertEqual(graph_json_text(payload, pretty=False), graph_json_text(payload, pretty=False))
        self.assertNotIn("\n  ", graph_json_text(payload, pretty=False))

    def test_source_hash_validation_accepts_matching_source_file(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            source = root / "README.md"
            source.write_text("hello\n", encoding="utf-8")
            payload = valid_payload(
                nodes=[
                    ["src:README.md", "source.file", "markdown", "README", "README.md", "5891b5b522d5df08"],
                ],
                edges=[],
                coverage={"nodes": 1, "edges": 0},
            )

            validate_source_file_hashes(load_from_payload(payload), root)

    def test_source_hash_validation_rejects_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            source = root / "README.md"
            source.write_text("changed\n", encoding="utf-8")
            payload = valid_payload(
                nodes=[
                    ["src:README.md", "source.file", "markdown", "README", "README.md", "5891b5b522d5df08"],
                ],
                edges=[],
                coverage={"nodes": 1, "edges": 0},
            )

            with self.assertRaisesRegex(V8GraphQueryError, "source hash mismatch"):
                validate_source_file_hashes(load_from_payload(payload), root)

    def test_source_hash_validation_rejects_repo_escape(self) -> None:
        payload = valid_payload(
            nodes=[
                ["src:escape", "source.file", "markdown", "escape", "../README.md", "0123456789abcdef"],
            ],
            edges=[],
            coverage={"nodes": 1, "edges": 0},
        )

        with tempfile.TemporaryDirectory() as raw_dir:
            with self.assertRaisesRegex(V8GraphQueryError, "escapes repo root"):
                validate_source_file_hashes(load_from_payload(payload), Path(raw_dir))


def valid_payload(
    nodes: list[list[object]] | None = None,
    edges: list[list[object]] | None = None,
    contract: dict[str, object] | None = None,
    coverage: dict[str, object] | None = None,
) -> dict[str, object]:
    node_rows = nodes if nodes is not None else [
        ["n:a", "kind", "", "A", "source:a", "0123456789abcdef"],
        ["n:b", "kind", "", "B", "source:b", "fedcba9876543210"],
    ]
    edge_rows = edges if edges is not None else [["n:a", "depends_on", "n:b", "fixture"]]
    return {
        "schema": "idt-v8-ai-theory-graph/1",
        "contract": contract if contract is not None else {
            "proof_authority": "lean_only",
            "manifest_role": "residual_input_not_proof_truth",
            "claim_upgrade_policy": "no_artifact_no_upgrade",
            "full_text_policy": "use source paths and sha16 digests to fetch exact repository files",
        },
        "coverage": coverage if coverage is not None else {
            "nodes": len(node_rows),
            "edges": len(edge_rows),
        },
        "nodes": node_rows,
        "edges": edge_rows,
    }


def load_from_payload(payload: dict[str, object]) -> TheoryGraph:
    with tempfile.TemporaryDirectory() as raw_dir:
        path = Path(raw_dir) / "graph.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        return load_theory_graph(path)


if __name__ == "__main__":
    unittest.main()
