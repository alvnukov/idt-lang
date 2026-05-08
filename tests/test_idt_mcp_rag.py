from __future__ import annotations

import io
import hashlib
import json
import shutil
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from scripts.build_ai_theory_graph import build_v8_ai_theory_graph
from theory_verifier.ai_theory_graph import V8GraphQueryError
from theory_verifier.idt_mcp_server import IdtMcpServer, handle_line, serve
from theory_verifier.idt_rag import (
    IdtRagError,
    IdtRagIndex,
    graph_json_load_for_tests,
    lock_path_for,
    write_locked_graph_for_tests,
)


class IdtMcpRagTests(unittest.TestCase):
    def test_rag_retrieve_is_source_grounded_and_boundary_limited(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            index = load_fixture_index(root)

            result = index.retrieve("Born claim_source_aliasing", limit=3, max_lines_per_source=4)

            contract = require_mapping(result["contract"])
            self.assertEqual("lean_only", contract["proof_authority"])
            self.assertEqual("no_artifact_no_upgrade", contract["claim_upgrade_policy"])
            source_hits = require_list(result["source_hits"])
            self.assertGreater(len(source_hits), 0)
            first_hit = require_mapping(source_hits[0])
            source = require_string(first_hit["source"])
            self.assertIn("Proofs/QMClosure/A.lean", source)
            self.assertEqual(16, len(require_string(first_hit["sha16"])))

    def test_rag_refreshes_stale_graph_on_load(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                "def changedBornFixture := True\n",
                encoding="utf-8",
            )

            index = load_fixture_index(root)
            result = index.retrieve("changedBornFixture", limit=3, max_lines_per_source=4)

            source_hits = require_list(result["source_hits"])
            self.assertGreater(len(source_hits), 0)
            first_hit = require_mapping(source_hits[0])
            lines = require_list(first_hit["lines"])
            self.assertIn("changedBornFixture", "\n".join(require_string(line) for line in lines))

    def test_rag_rejects_source_hash_mismatch_when_refresh_disabled(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
            (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                "def changed := True\n",
                encoding="utf-8",
            )

            with self.assertRaisesRegex(V8GraphQueryError, "source hash mismatch"):
                IdtRagIndex.load(root, graph_path, check_source_hashes=True, auto_refresh=False)

    def test_mcp_tools_list_exposes_idt_tools(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "tools/list",
                    "params": {},
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            tools = require_list(result["tools"])
            names = {require_string(require_mapping(tool)["name"]) for tool in tools}
            self.assertIn("idt_graph_search", names)
            self.assertIn("idt_rag_retrieve", names)
            self.assertIn("idt_research_context", names)
            self.assertIn("idt_claim_audit", names)
            self.assertIn("idt_missing_proof_artifacts", names)
            self.assertIn("idt_graph_diff", names)
            self.assertIn("idt_lean_build_target", names)
            self.assertIn("idt_run_check", names)
            self.assertIn("idt_guarded_replace", names)

    def test_mcp_rag_tool_returns_text_and_structured_content(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "rag-1",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_rag_retrieve",
                        "arguments": {"query": "localTomography", "limit": 2},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            content = require_list(result["content"])
            text = require_string(require_mapping(content[0])["text"])
            self.assertIn("Lean remains proof authority", text)
            structured = require_mapping(result["structuredContent"])
            self.assertEqual("localTomography", structured["query"])

    def test_claim_audit_flags_formal_proof_without_lean_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir), formal_proof_card=True)
            index = load_fixture_index(root)

            result = index.claim_audit()

            self.assertEqual(False, result["ok"])
            issues = require_list(result["issues"])
            issue_text = json.dumps(issues, sort_keys=True)
            self.assertIn("formal_proof residual", issue_text)
            self.assertIn("Lean artifact", issue_text)

    def test_missing_proof_artifacts_lists_nonformal_theory_targets(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))

            result = index.missing_proof_artifacts(limit=10)

            self.assertEqual("lean_only", result["proof_authority"])
            items = require_list(result["items"])
            item_text = json.dumps(items, sort_keys=True)
            self.assertIn("conditional_fixture_theorem", item_text)
            self.assertIn("open_fixture_obligation", item_text)

    def test_research_context_includes_audit_and_neighborhoods(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "context-1",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_research_context",
                        "arguments": {"query": "conditional_fixture_theorem", "depth": 1, "limit": 3},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            structured = require_mapping(result["structuredContent"])
            contract = require_mapping(structured["contract"])
            self.assertEqual("lean_only", contract["proof_authority"])
            self.assertIn("claim_audit", structured)
            self.assertGreater(len(require_list(structured["neighborhoods"])), 0)

    def test_mcp_refreshes_graph_during_tool_request(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            server = IdtMcpServer(load_fixture_index(root))
            (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                "def requestTimeGraphRefresh := True\n",
                encoding="utf-8",
            )

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "refresh-1",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_rag_retrieve",
                        "arguments": {"query": "requestTimeGraphRefresh", "limit": 2},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            content = require_list(result["content"])
            text = require_string(require_mapping(content[0])["text"])
            self.assertIn("requestTimeGraphRefresh", text)

    def test_graph_diff_reports_changed_live_graph(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
            baseline_path = root / "dist" / "baseline.json"
            shutil.copyfile(graph_path, baseline_path)
            (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                "def diffGraphRefresh := True\n",
                encoding="utf-8",
            )
            index = IdtRagIndex.load(root, graph_path)

            result = index.graph_diff(Path("dist/baseline.json"), limit=10)

            summary = require_mapping(result["summary"])
            self.assertGreater(require_int(summary["changed_nodes"]) + require_int(summary["added_nodes"]), 0)
            self.assertEqual("lean_only", result["proof_authority"])

    def test_run_check_validates_current_graph(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))

            result = index.run_check("graph_validate")

            self.assertEqual(True, result["ok"])
            self.assertEqual("check_result_is_not_formal_proof", result["proof_boundary"])

    def test_mcp_rejects_unsafe_lean_target(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "lean-bad",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_lean_build_target",
                        "arguments": {"target": "../bad"},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            error = require_mapping(response["error"])
            self.assertIn("unsafe Lean target", require_string(error["message"]))

    def test_guarded_replace_dry_run_does_not_write(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            source_path = root / "Proofs" / "QMClosure" / "A.lean"
            expected_sha16 = file_sha16(source_path)
            index = load_fixture_index(root)

            result = index.guarded_replace(
                Path("Proofs/QMClosure/A.lean"),
                expected_sha16,
                "def localTomography := True",
                "def localTomographyDryRun := True",
                dry_run=True,
            )

            self.assertEqual(True, result["ok"])
            self.assertEqual("dry_run", result["status"])
            self.assertIn("def localTomography := True", source_path.read_text(encoding="utf-8"))

    def test_guarded_replace_applies_under_hash_guard(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            source_path = root / "Proofs" / "QMClosure" / "A.lean"
            expected_sha16 = file_sha16(source_path)
            index = load_fixture_index(root)

            result = index.guarded_replace(
                Path("Proofs/QMClosure/A.lean"),
                expected_sha16,
                "def localTomography := True",
                "def localTomographyApplied := True",
                dry_run=False,
            )

            self.assertEqual(True, result["ok"])
            self.assertEqual("applied", result["status"])
            self.assertIn("def localTomographyApplied := True", source_path.read_text(encoding="utf-8"))

    def test_guarded_replace_rejects_hash_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            index = load_fixture_index(root)

            with self.assertRaisesRegex(IdtRagError, "file hash mismatch"):
                index.guarded_replace(
                    Path("Proofs/QMClosure/A.lean"),
                    "0000000000000000",
                    "def localTomography := True",
                    "def localTomographyApplied := True",
                    dry_run=False,
                )

    def test_guarded_replace_blocks_status_upgrade_token(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            source_path = root / "Proofs" / "QMClosure" / "A.lean"
            expected_sha16 = file_sha16(source_path)
            index = load_fixture_index(root)

            result = index.guarded_replace(
                Path("Proofs/QMClosure/A.lean"),
                expected_sha16,
                "def localTomography := True",
                "def localTomography := formal_proof",
                dry_run=False,
            )

            self.assertEqual(False, result["ok"])
            self.assertEqual("blocked_by_guard", result["status"])
            self.assertNotIn("formal_proof", source_path.read_text(encoding="utf-8"))

    def test_guarded_replace_rejects_generated_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
            expected_sha16 = file_sha16(graph_path)
            index = load_fixture_index(root)

            with self.assertRaisesRegex(IdtRagError, "generated or internal path"):
                index.guarded_replace(
                    Path("dist/idt-v8-ai-theory-graph.json"),
                    expected_sha16,
                    "idt-v8-ai-theory-graph",
                    "changed",
                    dry_run=True,
                )

    def test_parallel_refreshes_do_not_leave_partial_graph(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
            (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                "def concurrentGraphRefresh := True\n",
                encoding="utf-8",
            )

            def load_and_retrieve() -> int:
                index = IdtRagIndex.load(root, graph_path)
                result = index.retrieve("concurrentGraphRefresh", limit=1, max_lines_per_source=2)
                return len(require_list(result["source_hits"]))

            with ThreadPoolExecutor(max_workers=4) as executor:
                hit_counts = list(executor.map(lambda _: load_and_retrieve(), range(8)))

            self.assertTrue(all(count > 0 for count in hit_counts))
            graph_payload = graph_json_load_for_tests(graph_path)
            self.assertEqual("idt-v8-ai-theory-graph/1", graph_payload["schema"])
            self.assertTrue(lock_path_for(graph_path).is_file())

    def test_mcp_unknown_tool_returns_json_rpc_error(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": 2,
                    "method": "tools/call",
                    "params": {"name": "upgrade_claim_status", "arguments": {}},
                }
            )

            if response is None:
                raise AssertionError("expected response")
            error = require_mapping(response["error"])
            self.assertIn("unknown IDT MCP tool", require_string(error["message"]))

    def test_stdio_server_handles_multiple_json_rpc_lines(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))
            stdin = io.StringIO(
                "\n".join(
                    [
                        json.dumps({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}}),
                        json.dumps({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}}),
                    ]
                )
                + "\n"
            )
            stdout = io.StringIO()

            exit_code = serve(server, stdin, stdout)

            self.assertEqual(0, exit_code)
            lines = [json.loads(line) for line in stdout.getvalue().splitlines()]
            self.assertEqual([1, 2], [line["id"] for line in lines])

    def test_invalid_json_line_returns_parse_error(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = handle_line(server, "{")

            if response is None:
                raise AssertionError("expected response")
            error = require_mapping(response["error"])
            self.assertEqual(-32700, error["code"])


def write_fixture_repo(root: Path, formal_proof_card: bool = False) -> Path:
    proof_dir = root / "Proofs" / "QMClosure"
    proof_dir.mkdir(parents=True)
    (proof_dir / "A.lean").write_text(
        "\n".join(
            [
                "def claim_source_aliasing_boundary := True",
                "theorem born_readout_context : claim_source_aliasing_boundary := by",
                "  trivial",
                "def localTomography := True",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    manifest_path = root / "theory_verifier_manifest.json"
    manifest_path.write_text(
        json.dumps(fixture_manifest(formal_proof_card)),
        encoding="utf-8",
    )
    graph = build_v8_ai_theory_graph(
        repo_root=root,
        manifest_path=manifest_path,
        include_sources=True,
    )
    graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
    write_locked_graph_for_tests(graph_path, graph)
    return root


def fixture_manifest(formal_proof_card: bool) -> dict[str, object]:
    proof_status = "formal_proof" if formal_proof_card else "conditional_proof"
    return {
        "schema_version": "test",
        "theory_version": "v8.0.0",
        "symbols": {"born_readout_I": {"status": "target"}},
        "equations": [],
        "derivations": [],
        "forbidden_paths": [],
        "finite_gates": [],
        "qm_experiments": [],
        "qm_universal_patterns": [],
        "qm_core_proof_obligations": [
            {
                "id": "open_fixture_obligation",
                "status": "open",
                "statement": "Fixture obligation intentionally remains open.",
                "dependencies": [],
            }
        ],
        "theorem_cards": [
            {
                "id": "conditional_fixture_theorem",
                "statement": "Fixture theorem card used to test proof boundaries.",
                "role": "theorem",
                "assumptions": [],
                "dependencies": [],
                "proof_status": proof_status,
                "verifier": "",
                "known_failures": [],
                "physical_scope": "fixture only",
                "forbidden_claims": ["does_not_prove_QM"],
            }
        ],
    }


def load_fixture_index(root: Path) -> IdtRagIndex:
    return IdtRagIndex.load(root, root / "dist" / "idt-v8-ai-theory-graph.json")


def require_mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise AssertionError("expected mapping")
    return value


def require_list(value: object) -> list[object]:
    if not isinstance(value, list):
        raise AssertionError("expected list")
    return value


def require_string(value: object) -> str:
    if not isinstance(value, str):
        raise AssertionError("expected string")
    return value


def require_int(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise AssertionError("expected integer")
    return value


def file_sha16(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


if __name__ == "__main__":
    unittest.main()
