from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import Mock, patch

import scripts.build_ai_theory_graph as graph_builder
from scripts.build_ai_theory_graph import DEFAULT_SOURCE_GLOBS, build_v8_ai_theory_graph
from theory_verifier.ai_theory_graph import (
    V8GraphQueryError,
    theory_graph_from_payload,
    validate_source_file_hashes,
)
from theory_verifier.idt_mcp_server import IdtMcpServer, handle_line, serve
from theory_verifier.idt_rag import (
    CheckCommand,
    IdtRagError,
    IdtRagIndex,
    failure_diagnostics,
    graph_json_load_for_tests,
    guarded_edit_diagnostics,
    guarded_edit_issues,
    guarded_edit_text,
    lock_path_for,
    run_command_evidence,
    stop_command,
    write_locked_graph_for_tests,
)


def completed_command(returncode: int, stdout: str, stderr: str) -> Mock:
    process = Mock(spec=subprocess.Popen)
    process.returncode = returncode
    process.pid = 4321
    process.communicate.return_value = (stdout, stderr)
    process.stdout = Mock()
    process.stderr = Mock()
    return process


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
            self.assertIn("idt_leandojo_status", names)
            self.assertIn("idt_leandojo_list_goals", names)
            self.assertIn("idt_leandojo_record_attempt", names)
            self.assertIn("idt_guarded_replace", names)
            self.assertIn("idt_reload_code", names)

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

    def test_research_context_token_union_fallback_finds_multiple_aliases(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "context-token-union",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_research_context",
                        "arguments": {"query": "born_readout_context localTomography", "depth": 0, "limit": 10},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            structured = require_mapping(result["structuredContent"])
            matches = require_mapping(structured["matches"])
            node_rows = require_list(matches["nodes"])
            node_text = json.dumps(node_rows, sort_keys=True)
            self.assertIn("born_readout_context", node_text)
            self.assertIn("localTomography", node_text)
            self.assertGreaterEqual(require_int(matches["count"]), 2)

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

    def test_mcp_refreshes_graph_when_new_source_file_is_added(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            server = IdtMcpServer(load_fixture_index(root))
            (root / "Proofs" / "QMClosure" / "Added.lean").write_text(
                "theorem newlyAddedSource : True := by trivial\n",
                encoding="utf-8",
            )

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "new-source",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_graph_search",
                        "arguments": {"query": "newlyAddedSource", "limit": 2},
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            structured = require_mapping(result["structuredContent"])
            self.assertEqual(1, structured["count"])
            nodes = require_list(structured["nodes"])
            self.assertIn("newlyAddedSource", json.dumps(nodes))

    def test_rag_rejects_added_source_when_refresh_disabled(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            (root / "Proofs" / "QMClosure" / "Added.lean").write_text(
                "def newlyAddedSource := True\n", encoding="utf-8"
            )

            with self.assertRaisesRegex(V8GraphQueryError, "source inventory mismatch"):
                IdtRagIndex.load(root, check_source_hashes=True, auto_refresh=False)

    def test_rag_refreshes_legacy_graph_without_source_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
            graph = graph_json_load_for_tests(graph_path)
            require_mapping(graph["coverage"]).pop("source_inventory")
            write_locked_graph_for_tests(graph_path, graph)

            index = load_fixture_index(root)

            self.assertIn("source_inventory", index.graph.coverage)

    def test_auto_refresh_does_not_expand_custom_or_focused_graphs(self) -> None:
        for mode in ("custom", "focused", "disabled"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as raw_dir:
                root = write_fixture_repo(Path(raw_dir))
                graph = build_v8_ai_theory_graph(
                    repo_root=root,
                    source_globs=("Proofs/QMClosure/A.lean",) if mode == "custom" else DEFAULT_SOURCE_GLOBS,
                    focus="localTomography" if mode == "focused" else None,
                    include_sources=mode != "disabled",
                )
                graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
                write_locked_graph_for_tests(graph_path, graph)
                original = graph_path.read_bytes()
                if mode == "disabled":
                    # A missing inventory must not turn a disabled source layer on.
                    require_mapping(graph["coverage"]).pop("source_inventory")
                    write_locked_graph_for_tests(graph_path, graph)
                    original = graph_path.read_bytes()
                else:
                    (root / "Proofs" / "QMClosure" / "A.lean").write_text(
                        "def changed := True\n", encoding="utf-8"
                    )

                with self.assertRaisesRegex(IdtRagError, "custom or partial graph scope"):
                    load_fixture_index(root)

                self.assertEqual(original, graph_path.read_bytes())

    def test_legacy_custom_path_requires_explicit_graph_options(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            graph = build_v8_ai_theory_graph(
                repo_root=root, source_globs=("Proofs/QMClosure/A.lean",)
            )
            require_mapping(graph["coverage"]).pop("source_inventory")
            graph_path = root / "dist" / "custom-legacy-graph.json"
            write_locked_graph_for_tests(graph_path, graph)
            original = graph_path.read_bytes()

            with self.assertRaisesRegex(IdtRagError, "unknown source options"):
                IdtRagIndex.load(root, graph_path)

            self.assertEqual(original, graph_path.read_bytes())

    def test_source_inventory_respects_selected_scope(self) -> None:
        for mode in ("default", "custom", "focused", "disabled"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as raw_dir:
                root = write_fixture_repo(Path(raw_dir))
                graph = theory_graph_from_payload(build_v8_ai_theory_graph(
                    repo_root=root,
                    source_globs=("Proofs/QMClosure/A.lean",) if mode == "custom" else DEFAULT_SOURCE_GLOBS,
                    focus="localTomography" if mode == "focused" else None,
                    include_sources=mode != "disabled",
                ))
                validate_source_file_hashes(graph, root, require_inventory=True)
                for excluded in ("unrelated.txt", ".lake/Proofs/B.lean", ".git/B.lean", "archive/B.lean"):
                    path = root / excluded
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("def outsideSelectedScope := True\n", encoding="utf-8")
                validate_source_file_hashes(graph, root, require_inventory=True)
                (root / "Proofs" / "QMClosure" / "B.lean").write_text(
                    "def newlyAddedSource := True\n", encoding="utf-8"
                )

                if mode in {"custom", "disabled"}:
                    validate_source_file_hashes(graph, root, require_inventory=True)
                else:
                    with self.assertRaisesRegex(V8GraphQueryError, "source inventory mismatch"):
                        validate_source_file_hashes(graph, root, require_inventory=True)

    def test_mcp_reload_code_tool_schedules_in_process_reload(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "reload-code-1",
                    "method": "tools/call",
                    "params": {"name": "idt_reload_code", "arguments": {}},
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            structured = require_mapping(result["structuredContent"])
            self.assertEqual(True, structured["ok"])
            self.assertEqual("reload_scheduled_after_response", structured["status"])
            self.assertEqual("reload_is_tooling_only_not_proof_evidence", structured["proof_boundary"])
            self.assertEqual(True, server.reload_code_requested)

    def test_reload_refreshes_cached_builder_before_rebuilding_legacy_graph(self) -> None:
        process = subprocess.run(
            [sys.executable, "-c", "from tests.test_idt_mcp_rag import exercise_stale_builder_reload; exercise_stale_builder_reload()"],
            cwd=Path(__file__).resolve().parents[1],
            capture_output=True,
            text=True,
            check=False,
            timeout=20,
        )

        self.assertEqual(0, process.returncode, process.stderr)

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

    def test_mcp_lean_failure_retains_early_errors_before_warning_tail(self) -> None:
        stdout_error = "Proofs/A.lean:4:7: error: type mismatch"
        stderr_error = "error: Proofs/B.lean:9:2: tactic failed"
        warnings = "\n".join(f"Proofs/A.lean:{line}:1: warning: unused variable" for line in range(100))
        stdout = f"{stdout_error}\n  actual type\n  expected type\n{warnings}"
        stderr = f"{stderr_error}\n  remaining goal\n{warnings}"
        with tempfile.TemporaryDirectory() as raw_dir:
            server = IdtMcpServer(load_fixture_index(write_fixture_repo(Path(raw_dir))))
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(1, stdout, stderr),
            ):
                response = server.handle_payload({
                    "jsonrpc": "2.0",
                    "id": "lean-failed",
                    "method": "tools/call",
                    "params": {"name": "idt_lean_build_target", "arguments": {"target": "Fixture"}},
                })

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            evidence = require_mapping(result["structuredContent"])
            self.assertEqual(False, evidence["ok"])
            self.assertEqual(1, evidence["exit_code"])
            self.assertNotIn(stdout_error, require_string(evidence["stdout_tail"]))
            self.assertNotIn(stderr_error, require_string(evidence["stderr_tail"]))
            diagnostics = [require_mapping(item) for item in require_list(evidence["diagnostics"])]
            self.assertEqual(["stdout", "stderr"], [item["stream"] for item in diagnostics])
            self.assertEqual([1, 1], [item["line"] for item in diagnostics])
            self.assertIn("expected type", require_string(diagnostics[0]["excerpt"]))
            self.assertIn(stderr_error, require_string(diagnostics[1]["excerpt"]))
            self.assertEqual(2, evidence["diagnostic_count"])
            self.assertEqual(False, evidence["diagnostics_truncated"])
            text = require_string(require_mapping(require_list(result["content"])[0])["text"])
            self.assertIn(stdout_error, text)
            self.assertIn(stderr_error, text)
            handle = require_mapping(evidence["full_log"])
            self.assertIn(require_string(handle["path"]), text)
            self.assertIn(require_string(handle["sha256"]), text)
            self.assertIn(f"bytes={handle['bytes']}", text)

    def test_lean_failure_diagnostics_bound_count_and_excerpt_length(self) -> None:
        output = "\n".join(f"Proofs/A.lean:{line}:1: error: {'x' * 1000}" for line in range(12))
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(1, output, output),
            ):
                evidence = index.lean_build_target("Fixture")

            diagnostics = [require_mapping(item) for item in require_list(evidence["diagnostics"])]
            self.assertEqual(8, len(diagnostics))
            self.assertEqual(24, evidence["diagnostic_count"])
            self.assertEqual(True, evidence["diagnostics_truncated"])
            self.assertEqual(["stdout"] * 4 + ["stderr"] * 4, [item["stream"] for item in diagnostics])
            self.assertTrue(all(len(require_string(item["excerpt"])) <= 800 for item in diagnostics))

    def test_command_log_retains_all_errors_after_compact_diagnostics_truncate(self) -> None:
        stdout = "\n".join(f"Proofs/A.lean:{line}:1: error: σ{line} {'x' * 1000}" for line in range(30))
        stderr = "\n".join(f"Proofs/B.lean:{line}:1: error: stderr {line}" for line in range(19))
        command = CheckCommand("synthetic_failure", ("unused", "Fixture"), 1, "mock failed check")
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(1, stdout, stderr),
            ) as runner:
                evidence = run_command_evidence(root, command)
            handle = require_mapping(evidence["full_log"])
            artifact_path = Path(require_string(handle["path"]))
            artifact_bytes = artifact_path.read_bytes()
            artifact = require_mapping(json.loads(artifact_bytes))

            self.assertEqual((root / ".idt" / "check-logs").resolve(), artifact_path.parent)
            self.assertEqual("idt-v8-check-log/1", artifact["schema"])
            self.assertEqual(stdout, artifact["stdout"])
            self.assertEqual(stderr, artifact["stderr"])
            self.assertEqual(command.name, artifact["name"])
            self.assertEqual(command.description, artifact["description"])
            self.assertEqual(list(command.command), artifact["command"])
            self.assertEqual(1, artifact["exit_code"])
            self.assertEqual(evidence["proof_boundary"], artifact["proof_boundary"])
            self.assertEqual(len(artifact_bytes), handle["bytes"])
            self.assertEqual(hashlib.sha256(artifact_bytes).hexdigest(), handle["sha256"])
            self.assertEqual(False, evidence["ok"])
            self.assertEqual(1, evidence["exit_code"])
            self.assertEqual(list(command.command), evidence["command"])
            self.assertEqual("idt-v8-check-evidence/1", evidence["schema"])
            self.assertEqual(49, evidence["diagnostic_count"])
            self.assertEqual(True, evidence["diagnostics_truncated"])
            self.assertEqual(8, len(require_list(evidence["diagnostics"])))
            self.assertNotEqual(stdout, evidence["stdout_tail"])
            runner.assert_called_once()

    def test_command_log_captures_complete_success_output_and_empty_streams(self) -> None:
        command = CheckCommand("synthetic_success", ("unused",), 1, "mock successful check")
        for stdout, stderr in (("α\ncompleted without final newline", "stderr\n"), ("", "")):
            with self.subTest(stdout=stdout, stderr=stderr), tempfile.TemporaryDirectory() as raw_dir:
                with patch(
                    "theory_verifier.idt_rag.subprocess.Popen",
                    return_value=completed_command(0, stdout, stderr),
                ):
                    evidence = run_command_evidence(Path(raw_dir), command)
                handle = require_mapping(evidence["full_log"])
                artifact_bytes = Path(require_string(handle["path"])).read_bytes()
                artifact = require_mapping(json.loads(artifact_bytes))

                self.assertEqual(stdout, artifact["stdout"])
                self.assertEqual(stderr, artifact["stderr"])
                self.assertEqual(0, artifact["exit_code"])
                self.assertEqual(len(artifact_bytes), handle["bytes"])
                self.assertEqual(hashlib.sha256(artifact_bytes).hexdigest(), handle["sha256"])
                self.assertEqual(True, evidence["ok"])
                self.assertEqual(0, evidence["exit_code"])
                self.assertEqual([], evidence["diagnostics"])
                self.assertEqual(0, evidence["diagnostic_count"])
                self.assertEqual(False, evidence["diagnostics_truncated"])

    def test_command_log_retains_drained_timeout_output(self) -> None:
        command = CheckCommand("synthetic_timeout", ("unused",), 1, "mock timeout")
        stdout = b"error: interrupted UTF-8 \xe2"
        stderr = b"stderr before timeout\n"
        process = completed_command(-9, "", "")
        process.communicate.side_effect = [
            subprocess.TimeoutExpired(command.command, 1, output=stdout, stderr=stderr),
            (stdout, stderr),
        ]
        with tempfile.TemporaryDirectory() as raw_dir:
            with patch("theory_verifier.idt_rag.subprocess.Popen", return_value=process), patch(
                "theory_verifier.idt_rag.os.killpg",
            ):
                evidence = run_command_evidence(Path(raw_dir), command)
            handle = require_mapping(evidence["full_log"])
            artifact = require_mapping(json.loads(Path(require_string(handle["path"])).read_bytes()))

            self.assertEqual(stdout.decode("utf-8", errors="replace"), artifact["stdout"])
            self.assertEqual(stderr.decode("utf-8", errors="replace"), artifact["stderr"])
            self.assertEqual(-1, artifact["exit_code"])
            self.assertEqual(False, evidence["ok"])
            self.assertEqual(-1, evidence["exit_code"])
            self.assertEqual(1, evidence["diagnostic_count"])
            self.assertEqual(artifact["proof_boundary"], evidence["proof_boundary"])

    def test_command_logs_use_unique_paths_and_preserve_previous_capture(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock check")
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            processes = [completed_command(0, "first", ""), completed_command(0, "second", "")]
            with patch("theory_verifier.idt_rag.subprocess.Popen", side_effect=processes):
                first = run_command_evidence(root, command)
                second = run_command_evidence(root, command)
            first_path = Path(require_string(require_mapping(first["full_log"])["path"]))
            second_path = Path(require_string(require_mapping(second["full_log"])["path"]))

            self.assertNotEqual(first_path, second_path)
            self.assertEqual("first", require_mapping(json.loads(first_path.read_bytes()))["stdout"])
            self.assertEqual("second", require_mapping(json.loads(second_path.read_bytes()))["stdout"])
            if os.name == "posix":
                self.assertEqual(0, first_path.stat().st_mode & 0o077)
                self.assertEqual(0, second_path.stat().st_mode & 0o077)

    def test_command_log_write_failure_keeps_original_check_result(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock check")
        with tempfile.TemporaryDirectory() as raw_dir:
            for returncode in (0, 1):
                with self.subTest(returncode=returncode), patch(
                    "theory_verifier.idt_rag.subprocess.Popen",
                    return_value=completed_command(returncode, "captured stdout", "captured stderr"),
                ), patch(
                    "theory_verifier.idt_rag.tempfile.NamedTemporaryFile",
                    side_effect=OSError("synthetic disk failure"),
                ):
                    evidence = run_command_evidence(Path(raw_dir), command)

                self.assertEqual(returncode == 0, evidence["ok"])
                self.assertEqual(returncode, evidence["exit_code"])
                self.assertEqual("captured stdout", evidence["stdout_tail"])
                self.assertEqual("captured stderr", evidence["stderr_tail"])
                self.assertNotIn("full_log", evidence)
                self.assertIn("synthetic disk failure", require_string(evidence["full_log_error"]))

    def test_command_log_error_message_is_bounded(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock check")
        with tempfile.TemporaryDirectory() as raw_dir:
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(0, "captured stdout", "captured stderr"),
            ), patch(
                "theory_verifier.idt_rag.tempfile.NamedTemporaryFile",
                side_effect=OSError("x" * 25000),
            ):
                evidence = run_command_evidence(Path(raw_dir), command)

            error_message = require_string(evidence["full_log_error"])
            self.assertEqual(400, len(error_message))
            self.assertTrue(error_message.startswith("could not persist captured output: "))
            self.assertNotIn("full_log", evidence)
            self.assertEqual(True, evidence["ok"])
            self.assertEqual(0, evidence["exit_code"])
            self.assertEqual("captured stdout", evidence["stdout_tail"])
            self.assertEqual("captured stderr", evidence["stderr_tail"])

    def test_command_log_fsync_failure_removes_incomplete_artifact(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock check")
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(0, "captured stdout", ""),
            ), patch("theory_verifier.idt_rag.os.fsync", side_effect=OSError("synthetic fsync failure")):
                evidence = run_command_evidence(root, command)

            self.assertEqual(True, evidence["ok"])
            self.assertNotIn("full_log", evidence)
            self.assertIn("synthetic fsync failure", require_string(evidence["full_log_error"]))
            self.assertEqual([], list((root / ".idt" / "check-logs").iterdir()))

    def test_lean_success_does_not_become_failure_from_error_like_output(self) -> None:
        output = "Proofs/A.lean:1:1: error: quoted diagnostic example"
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(0, output, ""),
            ):
                evidence = index.lean_build_target("Fixture")

            self.assertEqual(True, evidence["ok"])
            self.assertEqual(0, evidence["exit_code"])
            self.assertEqual(output, evidence["stdout_tail"])
            self.assertEqual([], evidence["diagnostics"])
            self.assertEqual(0, evidence["diagnostic_count"])
            self.assertEqual(False, evidence["diagnostics_truncated"])

    def test_lean_long_error_context_retains_location_and_trailing_goal(self) -> None:
        header = "error: Proofs/FixedReferenceBalanceBridge.lean:42:7: unsolved goals"
        context = "\n".join(f"h{line} : {'LongVariableContext ' * 6}" for line in range(40))
        goal = "⊢ fixedReferenceBalance left right = normalizedBalance left right"
        warnings = "\n".join(f"Proofs/A.lean:{line}:1: warning: unused variable" for line in range(100))
        output = f"{header}\ncase h.e'_9\nV : Type*\n{context}\n{goal}\n{warnings}"
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))
            with patch(
                "theory_verifier.idt_rag.subprocess.Popen",
                return_value=completed_command(1, output, ""),
            ):
                evidence = index.lean_build_target("Fixture")

            diagnostics = require_list(evidence["diagnostics"])
            self.assertEqual(1, len(diagnostics))
            excerpt = require_string(require_mapping(diagnostics[0])["excerpt"])
            self.assertTrue(excerpt.startswith(header))
            self.assertTrue(excerpt.endswith(goal))
            self.assertIn("\n[...]\n", excerpt)
            self.assertEqual(800, len(excerpt))
            self.assertNotIn("warning:", excerpt)
            self.assertNotIn(goal, require_string(evidence["stdout_tail"]))
            self.assertEqual(True, evidence["diagnostics_truncated"])
            self.assertEqual(False, evidence["ok"])

    def test_lean_error_block_stops_at_next_diagnostic_or_build_header(self) -> None:
        block = "error: Proofs/A.lean:1:1: unsolved goals\ncase h\nV : Type*\nx : V\n⊢ x = x"
        for boundary in (
            "Proofs/A.lean:2:1: warning: unused variable",
            "warning: Proofs/A.lean:2:1: unused variable",
            "Proofs/A.lean:2:1: error: another error",
            "error: Proofs/A.lean:2:1: another error",
            "info: Proofs/A.lean:2:1: another message",
            "✔ [2/3] Built Another",
            "✖ [2/3] Building Another",
            "⚠ [2/3] Replayed Another",
            "ℹ [2/3] Replayed Another",
            "[2/3] Building Another",
            "Build completed successfully.",
            "Build failed.",
            "Some required builds logged failures:",
            "Some required targets logged failures:",
        ):
            with self.subTest(boundary=boundary):
                evidence = failure_diagnostics(f"{block}\n{boundary}\nunrelated output", "")
                diagnostics = require_list(evidence["diagnostics"])
                excerpt = require_string(require_mapping(diagnostics[0])["excerpt"])
                self.assertEqual(block, excerpt)
                self.assertEqual(False, evidence["diagnostics_truncated"])

    def test_lean_letterlike_identifier_is_not_a_build_header(self) -> None:
        block = "error: Proofs/A.lean:1:1: unsolved goals\nℹ : ℝ\n⊢ ℹ = 0"

        evidence = failure_diagnostics(block, "")

        diagnostics = require_list(evidence["diagnostics"])
        self.assertEqual(1, len(diagnostics))
        self.assertEqual(block, require_mapping(diagnostics[0])["excerpt"])
        self.assertEqual(False, evidence["diagnostics_truncated"])

    def test_lean_timeout_preserves_early_error_diagnostics(self) -> None:
        output = "error: Proofs/A.lean:1:1: tactic failed\n" + "warning: later output\n" * 100
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))
            for captured_output in (output, output.encode("utf-8")):
                process = completed_command(-9, "", "")
                process.communicate.side_effect = [
                    subprocess.TimeoutExpired(("lake", "build", "Fixture"), 60, output=captured_output),
                    (captured_output, ""),
                ]
                with self.subTest(output_type=type(captured_output).__name__), patch(
                    "theory_verifier.idt_rag.subprocess.Popen", return_value=process,
                ), patch("theory_verifier.idt_rag.os.killpg"):
                    evidence = index.lean_build_target("Fixture")

                self.assertEqual(False, evidence["ok"])
                self.assertEqual(-1, evidence["exit_code"])
                self.assertEqual("timeout expired", evidence["stderr_tail"])
                diagnostics = require_list(evidence["diagnostics"])
                self.assertEqual(1, len(diagnostics))
                self.assertIn("tactic failed", require_string(require_mapping(diagnostics[0])["excerpt"]))

    @unittest.skipUnless(os.name == "posix", "requires POSIX process groups")
    def test_command_timeout_kills_inherited_child_and_retains_output(self) -> None:
        child_script = (
            "import os, sys, time; from pathlib import Path; "
            "Path(sys.argv[1]).write_text(str(os.getpid())); time.sleep(30)"
        )
        parent_script = (
            "import os, subprocess, sys, time\n"
            "from pathlib import Path\n"
            "Path(sys.argv[1]).write_text(str(os.getpid()))\n"
            "subprocess.Popen([sys.executable, '-c', sys.argv[3], sys.argv[2]])\n"
            "while not Path(sys.argv[2]).exists(): time.sleep(0.01)\n"
            "print('error: Fixture.lean:1:1: flushed stdout', flush=True)\n"
            "print('error: Fixture.lean:2:1: flushed stderr', file=sys.stderr, flush=True)\n"
            "time.sleep(30)\n"
        )
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            parent_path = root / "parent.pid"
            child_path = root / "child.pid"
            command = CheckCommand(
                "synthetic_timeout",
                (sys.executable, "-c", parent_script, str(parent_path), str(child_path), child_script),
                2,
                "Python parent and inherited-pipe child",
            )
            started = time.monotonic()
            try:
                evidence = run_command_evidence(root, command)
                self.assertLess(time.monotonic() - started, 6)
                self.assertEqual(False, evidence["ok"])
                self.assertEqual(-1, evidence["exit_code"])
                self.assertIn("flushed stdout", require_string(evidence["stdout_tail"]))
                self.assertIn("flushed stderr", require_string(evidence["stderr_tail"]))
                self.assertEqual(2, evidence["diagnostic_count"])
                child_pid = int(child_path.read_text())
                for _ in range(50):
                    status = subprocess.run(
                        ("ps", "-p", str(child_pid), "-o", "stat="),
                        capture_output=True, text=True, check=False, timeout=1,
                    ).stdout.strip()
                    if not status or status.startswith("Z"):
                        break
                    time.sleep(0.02)
                else:
                    self.fail("synthetic child is still running after timeout")
            finally:
                for pid_path in (child_path, parent_path):
                    if pid_path.exists():
                        with contextlib.suppress(ProcessLookupError):
                            os.kill(int(pid_path.read_text()), signal.SIGKILL)

    def test_timeout_preserves_incomplete_utf8_diagnostic(self) -> None:
        script = (
            r"import sys, time; sys.stdout.buffer.write(b'error: interrupted UTF-8 \xe2'); "
            "sys.stdout.buffer.flush(); time.sleep(30)"
        )
        command = CheckCommand("incomplete_utf8", (sys.executable, "-c", script), 1, "partial UTF-8 timeout")
        evidence = run_command_evidence(Path.cwd(), command)
        self.assertEqual(False, evidence["ok"])
        self.assertEqual(-1, evidence["exit_code"])
        self.assertIn("error: interrupted UTF-8 \ufffd", require_string(evidence["stdout_tail"]))
        self.assertEqual(1, evidence["diagnostic_count"])

    def test_non_posix_drain_timeout_leaves_reader_owned_streams_open(self) -> None:
        root = Path.cwd()
        command = CheckCommand("synthetic", ("unused",), 1, "mock command")
        process = completed_command(-9, "", "")
        output = b"error: inherited pipe remains open"
        process.communicate.side_effect = [
            subprocess.TimeoutExpired(command.command, 1, output=output),
            subprocess.TimeoutExpired(command.command, 1, output=output),
        ]
        for stream in (process.stdout, process.stderr):
            stream.close.side_effect = AssertionError("reader-owned close may block")
        with patch("theory_verifier.idt_rag.os.name", "nt"), patch(
            "theory_verifier.idt_rag.subprocess.Popen", return_value=process,
        ):
            evidence = run_command_evidence(root, command)
        self.assertEqual(-1, evidence["exit_code"])
        self.assertEqual(1, evidence["diagnostic_count"])
        self.assertEqual(2, process.kill.call_count)
        process.wait.assert_called_once_with(timeout=1)
        self.assertEqual([1, 1], [call.kwargs["timeout"] for call in process.communicate.call_args_list])
        process.stdout.close.assert_not_called()
        process.stderr.close.assert_not_called()

    def test_command_exception_preserves_original_during_cleanup(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock command")
        for error in (KeyboardInterrupt(), RuntimeError("execution failed")):
            for cleanup_error in (None, RuntimeError("cleanup failed")):
                process = completed_command(-9, "", "")
                process.communicate.side_effect = [error, cleanup_error if cleanup_error else ("", "")]
                with self.subTest(error=type(error).__name__, cleanup_error=cleanup_error), patch(
                    "theory_verifier.idt_rag.subprocess.Popen", return_value=process,
                ), patch("theory_verifier.idt_rag.os.killpg") as kill_group, self.assertRaises(type(error)) as caught:
                    run_command_evidence(Path.cwd(), command)
                self.assertIs(error, caught.exception)
                kill_group.assert_called_once_with(process.pid, signal.SIGKILL)
                self.assertEqual(1, process.communicate.call_args.kwargs["timeout"])

    def test_timeout_drain_remains_bounded_when_pipe_stays_open(self) -> None:
        command = CheckCommand("synthetic", ("unused",), 1, "mock command")
        process = completed_command(-9, "", "")
        output = b"error: Fixture.lean:1:1: retained output"
        process.communicate.side_effect = [
            subprocess.TimeoutExpired(command.command, 1, output=output),
            subprocess.TimeoutExpired(command.command, 1, output=output),
        ]
        with patch("theory_verifier.idt_rag.subprocess.Popen", return_value=process), patch(
            "theory_verifier.idt_rag.os.killpg",
        ):
            evidence = run_command_evidence(Path.cwd(), command)
        self.assertEqual(-1, evidence["exit_code"])
        self.assertEqual(1, evidence["diagnostic_count"])
        self.assertIn("retained output", require_string(evidence["stdout_tail"]))
        process.kill.assert_called_once_with()
        process.wait.assert_called_once_with(timeout=1)
        process.stdout.close.assert_called_once_with()
        process.stderr.close.assert_called_once_with()

    def test_cleanup_reports_bounded_parent_reap_failure(self) -> None:
        process = completed_command(-9, "", "")
        process.communicate.side_effect = subprocess.TimeoutExpired(("unused",), 1)
        process.wait.side_effect = subprocess.TimeoutExpired(("unused",), 1)
        with patch("theory_verifier.idt_rag.os.killpg"), self.assertRaisesRegex(
            IdtRagError, "did not exit after forced cleanup",
        ):
            stop_command(process)
        process.wait.assert_called_once_with(timeout=1)
        process.stdout.close.assert_called_once_with()
        process.stderr.close.assert_called_once_with()

    def test_non_posix_cleanup_kills_immediate_child(self) -> None:
        process = completed_command(-9, "", "")
        with patch("theory_verifier.idt_rag.os.name", "nt"), patch(
            "theory_verifier.idt_rag.os.killpg",
        ) as kill_group:
            self.assertEqual(("", ""), stop_command(process))
        kill_group.assert_not_called()
        process.kill.assert_called_once_with()
        process.communicate.assert_called_once_with(timeout=1)

    def test_leandojo_status_is_optional_and_boundary_limited(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))

            result = index.leandojo_status()

            self.assertEqual("lean_only", result["proof_authority"])
            self.assertEqual("no_artifact_no_upgrade", result["claim_upgrade_policy"])
            packages = require_list(result["packages"])
            package_text = json.dumps(packages, sort_keys=True)
            self.assertIn("lean-dojo-v2", package_text)

    def test_leandojo_goal_candidates_lists_context_only_goals(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))

            result = index.leandojo_goal_candidates("born_readout_context", limit=10)

            self.assertEqual("lean_only", result["proof_authority"])
            items = require_list(result["items"])
            item_text = json.dumps(items, sort_keys=True)
            self.assertIn("born_readout_context", item_text)
            self.assertIn("candidate_goal_context_only", item_text)

    def test_mcp_leandojo_record_attempt_writes_attempt_log_without_manifest_change(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = write_fixture_repo(Path(raw_dir))
            manifest_before = (root / "theory_verifier_manifest.json").read_text(encoding="utf-8")
            server = IdtMcpServer(load_fixture_index(root))

            response = server.handle_payload(
                {
                    "jsonrpc": "2.0",
                    "id": "leandojo-attempt-1",
                    "method": "tools/call",
                    "params": {
                        "name": "idt_leandojo_record_attempt",
                        "arguments": {
                            "goal": "born_readout_context",
                            "status": "failed",
                            "summary": "Fixture attempt failed before proof search.",
                            "artifact_paths": ["Proofs/QMClosure/A.lean"],
                        },
                    },
                }
            )

            if response is None:
                raise AssertionError("expected response")
            result = require_mapping(response["result"])
            structured = require_mapping(result["structuredContent"])
            self.assertEqual(True, structured["ok"])
            self.assertEqual(manifest_before, (root / "theory_verifier_manifest.json").read_text(encoding="utf-8"))
            attempt_path = root / ".idt" / "proof_attempts" / "leandojo_attempts.jsonl"
            attempt_text = attempt_path.read_text(encoding="utf-8")
            self.assertIn("attempt_log_is_not_claim_status", attempt_text)
            self.assertIn("born_readout_context", attempt_text)

    def test_leandojo_record_attempt_rejects_unknown_status(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            index = load_fixture_index(write_fixture_repo(Path(raw_dir)))

            with self.assertRaisesRegex(IdtRagError, "status must be one of"):
                index.record_leandojo_attempt(
                    "born_readout_context",
                    "formal_proof",
                    "Do not allow claim-status terms as attempt status.",
                    (),
                )

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

    def test_guarded_replace_explains_negated_and_caveated_prose_without_writing(self) -> None:
        cases = (
            ("Physical availability remains supplied, not derived.", "derived"),
            ("Any proved equivalence would be conditional on the supplied event laws.", "proved"),
        )
        for new_text, token in cases:
            for dry_run in (True, False):
                with self.subTest(text=new_text, dry_run=dry_run), tempfile.TemporaryDirectory() as raw_dir:
                    root = write_fixture_repo(Path(raw_dir))
                    source_path = root / "Proofs" / "QMClosure" / "A.lean"
                    original_bytes = source_path.read_bytes()
                    expected_sha16 = file_sha16(source_path)
                    server = IdtMcpServer(load_fixture_index(root))

                    response = server.handle_payload(
                        {
                            "jsonrpc": "2.0",
                            "id": "lexical-caveat",
                            "method": "tools/call",
                            "params": {
                                "name": "idt_guarded_replace",
                                "arguments": {
                                    "file_path": "Proofs/QMClosure/A.lean",
                                    "expected_sha16": expected_sha16,
                                    "old_text": "def localTomography := True",
                                    "new_text": new_text,
                                    "dry_run": dry_run,
                                },
                            },
                        }
                    )

                    if response is None:
                        raise AssertionError("expected response")
                    tool_result = require_mapping(response["result"])
                    result = require_mapping(tool_result["structuredContent"])
                    self.assertEqual(False, result["ok"])
                    self.assertEqual("blocked_by_guard", result["status"])
                    self.assertEqual([f"forbidden status upgrade token introduced: {token}"], result["issues"])
                    self.assertEqual(expected_sha16, result["old_sha16"])
                    self.assertEqual(expected_sha16, result["new_sha16"])
                    self.assertEqual(original_bytes, source_path.read_bytes())
                    self.assertEqual(expected_sha16, file_sha16(source_path))
                    diagnostics = require_list(result["diagnostics"])
                    self.assertEqual(1, len(diagnostics))
                    diagnostic = require_mapping(diagnostics[0])
                    self.assertEqual("lexical_token_count_increase", diagnostic["kind"])
                    self.assertEqual(token, diagnostic["token"])
                    self.assertEqual(0, diagnostic["original_count"])
                    self.assertEqual(1, diagnostic["updated_count"])
                    self.assertEqual(1, diagnostic["introduced_count"])
                    self.assertEqual(False, diagnostic["semantic_status_promotion_inferred"])
                    self.assertEqual("updated_file_occurrences_not_attributed", diagnostic["occurrences_scope"])
                    self.assertEqual(False, diagnostic["locations_truncated"])
                    location = require_mapping(require_list(diagnostic["locations"])[0])
                    self.assertEqual(4, location["line"])
                    self.assertEqual(new_text.index(token) + 1, location["column"])
                    self.assertEqual(new_text, location["context"])
                    self.assertEqual(1, location["context_column"])
                    self.assertEqual(False, location["context_truncated"])
                    content = require_mapping(require_list(tool_result["content"])[0])
                    text = require_string(content["text"])
                    self.assertIn("Conservative lexical guard; semantic status promotion not inferred.", text)
                    self.assertIn(f"token={token}; introduced_count=1; counts=0->1", text)
                    self.assertIn(f"updated file line 4, column {new_text.index(token) + 1}", text)
                    self.assertIn(new_text, text)

    def test_guarded_replace_keeps_real_promotions_and_overclaims_blocked(self) -> None:
        cases = (
            ("formal_proof", ["forbidden status upgrade token introduced: formal_proof"]),
            ("derived", ["forbidden status upgrade token introduced: derived"]),
            ("proved", ["forbidden status upgrade token introduced: proved"]),
            (
                "QM is proved",
                [
                    "forbidden status upgrade token introduced: proved",
                    "forbidden overclaim introduced: QM is proved",
                ],
            ),
        )
        for new_text, expected_issues in cases:
            for dry_run in (True, False):
                with self.subTest(text=new_text, dry_run=dry_run), tempfile.TemporaryDirectory() as raw_dir:
                    root = write_fixture_repo(Path(raw_dir))
                    source_path = root / "Proofs" / "QMClosure" / "A.lean"
                    original_bytes = source_path.read_bytes()
                    expected_sha16 = file_sha16(source_path)
                    index = load_fixture_index(root)

                    result = index.guarded_replace(
                        Path("Proofs/QMClosure/A.lean"),
                        expected_sha16,
                        "def localTomography := True",
                        new_text,
                        dry_run=dry_run,
                    )

                    self.assertEqual(False, result["ok"])
                    self.assertEqual("blocked_by_guard", result["status"])
                    self.assertEqual(expected_issues, result["issues"])
                    self.assertEqual(expected_sha16, result["old_sha16"])
                    self.assertEqual(expected_sha16, result["new_sha16"])
                    self.assertEqual(original_bytes, source_path.read_bytes())
                    self.assertEqual(expected_sha16, file_sha16(source_path))
                    diagnostics = require_list(result["diagnostics"])
                    self.assertEqual(len(expected_issues), len(diagnostics))
                    if new_text == "QM is proved":
                        phrase = require_mapping(diagnostics[1])
                        self.assertEqual("forbidden_phrase_introduced", phrase["kind"])
                        self.assertEqual(new_text, phrase["token"])

    def test_guarded_edit_diagnostics_bound_context_without_attributing_moved_tokens(self) -> None:
        original = "derived\n"
        updated = "derivedGroup\n" + "x" * 1000 + " derived " + "y" * 1000 + "\n" + "derived\n" * 9
        issues = guarded_edit_issues(original, updated)

        diagnostics = guarded_edit_diagnostics(original, updated, issues)

        self.assertEqual(diagnostics, guarded_edit_diagnostics(original, updated, issues))
        self.assertEqual(1, len(diagnostics))
        diagnostic = diagnostics[0]
        self.assertEqual(1, diagnostic["original_count"])
        self.assertEqual(10, diagnostic["updated_count"])
        self.assertEqual(9, diagnostic["introduced_count"])
        self.assertEqual("updated_file_occurrences_not_attributed", diagnostic["occurrences_scope"])
        locations = require_list(diagnostic["locations"])
        self.assertEqual(3, len(locations))
        self.assertEqual(True, diagnostic["locations_truncated"])
        first = require_mapping(locations[0])
        self.assertEqual(2, first["line"])
        self.assertEqual(1002, first["column"])
        self.assertEqual(942, first["context_column"])
        self.assertEqual(True, first["context_truncated"])
        for item in locations:
            location = require_mapping(item)
            context = require_string(location["context"])
            self.assertLessEqual(len(context), 160)
            self.assertNotIn("\n", context)
            offset = require_int(location["column"]) - require_int(location["context_column"])
            self.assertEqual("derived", context[offset : offset + len("derived")])
        self.assertLess(len(json.dumps(diagnostics)), 2000)
        formatted = guarded_edit_text({"diagnostics": diagnostics})
        self.assertIn("updated file line 2, column 1002: [context column 942, clipped=True]", formatted)

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

    def test_guarded_edit_allows_status_substrings_in_identifier_components(self) -> None:
        for identifier in (
            "RawOperationalHilbert.Data.derivedGroup",
            "Namespace.provedLemma",
            "Namespace.formal_proofCard",
            "underived",
            "derived2",
            "derivedÉvidence",
            "éderived",
        ):
            with self.subTest(identifier=identifier):
                self.assertEqual((), guarded_edit_issues("pending", f'"{identifier}"'))

    def test_guarded_edit_blocks_status_components(self) -> None:
        for status in ("formal_proof", "derived", "proved"):
            for value in (status, f"{status}_extra", f"status_{status}", f"Namespace.{status}"):
                with self.subTest(status=status, value=value):
                    self.assertIn(
                        f"forbidden status upgrade token introduced: {status}",
                        guarded_edit_issues("pending", json.dumps({"status": value})),
                    )
        self.assertIn(
            "forbidden status upgrade token introduced: derived",
            guarded_edit_issues("pending", '"derived_conditional"'),
        )

    def test_guarded_edit_counts_components_instead_of_identifier_substrings(self) -> None:
        self.assertIn(
            "forbidden status upgrade token introduced: derived",
            guarded_edit_issues("RawOperationalHilbert.Data.derivedGroup", "derived"),
        )
        self.assertEqual((), guarded_edit_issues('"derived"', 'status := "derived"'))
        self.assertIn(
            "forbidden status upgrade token introduced: derived",
            guarded_edit_issues('"derived"', '"derived" "derived"'),
        )
        self.assertEqual((), guarded_edit_issues("pending", '"DERIVED"'))

    def test_guarded_edit_preserves_overclaim_phrase_guard(self) -> None:
        for claim in ("QM is proved", "Born is proved", "Hilbert is proved", "hbar is derived"):
            with self.subTest(claim=claim):
                self.assertIn(
                    f"forbidden overclaim introduced: {claim}",
                    guarded_edit_issues("pending", claim),
                )
                self.assertEqual((), guarded_edit_issues(claim, claim + "."))

    def test_guarded_replace_accepts_symbol_evidence_in_dry_run_and_apply(self) -> None:
        for dry_run in (True, False):
            with self.subTest(dry_run=dry_run), tempfile.TemporaryDirectory() as raw_dir:
                root = write_fixture_repo(Path(raw_dir))
                source_path = root / "Proofs" / "QMClosure" / "A.lean"
                original_text = source_path.read_text(encoding="utf-8")
                expected_sha16 = file_sha16(source_path)
                index = load_fixture_index(root)
                old_text = "def localTomography := True"
                new_text = 'def evidence := "RawOperationalHilbert.Data.derivedGroup"'

                result = index.guarded_replace(
                    Path("Proofs/QMClosure/A.lean"),
                    expected_sha16,
                    old_text,
                    new_text,
                    dry_run=dry_run,
                )

                self.assertEqual(True, result["ok"])
                self.assertEqual("dry_run" if dry_run else "applied", result["status"])
                self.assertEqual(expected_sha16, result["old_sha16"])
                updated_text = original_text.replace(old_text, new_text, 1)
                self.assertEqual(
                    hashlib.sha256(updated_text.encode("utf-8")).hexdigest()[:16],
                    result["new_sha16"],
                )
                self.assertEqual(
                    original_text if dry_run else updated_text,
                    source_path.read_text(encoding="utf-8"),
                )

    def test_guarded_replace_rejects_nonunique_old_text(self) -> None:
        for old_text, count in (("absent", 0), ("repeated", 2)):
            with self.subTest(count=count), tempfile.TemporaryDirectory() as raw_dir:
                root = write_fixture_repo(Path(raw_dir))
                index = load_fixture_index(root)
                source_path = root / "Proofs" / "QMClosure" / "A.lean"
                original_text = "-- repeated repeated\n"
                source_path.write_text(original_text, encoding="utf-8")

                with self.assertRaisesRegex(IdtRagError, f"old_text must occur exactly once, got {count}"):
                    index.guarded_replace(
                        Path("Proofs/QMClosure/A.lean"),
                        file_sha16(source_path),
                        old_text,
                        "RawOperationalHilbert.Data.derivedGroup",
                        dry_run=False,
                    )

                self.assertEqual(original_text, source_path.read_text(encoding="utf-8"))

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


def exercise_stale_builder_reload() -> None:
    """Exercise old cached builder / new validator skew in an isolated process."""
    with tempfile.TemporaryDirectory() as raw_dir:
        root = write_fixture_repo(Path(raw_dir))
        server = IdtMcpServer(load_fixture_index(root))
        graph_path = root / "dist" / "idt-v8-ai-theory-graph.json"
        graph = graph_json_load_for_tests(graph_path)
        require_mapping(graph["coverage"]).pop("source_inventory")
        write_locked_graph_for_tests(graph_path, graph)
        current_builder = graph_builder.build_v8_ai_theory_graph

        def legacy_builder(*, repo_root: Path) -> dict[str, object]:
            payload = current_builder(repo_root=repo_root)
            require_mapping(payload["coverage"]).pop("source_inventory")
            return payload

        requests = [
            {"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "idt_reload_code", "arguments": {}}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "idt_graph_search", "arguments": {"query": "localTomography", "limit": 2}}},
        ]
        stdout = io.StringIO()
        with patch.object(graph_builder, "build_v8_ai_theory_graph", legacy_builder):
            result = serve(server, io.StringIO("\n".join(json.dumps(row) for row in requests)), stdout)
        responses = [require_mapping(json.loads(line)) for line in stdout.getvalue().splitlines()]
        if result != 0 or len(responses) != 2:
            raise AssertionError("reload must return both replies without closing the transport")
        search = require_mapping(require_mapping(responses[1]["result"])["structuredContent"])
        if search["count"] != 1:
            raise AssertionError("fresh graph must remain searchable after reload")


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
