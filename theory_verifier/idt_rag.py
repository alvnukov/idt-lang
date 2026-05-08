from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path

from theory_verifier.ai_theory_graph import (
    DEFAULT_GRAPH,
    GraphEdge,
    GraphNode,
    JsonObject,
    TheoryGraph,
    V8GraphQueryError,
    graph_json_text,
    graph_summary,
    load_theory_graph,
    neighbor_subgraph,
    search_nodes,
    show_node,
    source_pointers,
    validate_source_file_hashes,
)


class IdtRagError(ValueError):
    pass


@dataclass(frozen=True)
class SourceHit:
    source: str
    sha16: str
    score: int
    lines: tuple[str, ...]

    def row(self) -> JsonObject:
        return {
            "source": self.source,
            "sha16": self.sha16,
            "score": self.score,
            "lines": list(self.lines),
        }


@dataclass(frozen=True)
class AuditIssue:
    severity: str
    node_id: str
    message: str
    source: str
    evidence: str

    def row(self) -> JsonObject:
        return {
            "severity": self.severity,
            "node_id": self.node_id,
            "message": self.message,
            "source": self.source,
            "evidence": self.evidence,
        }


@dataclass(frozen=True)
class CheckCommand:
    name: str
    command: tuple[str, ...]
    timeout_seconds: int
    description: str


@dataclass(frozen=True)
class IdtRagIndex:
    repo_root: Path
    graph_path: Path
    graph: TheoryGraph

    @classmethod
    def load(
        cls,
        repo_root: Path,
        graph_path: Path = DEFAULT_GRAPH,
        check_source_hashes: bool = True,
        auto_refresh: bool = True,
    ) -> IdtRagIndex:
        root = repo_root.resolve()
        resolved_graph_path = resolve_graph_path(root, graph_path)
        graph = load_or_refresh_graph(root, resolved_graph_path, check_source_hashes, auto_refresh)
        return cls(root, resolved_graph_path, graph)

    def refresh(self) -> IdtRagIndex:
        return self.load(
            self.repo_root,
            self.graph_path,
            check_source_hashes=True,
            auto_refresh=True,
        )

    def summary(self) -> JsonObject:
        return graph_summary(self.graph)

    def search_graph(
        self,
        query: str,
        kind: str = "",
        status: str = "",
        limit: int = 20,
    ) -> JsonObject:
        return search_nodes(self.graph, query, kind, status, limit)

    def show(self, query: str) -> JsonObject:
        return show_node(self.graph, query)

    def neighborhood(self, query: str, depth: int = 1) -> JsonObject:
        return neighbor_subgraph(self.graph, query, depth)

    def sources(self, query: str, depth: int = 1) -> JsonObject:
        return source_pointers(self.graph, query, depth)

    def claim_audit(self) -> JsonObject:
        issues = claim_audit_issues(self.graph)
        return {
            "schema": "idt-v8-claim-audit/1",
            "contract": {
                "proof_authority": "lean_only",
                "audit_role": "read_only_consistency_check",
                "claim_upgrade_policy": "no_artifact_no_upgrade",
            },
            "ok": not issues,
            "summary": {
                "issues": len(issues),
                "formal_proof_residuals": len(nodes_with_status(self.graph, "formal_proof")),
                "lean_theorems": len(
                    [
                        node
                        for node in self.graph.nodes
                        if node.kind == "lean.decl" and node.status == "theorem"
                    ]
                ),
                "conditional_residuals": len(nodes_with_status(self.graph, "conditional_proof")),
                "executable_gate_residuals": len(nodes_with_status(self.graph, "executable_gate")),
            },
            "issues": [issue.row() for issue in issues],
        }

    def missing_proof_artifacts(self, limit: int = 50) -> JsonObject:
        if limit <= 0:
            raise IdtRagError("limit must be > 0")
        rows: list[JsonObject] = []
        for node in self.graph.nodes:
            if node.kind != "manifest.residual":
                continue
            if not proof_relevant_residual(node):
                continue
            if node.status == "formal_proof":
                continue
            rows.append(
                {
                    "node_id": node.identifier,
                    "status": node.status,
                    "label": node.label,
                    "source": node.source,
                    "sha16": node.digest,
                    "reason": "not_formal_proof_without_lean_artifact",
                }
            )
        limited = rows[:limit]
        return {
            "schema": "idt-v8-missing-proof-artifacts/1",
            "proof_authority": "lean_only",
            "count": len(rows),
            "truncated": len(rows) > len(limited),
            "items": limited,
        }

    def research_context(
        self,
        query: str,
        depth: int = 1,
        limit: int = 8,
    ) -> JsonObject:
        if depth < 0:
            raise IdtRagError("depth must be >= 0")
        if limit <= 0:
            raise IdtRagError("limit must be > 0")
        matches = self.search_graph(query, "", "", limit)
        graph_rows = require_node_rows(matches.get("nodes"))
        focus_rows = graph_rows[:3]
        neighborhoods: list[JsonObject] = []
        source_sets: list[JsonObject] = []
        for row in focus_rows:
            neighborhoods.append(compact_subgraph(self.neighborhood(row[0], depth)))
            source_sets.append(self.sources(row[0], depth))
        return {
            "schema": "idt-v8-research-context/1",
            "query": query,
            "contract": {
                "proof_authority": "lean_only",
                "context_role": "compressed_navigation_context",
                "claim_upgrade_policy": "no_artifact_no_upgrade",
                "forbidden_use": "do_not_treat_rag_or_experiments_as_formal_proof",
            },
            "summary": compact_summary(self.summary()),
            "claim_audit": self.claim_audit(),
            "matches": matches,
            "neighborhoods": neighborhoods,
            "sources": source_sets,
        }

    def graph_diff(self, base_graph_path: Path, limit: int = 40) -> JsonObject:
        if limit <= 0:
            raise IdtRagError("limit must be > 0")
        resolved_base = self.safe_repo_path(base_graph_path)
        base_graph = load_theory_graph(resolved_base)
        old_nodes = {node.identifier: node for node in base_graph.nodes}
        new_nodes = {node.identifier: node for node in self.graph.nodes}
        old_edges = {tuple(edge.row()) for edge in base_graph.edges}
        new_edges = {tuple(edge.row()) for edge in self.graph.edges}
        added_nodes = sorted(set(new_nodes) - set(old_nodes))
        removed_nodes = sorted(set(old_nodes) - set(new_nodes))
        changed_nodes = sorted(
            node_id
            for node_id in set(old_nodes).intersection(new_nodes)
            if old_nodes[node_id].row() != new_nodes[node_id].row()
        )
        added_edges = sorted(new_edges - old_edges)
        removed_edges = sorted(old_edges - new_edges)
        return {
            "schema": "idt-v8-graph-diff/1",
            "base_graph": resolved_base.relative_to(self.repo_root).as_posix(),
            "current_graph": relative_path_or_absolute(self.repo_root, self.graph_path),
            "proof_authority": "lean_only",
            "summary": {
                "added_nodes": len(added_nodes),
                "removed_nodes": len(removed_nodes),
                "changed_nodes": len(changed_nodes),
                "added_edges": len(added_edges),
                "removed_edges": len(removed_edges),
            },
            "samples": {
                "added_nodes": added_nodes[:limit],
                "removed_nodes": removed_nodes[:limit],
                "changed_nodes": changed_nodes[:limit],
                "added_edges": [list(edge) for edge in added_edges[:limit]],
                "removed_edges": [list(edge) for edge in removed_edges[:limit]],
            },
            "truncated": any(
                len(items) > limit
                for items in (added_nodes, removed_nodes, changed_nodes, added_edges, removed_edges)
            ),
        }

    def lean_build_target(self, target: str, timeout_seconds: int = 60) -> JsonObject:
        if not safe_target_name(target):
            raise IdtRagError(f"unsafe Lean target {target!r}")
        if timeout_seconds <= 0 or timeout_seconds > 600:
            raise IdtRagError("timeout_seconds must be in 1..600")
        return run_command_evidence(
            self.repo_root,
            CheckCommand(
                name=f"lake_build:{target}",
                command=("lake", "build", target),
                timeout_seconds=timeout_seconds,
                description="Lean build target",
            ),
        )

    def run_check(self, name: str) -> JsonObject:
        checks = allowed_checks()
        command = checks.get(name)
        if command is None:
            raise IdtRagError(f"unknown check {name!r}; allowed: {', '.join(sorted(checks))}")
        if command.command == ("__graph_validate__",):
            validate_source_file_hashes(self.graph, self.repo_root)
            return {
                "schema": "idt-v8-check-evidence/1",
                "name": command.name,
                "description": command.description,
                "ok": True,
                "exit_code": 0,
                "duration_seconds": 0.0,
                "command": ["graph_validate"],
                "stdout_tail": "graph schema and source hashes are valid",
                "stderr_tail": "",
                "proof_boundary": "check_result_is_not_formal_proof",
            }
        return run_command_evidence(self.repo_root, command)

    def guarded_replace(
        self,
        file_path: Path,
        expected_sha16: str,
        old_text: str,
        new_text: str,
        dry_run: bool = True,
    ) -> JsonObject:
        resolved_path = self.safe_edit_path(file_path)
        if not expected_sha16 or not is_sha16(expected_sha16):
            raise IdtRagError("expected_sha16 must be a 16-character lowercase sha256 prefix")
        if not old_text:
            raise IdtRagError("old_text must be non-empty")
        if old_text == new_text:
            raise IdtRagError("old_text and new_text must differ")
        with graph_file_lock(resolved_path):
            original_bytes = resolved_path.read_bytes()
            actual_sha16 = hashlib.sha256(original_bytes).hexdigest()[:16]
            if actual_sha16 != expected_sha16:
                raise IdtRagError(
                    f"file hash mismatch for {relative_path_or_absolute(self.repo_root, resolved_path)}: "
                    f"expected={expected_sha16} actual={actual_sha16}"
                )
            original_text = original_bytes.decode("utf-8")
            occurrence_count = original_text.count(old_text)
            if occurrence_count != 1:
                raise IdtRagError(f"old_text must occur exactly once, got {occurrence_count}")
            updated_text = original_text.replace(old_text, new_text, 1)
            guard_issues = guarded_edit_issues(original_text, updated_text)
            if guard_issues:
                return guarded_edit_result(
                    self.repo_root,
                    resolved_path,
                    dry_run,
                    actual_sha16,
                    actual_sha16,
                    False,
                    guard_issues,
                    "blocked_by_guard",
                )
            updated_sha16 = hashlib.sha256(updated_text.encode("utf-8")).hexdigest()[:16]
            if not dry_run:
                atomic_write_text(resolved_path, updated_text)
            return guarded_edit_result(
                self.repo_root,
                resolved_path,
                dry_run,
                actual_sha16,
                updated_sha16,
                True,
                (),
                "dry_run" if dry_run else "applied",
            )

    def retrieve(
        self,
        query: str,
        limit: int = 8,
        max_lines_per_source: int = 8,
    ) -> JsonObject:
        if not query.strip():
            raise IdtRagError("query must be non-empty")
        if limit <= 0:
            raise IdtRagError("limit must be > 0")
        if max_lines_per_source <= 0:
            raise IdtRagError("max_lines_per_source must be > 0")
        terms = query_terms(query)
        graph_result = search_nodes(self.graph, query, "", "", max(limit * 3, limit))
        graph_rows = require_node_rows(graph_result.get("nodes"))
        source_nodes = self.matching_source_nodes(graph_rows, terms)
        hits = self.rank_source_hits(source_nodes, terms, limit, max_lines_per_source)
        return {
            "query": query,
            "contract": {
                "proof_authority": "lean_only",
                "rag_role": "source_grounded_development_context",
                "claim_upgrade_policy": "no_artifact_no_upgrade",
            },
            "graph_matches": graph_rows[:limit],
            "source_hits": [hit.row() for hit in hits],
        }

    def matching_source_nodes(
        self,
        graph_rows: Sequence[list[str]],
        terms: Sequence[str],
    ) -> tuple[GraphNode, ...]:
        by_id = self.graph.node_index
        selected: dict[str, GraphNode] = {}
        for row in graph_rows:
            node = by_id.get(row[0])
            if node is not None and node.source:
                source_path = source_path_without_line(node.source)
                source_node = self.source_file_node(source_path)
                if source_node is not None:
                    selected[source_path] = source_node
        for node in self.graph.nodes:
            if node.kind != "source.file":
                continue
            haystack = f"{node.identifier}\n{node.label}\n{node.source}".casefold()
            if any(term in haystack for term in terms):
                selected[node.source] = node
        for node in self.graph.nodes:
            if node.kind == "source.file":
                selected.setdefault(node.source, node)
        return tuple(sorted(selected.values(), key=lambda item: item.source))

    def rank_source_hits(
        self,
        source_nodes: Sequence[GraphNode],
        terms: Sequence[str],
        limit: int,
        max_lines_per_source: int,
    ) -> tuple[SourceHit, ...]:
        hits: list[SourceHit] = []
        for node in source_nodes:
            path = self.safe_source_path(node.source)
            source_bytes = path.read_bytes()
            actual_sha16 = hashlib.sha256(source_bytes).hexdigest()[:16]
            if actual_sha16 != node.digest:
                raise IdtRagError(
                    f"source hash mismatch for {node.source}: "
                    f"graph={node.digest} actual={actual_sha16}"
                )
            lines = source_bytes.decode("utf-8").splitlines()
            matching_lines = matching_source_lines(lines, terms, max_lines_per_source)
            score = source_score(node, matching_lines, terms)
            if score > 0:
                hits.append(SourceHit(node.source, node.digest, score, tuple(matching_lines)))
        return tuple(
            sorted(hits, key=lambda hit: (-hit.score, hit.source))[:limit]
        )

    def safe_source_path(self, source: str) -> Path:
        clean_source = source_path_without_line(source)
        if not clean_source:
            raise IdtRagError("source path must be non-empty")
        if Path(clean_source).is_absolute():
            raise IdtRagError(f"absolute source path is not allowed: {source}")
        path = (self.repo_root / clean_source).resolve()
        try:
            path.relative_to(self.repo_root)
        except ValueError as error:
            raise IdtRagError(f"source path escapes repo root: {source}") from error
        if not path.is_file():
            raise IdtRagError(f"source path does not exist: {source}")
        return path

    def source_file_node(self, source: str) -> GraphNode | None:
        clean_source = source_path_without_line(source)
        for node in self.graph.nodes:
            if node.kind == "source.file" and node.source == clean_source:
                return node
        return None

    def safe_repo_path(self, path: Path) -> Path:
        candidate = path if path.is_absolute() else self.repo_root / path
        resolved = candidate.resolve()
        try:
            resolved.relative_to(self.repo_root)
        except ValueError as error:
            raise IdtRagError(f"path escapes repo root: {path}") from error
        if not resolved.is_file():
            raise IdtRagError(f"path does not exist: {path}")
        return resolved

    def safe_edit_path(self, path: Path) -> Path:
        resolved = self.safe_repo_path(path)
        relative = resolved.relative_to(self.repo_root).as_posix()
        if relative.startswith(("dist/", ".git/", ".lake/", "archive/")):
            raise IdtRagError(f"editing generated or internal path is not allowed: {relative}")
        if relative == "theory_verifier_manifest.json":
            raise IdtRagError("manifest edits are not allowed through MCP guarded_replace")
        if not relative.endswith((".md", ".lean", ".json", ".py", ".toml", ".yml", ".yaml")):
            raise IdtRagError(f"unsupported editable file type: {relative}")
        return resolved


def resolve_graph_path(repo_root: Path, graph_path: Path) -> Path:
    if graph_path.is_absolute():
        return graph_path
    return repo_root / graph_path


def load_or_refresh_graph(
    repo_root: Path,
    graph_path: Path,
    check_source_hashes: bool,
    auto_refresh: bool,
) -> TheoryGraph:
    if not auto_refresh:
        return checked_load_graph(repo_root, graph_path, check_source_hashes)
    with graph_file_lock(graph_path):
        try:
            return checked_load_graph(repo_root, graph_path, check_source_hashes)
        except (OSError, V8GraphQueryError):
            rebuild_graph(repo_root, graph_path)
            try:
                return checked_load_graph(repo_root, graph_path, check_source_hashes)
            except (OSError, V8GraphQueryError) as refresh_error:
                raise IdtRagError(
                    f"graph refresh did not produce a valid source-grounded graph: {refresh_error}"
                ) from refresh_error


def checked_load_graph(
    repo_root: Path,
    graph_path: Path,
    check_source_hashes: bool,
) -> TheoryGraph:
    graph = load_theory_graph(graph_path)
    if check_source_hashes:
        validate_source_file_hashes(graph, repo_root)
    return graph


@contextlib.contextmanager
def graph_file_lock(graph_path: Path) -> Iterator[None]:
    lock_path = lock_path_for(graph_path)
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield None
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def lock_path_for(path: Path) -> Path:
    digest = hashlib.sha256(str(path.resolve()).encode("utf-8")).hexdigest()
    return Path(tempfile.gettempdir()) / "idt-mcp-locks" / f"{digest}.lock"


def rebuild_graph(repo_root: Path, graph_path: Path) -> None:
    from scripts.build_ai_theory_graph import build_v8_ai_theory_graph

    graph = build_v8_ai_theory_graph(repo_root=repo_root)
    atomic_write_text(graph_path, graph_json_text(graph, pretty=False) + "\n")


def atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_path = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        temporary_path.write_text(text, encoding="utf-8")
        with temporary_path.open("r+", encoding="utf-8") as temporary_file:
            temporary_file.flush()
            os.fsync(temporary_file.fileno())
        temporary_path.replace(path)
        directory_fd = os.open(str(path.parent), os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temporary_path.unlink()


def write_locked_graph_for_tests(path: Path, graph: Mapping[str, object]) -> None:
    with graph_file_lock(path):
        atomic_write_text(path, graph_json_text(graph, pretty=False) + "\n")


def graph_json_load_for_tests(path: Path) -> JsonObject:
    return require_json_object(json.loads(path.read_text(encoding="utf-8")), "graph")


def is_sha16(value: str) -> bool:
    return re.fullmatch(r"[0-9a-f]{16}", value) is not None


def guarded_edit_issues(original_text: str, updated_text: str) -> tuple[str, ...]:
    issues: list[str] = []
    forbidden_statuses = ("formal_proof", "derived", "proved")
    for status in forbidden_statuses:
        if updated_text.count(status) > original_text.count(status):
            issues.append(f"forbidden status upgrade token introduced: {status}")
    forbidden_claims = ("QM is proved", "Born is proved", "Hilbert is proved", "hbar is derived")
    for claim in forbidden_claims:
        if claim not in original_text and claim in updated_text:
            issues.append(f"forbidden overclaim introduced: {claim}")
    return tuple(issues)


def guarded_edit_result(
    repo_root: Path,
    path: Path,
    dry_run: bool,
    old_sha16: str,
    new_sha16: str,
    ok: bool,
    issues: Sequence[str],
    status: str,
) -> JsonObject:
    return {
        "schema": "idt-v8-guarded-edit/1",
        "ok": ok,
        "status": status,
        "dry_run": dry_run,
        "path": relative_path_or_absolute(repo_root, path),
        "old_sha16": old_sha16,
        "new_sha16": new_sha16,
        "issues": list(issues),
        "safety": {
            "hash_guard": True,
            "exclusive_lock": True,
            "atomic_write": not dry_run and ok,
            "forbidden_status_scan": True,
            "proof_boundary": "edit_result_is_not_formal_proof",
        },
    }


def allowed_checks() -> dict[str, CheckCommand]:
    return {
        "graph_validate": CheckCommand(
            name="graph_validate",
            command=("__graph_validate__",),
            timeout_seconds=1,
            description="Validate current graph schema and source hashes.",
        ),
        "declarative_rules": CheckCommand(
            name="declarative_rules",
            command=("python3", "scripts/check_declarative_rules.py", "--json"),
            timeout_seconds=60,
            description="Validate IDT v8 declarative rules.",
        ),
        "mcp_rag_tests": CheckCommand(
            name="mcp_rag_tests",
            command=("python3", "-m", "unittest", "tests.test_idt_mcp_rag"),
            timeout_seconds=60,
            description="Run targeted MCP/RAG unit tests.",
        ),
        "v8_protocol_boundary": CheckCommand(
            name="v8_protocol_boundary",
            command=("lake", "exe", "idt_v8_protocol_status", "--", "--check-boundary"),
            timeout_seconds=120,
            description="Run the Lean-sourced v8 protocol boundary check.",
        ),
    }


def run_command_evidence(repo_root: Path, check: CheckCommand) -> JsonObject:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            check.command,
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=check.timeout_seconds,
            check=False,
        )
        duration = time.monotonic() - started
        return {
            "schema": "idt-v8-check-evidence/1",
            "name": check.name,
            "description": check.description,
            "ok": completed.returncode == 0,
            "exit_code": completed.returncode,
            "duration_seconds": round(duration, 3),
            "command": list(check.command),
            "stdout_tail": tail_text(completed.stdout),
            "stderr_tail": tail_text(completed.stderr),
            "proof_boundary": "check_result_is_not_formal_proof",
        }
    except subprocess.TimeoutExpired as error:
        duration = time.monotonic() - started
        return {
            "schema": "idt-v8-check-evidence/1",
            "name": check.name,
            "description": check.description,
            "ok": False,
            "exit_code": -1,
            "duration_seconds": round(duration, 3),
            "command": list(check.command),
            "stdout_tail": tail_text(error.stdout if isinstance(error.stdout, str) else ""),
            "stderr_tail": tail_text(error.stderr if isinstance(error.stderr, str) else "timeout expired"),
            "proof_boundary": "check_result_is_not_formal_proof",
        }


def tail_text(text: str, max_lines: int = 20, max_chars: int = 4000) -> str:
    lines = text.splitlines()
    tail = "\n".join(lines[-max_lines:])
    if len(tail) <= max_chars:
        return tail
    return tail[-max_chars:]


def safe_target_name(target: str) -> bool:
    return re.fullmatch(r"[A-Za-z0-9_.:/-]+", target) is not None and ".." not in target


def relative_path_or_absolute(repo_root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root).as_posix()
    except ValueError:
        return str(path)


def claim_audit_issues(graph: TheoryGraph) -> tuple[AuditIssue, ...]:
    issues: list[AuditIssue] = []
    node_index = graph.node_index
    outgoing = outgoing_edges_by_source(graph.edges)
    for node in graph.nodes:
        if node.kind != "manifest.residual":
            continue
        if node.status != "formal_proof":
            continue
        proof_edges = [
            edge
            for edge in outgoing.get(node.identifier, ())
            if edge.relation in {"verified_by", "proof_artifact"}
        ]
        if not proof_edges:
            issues.append(
                AuditIssue(
                    "error",
                    node.identifier,
                    "formal_proof residual has no Lean artifact proof edge",
                    node.source,
                    "missing verified_by/proof_artifact edge",
                )
            )
            continue
        if not any(edge_targets_lean_artifact(edge, node_index) for edge in proof_edges):
            issues.append(
                AuditIssue(
                    "error",
                    node.identifier,
                    "formal_proof residual is not grounded in a Lean artifact",
                    node.source,
                    ",".join(edge.target for edge in proof_edges),
                )
            )
    return tuple(sorted(issues, key=lambda issue: (issue.severity, issue.node_id, issue.message)))


def outgoing_edges_by_source(edges: Sequence[GraphEdge]) -> dict[str, tuple[GraphEdge, ...]]:
    buckets: dict[str, list[GraphEdge]] = {}
    for edge in edges:
        buckets.setdefault(edge.source, []).append(edge)
    return {
        source: tuple(sorted(items, key=lambda edge: (edge.relation, edge.target, edge.evidence)))
        for source, items in buckets.items()
    }


def edge_targets_lean_artifact(edge: GraphEdge, node_index: Mapping[str, GraphNode]) -> bool:
    target = node_index.get(edge.target)
    if target is None:
        return False
    if target.kind == "lean.decl":
        return True
    return target.kind == "source.file" and target.source.startswith(("Proofs/", "Experiments/"))


def nodes_with_status(graph: TheoryGraph, status: str) -> tuple[GraphNode, ...]:
    return tuple(node for node in graph.nodes if node.status == status)


def proof_relevant_residual(node: GraphNode) -> bool:
    if not node.identifier.startswith(("res:theorem_cards:", "res:qm_core_proof_obligations:")):
        return False
    return node.status in {
        "blocked",
        "bridge_assumption",
        "conditional_proof",
        "derived_conditional",
        "executable_gate",
        "finite_verifier_pass",
        "open",
        "target",
    }


def compact_summary(summary: Mapping[str, object]) -> JsonObject:
    coverage = require_json_object(summary.get("coverage"), "coverage")
    compact_coverage: JsonObject = {
        "nodes": coverage.get("nodes", 0),
        "edges": coverage.get("edges", 0),
        "manifest_counts": coverage.get("manifest_counts", {}),
    }
    return {
        "schema": summary.get("schema", ""),
        "contract": summary.get("contract", {}),
        "coverage": compact_coverage,
        "node_kinds": summary.get("node_kinds", {}),
        "node_statuses": summary.get("node_statuses", {}),
        "edge_relations": summary.get("edge_relations", {}),
    }


def compact_subgraph(subgraph: Mapping[str, object]) -> JsonObject:
    nodes = require_node_rows(subgraph.get("nodes"))
    edges = require_edge_rows(subgraph.get("edges"))
    max_nodes = 12
    max_edges = 24
    limited_nodes = nodes[:max_nodes]
    limited_node_ids = {row[0] for row in limited_nodes}
    local_edges = [
        edge
        for edge in edges
        if edge[0] in limited_node_ids and edge[2] in limited_node_ids
    ][:max_edges]
    return {
        "query": subgraph.get("query", ""),
        "resolved": subgraph.get("resolved", ""),
        "depth": subgraph.get("depth", 0),
        "nodes": limited_nodes,
        "edges": local_edges,
        "truncated": len(nodes) > len(limited_nodes) or len(edges) > len(local_edges),
        "full_counts": {
            "nodes": len(nodes),
            "edges": len(edges),
        },
    }


def query_terms(query: str) -> tuple[str, ...]:
    terms = tuple(
        term.casefold()
        for term in re.findall(r"[A-Za-z0-9_./:-]+", query)
        if len(term) >= 2
    )
    if not terms:
        raise IdtRagError("query must contain at least one searchable term")
    return terms


def source_path_without_line(source: str) -> str:
    match = re.fullmatch(r"(.+\.(?:lean|md|json|py|toml|yml|yaml)):\d+", source)
    if match is None:
        return source
    return match.group(1)


def matching_source_lines(
    lines: Sequence[str],
    terms: Sequence[str],
    limit: int,
) -> list[str]:
    matches: list[str] = []
    for line_number, line in enumerate(lines, start=1):
        folded = line.casefold()
        if any(term in folded for term in terms):
            matches.append(f"{line_number}: {line[:240]}")
            if len(matches) >= limit:
                break
    return matches


def source_score(
    node: GraphNode,
    matching_lines: Sequence[str],
    terms: Sequence[str],
) -> int:
    haystack = f"{node.identifier}\n{node.kind}\n{node.status}\n{node.label}\n{node.source}".casefold()
    node_score = sum(3 for term in terms if term in haystack)
    line_score = len(matching_lines)
    return node_score + line_score


def require_node_rows(value: object) -> list[list[str]]:
    if not isinstance(value, list):
        raise IdtRagError("nodes must be a list")
    rows: list[list[str]] = []
    for item in value:
        if not isinstance(item, list) or len(item) != 6:
            raise IdtRagError("node rows must have six columns")
        row: list[str] = []
        for cell in item:
            if not isinstance(cell, str):
                raise IdtRagError("node row cells must be strings")
            row.append(cell)
        rows.append(row)
    return rows


def require_edge_rows(value: object) -> list[list[str]]:
    if not isinstance(value, list):
        raise IdtRagError("edges must be a list")
    rows: list[list[str]] = []
    for item in value:
        if not isinstance(item, list) or len(item) != 4:
            raise IdtRagError("edge rows must have four columns")
        row: list[str] = []
        for cell in item:
            if not isinstance(cell, str):
                raise IdtRagError("edge row cells must be strings")
            row.append(cell)
        rows.append(row)
    return rows


def require_json_object(value: object, name: str) -> JsonObject:
    if not isinstance(value, dict):
        raise IdtRagError(f"{name} must be an object")
    output: JsonObject = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise IdtRagError(f"{name} keys must be strings")
        output[key] = item
    return output


def require_string_arg(args: Mapping[str, object], name: str) -> str:
    value = args.get(name)
    if not isinstance(value, str) or not value:
        raise IdtRagError(f"{name} must be a non-empty string")
    return value


def optional_string_arg(args: Mapping[str, object], name: str, default: str = "") -> str:
    value = args.get(name, default)
    if not isinstance(value, str):
        raise IdtRagError(f"{name} must be a string")
    return value


def optional_int_arg(args: Mapping[str, object], name: str, default: int) -> int:
    value = args.get(name, default)
    if not isinstance(value, int) or isinstance(value, bool):
        raise IdtRagError(f"{name} must be an integer")
    return value


def optional_bool_arg(args: Mapping[str, object], name: str, default: bool) -> bool:
    value = args.get(name, default)
    if not isinstance(value, bool):
        raise IdtRagError(f"{name} must be a boolean")
    return value


def rag_result_text(result: Mapping[str, object]) -> str:
    query = result.get("query", "")
    source_hits = result.get("source_hits", [])
    if not isinstance(query, str) or not isinstance(source_hits, list):
        raise IdtRagError("invalid RAG result")
    lines = [
        f"IDT RAG query: {query}",
        "Boundary: context only; Lean remains proof authority; no claim upgrades.",
    ]
    for raw_hit in source_hits:
        if not isinstance(raw_hit, dict):
            continue
        source = raw_hit.get("source", "")
        sha16 = raw_hit.get("sha16", "")
        score = raw_hit.get("score", 0)
        raw_lines = raw_hit.get("lines", [])
        if not isinstance(source, str) or not isinstance(sha16, str):
            continue
        lines.append(f"- {source} sha16={sha16} score={score}")
        if isinstance(raw_lines, list):
            for raw_line in raw_lines[:6]:
                if isinstance(raw_line, str):
                    lines.append(f"  {raw_line}")
    return "\n".join(lines)


def audit_result_text(result: Mapping[str, object]) -> str:
    ok = result.get("ok", False)
    summary = require_json_object(result.get("summary"), "summary")
    return (
        f"IDT claim audit: ok={ok}; issues={summary.get('issues', 0)}; "
        f"formal_proof_residuals={summary.get('formal_proof_residuals', 0)}; "
        "proof_authority=lean_only"
    )


def missing_artifacts_text(result: Mapping[str, object]) -> str:
    return (
        f"IDT missing proof artifacts: count={result.get('count', 0)}; "
        f"truncated={result.get('truncated', False)}; proof_authority=lean_only"
    )


def research_context_text(result: Mapping[str, object]) -> str:
    matches = require_json_object(result.get("matches"), "matches")
    audit = require_json_object(result.get("claim_audit"), "claim_audit")
    return (
        f"IDT research context: query={result.get('query', '')}; "
        f"matches={matches.get('count', 0)}; truncated={matches.get('truncated', False)}; "
        f"audit_ok={audit.get('ok', False)}; proof_authority=lean_only; "
        "use structuredContent for graph rows and source pointers"
    )


def check_evidence_text(result: Mapping[str, object]) -> str:
    return (
        f"IDT check: name={result.get('name', '')}; ok={result.get('ok', False)}; "
        f"exit_code={result.get('exit_code', '')}; duration={result.get('duration_seconds', '')}s; "
        "proof_boundary=check_result_is_not_formal_proof"
    )


def graph_diff_text(result: Mapping[str, object]) -> str:
    summary = require_json_object(result.get("summary"), "summary")
    return (
        "IDT graph diff: "
        f"added_nodes={summary.get('added_nodes', 0)}; "
        f"removed_nodes={summary.get('removed_nodes', 0)}; "
        f"changed_nodes={summary.get('changed_nodes', 0)}; "
        f"added_edges={summary.get('added_edges', 0)}; "
        f"removed_edges={summary.get('removed_edges', 0)}; "
        f"truncated={result.get('truncated', False)}"
    )


def guarded_edit_text(result: Mapping[str, object]) -> str:
    return (
        f"IDT guarded edit: path={result.get('path', '')}; ok={result.get('ok', False)}; "
        f"status={result.get('status', '')}; dry_run={result.get('dry_run', True)}; "
        f"old_sha16={result.get('old_sha16', '')}; new_sha16={result.get('new_sha16', '')}"
    )
