from __future__ import annotations

import json
import os
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from importlib import metadata
from importlib.util import find_spec
from pathlib import Path

from theory_verifier.ai_theory_graph import GraphNode, JsonObject, TheoryGraph
from theory_verifier.idt_rag import IdtRagError, atomic_write_text, relative_path_or_absolute


@dataclass(frozen=True)
class LeanDojoPackageProbe:
    distribution: str
    module: str
    installed: bool
    importable: bool
    version: str

    def row(self) -> JsonObject:
        return {
            "distribution": self.distribution,
            "module": self.module,
            "installed": self.installed,
            "importable": self.importable,
            "version": self.version,
        }


LEANDOJO_PACKAGES: tuple[tuple[str, str], ...] = (
    ("lean-dojo-v2", "lean_dojo_v2"),
    ("lean-dojo", "lean_dojo"),
)


def leandojo_status(repo_root: Path) -> JsonObject:
    probes = tuple(probe_package(distribution, module) for distribution, module in LEANDOJO_PACKAGES)
    v2_probe = probes[0]
    lean_toolchain_path = repo_root / "lean-toolchain"
    lean_toolchain = ""
    if lean_toolchain_path.is_file():
        lean_toolchain = lean_toolchain_path.read_text(encoding="utf-8").strip()
    return {
        "schema": "idt-leandojo-status/1",
        "available": v2_probe.installed and v2_probe.importable,
        "role": "optional_proof_search_adapter_not_claim_authority",
        "proof_authority": "lean_only",
        "claim_upgrade_policy": "no_artifact_no_upgrade",
        "packages": [probe.row() for probe in probes],
        "repo": {
            "lean_toolchain": lean_toolchain,
            "lakefile_exists": (repo_root / "lakefile.lean").is_file(),
            "proofs_dir_exists": (repo_root / "Proofs").is_dir(),
        },
        "next_step": (
            "install lean-dojo-v2 and PyPantograph in a separate environment"
            if not (v2_probe.installed and v2_probe.importable)
            else "ready_for_trace_or_agent_adapter"
        ),
    }


def leandojo_status_text(result: Mapping[str, object]) -> str:
    return (
        f"IDT LeanDojo status: available={result.get('available', False)}; "
        "role=optional_proof_search_adapter_not_claim_authority; "
        "proof_authority=lean_only"
    )


def probe_package(distribution: str, module: str) -> LeanDojoPackageProbe:
    version = ""
    installed = True
    try:
        version = metadata.version(distribution)
    except metadata.PackageNotFoundError:
        installed = False
    importable = find_spec(module) is not None
    return LeanDojoPackageProbe(
        distribution=distribution,
        module=module,
        installed=installed,
        importable=importable,
        version=version,
    )


def leandojo_goal_candidates(
    graph: TheoryGraph,
    query: str,
    limit: int,
) -> JsonObject:
    if limit <= 0:
        raise IdtRagError("limit must be > 0")
    terms = tuple(term.casefold() for term in query.split() if term.strip())
    rows: list[JsonObject] = []
    for node in graph.nodes:
        if not is_candidate_goal(node):
            continue
        haystack = f"{node.identifier}\n{node.label}\n{node.status}\n{node.source}".casefold()
        if terms and not all(term in haystack for term in terms):
            continue
        rows.append(
            {
                "node_id": node.identifier,
                "kind": node.kind,
                "status": node.status,
                "label": node.label,
                "source": node.source,
                "sha16": node.digest,
                "leandojo_role": "candidate_goal_context_only",
            }
        )
    limited = rows[:limit]
    return {
        "schema": "idt-leandojo-goal-candidates/1",
        "query": query,
        "count": len(rows),
        "truncated": len(rows) > len(limited),
        "proof_authority": "lean_only",
        "claim_upgrade_policy": "no_artifact_no_upgrade",
        "items": limited,
    }


def leandojo_goal_candidates_text(result: Mapping[str, object]) -> str:
    return (
        f"IDT LeanDojo goal candidates: query={result.get('query', '')}; "
        f"count={result.get('count', 0)}; truncated={result.get('truncated', False)}; "
        "claim_upgrade_policy=no_artifact_no_upgrade"
    )


def is_candidate_goal(node: GraphNode) -> bool:
    if node.kind == "lean.decl" and node.status == "theorem":
        return True
    if node.kind != "manifest.residual":
        return False
    return node.status in {
        "blocked",
        "conditional_proof",
        "derived_conditional",
        "open",
        "regression_supported",
        "target",
    }


def record_leandojo_attempt(
    repo_root: Path,
    goal: str,
    status: str,
    summary: str,
    artifact_paths: Sequence[str],
) -> JsonObject:
    if not goal.strip():
        raise IdtRagError("goal must be non-empty")
    if not summary.strip():
        raise IdtRagError("summary must be non-empty")
    allowed_statuses = {"candidate", "proved_by_lean", "failed", "timeout", "blocked_by_import"}
    if status not in allowed_statuses:
        raise IdtRagError(f"status must be one of: {', '.join(sorted(allowed_statuses))}")
    normalized_artifacts = tuple(validate_attempt_artifact(repo_root, path) for path in artifact_paths)
    attempt_dir = repo_root / ".idt" / "proof_attempts"
    attempt_dir.mkdir(parents=True, exist_ok=True)
    attempt_path = attempt_dir / "leandojo_attempts.jsonl"
    row: JsonObject = {
        "schema": "idt-leandojo-attempt/1",
        "created_unix": int(time.time()),
        "goal": goal,
        "status": status,
        "summary": summary,
        "artifact_paths": list(normalized_artifacts),
        "proof_boundary": "attempt_log_is_not_claim_status",
        "claim_upgrade_policy": "no_artifact_no_upgrade",
    }
    existing = ""
    if attempt_path.is_file():
        existing = attempt_path.read_text(encoding="utf-8")
    atomic_write_text(attempt_path, existing + json.dumps(row, sort_keys=True) + "\n")
    return {
        "schema": "idt-leandojo-record-attempt-result/1",
        "ok": True,
        "path": relative_path_or_absolute(repo_root, attempt_path),
        "attempt": row,
    }


def leandojo_record_attempt_text(result: Mapping[str, object]) -> str:
    attempt = result.get("attempt", {})
    status = ""
    goal = ""
    if isinstance(attempt, dict):
        raw_status = attempt.get("status", "")
        raw_goal = attempt.get("goal", "")
        status = raw_status if isinstance(raw_status, str) else ""
        goal = raw_goal if isinstance(raw_goal, str) else ""
    return (
        f"IDT LeanDojo attempt recorded: ok={result.get('ok', False)}; "
        f"status={status}; goal={goal}; path={result.get('path', '')}; "
        "attempt_log_is_not_claim_status"
    )


def validate_attempt_artifact(repo_root: Path, path_text: str) -> str:
    if not path_text:
        raise IdtRagError("artifact path must be non-empty")
    path = Path(path_text)
    if path.is_absolute():
        candidate = path.resolve()
    else:
        candidate = (repo_root / path).resolve()
    try:
        relative = candidate.relative_to(repo_root)
    except ValueError as error:
        raise IdtRagError(f"artifact path escapes repo root: {path_text}") from error
    relative_text = relative.as_posix()
    if relative_text.startswith((".git/", ".lake/", "dist/")):
        raise IdtRagError(f"artifact path points to generated or internal path: {relative_text}")
    if os.sep == "\\":
        return relative_text.replace("\\", "/")
    return relative_text
