"""Batch exact screens with a conservative, local, content-addressed result cache."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import stat
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import TypeAlias

from theory_experiments import primitive_screen as primitive
from theory_experiments.physics_screen import (
    ChiralSpectrum,
    PhysicsCandidate,
    QuantumReadout,
    evaluate_qm,
    evaluate_sm,
    parse_physics,
    physics_controls,
    scope,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    canonical_json,
    object_fields,
    parse_limits,
)

Hypothesis: TypeAlias = primitive.Candidate | PhysicsCandidate
ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "idt-hypothesis-screen/1"
CACHE_SCHEMA = "idt-screen-cache/1"
SOURCE_PATHS = tuple(sorted(set(primitive.SOURCE_PATHS) | {
    "theory_experiments/__init__.py",
    "theory_experiments/candidate_pipeline.py", "theory_experiments/physics_screen.py",
    "scripts/screen_hypotheses.py", "HYPOTHESIS_PIPELINE.md",
}))


def digest(value: object) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def provenance() -> dict[str, object]:
    # Conservative superset: an unrelated backend edit may miss the cache, never reuse stale work.
    return {"source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                              for path in SOURCE_PATHS},
            "runtime": {"implementation": platform.python_implementation(),
                        "version": sys.version, "platform": platform.platform(),
                        "machine": platform.machine()}}


# A long-lived interpreter must not label old loaded code with new on-disk hashes.
LOADED_SOURCE_HASHES = provenance()["source_sha256"]


def parse_hypothesis(value: object) -> Hypothesis:
    row = object_fields(value)
    return (parse_physics(row) if row.get("family") in ("qm_readout", "sm_chiral")
            else primitive.parse_candidate(row))


def controls() -> dict[str, Hypothesis]:
    result: dict[str, Hypothesis] = dict(primitive.builtin_candidates())
    result.update(physics_controls())
    return result


def request_for(candidate: Hypothesis, limits: Limits, sources: dict[str, object]) -> dict[str, object]:
    return {"schema": SCHEMA, "candidate": candidate.specification(),
            "limits": limits.specification(), "provenance": sources}


def compute(candidate: Hypothesis, limits: Limits, request: dict[str, object]) -> dict[str, object]:
    checks: tuple[Check, ...]
    details: dict[str, object]
    if isinstance(candidate, QuantumReadout):
        checks, details = evaluate_qm(candidate, limits), scope(candidate)
    elif isinstance(candidate, ChiralSpectrum):
        checks, details = evaluate_sm(candidate, limits), scope(candidate)
    else:
        checks, details = primitive.evaluate(candidate, limits), {"untested": list(primitive.UNTESTED)}
    return {"request": request, "status": primitive.aggregate_status(checks),
            "checks": [check.specification() for check in checks], "scope": details,
            "arithmetic": "exact_rational", "evidence_kind": "bounded_computation",
            "proof_status": "not_attempted", "empirical_status": "not_tested",
            "rejection_scope": "candidate_plus_stated_imports_and_selected_requirements"}


def read_entry(path: Path, request: dict[str, object]) -> dict[str, object]:
    # Refuse symlinks, non-regular files, oversized and partial entries. The directory is trusted.
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise ValueError("cache entry is not a regular file")
        raw = source.read(524289)
    if len(raw) > 524288:
        raise ValueError("cache entry exceeds 512 KiB")
    value: object = json.loads(raw, object_pairs_hook=primitive.reject_duplicate_keys,
                              parse_float=primitive.reject_nonexact_number,
                              parse_constant=primitive.reject_nonexact_number)
    envelope = object_fields(value, {"schema", "key", "report_sha256", "report"})
    report = object_fields(envelope["report"], {"request", "status", "checks", "scope",
        "arithmetic", "evidence_kind", "proof_status", "empirical_status", "rejection_scope"})
    if (envelope["schema"] != CACHE_SCHEMA or envelope["key"] != digest(request)
            or canonical_json(report["request"]) != canonical_json(request)
            or envelope["report_sha256"] != digest(report)):
        raise ValueError("cache integrity/request mismatch; use a new directory and recompute")
    return report


def publish(path: Path, report: dict[str, object], request: dict[str, object]) -> None:
    envelope = {"schema": CACHE_SCHEMA, "key": digest(request),
                "report_sha256": digest(report), "report": report}
    # Hard-link publication is atomic and refuses replacement, including a competing publisher.
    descriptor, temporary = tempfile.mkstemp(prefix=".screen-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(canonical_json(envelope) + "\n")
            output.flush()
            os.fsync(output.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError:
            if canonical_json(read_entry(path, request)) != canonical_json(report):
                raise ValueError("fresh computation disagrees with existing cache; nothing overwritten") from None
    finally:
        os.unlink(temporary)


@dataclass(frozen=True)
class Result:
    report: dict[str, object]
    key: str
    reused: bool
    artifact: Path | None

    def card(self) -> dict[str, object]:
        request = object_fields(self.report["request"])
        candidate = object_fields(request["candidate"])
        values = self.report["checks"]
        if not isinstance(values, list):
            raise TypeError("invalid report checks")
        checks = [object_fields(value) for value in values]
        return {"id": candidate["id"], "family": candidate["family"],
                "status": self.report["status"], "reused": self.reused,
                "checks": [{"id": row["id"], "status": row["status"],
                            "checked": row["checked"], "planned": row["planned"],
                            "actual": None if row["witness"] is None else
                            object_fields(row["witness"])["actual"]} for row in checks],
                "artifact": str(self.artifact) if self.artifact else None,
                "key": self.key, "proof_status": self.report["proof_status"],
                "empirical_status": self.report["empirical_status"]}


def run_batch(specifications: list[object], limits: Limits | None = None,
              cache_dir: Path | None = None, *, fresh: bool = False) -> tuple[Result, ...]:
    primitive.bounded_int(len(specifications), 1, 64)
    # Validate the entire input before creating cache files.
    candidates = tuple(parse_hypothesis(value) for value in specifications)
    limits = limits if limits is not None else Limits()
    sources = provenance()
    if sources.get("source_sha256") != LOADED_SOURCE_HASHES:
        raise ValueError("sources changed since import; restart the interpreter from a stable checkout")
    if cache_dir is not None:
        cache_dir = cache_dir.resolve()
        cache_dir.mkdir(parents=True, exist_ok=True)
    results: list[Result] = []
    memory: dict[str, dict[str, object]] = {}
    for candidate in candidates:
        request = request_for(candidate, limits, sources)
        key = digest(request)
        path = cache_dir / (key + ".json") if cache_dir else None
        reused = False
        report = memory.get(key)
        if report is not None:
            reused = True
        elif path is not None and not fresh:
            try:
                report = read_entry(path, request)
                reused = True
            except FileNotFoundError:
                pass
        if report is None:
            report = compute(candidate, limits, request)
            if provenance() != sources:
                raise ValueError("sources changed during batch; rerun from a stable checkout")
            if path is not None:
                publish(path, report, request)
        memory[key] = report
        results.append(Result(report, key, reused, path))
    if provenance() != sources:
        raise ValueError("sources changed during batch; no batch result returned")
    return tuple(results)


def replay_artifact(path: Path) -> dict[str, object]:
    envelope = object_fields(primitive.load_json(path))
    saved = object_fields(envelope.get("report"))
    request = object_fields(saved.get("request"), {"schema", "candidate", "limits", "provenance"})
    saved = read_entry(path, request)
    candidate = parse_hypothesis(request["candidate"])
    limits = parse_limits(request["limits"])
    current_request = request_for(candidate, limits, provenance())
    if (object_fields(current_request["provenance"]).get("source_sha256") != LOADED_SOURCE_HASHES
            or canonical_json(current_request) != canonical_json(request)):
        raise ValueError("replay sources/runtime/request differ")
    current = compute(candidate, limits, current_request)
    if provenance() != current_request["provenance"] or canonical_json(current) != canonical_json(saved):
        raise ValueError("replay mismatch")
    return current


def exit_code(results: tuple[Result, ...]) -> int:
    statuses = [result.report["status"] for result in results]
    if "counterexample" in statuses:
        return 1
    return 0 if statuses and all(x == "no_counterexample_within_bounds" for x in statuses) else 3
