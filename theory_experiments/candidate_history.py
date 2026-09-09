"""Durable observations, not truth labels; fresh cross-version regression checks.

The archive directory is trusted, as is a Git-reviewed baseline selection.
Publication never overwrites history. Digests detect corruption, not forgery.
"""

from __future__ import annotations

import gzip
import json
import os
import re
import stat
import tempfile
from dataclasses import dataclass
from pathlib import Path

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import (
    Limits,
    bounded_int,
    canonical_json,
    object_fields,
    parse_limits,
    reject_duplicate_keys,
    reject_nonexact_number,
)

DEFAULT_HISTORY = pipeline.ROOT / "data/candidate_history"
SCHEMA = "idt-candidate-history/1"
MAX_BYTES = 16 * 1024 * 1024


def _key(value: object) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("invalid history digest")
    return value


def _list(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("history array required")
    return list(value)


def _read(path: Path) -> dict[str, object]:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise ValueError("history entry must be a regular file")
        if path.suffix == ".gz":
            with gzip.GzipFile(fileobj=source) as compressed:
                raw = compressed.read(MAX_BYTES + 1)
        else:
            raw = source.read(MAX_BYTES + 1)
    if len(raw) > MAX_BYTES:
        raise ValueError("history entry exceeds size limit")
    value: object = json.loads(raw, object_pairs_hook=reject_duplicate_keys,
                              parse_float=reject_nonexact_number,
                              parse_constant=reject_nonexact_number)
    return object_fields(value)


def _publish(path: Path, value: dict[str, object]) -> None:
    raw = (canonical_json(value) + "\n").encode("utf-8")
    if len(raw) > MAX_BYTES:
        raise ValueError("history entry exceeds size limit")
    if path.suffix == ".gz":
        raw = gzip.compress(raw, mtime=0)
    descriptor, temporary = tempfile.mkstemp(prefix=".history-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(raw)
            output.flush()
            os.fsync(output.fileno())
        try:
            os.link(temporary, path)
            directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        except FileExistsError:
            if canonical_json(_read(path)) != canonical_json(value):
                raise ValueError("conflicting history entry; nothing overwritten") from None
    finally:
        os.unlink(temporary)


@dataclass(frozen=True)
class History:
    root: Path = DEFAULT_HISTORY

    def _directory(self, name: str, *, create: bool = False) -> Path:
        directory = self.root / name
        # The parent filesystem is trusted; refuse symlinked archive roots/subdirectories.
        if self.root.is_symlink() or directory.is_symlink():
            raise ValueError("history directories must not be symlinks")
        if create:
            directory.mkdir(parents=True, exist_ok=True)
        return directory

    def put(self, kind: str, value: dict[str, object]) -> str:
        if kind not in ("submissions", "observations") or value.get("schema") != SCHEMA:
            raise ValueError("invalid history record kind/schema")
        key = pipeline.digest(value)
        suffix = ".json.gz" if kind == "observations" else ".json"
        _publish(self._directory(kind, create=True) / (key + suffix), value)
        return key

    def get(self, kind: str, key: str) -> dict[str, object]:
        if kind not in ("submissions", "observations"):
            raise ValueError("invalid history record kind")
        suffix = ".json.gz" if kind == "observations" else ".json"
        value = _read(self._directory(kind) / (_key(key) + suffix))
        if value.get("schema") != SCHEMA or pipeline.digest(value) != key:
            raise ValueError("history integrity/schema mismatch")
        return value

    def submit(self, specifications: list[object], limits: Limits) -> str:
        bounded_int(len(specifications), 1, 64)
        # Keep the submitted representation, including unsupported families, before parsing.
        if len(canonical_json(specifications).encode("utf-8")) > 131072:
            raise ValueError("candidate submission exceeds 128 KiB")
        return self.put("submissions", {"schema": SCHEMA, "candidates": specifications,
                                        "limits": limits.specification()})

    def observe(self, submission: str, reports: list[object], *, error: str | None = None) -> str:
        submitted = self.get("submissions", submission)
        if error is None:
            specs = _list(submitted["candidates"])
            for spec, item in zip(specs, reports):
                request = object_fields(object_fields(item)["request"])
                if canonical_json(pipeline.parse_hypothesis(spec).specification()) != canonical_json(request["candidate"]):
                    raise ValueError("observation does not evaluate the submitted candidate")
        record: dict[str, object] = {"schema": SCHEMA, "submission": _key(submission),
                                    "reports": reports, "execution_error": error,
                                    "capture_provenance": pipeline.provenance()}
        validate_observation(submitted, record)
        return self.put("observations", record)

    def pin_initial(self, submission: str, observation: str) -> None:
        record = self.get("observations", observation)
        if record["submission"] != submission or record["execution_error"] is not None:
            raise ValueError("only a matching completed observation can initialize a baseline")
        path = self._directory("baselines", create=True) / (_key(submission) + ".json")
        value: dict[str, object] = {"schema": SCHEMA, "submission": submission,
            "observation": _key(observation),
            "reason": "Initial computational observation only; not a physical truth label."}
        try:
            _publish(path, value)
        except ValueError:
            # Another valid initial observation may already be pinned. Never replace it.
            self.baseline(submission)

    def baseline(self, submission: str) -> dict[str, object]:
        pin = object_fields(_read(self._directory("baselines") / (_key(submission) + ".json")),
                            {"schema", "submission", "observation", "reason"})
        reason = pin["reason"]
        if (pin["schema"] != SCHEMA or pin["submission"] != submission
                or not isinstance(reason, str) or not reason.strip()):
            raise ValueError("invalid history baseline; an explicit review reason is required")
        record = self.get("observations", _key(pin["observation"]))
        if record["submission"] != submission or record["execution_error"] is not None:
            raise ValueError("baseline observation does not match submission")
        validate_observation(self.get("submissions", submission), record)
        return record


def validate_observation(submission: dict[str, object], record: dict[str, object]) -> None:
    object_fields(submission, {"schema", "candidates", "limits"})
    object_fields(record, {"schema", "submission", "reports", "execution_error", "capture_provenance"})
    object_fields(record["capture_provenance"])
    specs = _list(submission["candidates"])
    bounded_int(len(specs), 1, 64)
    parse_limits(submission["limits"])
    reports = _list(record["reports"])
    if record["execution_error"] is not None:
        if reports or not isinstance(record["execution_error"], str) or not record["execution_error"]:
            raise ValueError("invalid execution-error observation")
        return
    if len(reports) != len(specs):
        raise ValueError("history must retain every candidate, including rejected candidates")
    for spec, item in zip(specs, reports):
        report = object_fields(item)
        request = object_fields(report["request"])
        # Historical decoding does not run today's adapter: a removed adapter must not
        # erase the old evidence or prevent rechecking the other candidates. Normalized
        # input binding is checked on publication; both raw and normalized inputs are kept.
        if (object_fields(request["candidate"])["id"] != object_fields(spec)["id"]
                or canonical_json(request["limits"]) != canonical_json(submission["limits"])):
            raise ValueError("historical report input/bounds mismatch")
        semantic_report(report)


def semantic_report(report: dict[str, object]) -> dict[str, object]:
    """Compare all evidence except request provenance/protocol metadata.

    Requirements, assumptions, coverage, witnesses and proof/empirical boundaries
    remain significant even when the aggregate verdict has not changed.
    """
    result = {key: value for key, value in report.items() if key != "request"}
    request = object_fields(report["request"])
    result["input"] = {key: value for key, value in request.items() if key not in ("schema", "provenance")}
    checks: dict[str, object] = {}
    for item in _list(report["checks"]):
        check = object_fields(item)
        name = check.get("id")
        if not isinstance(name, str) or name in checks:
            raise ValueError("invalid or duplicate historical check id")
        checks[name] = check
    result["checks"] = checks
    return result


def _changed_paths(before: object, after: object, prefix: str = "") -> list[str]:
    if isinstance(before, dict) and isinstance(after, dict):
        left, right = object_fields(before), object_fields(after)
        changes: list[str] = []
        for key in sorted(set(left) | set(right)):
            path = f"{prefix}.{key}" if prefix else key
            if key not in left or key not in right:
                changes.append(path)
            else:
                changes.extend(_changed_paths(left[key], right[key], path))
        return changes
    return [] if canonical_json(before) == canonical_json(after) else [prefix]


def compare(before: dict[str, object], after: list[object]) -> list[dict[str, object]]:
    previous = _list(before["reports"])
    if len(previous) != len(after):
        raise ValueError("comparison cannot drop candidates")
    changes: list[dict[str, object]] = []
    for index, (old, new) in enumerate(zip(previous, after)):
        left, right = object_fields(old), object_fields(new)
        paths = _changed_paths(semantic_report(left), semantic_report(right))
        if paths:
            candidate = object_fields(object_fields(left["request"])["candidate"])
            changes.append({"index": index, "candidate_id": candidate["id"],
                "before": left["status"], "after": right["status"], "changed_paths": paths})
    return changes


@dataclass(frozen=True)
class RecordedRun:
    results: tuple[pipeline.Result, ...]
    submission: str
    observation: str
    changes: list[dict[str, object]]


def record_batch(specifications: list[object], limits: Limits | None = None,
                 cache_dir: Path | None = None, *, fresh: bool = False,
                 history: History | None = None) -> RecordedRun:
    archive = history if history is not None else History()
    limits = limits if limits is not None else Limits()
    submission = archive.submit(specifications, limits)
    try:
        results = pipeline.run_batch(specifications, limits, cache_dir, fresh=fresh)
        reports: list[object] = [result.report for result in results]
        observation = archive.observe(submission, reports)
    except Exception as error:
        # A crash is not a counterexample. Even if error publication fails, input is already kept.
        archive.observe(submission, [], error=f"{type(error).__name__}: {error}")
        raise
    archive.pin_initial(submission, observation)
    return RecordedRun(results, submission, observation, compare(archive.baseline(submission), reports))


def recheck_history(history: History, *, record: bool = False) -> dict[str, object]:
    """Recompute every submitted candidate at its original bounds; never update pins."""
    submissions = sorted(history._directory("submissions").glob("*.json"))
    if not submissions:
        raise ValueError("candidate history is empty")
    keys = {path.stem for path in submissions}
    # Validate every retained generation, including non-baseline observations.
    observation_count = 0
    for path in sorted(history._directory("observations").glob("*.json.gz")):
        saved = history.get("observations", path.name.removesuffix(".json.gz"))
        submission = _key(saved["submission"])
        if submission not in keys:
            raise ValueError("orphaned observation: candidate submission is missing")
        validate_observation(history.get("submissions", submission), saved)
        observation_count += 1
    for path in history._directory("baselines").glob("*.json"):
        if path.stem not in keys:
            raise ValueError("orphaned baseline: candidate submission is missing")
    changes: list[dict[str, object]] = []
    errors: list[dict[str, object]] = []
    candidates = 0
    sources = pipeline.provenance()
    if sources.get("source_sha256") != pipeline.LOADED_SOURCE_HASHES:
        raise ValueError("sources changed since import; restart before history recheck")
    for path in submissions:
        key = path.stem
        saved = history.get("submissions", key)
        specs = _list(saved["candidates"])
        candidates += len(specs)
        try:
            baseline = history.baseline(key)
        except FileNotFoundError:
            baseline = None
        reports: list[object] = []
        batch_errors: list[dict[str, object]] = []
        batch_changes: list[dict[str, object]] = []
        limits = parse_limits(saved["limits"])
        for index, spec in enumerate(specs):
            try:
                # One adapter failure must not hide the rest of a historical batch.
                # No disk cache and no filtering by previous verdict.
                result = pipeline.run_batch([spec], limits, fresh=True)[0]
            except (ValueError, TypeError, OSError, KeyError, RuntimeError, AssertionError, ArithmeticError) as error:
                batch_errors.append({"submission": key, "index": index,
                    "execution_error": f"{type(error).__name__}: {error}",
                    "meaning": "checker_error_not_candidate_rejection"})
            else:
                reports.append(result.report)
                if baseline is not None:
                    previous = _list(baseline["reports"])[index]
                    batch_changes.extend({**change, "index": index} for change in
                                         compare({"reports": [previous]}, [result.report]))
            if pipeline.provenance() != sources:
                raise ValueError("sources changed during history recheck; no comparison accepted")
        observation = None
        if record:
            observation = (history.observe(key, [], error=canonical_json(batch_errors)) if batch_errors
                           else history.observe(key, reports))
        errors.extend(batch_errors)
        if baseline is None:
            changes.append({"submission": key, "reason": "missing_baseline_requires_review",
                            "current_observation": observation})
        else:
            changes.extend({"submission": key, "current_observation": observation, **change}
                           for change in batch_changes)
    return {"schema": SCHEMA, "status": "review_required" if changes or errors else "unchanged",
            "submissions": len(submissions), "candidates": candidates,
            "retained_observations": observation_count, "changes": changes, "errors": errors,
            "meaning": "regression_comparison_not_a_physical_truth_verdict"}
