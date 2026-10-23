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
from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    evaluate_amplitude_algebra,
    evaluate_archived_source,
    parse_amplitude_algebra,
)
from theory_experiments.bell_trial_test import (
    BellLocalResponse,
    evaluate_bell_local_response,
    parse_bell_local_response,
)
from theory_experiments.bell_trial_test import (
    assert_loaded_sources as assert_bell_sources,
)
from theory_experiments.identical_particles import (
    IdenticalPairAmplitudes,
    evaluate_identical_pair,
    parse_identical_pair,
)
from theory_experiments.native_bell_bridge import (
    NativeBellBridge,
    evaluate_native_bell_bridge,
    parse_native_bell_bridge,
)
from theory_experiments.native_readout_probe import (
    NativeReadoutProbe,
    evaluate_native_readout_probe,
    parse_native_readout_probe,
)
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
from theory_experiments.published_observation import (
    PublishedObservation,
    evaluate_published_observation,
    parse_published_observation,
)
from theory_experiments.quadratic_certificate import certify, verify_certificate
from theory_experiments.source_candidate import (
    SourceCandidate,
    parse_source_candidate,
)
from theory_experiments.universe_bench import (
    UniverseBench,
    evaluate_universe_bench,
    parse_universe_bench,
)

Hypothesis: TypeAlias = (
    primitive.Candidate | PhysicsCandidate | SourceCandidate | AmplitudeAlgebra | IdenticalPairAmplitudes | UniverseBench
    | PublishedObservation | BellLocalResponse | NativeBellBridge | NativeReadoutProbe
)
ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "idt-hypothesis-screen/2"
CACHE_SCHEMA = "idt-screen-cache/1"
SOURCE_PATHS = tuple(sorted(set(primitive.SOURCE_PATHS) | {
    "theory_experiments/__init__.py",
    "theory_experiments/candidate_pipeline.py", "theory_experiments/physics_screen.py",
    "theory_experiments/quadratic_certificate.py",
    "theory_experiments/candidate_history.py", "scripts/check_candidate_history.py",
    "theory_experiments/source_candidate.py", "theory_experiments/amplitude_algebra.py",
    "theory_experiments/universe_bench.py",
    "theory_experiments/native_bell_bridge.py", "data/native_bell_bridge_controls.json",
    "theory_experiments/native_readout_probe.py", "data/native_readout_controls.json",
    "Proofs/QMClosure/NativeReadoutSelection.lean",
    "Proofs/QMClosure/NativeBellScaledBridge.lean",
    "theory_experiments/published_observation.py",
    "theory_experiments/bell_trial_test.py", "scripts/replay_hensen2015.py",
    "data/raw_observations/hensen2015.json", "data/bell_local_response_controls.json",
    "Proofs/QMClosure/BellLocalTrialNull.lean",
    "data/published_observations/sinha2010_hsps_kappa.json",
    "Proofs/QMClosure/PublishedSorkinNull.lean",
    "lakefile.lean", "lean-toolchain",
    "theory_experiments/identical_particles.py", "scripts/check_identical_particles.py",
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
    if row.get("family") == "native_readout_probe":
        return parse_native_readout_probe(row)
    if row.get("family") == "native_bell_bridge":
        return parse_native_bell_bridge(row)
    if row.get("family") == "bell_local_response":
        return parse_bell_local_response(row)
    if row.get("family") == "published_observation":
        return parse_published_observation(row)
    if row.get("family") == "universe_bench":
        return parse_universe_bench(row)
    if row.get("family") == "identical_pair_amplitudes":
        return parse_identical_pair(row)
    if row.get("family") == "amplitude_algebra":
        return parse_amplitude_algebra(row)
    if row.get("family") == "source_theory":
        return parse_source_candidate(row)
    return (parse_physics(row) if row.get("family") in ("qm_readout", "sm_chiral")
            else primitive.parse_candidate(row))


def controls() -> dict[str, Hypothesis]:
    result: dict[str, Hypothesis] = dict(primitive.builtin_candidates())
    result.update(physics_controls())
    return result


def request_for(candidate: Hypothesis, limits: Limits, sources: dict[str, object]) -> dict[str, object]:
    return {"schema": SCHEMA, "candidate": candidate.specification(),
            "limits": limits.specification(), "provenance": sources}


def _certified_kernel_check(candidate: primitive.PairKernel, certificate: object) -> Check:
    if not verify_certificate(candidate.matrix, certificate):
        raise ValueError("invalid positivity certificate: checker error, not candidate rejection")
    row = object_fields(certificate)
    negative = row["kind"] == "negative_direction"
    witness = ({"inputs": {"reference_vector": row["vector"]},
                "actual": row["normalized_reference_weight"], "required": ">=0"} if negative else None)
    return Check("exact_kernel_positivity",
                 "counterexample" if negative else "no_counterexample_within_bounds",
                 1, 1, ">=0", ("symmetric_rational_kernel_dimension_1_to_3",
                     "admit_all_normalized_signed_rank_one_references_with_nonzero_sum",
                     "tensor_multiplication", "exact_algebraic_certificate_not_Lean_proof"), witness)


def compute(candidate: Hypothesis, limits: Limits, request: dict[str, object]) -> dict[str, object]:
    checks: tuple[Check, ...]
    details: dict[str, object]
    if isinstance(candidate, NativeReadoutProbe):
        checks, details = evaluate_native_readout_probe(candidate, limits)
    elif isinstance(candidate, NativeBellBridge):
        checks, details = evaluate_native_bell_bridge(candidate, limits)
    elif isinstance(candidate, BellLocalResponse):
        checks, details = evaluate_bell_local_response(candidate, limits)
    elif isinstance(candidate, PublishedObservation):
        checks, details = evaluate_published_observation(candidate, limits)
    elif isinstance(candidate, SourceCandidate):
        checks, details = evaluate_archived_source(candidate, limits)
    elif isinstance(candidate, UniverseBench):
        checks, details = evaluate_universe_bench(candidate, limits)
    elif isinstance(candidate, IdenticalPairAmplitudes):
        checks, details = evaluate_identical_pair(candidate, limits)
    elif isinstance(candidate, AmplitudeAlgebra):
        checks, details = evaluate_amplitude_algebra(candidate, limits)
    elif isinstance(candidate, QuantumReadout):
        checks, details = evaluate_qm(candidate, limits), scope(candidate)
    elif isinstance(candidate, ChiralSpectrum):
        checks, details = evaluate_sm(candidate, limits), scope(candidate)
    else:
        checks, details = primitive.evaluate(candidate, limits), {"untested": list(primitive.UNTESTED)}
        if isinstance(candidate, primitive.PairKernel):
            certificate = certify(candidate.matrix)
            checks += (_certified_kernel_check(candidate, certificate),)
            details["positivity_certificate"] = certificate
            details["positivity_scope"] = "all_rational_coefficient_vectors_for_this_supplied_matrix"
            details["positivity_coverage"] = "one_exact_certificate_not_one_sampled_direction"
    completed_observation = isinstance(candidate, PublishedObservation) and details["execution_status"] == "complete"
    return {"request": request, "status": primitive.aggregate_status(checks),
            "checks": [check.specification() for check in checks], "scope": details,
            "arithmetic": "exact_rational", "evidence_kind": "computation_with_explicit_algebraic_or_bounded_scope",
            "proof_status": "not_attempted",
            "empirical_status": (details["empirical_status"] if isinstance(candidate, BellLocalResponse)
                                 else "published_summary_compared_conditionally" if completed_observation else "not_tested"),
            "rejection_scope": ("conditional_statistical_null_and_bridges_not_exact_counterexample"
                                if isinstance(candidate, BellLocalResponse)
                                else "no_primitive_rejection_descriptive_comparison_only"
                                if isinstance(candidate, PublishedObservation)
                                else "no_primitive_rejection_execution_diagnostics_only"
                                if isinstance(candidate, (NativeBellBridge, NativeReadoutProbe))
                                else "candidate_plus_stated_imports_and_selected_requirements")}


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
    candidate = parse_hypothesis(request["candidate"])
    if isinstance(candidate, primitive.PairKernel):
        # A cache hit rechecks the small certificate, not the expensive search/generation.
        certificate = object_fields(report["scope"]).get("positivity_certificate")
        exact_check = _certified_kernel_check(candidate, certificate)
        checks = report["checks"]
        if (not isinstance(checks, list) or not checks
                or canonical_json(checks[-1]) != canonical_json(exact_check.specification())
                or (exact_check.status == "counterexample" and report["status"] != "counterexample")):
            raise ValueError("cached positivity check/status disagrees with verified certificate")
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
    if any(isinstance(candidate, BellLocalResponse) for candidate in candidates):
        assert_bell_sources()
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
