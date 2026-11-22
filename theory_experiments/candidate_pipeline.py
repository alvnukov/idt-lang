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
from functools import lru_cache
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
from theory_experiments.binary_overlap_cut import (
    LOADED_SOURCE_SHA256 as BINARY_OVERLAP_CUT_LOADED_SOURCE_SHA256,
)
from theory_experiments.binary_overlap_cut import (
    SCOPE as BINARY_OVERLAP_CUT_SCOPE,
)
from theory_experiments.binary_overlap_cut import (
    BinaryOverlapCut,
    evaluate_binary_overlap_cut,
    parse_binary_overlap_cut,
)
from theory_experiments.chiral_pencil import (
    LOADED_SOURCE_SHA256 as CHIRAL_PENCIL_LOADED_SOURCE_SHA256,
)
from theory_experiments.chiral_pencil import (
    ChiralPencil,
    evaluate_chiral_pencil,
    parse_chiral_pencil,
)
from theory_experiments.driven_event_selector import (
    LOADED_SOURCE_SHA256 as DRIVEN_EVENT_SELECTOR_LOADED_SOURCE_SHA256,
)
from theory_experiments.driven_event_selector import (
    DrivenEventSelector,
    evaluate_driven_event_selector,
    parse_driven_event_selector,
)
from theory_experiments.identical_particles import (
    IdenticalPairAmplitudes,
    evaluate_identical_pair,
    parse_identical_pair,
)
from theory_experiments.marked_relay import (
    LOADED_SOURCE_SHA256 as MARKED_RELAY_LOADED_SOURCE_SHA256,
)
from theory_experiments.marked_relay import (
    MarkedRelay,
    evaluate_marked_relay,
    parse_marked_relay,
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
from theory_experiments.native_readout_search import (
    NativeReadoutSearch,
    evaluate_native_readout_search,
    parse_native_readout_search,
)
from theory_experiments.neutral_current_width import (
    DATA_PATH as NEUTRAL_WIDTH_DATA_PATH,
)
from theory_experiments.neutral_current_width import (
    DATA_SHA256 as NEUTRAL_WIDTH_DATA_SHA256,
)
from theory_experiments.neutral_current_width import (
    LOADED_SOURCE_SHA256 as NEUTRAL_WIDTH_LOADED_SOURCE_SHA256,
)
from theory_experiments.neutral_current_width import (
    NeutralCurrentWidth,
    evaluate_neutral_current_width,
    parse_neutral_current_width,
)
from theory_experiments.neutral_current_width import (
    assert_loaded_sources as assert_neutral_width_sources,
)
from theory_experiments.opposition_flag import (
    OppositionFlag,
    evaluate_opposition_flag,
    parse_opposition_flag,
)
from theory_experiments.periodic_contact_observer import (
    LOADED_SOURCE_SHA256 as PERIODIC_CONTACT_LOADED_SOURCE_SHA256,
)
from theory_experiments.periodic_contact_observer import (
    SCOPE as PERIODIC_CONTACT_SCOPE,
)
from theory_experiments.periodic_contact_observer import (
    PeriodicContactObserver,
    evaluate_periodic_contact_observer,
    parse_periodic_contact_observer,
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
from theory_experiments.prepare_measure_cut import (
    LOADED_SOURCE_SHA256 as PREPARE_MEASURE_CUT_LOADED_SOURCE_SHA256,
)
from theory_experiments.prepare_measure_cut import (
    RANK_CHECK_ID,
    TRACE_CHECK_ID,
    PrepareMeasureCut,
    evaluate_prepare_measure_cut,
    parse_prepare_measure_cut,
)
from theory_experiments.prepare_measure_cut import (
    SCOPE as PREPARE_MEASURE_CUT_SCOPE,
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
from theory_experiments.relational_germ_observer import (
    LOADED_SOURCE_SHA256 as RELATIONAL_GERM_LOADED_SOURCE_SHA256,
)
from theory_experiments.relational_germ_observer import (
    SCOPE as RELATIONAL_GERM_SCOPE,
)
from theory_experiments.relational_germ_observer import (
    RelationalGermObserver,
    evaluate_relational_germ_observer,
    parse_relational_germ_observer,
)
from theory_experiments.source_candidate import (
    SourceCandidate,
    parse_source_candidate,
)
from theory_experiments.triangle_stock import (
    LOADED_SOURCE_SHA256 as TRIANGLE_STOCK_LOADED_SOURCE_SHA256,
)
from theory_experiments.triangle_stock import (
    TriangleStock,
    evaluate_triangle_stock,
    parse_triangle_stock,
)
from theory_experiments.universe_bench import (
    UniverseBench,
    evaluate_universe_bench,
    parse_universe_bench,
)
from theory_experiments.unsigned_pair_packet import (
    UnsignedPairPacket,
    evaluate_unsigned_pair_packet,
    parse_unsigned_pair_packet,
)

Hypothesis: TypeAlias = (
    primitive.Candidate | PhysicsCandidate | SourceCandidate | AmplitudeAlgebra | IdenticalPairAmplitudes | UniverseBench
    | PublishedObservation | BellLocalResponse | NativeBellBridge | NativeReadoutProbe | NativeReadoutSearch
    | UnsignedPairPacket | OppositionFlag | MarkedRelay | ChiralPencil | NeutralCurrentWidth | TriangleStock
    | DrivenEventSelector | PeriodicContactObserver | PrepareMeasureCut | BinaryOverlapCut | RelationalGermObserver
)
ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "idt-hypothesis-screen/2"
CACHE_SCHEMA = "idt-screen-cache/1"
_CACHE_MAX_BYTES = 512 * 1024
_PREPARE_MEASURE_EVIDENCE = "necessary_conditions_on_submitted_finite_table_only"
_BINARY_OVERLAP_EVIDENCE = "necessary_binary_overlap_bounds_on_submitted_event_table_only"
_RELATIONAL_GERM_EVIDENCE = "finite_local_germ_transport_and_submitted_tally_comparison_only"
SOURCE_PATHS = tuple(sorted(set(primitive.SOURCE_PATHS) | {
    "theory_experiments/__init__.py",
    "theory_experiments/candidate_pipeline.py", "theory_experiments/physics_screen.py",
    "theory_experiments/quadratic_certificate.py",
    "theory_experiments/candidate_history.py", "scripts/check_candidate_history.py",
    "theory_experiments/source_candidate.py", "theory_experiments/amplitude_algebra.py",
    "theory_experiments/universe_bench.py",
    "theory_experiments/unsigned_pair_packet.py",
    "theory_experiments/opposition_flag.py",
    "theory_experiments/marked_relay.py",
    "theory_experiments/chiral_pencil.py",
    "theory_experiments/neutral_current_width.py", NEUTRAL_WIDTH_DATA_PATH,
    "theory_experiments/triangle_stock.py",
    "theory_experiments/driven_event_selector.py",
    "theory_experiments/periodic_contact_observer.py",
    "theory_experiments/prepare_measure_cut.py",
    "theory_experiments/binary_overlap_cut.py",
    "theory_experiments/relational_germ_observer.py",
    "theory_experiments/native_bell_bridge.py", "data/native_bell_bridge_controls.json",
    "theory_experiments/native_readout_probe.py", "data/native_readout_controls.json",
    "theory_experiments/native_readout_search.py", "data/native_readout_search_controls.json",
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


def _is_marked_relay_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "marked_relay"


def _is_chiral_pencil_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "chiral_pencil"


def _is_neutral_width_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "neutral_current_width"


def _is_triangle_stock_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "triangle_stock"


def _is_driven_event_selector_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "driven_event_selector"


def _is_periodic_contact_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "periodic_contact_observer"


def _is_prepare_measure_cut_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "prepare_measure_cut"


def _is_binary_overlap_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "binary_overlap_cut"


def _is_relational_germ_spec(value: object) -> bool:
    return isinstance(value, dict) and value.get("family") == "relational_germ_observer"


def _assert_relational_germ_sources(sources: object, *, check_current: bool = False) -> None:
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded in (
        ("theory_experiments/relational_germ_observer.py", RELATIONAL_GERM_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded)):
            raise ValueError(f"relational germ source changed since import: {path}; restart from a stable checkout")


def _assert_binary_overlap_sources(sources: object, *, check_current: bool = False) -> None:
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded in (
        ("theory_experiments/binary_overlap_cut.py", BINARY_OVERLAP_CUT_LOADED_SOURCE_SHA256),
        ("theory_experiments/prepare_measure_cut.py", PREPARE_MEASURE_CUT_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded)):
            raise ValueError(f"binary overlap cut source changed since import: {path}; restart from a stable checkout")


def _assert_prepare_measure_cut_sources(sources: object, *, check_current: bool = False) -> None:
    """Pin stable loaded table-checker sources, not a physical data adapter."""
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/prepare_measure_cut.py", PREPARE_MEASURE_CUT_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"prepare-measure cut source changed since import: {path}; "
                             "restart from a stable checkout")


def _assert_periodic_contact_sources(sources: object, *, check_current: bool = False) -> None:
    """Pin the loaded finite checker and shared helpers, not a physical adapter."""
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/periodic_contact_observer.py", PERIODIC_CONTACT_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"periodic contact observer source changed since import: {path}; "
                             "restart from a stable checkout")


def _assert_driven_event_selector_sources(sources: object, *, check_current: bool = False) -> None:
    """Pin the loaded submitted-transducer checker and its primitive helpers.

    This assumes stable normal imports, not arbitrary loaders or interpreter
    attestation. Cache receipts do not attest a physical prediction adapter.
    """
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/driven_event_selector.py", DRIVEN_EVENT_SELECTOR_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"driven event selector source changed since import: {path}; restart from a stable checkout")


def _assert_triangle_stock_sources(sources: object, *, check_current: bool = False) -> None:
    """Refuse a stale loaded stock adapter or its directly used primitive helpers."""
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/triangle_stock.py", TRIANGLE_STOCK_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"triangle stock source changed since import: {path}; restart from a stable checkout")


def _assert_neutral_width_sources(sources: object, *, check_current: bool = False) -> None:
    """Refuse stale code or receipt bytes, including warm-cache and replay paths."""
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, expected_hash in (
        ("theory_experiments/neutral_current_width.py", NEUTRAL_WIDTH_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
        (NEUTRAL_WIDTH_DATA_PATH, NEUTRAL_WIDTH_DATA_SHA256),
    ):
        if (hashes.get(path) != expected_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected_hash)):
            raise ValueError(f"neutral-current source changed since import: {path}; restart from a stable checkout")
    assert_neutral_width_sources()


def _assert_chiral_pencil_sources(sources: object, *, check_current: bool = False) -> None:
    """Check the loaded pencil adapter and its directly used primitive helpers.

    Like the relay guard, this assumes a stable normal module import, not
    arbitrary loaders, in-process tampering or interpreter attestation.
    """
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/chiral_pencil.py", CHIRAL_PENCIL_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"chiral pencil source changed since import: {path}; restart from a stable checkout")


def _assert_marked_relay_sources(sources: object, *, check_current: bool = False) -> None:
    """Refuse preloaded modules changed on disk before this pipeline imported.

    This assumes a stable checkout during each normal module import. It covers
    the relay adapter and its directly used primitive helpers, not arbitrary
    loaders, in-process tampering, or the import history of other adapters.
    """
    hashes = object_fields(object_fields(sources)["source_sha256"])
    for path, loaded_hash in (
        ("theory_experiments/marked_relay.py", MARKED_RELAY_LOADED_SOURCE_SHA256),
        ("theory_experiments/primitive_screen.py", primitive.LOADED_SOURCE_SHA256),
    ):
        if (hashes.get(path) != loaded_hash or
                (check_current and hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != loaded_hash)):
            raise ValueError(f"marked relay source changed since import: {path}; restart from a stable checkout")


def parse_hypothesis(value: object) -> Hypothesis:
    row = object_fields(value)
    if _is_relational_germ_spec(row):
        return parse_relational_germ_observer(row)
    if _is_binary_overlap_spec(row):
        return parse_binary_overlap_cut(row)
    if row.get("family") == "prepare_measure_cut":
        return parse_prepare_measure_cut(row)
    if row.get("family") == "periodic_contact_observer":
        return parse_periodic_contact_observer(row)
    if row.get("family") == "driven_event_selector":
        return parse_driven_event_selector(row)
    if row.get("family") == "triangle_stock":
        return parse_triangle_stock(row)
    if row.get("family") == "neutral_current_width":
        return parse_neutral_current_width(row)
    if row.get("family") == "chiral_pencil":
        return parse_chiral_pencil(row)
    if row.get("family") == "marked_relay":
        return parse_marked_relay(row)
    if row.get("family") == "opposition_flag":
        return parse_opposition_flag(row)
    if row.get("family") == "unsigned_pair_packet":
        return parse_unsigned_pair_packet(row)
    if row.get("family") == "native_readout_search":
        return parse_native_readout_search(row)
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


def _bind_relational_germ(candidate: Hypothesis, limits: Limits, request: dict[str, object]) -> None:
    if (type(candidate) is not RelationalGermObserver or type(limits) is not Limits
            or set(request) != {"schema", "candidate", "limits", "provenance"} or request["schema"] != SCHEMA
            or canonical_json(request["candidate"]) != canonical_json(candidate.specification())
            or canonical_json(request["limits"]) != canonical_json(limits.specification())):
        raise ValueError("relational germ candidate/limits do not match request")
    _assert_relational_germ_sources(request["provenance"], check_current=True)


def _relational_germ_body(candidate: RelationalGermObserver, limits: Limits) -> dict[str, object]:
    checks, details = evaluate_relational_germ_observer(candidate, limits)
    return {"status": primitive.aggregate_status(checks), "checks": [c.specification() for c in checks],
            "scope": details, "arithmetic": "exact_finite_graph_and_integer_ballots",
            "evidence_kind": _RELATIONAL_GERM_EVIDENCE, "proof_status": "not_attempted",
            "empirical_status": "not_tested", "rejection_scope": RELATIONAL_GERM_SCOPE}


@lru_cache(maxsize=128)
def _verified_germ_body_digest(candidate: RelationalGermObserver, limits: Limits) -> str:
    # Only locally recomputed expected digests, never caller/file-provided
    # hashes. An unfamiliar disk receipt requires the bounded traversal once.
    # A verified repeat needs no domain evaluation. Candidate and limits are
    # exact frozen values; callers must validate loaded/disk pins on EVERY hit.
    return digest(_relational_germ_body(candidate, limits))


def _binary_overlap_report(candidate: Hypothesis, limits: Limits, request: dict[str, object]) -> dict[str, object]:
    """Bind the exact normalized objects and the loaded checker to this standalone table."""
    if (type(candidate) is not BinaryOverlapCut or type(limits) is not Limits
            or set(request) != {"schema", "candidate", "limits", "provenance"} or request["schema"] != SCHEMA
            or canonical_json(request["candidate"]) != canonical_json(candidate.specification())
            or canonical_json(request["limits"]) != canonical_json(limits.specification())):
        raise ValueError("binary overlap cut candidate/limits do not match request")
    _assert_binary_overlap_sources(request["provenance"], check_current=True)
    checks, details = evaluate_binary_overlap_cut(candidate, limits)
    return {"request": request, "status": primitive.aggregate_status(checks),
            "checks": [c.specification() for c in checks], "scope": details,
            "arithmetic": "exact_rational_outward_bounds", "evidence_kind": _BINARY_OVERLAP_EVIDENCE,
            "proof_status": "not_attempted", "empirical_status": "not_tested",
            "rejection_scope": BINARY_OVERLAP_CUT_SCOPE}


def compute(candidate: Hypothesis, limits: Limits, request: dict[str, object]) -> dict[str, object]:
    if isinstance(candidate, RelationalGermObserver) or _is_relational_germ_spec(request.get("candidate")):
        _bind_relational_germ(candidate, limits, request)
        return {"request": request, **_relational_germ_body(candidate, limits)}
    if isinstance(candidate, BinaryOverlapCut) or _is_binary_overlap_spec(request.get("candidate")):
        return _binary_overlap_report(candidate, limits, request)
    checks: tuple[Check, ...]
    details: dict[str, object]
    cut_receipt = isinstance(candidate, PrepareMeasureCut) or _is_prepare_measure_cut_spec(request.get("candidate"))
    if cut_receipt and (type(candidate) is not PrepareMeasureCut or type(limits) is not Limits
            or canonical_json(request.get("candidate")) != canonical_json(candidate.specification())
            or canonical_json(request.get("limits")) != canonical_json(limits.specification())):
        raise ValueError("prepare-measure cut candidate/limits do not match request")
    periodic_receipt = (isinstance(candidate, PeriodicContactObserver) or
                        _is_periodic_contact_spec(request.get("candidate")))
    if periodic_receipt and (type(candidate) is not PeriodicContactObserver or type(limits) is not Limits
            or canonical_json(request.get("candidate")) != canonical_json(candidate.specification())
            or canonical_json(request.get("limits")) != canonical_json(limits.specification())):
        raise ValueError("periodic contact observer candidate/limits do not match request")
    # A verdict must be for the supplied transducer and budget. Keep the
    # historical behavior of calls that do not involve this family.
    driven_receipt = isinstance(candidate, DrivenEventSelector) or _is_driven_event_selector_spec(request.get("candidate"))
    if driven_receipt and (not isinstance(candidate, DrivenEventSelector)
            or canonical_json(request.get("candidate")) != canonical_json(candidate.specification())
            or canonical_json(request.get("limits")) != canonical_json(limits.specification())):
        raise ValueError("driven event selector candidate/limits do not match request")
    if isinstance(candidate, PrepareMeasureCut):
        _assert_prepare_measure_cut_sources(request["provenance"], check_current=True)
        checks, details = evaluate_prepare_measure_cut(candidate, limits)
    elif isinstance(candidate, PeriodicContactObserver):
        _assert_periodic_contact_sources(request["provenance"], check_current=True)
        checks, details = evaluate_periodic_contact_observer(candidate, limits)
    elif isinstance(candidate, DrivenEventSelector):
        _assert_driven_event_selector_sources(request["provenance"], check_current=True)
        checks, details = evaluate_driven_event_selector(candidate, limits)
    elif isinstance(candidate, TriangleStock):
        _assert_triangle_stock_sources(request["provenance"], check_current=True)
        checks, details = evaluate_triangle_stock(candidate, limits)
    elif isinstance(candidate, NeutralCurrentWidth):
        _assert_neutral_width_sources(request["provenance"], check_current=True)
        checks, details = evaluate_neutral_current_width(candidate, limits)
    elif isinstance(candidate, ChiralPencil):
        _assert_chiral_pencil_sources(request["provenance"], check_current=True)
        checks, details = evaluate_chiral_pencil(candidate, limits)
    elif isinstance(candidate, MarkedRelay):
        _assert_marked_relay_sources(request["provenance"], check_current=True)
        checks, details = evaluate_marked_relay(candidate, limits)
    elif isinstance(candidate, OppositionFlag):
        checks, details = evaluate_opposition_flag(candidate, limits)
    elif isinstance(candidate, UnsignedPairPacket):
        checks, details = evaluate_unsigned_pair_packet(candidate, limits)
    elif isinstance(candidate, NativeReadoutSearch):
        checks, details = evaluate_native_readout_search(candidate, limits)
    elif isinstance(candidate, NativeReadoutProbe):
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
            "arithmetic": "exact_rational",
            "evidence_kind": ("descriptive_completion_only" if isinstance(candidate, NeutralCurrentWidth)
                              else _PREPARE_MEASURE_EVIDENCE if isinstance(candidate, PrepareMeasureCut)
                              else "computation_with_explicit_algebraic_or_bounded_scope"),
            "proof_status": "not_attempted",
            "empirical_status": (details["empirical_status"] if isinstance(candidate, BellLocalResponse)
                                 else "published_summary_compared_conditionally" if completed_observation else "not_tested"),
            "rejection_scope": ("published_summary_comparison_not_candidate_rejection"
                                if isinstance(candidate, NeutralCurrentWidth)
                                else "conditional_statistical_null_and_bridges_not_exact_counterexample"
                                if isinstance(candidate, BellLocalResponse)
                                else "no_primitive_rejection_descriptive_comparison_only"
                                if isinstance(candidate, PublishedObservation)
                                else "no_primitive_rejection_execution_diagnostics_only"
                                if isinstance(candidate, (NativeBellBridge, NativeReadoutProbe, NativeReadoutSearch))
                                else "declared_markers_origins_and_supplied_relay_target_only"
                                if isinstance(candidate, MarkedRelay)
                                else "specified_weighted_support_and_rank_holdout_only"
                                if isinstance(candidate, ChiralPencil)
                                else "only_submitted_quasipolynomial_and_gain_law"
                                if isinstance(candidate, TriangleStock)
                                else "only_submitted_finite_transducer_and_calibrated_reference"
                                if isinstance(candidate, DrivenEventSelector)
                                else PERIODIC_CONTACT_SCOPE
                                if isinstance(candidate, PeriodicContactObserver)
                                else PREPARE_MEASURE_CUT_SCOPE
                                if isinstance(candidate, PrepareMeasureCut)
                                else "candidate_plus_stated_imports_and_selected_requirements")}


def _assert_cache_request_sources(request: dict[str, object]) -> None:
    if _is_relational_germ_spec(request.get("candidate")):
        _assert_relational_germ_sources(request["provenance"], check_current=True)
    if _is_binary_overlap_spec(request.get("candidate")):
        _assert_binary_overlap_sources(request["provenance"], check_current=True)
    if _is_prepare_measure_cut_spec(request.get("candidate")):
        _assert_prepare_measure_cut_sources(request["provenance"], check_current=True)
    if _is_periodic_contact_spec(request.get("candidate")):
        _assert_periodic_contact_sources(request["provenance"], check_current=True)
    if _is_driven_event_selector_spec(request.get("candidate")):
        _assert_driven_event_selector_sources(request["provenance"], check_current=True)
    if _is_triangle_stock_spec(request.get("candidate")):
        _assert_triangle_stock_sources(request["provenance"], check_current=True)
    if _is_neutral_width_spec(request.get("candidate")):
        _assert_neutral_width_sources(request["provenance"], check_current=True)
    if _is_marked_relay_spec(request.get("candidate")):
        _assert_marked_relay_sources(request["provenance"], check_current=True)
    if _is_chiral_pencil_spec(request.get("candidate")):
        _assert_chiral_pencil_sources(request["provenance"], check_current=True)


def _load_cache_envelope(path: Path) -> dict[str, object]:
    # Refuse symlink entries, non-regular files, oversized and partial entries.
    # The directory is trusted; these checks do not authenticate its contents.
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise ValueError("cache entry is not a regular file")
        raw = source.read(_CACHE_MAX_BYTES + 1)
    if len(raw) > _CACHE_MAX_BYTES:
        raise ValueError("cache entry exceeds 512 KiB")
    value: object = json.loads(raw, object_pairs_hook=primitive.reject_duplicate_keys,
                              parse_float=primitive.reject_nonexact_number,
                              parse_constant=primitive.reject_nonexact_number)
    return object_fields(value, {"schema", "key", "report_sha256", "report"})


def _assert_cut_receipt_scope(candidate: PrepareMeasureCut, report: dict[str, object]) -> None:
    """Basic consistency of a trusted local receipt, not authentication or replay."""
    checks = report["checks"]
    if not isinstance(checks, list) or len(checks) != 2:
        raise ValueError("cached prepare-measure cut has invalid checks")
    statuses = []
    for check, expected in zip(checks, (RANK_CHECK_ID, TRACE_CHECK_ID), strict=True):
        row = object_fields(check)
        status = row.get("status")
        if row.get("id") != expected or status not in ("counterexample", "inconclusive", "unsupported"):
            raise ValueError("cached prepare-measure cut has invalid checks")
        statuses.append(status)
    aggregate = next(status for status in ("counterexample", "inconclusive", "unsupported") if status in statuses)
    details = object_fields(report["scope"])
    claim_limits = {"proof_status": "not_attempted", "empirical_status": "not_tested",
                    "rejection_scope": PREPARE_MEASURE_CUT_SCOPE}
    if (report["status"] != aggregate or report["evidence_kind"] != _PREPARE_MEASURE_EVIDENCE
            or any(report[key] != value or details.get(key) != value for key, value in claim_limits.items())
            or details.get("scientific_status") != "unassessed"
            or details.get("necessary_conditions_only") is not True
            or details.get("event") != candidate.event or details.get("event_basis") != candidate.event_basis
            or (candidate.event_basis == "accepted_only" and statuses != ["unsupported", "unsupported"])):
        raise ValueError("cached prepare-measure cut status/scope disagrees with the necessary-test contract")


def _validate_cache_entry(envelope: dict[str, object], request: dict[str, object]) -> dict[str, object]:
    report = object_fields(envelope["report"], {"request", "status", "checks", "scope",
        "arithmetic", "evidence_kind", "proof_status", "empirical_status", "rejection_scope"})
    if (envelope["schema"] != CACHE_SCHEMA or envelope["key"] != digest(request)
            or canonical_json(report["request"]) != canonical_json(request)
            or envelope["report_sha256"] != digest(report)):
        raise ValueError("cache integrity/request mismatch; use a new directory and recompute")
    candidate = parse_hypothesis(request["candidate"])
    if isinstance(candidate, RelationalGermObserver):
        limits = parse_limits(request["limits"])
        _bind_relational_germ(candidate, limits, request)
        if digest({k: v for k, v in report.items() if k != "request"}) != _verified_germ_body_digest(candidate, limits):
            raise ValueError("cached relational germ verdict/routes disagree with the bounded graph check")
    elif isinstance(candidate, BinaryOverlapCut):
        # Local hashes are integrity checks, not evidence of a true verdict.
        # Redo this finite binary-only arithmetic (at most 276 pairs x 24
        # settings), including outward rounding and budget. No wide search,
        # statistics, or other adapter is run on a warm hit.
        expected = _binary_overlap_report(candidate, parse_limits(request["limits"]), request)
        if canonical_json(report) != canonical_json(expected):
            raise ValueError("cached binary overlap verdict/certificate disagrees with its bounded check")
    elif isinstance(candidate, PrepareMeasureCut):
        _assert_cut_receipt_scope(candidate, report)
    elif isinstance(candidate, primitive.PairKernel):
        # A cache hit rechecks the small certificate, not the expensive search/generation.
        certificate = object_fields(report["scope"]).get("positivity_certificate")
        exact_check = _certified_kernel_check(candidate, certificate)
        checks = report["checks"]
        if (not isinstance(checks, list) or not checks
                or canonical_json(checks[-1]) != canonical_json(exact_check.specification())
                or (exact_check.status == "counterexample" and report["status"] != "counterexample")):
            raise ValueError("cached positivity check/status disagrees with verified certificate")
    return report


def read_entry(path: Path, request: dict[str, object]) -> dict[str, object]:
    _assert_cache_request_sources(request)
    return _validate_cache_entry(_load_cache_envelope(path), request)


def publish(path: Path, report: dict[str, object], request: dict[str, object]) -> None:
    envelope = {"schema": CACHE_SCHEMA, "key": digest(request),
                "report_sha256": digest(report), "report": report}
    raw = (canonical_json(envelope) + "\n").encode("utf-8")
    if len(raw) > _CACHE_MAX_BYTES:
        raise ValueError("cache entry exceeds 512 KiB")
    saved_request = report.get("request")
    if any(check(request.get("candidate")) or (
            isinstance(saved_request, dict) and check(saved_request.get("candidate")))
            for check in (_is_binary_overlap_spec, _is_relational_germ_spec)):
        _validate_cache_entry(envelope, request)
    # Hard-link publication is atomic and refuses replacement, including a competing publisher.
    descriptor, temporary = tempfile.mkstemp(prefix=".screen-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(raw)
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
        card = {"id": candidate["id"], "family": candidate["family"],
                "status": self.report["status"], "reused": self.reused,
                "checks": [{"id": row["id"], "status": row["status"],
                            "checked": row["checked"], "planned": row["planned"],
                            "actual": None if row["witness"] is None else
                            object_fields(row["witness"])["actual"]} for row in checks],
                "artifact": str(self.artifact) if self.artifact else None,
                "key": self.key, "proof_status": self.report["proof_status"],
                "empirical_status": self.report["empirical_status"]}
        if candidate["family"] == "native_readout_search":
            details = object_fields(self.report["scope"])
            responses = details["responses"]
            if not isinstance(responses, list):
                raise TypeError("invalid search response rows")
            summary: list[dict[str, object]] = []
            for value in responses:
                row = object_fields(value)
                witness = row["first_witness"]
                first = None if witness is None else object_fields(witness)
                summary.append({"response": row["response"], "state": row["state"],
                    "preparations_checked": row["preparations_checked"],
                    "first_witness": None if first is None else {key: first[key]
                        for key in ("preparation_index", "coordinates", "reference_row")}})
            search_summary: dict[str, object] = {
                "completion_only": True, "rejection_scope": self.report["rejection_scope"],
                "stop_reason": details["stop_reason"], "search_complete": details["search_complete"],
                "domain_exhausted": details["domain_exhausted"], "responses": summary}
            if "unsupported_reason" in details:
                search_summary["unsupported_reason"] = details["unsupported_reason"]
            card["search"] = search_summary
        return card


def run_batch(specifications: list[object], limits: Limits | None = None,
              cache_dir: Path | None = None, *, fresh: bool = False) -> tuple[Result, ...]:
    primitive.bounded_int(len(specifications), 1, 64)
    has_relay = any(_is_marked_relay_spec(spec) for spec in specifications)
    has_pencil = any(_is_chiral_pencil_spec(spec) for spec in specifications)
    has_width = any(_is_neutral_width_spec(spec) for spec in specifications)
    has_stock = any(_is_triangle_stock_spec(spec) for spec in specifications)
    has_driven = any(_is_driven_event_selector_spec(spec) for spec in specifications)
    has_periodic = any(_is_periodic_contact_spec(spec) for spec in specifications)
    has_cut = any(_is_prepare_measure_cut_spec(spec) for spec in specifications)
    has_overlap = any(_is_binary_overlap_spec(spec) for spec in specifications)
    has_germ = any(_is_relational_germ_spec(spec) for spec in specifications)
    if has_germ and limits is not None and type(limits) is not Limits:
        raise ValueError("relational germ candidate/limits do not match request")
    if has_overlap and limits is not None and type(limits) is not Limits:
        raise ValueError("binary overlap cut candidate/limits do not match request")
    pins_sources = (has_relay or has_pencil or has_width or has_stock or has_driven or has_periodic or
                    has_cut or has_overlap or has_germ)
    sources = provenance() if pins_sources else None
    if has_germ:
        _assert_relational_germ_sources(sources)
    if has_overlap:
        _assert_binary_overlap_sources(sources)
    if has_cut:
        _assert_prepare_measure_cut_sources(sources)
    if has_periodic:
        _assert_periodic_contact_sources(sources)
    if has_driven:
        _assert_driven_event_selector_sources(sources)
    if has_stock:
        _assert_triangle_stock_sources(sources)
    if has_width:
        _assert_neutral_width_sources(sources)
    if has_relay:
        _assert_marked_relay_sources(sources)
    if has_pencil:
        _assert_chiral_pencil_sources(sources)
    # Validate the entire input before creating cache files.
    candidates = tuple(parse_hypothesis(value) for value in specifications)
    if any(isinstance(candidate, BellLocalResponse) for candidate in candidates):
        assert_bell_sources()
    limits = limits if limits is not None else Limits()
    if has_cut and type(limits) is not Limits:
        raise ValueError("prepare-measure cut requires exact Limits")
    if has_periodic and type(limits) is not Limits:
        raise ValueError("periodic contact observer requires exact Limits")
    sources = provenance() if sources is None else sources
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
    envelope = _load_cache_envelope(path)
    saved = object_fields(envelope["report"])
    request = object_fields(saved.get("request"), {"schema", "candidate", "limits", "provenance"})
    is_relay = _is_marked_relay_spec(request["candidate"])
    is_pencil = _is_chiral_pencil_spec(request["candidate"])
    is_width = _is_neutral_width_spec(request["candidate"])
    is_stock = _is_triangle_stock_spec(request["candidate"])
    is_driven = _is_driven_event_selector_spec(request["candidate"])
    is_periodic = _is_periodic_contact_spec(request["candidate"])
    is_cut = _is_prepare_measure_cut_spec(request["candidate"])
    is_overlap = _is_binary_overlap_spec(request["candidate"])
    is_germ = _is_relational_germ_spec(request["candidate"])
    pins_sources = (is_relay or is_pencil or is_width or is_stock or is_driven or is_periodic or
                    is_cut or is_overlap or is_germ)
    sources = provenance() if pins_sources else None
    if is_germ:
        _assert_relational_germ_sources(sources)
    if is_overlap:
        _assert_binary_overlap_sources(sources)
    if is_cut:
        _assert_prepare_measure_cut_sources(sources)
    if is_periodic:
        _assert_periodic_contact_sources(sources)
    if is_driven:
        _assert_driven_event_selector_sources(sources)
    if is_stock:
        _assert_triangle_stock_sources(sources)
    if is_width:
        _assert_neutral_width_sources(sources)
    if is_relay:
        _assert_marked_relay_sources(sources)
    if is_pencil:
        _assert_chiral_pencil_sources(sources)
    _assert_cache_request_sources(request)
    saved = _validate_cache_entry(envelope, request)
    candidate = parse_hypothesis(request["candidate"])
    limits = parse_limits(request["limits"])
    current_request = request_for(candidate, limits, provenance() if sources is None else sources)
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
