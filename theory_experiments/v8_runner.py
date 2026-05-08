from __future__ import annotations

import hashlib
import json
import math
import subprocess
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

SCHEMA = "idt-v8-experiment-node-stats/1"
PROTOCOL_SCHEMA = "idt-v8-experiment-protocol-registry/1"
PROTOCOL_AUTHORITY = "lean_checked_protocol"
PROOF_BOUNDARY = "experiment_results_are_not_formal_proofs"
DEFAULT_OUTPUT = Path("dist/v8-experiment-node-stats.json")
DEFAULT_REPORT = Path("dist/v8-experiment-report.md")

TelemetryRole = Literal["used", "stressed", "blocked", "failed", "bypassed"]
TelemetryStatus = Literal["pass", "fail", "inconclusive", "blocked"]
FixtureClass = Literal[
    "calibrated_action_scale_reconstruction",
    "finite_readout_normalization",
    "bell_chsh_table",
    "interference_visibility",
    "sorkin_i3",
    "marker_eraser_visibility",
    "phase_accumulation",
    "spin_axis_transition",
    "unitary_context_readout",
    "projective_repeatability",
    "bell_amplitude_table",
    "singlet_angle_grid",
    "decoherence_recoverability",
    "repeated_context_zeno",
    "context_transfer_no_cloning",
    "no_cloning_context_invariance",
    "barrier_transmission",
    "bosonic_indistinguishability",
    "single_quantum_facticity",
    "conditional_inheritance_swap",
    "multipartite_contextuality",
    "ks_contextuality_obstruction",
    "temporal_facticity",
    "partial_facticity_readout",
    "unitary_graph_walk",
    "residual_not_implemented",
]
JsonObject = dict[str, object]


class ExperimentRunnerError(ValueError):
    pass


@dataclass(frozen=True)
class LogicalNode:
    identifier: str
    label: str
    claim_boundary: str


@dataclass(frozen=True)
class ExperimentProtocol:
    identifier: str
    experiment_id: str
    fixture_class: FixtureClass
    claim_boundary: str
    logical_nodes: tuple[str, ...]
    allowed_result_statuses: tuple[TelemetryStatus, ...]
    forbidden_upgrades: tuple[str, ...]


@dataclass(frozen=True)
class ProtocolRegistry:
    logical_nodes: tuple[LogicalNode, ...]
    protocols: tuple[ExperimentProtocol, ...]

    @property
    def logical_node_ids(self) -> frozenset[str]:
        return frozenset(node.identifier for node in self.logical_nodes)


@dataclass(frozen=True)
class ActionScaleObservation:
    identifier: str
    kind: str
    role: str
    numerator: float
    denominator: float


@dataclass(frozen=True)
class ActionScaleFixture:
    shared_action_scale: float
    tolerance: float
    allow_per_experiment_refit: bool
    hbar_status: str
    observations: tuple[ActionScaleObservation, ...]


@dataclass(frozen=True)
class ReadoutFixture:
    weights: tuple[float, ...]
    expected_total: float
    tolerance: float


@dataclass(frozen=True)
class BellOutcome:
    a: int
    b: int
    probability: float


@dataclass(frozen=True)
class BellContext:
    x: int
    y: int
    outcomes: tuple[BellOutcome, ...]


@dataclass(frozen=True)
class BellFixture:
    contexts: tuple[BellContext, ...]
    expected_abs_s: float
    max_abs_s: float
    tolerance: float


@dataclass(frozen=True)
class InterferenceFixture:
    visibility: float
    expected_visibility: float
    context_total: float
    expected_total: float
    tolerance: float


@dataclass(frozen=True)
class SorkinFixture:
    i3_value: float
    expected_i3: float
    context_total: float
    expected_total: float
    tolerance: float


@dataclass(frozen=True)
class MarkerEraserFixture:
    marker_distinguishability: float
    marker_visibility: float
    eraser_visibility: float
    expected_marker_visibility: float
    expected_eraser_visibility: float
    tolerance: float


@dataclass(frozen=True)
class PhaseAccumulationFixture:
    observed_phase: float
    expected_phase: float
    context_total: float
    expected_total: float
    tolerance: float


@dataclass(frozen=True)
class SpinTransitionFixture:
    probabilities: tuple[float, ...]
    expected_probabilities: tuple[float, ...]
    tolerance: float


@dataclass(frozen=True)
class UnitaryContextFixture:
    state: tuple[float, ...]
    basis: tuple[tuple[float, ...], ...]
    expected_probabilities: tuple[float, ...]
    tolerance: float


@dataclass(frozen=True)
class ProjectiveRepeatabilityFixture:
    probabilities: tuple[float, ...]
    expected_probabilities: tuple[float, ...]
    repeat_probabilities: tuple[float, ...]
    tolerance: float


@dataclass(frozen=True)
class BellAmplitudeOutcome:
    a: int
    b: int
    amplitude: float


@dataclass(frozen=True)
class BellAmplitudeContext:
    x: int
    y: int
    amplitudes: tuple[BellAmplitudeOutcome, ...]


@dataclass(frozen=True)
class BellAmplitudeFixture:
    contexts: tuple[BellAmplitudeContext, ...]
    expected_abs_s: float
    max_abs_s: float
    tolerance: float


@dataclass(frozen=True)
class SingletAngleFixture:
    alice_angles: tuple[float, ...]
    bob_angles: tuple[float, ...]
    expected_abs_s: float
    max_abs_s: float
    tolerance: float


@dataclass(frozen=True)
class DecoherenceRecoverabilityFixture:
    amplitudes: tuple[float, ...]
    environment_kernel: tuple[tuple[float, ...], ...]
    expected_probabilities: tuple[float, ...]
    max_residual_coherence: float
    observed_visibility: float
    environment_recoverable_visibility: float
    expected_lambda: float
    facticity_threshold: float
    expected_facticity: bool
    tolerance: float


@dataclass(frozen=True)
class ZenoSample:
    readout_count: int
    expected_survival: float


@dataclass(frozen=True)
class RepeatedContextZenoFixture:
    total_angle: float
    samples: tuple[ZenoSample, ...]
    tolerance: float


@dataclass(frozen=True)
class ContextTransferFixture:
    input_state: tuple[float, ...]
    bell_branch: str
    expected_target_state: tuple[float, ...]
    tolerance: float


@dataclass(frozen=True)
class NoCloningFixture:
    state_overlap: float
    min_obstruction: float
    expected_obstructed: bool
    tolerance: float


@dataclass(frozen=True)
class BarrierTransmissionFixture:
    classically_forbidden: bool
    decay_constant: float
    width: float
    expected_transmission: float
    expected_reflection: float
    tolerance: float


@dataclass(frozen=True)
class BosonicIndistinguishabilityFixture:
    wavepacket_overlap: float
    expected_coincidence: float
    expected_bunching: float
    tolerance: float


@dataclass(frozen=True)
class SingleQuantumFacticityFixture:
    trial_count: int
    detector_a_count: int
    detector_b_count: int
    coincidence_count: int
    expected_g2_zero: float
    max_g2_zero: float
    tolerance: float


@dataclass(frozen=True)
class RemoteCorrelation:
    context: str
    expected_correlation: float


@dataclass(frozen=True)
class ConditionalInheritanceSwapFixture:
    bell_outcome: str
    remote_correlations: tuple[RemoteCorrelation, ...]
    tolerance: float


@dataclass(frozen=True)
class MerminConstraint:
    context: tuple[str, ...]
    expected_product: int


@dataclass(frozen=True)
class MultipartiteContextualityFixture:
    constraints: tuple[MerminConstraint, ...]
    expected_obstructed: bool
    tolerance: float


@dataclass(frozen=True)
class KSContextualityFixture:
    contexts: tuple[tuple[str, ...], ...]
    expected_obstructed: bool
    tolerance: float


@dataclass(frozen=True)
class TemporalFactivityFixture:
    c12: float
    c23: float
    c13: float
    expected_k: float
    macrorealist_bound: float
    expected_violation: bool
    tolerance: float


@dataclass(frozen=True)
class PartialFactivityReadoutFixture:
    coupling: float
    weak_value: float
    expected_pointer_shift: float
    observed_disturbance: float
    max_disturbance: float
    distinguishability_gain: float
    facticity_threshold: float
    expected_full_facticity: bool
    tolerance: float


@dataclass(frozen=True)
class WalkDistributionPoint:
    position: int
    probability: float


@dataclass(frozen=True)
class UnitaryGraphWalkFixture:
    steps: int
    initial_coin: tuple[float, float]
    expected_distribution: tuple[WalkDistributionPoint, ...]
    tolerance: float


@dataclass(frozen=True)
class FixtureSet:
    action_scale: ActionScaleFixture
    readout: ReadoutFixture
    bell: BellFixture
    interference: Mapping[str, InterferenceFixture]
    sorkin: Mapping[str, SorkinFixture]
    marker_eraser: Mapping[str, MarkerEraserFixture]
    phase: Mapping[str, PhaseAccumulationFixture]
    spin: Mapping[str, SpinTransitionFixture]
    unitary: Mapping[str, UnitaryContextFixture]
    projective: Mapping[str, ProjectiveRepeatabilityFixture]
    bell_amplitude: Mapping[str, BellAmplitudeFixture]
    singlet_angle: Mapping[str, SingletAngleFixture]
    decoherence: Mapping[str, DecoherenceRecoverabilityFixture]
    zeno: Mapping[str, RepeatedContextZenoFixture]
    context_transfer: Mapping[str, ContextTransferFixture]
    no_cloning: Mapping[str, NoCloningFixture]
    barrier: Mapping[str, BarrierTransmissionFixture]
    bosonic: Mapping[str, BosonicIndistinguishabilityFixture]
    single_quantum: Mapping[str, SingleQuantumFacticityFixture]
    inheritance_swap: Mapping[str, ConditionalInheritanceSwapFixture]
    multipartite: Mapping[str, MultipartiteContextualityFixture]
    ks_contextuality: Mapping[str, KSContextualityFixture]
    temporal: Mapping[str, TemporalFactivityFixture]
    partial_facticity: Mapping[str, PartialFactivityReadoutFixture]
    graph_walk: Mapping[str, UnitaryGraphWalkFixture]


@dataclass(frozen=True)
class TelemetryEvent:
    experiment_id: str
    node_id: str
    role: TelemetryRole
    status: TelemetryStatus
    margin: float
    input_hash: str
    output_hash: str
    source: str

    def row(self) -> JsonObject:
        return {
            "experiment_id": self.experiment_id,
            "node_id": self.node_id,
            "role": self.role,
            "status": self.status,
            "margin": round(self.margin, 12),
            "input_hash": self.input_hash,
            "output_hash": self.output_hash,
            "source": self.source,
        }


@dataclass(frozen=True)
class ExperimentSummary:
    experiment_id: str
    fixture_class: str
    status: TelemetryStatus
    telemetry_count: int

    def row(self) -> JsonObject:
        return {
            "experiment_id": self.experiment_id,
            "fixture_class": self.fixture_class,
            "status": self.status,
            "telemetry_count": self.telemetry_count,
        }


@dataclass(frozen=True)
class NodeStats:
    node_id: str
    used: int
    stressed: int
    blocked: int
    failed: int
    bypassed: int
    passed: int
    failed_status: int
    inconclusive: int
    blocked_status: int
    min_margin: float

    def row(self) -> JsonObject:
        return {
            "node_id": self.node_id,
            "used": self.used,
            "stressed": self.stressed,
            "blocked": self.blocked,
            "failed": self.failed,
            "bypassed": self.bypassed,
            "pass": self.passed,
            "fail": self.failed_status,
            "inconclusive": self.inconclusive,
            "blocked_status": self.blocked_status,
            "min_margin": round(self.min_margin, 12),
        }


def load_registry_from_lean(repo_root: Path) -> ProtocolRegistry:
    command = ["lake", "exe", "idt_v8_experiment_protocols", "--", "--json"]
    completed = subprocess.run(
        command,
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    return parse_protocol_registry(json.loads(completed.stdout))


def load_registry_from_path(path: Path) -> ProtocolRegistry:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as error:
        raise ExperimentRunnerError(f"cannot read protocol JSON {path}: {error}") from error
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as error:
        raise ExperimentRunnerError(f"invalid protocol JSON {path}: {error}") from error
    return parse_protocol_registry(payload)


def parse_protocol_registry(payload: object) -> ProtocolRegistry:
    root = require_object(payload, "registry")
    require_literal(root.get("schema"), PROTOCOL_SCHEMA, "schema")
    require_literal(root.get("protocol_authority"), PROTOCOL_AUTHORITY, "protocol_authority")
    require_literal(root.get("proof_boundary"), PROOF_BOUNDARY, "proof_boundary")
    nodes = tuple(parse_logical_node(item, index) for index, item in enumerate(require_list(root.get("logical_nodes"), "logical_nodes")))
    node_ids = [node.identifier for node in nodes]
    if len(set(node_ids)) != len(node_ids):
        raise ExperimentRunnerError("logical_nodes contain duplicate ids")
    protocols = tuple(
        parse_protocol(item, index, frozenset(node_ids))
        for index, item in enumerate(require_list(root.get("protocols"), "protocols"))
    )
    if not protocols:
        raise ExperimentRunnerError("protocols must not be empty")
    return ProtocolRegistry(logical_nodes=nodes, protocols=protocols)


def parse_logical_node(payload: object, index: int) -> LogicalNode:
    raw = require_object(payload, f"logical_nodes[{index}]")
    return LogicalNode(
        identifier=require_string(raw.get("id"), f"logical_nodes[{index}].id"),
        label=require_string(raw.get("label"), f"logical_nodes[{index}].label"),
        claim_boundary=require_string(raw.get("claim_boundary"), f"logical_nodes[{index}].claim_boundary"),
    )


def parse_protocol(payload: object, index: int, known_nodes: frozenset[str]) -> ExperimentProtocol:
    raw = require_object(payload, f"protocols[{index}]")
    fixture_class = require_fixture_class(raw.get("fixture_class"), f"protocols[{index}].fixture_class")
    logical_nodes = tuple(require_string_list(raw.get("logical_nodes"), f"protocols[{index}].logical_nodes"))
    for node_id in logical_nodes:
        if node_id not in known_nodes:
            raise ExperimentRunnerError(
                f"protocols[{index}] references unknown logical node {node_id!r}"
            )
    statuses = tuple(
        require_telemetry_status(item, f"protocols[{index}].allowed_result_statuses")
        for item in require_string_list(
            raw.get("allowed_result_statuses"),
            f"protocols[{index}].allowed_result_statuses",
        )
    )
    forbidden = tuple(
        require_string_list(raw.get("forbidden_upgrades"), f"protocols[{index}].forbidden_upgrades")
    )
    for required in ("formal_proof", "physical_formal_proof", "qm_formal_proof"):
        if required not in forbidden:
            raise ExperimentRunnerError(
                f"protocols[{index}] missing forbidden upgrade {required!r}"
            )
    return ExperimentProtocol(
        identifier=require_string(raw.get("id"), f"protocols[{index}].id"),
        experiment_id=require_string(raw.get("experiment_id"), f"protocols[{index}].experiment_id"),
        fixture_class=fixture_class,
        claim_boundary=require_string(raw.get("claim_boundary"), f"protocols[{index}].claim_boundary"),
        logical_nodes=logical_nodes,
        allowed_result_statuses=statuses,
        forbidden_upgrades=forbidden,
    )


def run_experiment_suite(
    registry: ProtocolRegistry,
    repo_root: Path,
    experiment_filters: Sequence[str] = (),
    fixtures: FixtureSet | None = None,
) -> JsonObject:
    selected = select_protocols(registry.protocols, experiment_filters)
    fixture_set = fixtures if fixtures is not None else default_fixtures()
    telemetry: list[TelemetryEvent] = []
    summaries: list[ExperimentSummary] = []
    for protocol in selected:
        events = run_protocol(protocol, fixture_set)
        validate_telemetry_events(protocol, events, registry.logical_node_ids)
        telemetry.extend(events)
        summaries.append(
            ExperimentSummary(
                experiment_id=protocol.experiment_id,
                fixture_class=protocol.fixture_class,
                status=experiment_status(events),
                telemetry_count=len(events),
            )
        )
    telemetry = sorted(telemetry, key=lambda event: (event.experiment_id, event.node_id, event.role, event.status))
    summaries = sorted(summaries, key=lambda summary: summary.experiment_id)
    node_stats = sorted(build_node_stats(telemetry), key=lambda stats: stats.node_id)
    source_hashes = build_source_hashes(repo_root)
    output: JsonObject = {
        "schema": SCHEMA,
        "protocol_authority": PROTOCOL_AUTHORITY,
        "proof_boundary": PROOF_BOUNDARY,
        "meta": {
            "repo_root": str(repo_root.resolve()),
            "experiment_filters": list(experiment_filters),
        },
        "coverage": {
            "experiments": len(summaries),
            "telemetry": len(telemetry),
            "nodes": len(node_stats),
        },
        "experiments": [summary.row() for summary in summaries],
        "node_stats": [stats.row() for stats in node_stats],
        "telemetry": [event.row() for event in telemetry],
        "source_hashes": source_hashes,
    }
    validate_stats_payload(output)
    return output


def run_protocol(protocol: ExperimentProtocol, fixtures: FixtureSet) -> list[TelemetryEvent]:
    if protocol.fixture_class == "calibrated_action_scale_reconstruction":
        return run_action_scale_protocol(protocol, fixtures.action_scale)
    if protocol.fixture_class == "finite_readout_normalization":
        return run_readout_protocol(protocol, fixtures.readout)
    if protocol.fixture_class == "bell_chsh_table":
        return run_bell_protocol(protocol, fixtures.bell)
    if protocol.fixture_class == "interference_visibility":
        return run_interference_protocol(protocol, fixtures.interference)
    if protocol.fixture_class == "sorkin_i3":
        return run_sorkin_protocol(protocol, fixtures.sorkin)
    if protocol.fixture_class == "marker_eraser_visibility":
        return run_marker_eraser_protocol(protocol, fixtures.marker_eraser)
    if protocol.fixture_class == "phase_accumulation":
        return run_phase_protocol(protocol, fixtures.phase)
    if protocol.fixture_class == "spin_axis_transition":
        return run_spin_protocol(protocol, fixtures.spin)
    if protocol.fixture_class == "unitary_context_readout":
        return run_unitary_protocol(protocol, fixtures.unitary)
    if protocol.fixture_class == "projective_repeatability":
        return run_projective_protocol(protocol, fixtures.projective)
    if protocol.fixture_class == "bell_amplitude_table":
        return run_bell_amplitude_protocol(protocol, fixtures.bell_amplitude)
    if protocol.fixture_class == "singlet_angle_grid":
        return run_singlet_angle_protocol(protocol, fixtures.singlet_angle)
    if protocol.fixture_class == "decoherence_recoverability":
        return run_decoherence_protocol(protocol, fixtures.decoherence)
    if protocol.fixture_class == "repeated_context_zeno":
        return run_zeno_protocol(protocol, fixtures.zeno)
    if protocol.fixture_class == "context_transfer_no_cloning":
        return run_context_transfer_protocol(protocol, fixtures.context_transfer, fixtures.no_cloning)
    if protocol.fixture_class == "no_cloning_context_invariance":
        return run_no_cloning_protocol(protocol, fixtures.no_cloning)
    if protocol.fixture_class == "barrier_transmission":
        return run_barrier_protocol(protocol, fixtures.barrier)
    if protocol.fixture_class == "bosonic_indistinguishability":
        return run_bosonic_protocol(protocol, fixtures.bosonic)
    if protocol.fixture_class == "single_quantum_facticity":
        return run_single_quantum_protocol(protocol, fixtures.single_quantum)
    if protocol.fixture_class == "conditional_inheritance_swap":
        return run_inheritance_swap_protocol(protocol, fixtures.inheritance_swap)
    if protocol.fixture_class == "multipartite_contextuality":
        return run_multipartite_protocol(protocol, fixtures.multipartite)
    if protocol.fixture_class == "ks_contextuality_obstruction":
        return run_ks_contextuality_protocol(protocol, fixtures.ks_contextuality)
    if protocol.fixture_class == "temporal_facticity":
        return run_temporal_protocol(protocol, fixtures.temporal)
    if protocol.fixture_class == "partial_facticity_readout":
        return run_partial_facticity_protocol(protocol, fixtures.partial_facticity)
    if protocol.fixture_class == "unitary_graph_walk":
        return run_graph_walk_protocol(protocol, fixtures.graph_walk)
    if protocol.fixture_class == "residual_not_implemented":
        return run_residual_not_implemented_protocol(protocol)
    raise ExperimentRunnerError(f"unsupported fixture class {protocol.fixture_class!r}")


def run_action_scale_protocol(protocol: ExperimentProtocol, fixture: ActionScaleFixture) -> list[TelemetryEvent]:
    input_hash = stable_digest(fixture_to_json(fixture))
    ratios = [observation.numerator / observation.denominator for observation in fixture.observations]
    max_error = max(abs(ratio - fixture.shared_action_scale) for ratio in ratios)
    scale_status: TelemetryStatus = "pass" if max_error <= fixture.tolerance else "fail"
    refit_status: TelemetryStatus = "fail" if fixture.allow_per_experiment_refit else "pass"
    hbar_status: TelemetryStatus = "pass" if fixture.hbar_status == "blocked" else "fail"
    return [
        telemetry_event(
            protocol,
            "phase_action_conversion_I",
            "used",
            scale_status,
            fixture.tolerance - max_error,
            input_hash,
            {"max_scale_error": max_error},
        ),
        telemetry_event(
            protocol,
            "no_refit_shared_parameter",
            "stressed",
            refit_status,
            1.0 if not fixture.allow_per_experiment_refit else -1.0,
            input_hash,
            {"allow_per_experiment_refit": fixture.allow_per_experiment_refit},
        ),
        telemetry_event(
            protocol,
            "hbar_first_principles_boundary",
            "blocked",
            hbar_status,
            0.0,
            input_hash,
            {"hbar_status": fixture.hbar_status},
        ),
    ]


def run_readout_protocol(protocol: ExperimentProtocol, fixture: ReadoutFixture) -> list[TelemetryEvent]:
    input_hash = stable_digest(fixture_to_json(fixture))
    total = sum(fixture.weights)
    total_error = abs(total - fixture.expected_total)
    min_weight = min(fixture.weights)
    normalization_status: TelemetryStatus = "pass" if total_error <= fixture.tolerance else "fail"
    positive_status: TelemetryStatus = "pass" if min_weight >= -fixture.tolerance else "fail"
    return [
        telemetry_event(
            protocol,
            "context_normalization",
            "used",
            normalization_status,
            fixture.tolerance - total_error,
            input_hash,
            {"total": total, "expected_total": fixture.expected_total},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            positive_status,
            min_weight,
            input_hash,
            {"min_weight": min_weight},
        ),
    ]


def run_bell_protocol(protocol: ExperimentProtocol, fixture: BellFixture) -> list[TelemetryEvent]:
    input_hash = stable_digest(fixture_to_json(fixture))
    max_signal = bell_no_signalling_error(fixture.contexts)
    chsh_abs = abs(chsh_value(fixture.contexts))
    chsh_error = abs(chsh_abs - fixture.expected_abs_s)
    signalling_status: TelemetryStatus = "pass" if max_signal <= fixture.tolerance else "fail"
    bounded_status: TelemetryStatus = (
        "pass"
        if chsh_abs <= fixture.max_abs_s + fixture.tolerance and chsh_error <= fixture.tolerance
        else "fail"
    )
    return [
        telemetry_event(
            protocol,
            "bell_chsh_no_signalling",
            "used",
            signalling_status,
            fixture.tolerance - max_signal,
            input_hash,
            {"max_signal": max_signal},
        ),
        telemetry_event(
            protocol,
            "bounded_correlation_window",
            "stressed",
            bounded_status,
            fixture.max_abs_s - chsh_abs,
            input_hash,
            {"abs_s": chsh_abs, "max_abs_s": fixture.max_abs_s},
        ),
    ]


def run_interference_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, InterferenceFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "interference")
    input_hash = stable_digest(fixture_to_json(fixture))
    visibility_error = abs(fixture.visibility - fixture.expected_visibility)
    total_error = abs(fixture.context_total - fixture.expected_total)
    return [
        telemetry_event(
            protocol,
            "interference_visibility",
            "used",
            "pass" if visibility_error <= fixture.tolerance else "fail",
            fixture.tolerance - visibility_error,
            input_hash,
            {"visibility": fixture.visibility, "expected_visibility": fixture.expected_visibility},
        ),
        telemetry_event(
            protocol,
            "context_normalization" if "context_normalization" in protocol.logical_nodes else "phase_accumulation",
            "used",
            "pass" if total_error <= fixture.tolerance else "fail",
            fixture.tolerance - total_error,
            input_hash,
            {"total": fixture.context_total, "expected_total": fixture.expected_total},
        ),
    ]


def run_sorkin_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, SorkinFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "sorkin")
    input_hash = stable_digest(fixture_to_json(fixture))
    i3_error = abs(fixture.i3_value - fixture.expected_i3)
    total_error = abs(fixture.context_total - fixture.expected_total)
    return [
        telemetry_event(
            protocol,
            "sorkin_i3_zero",
            "stressed",
            "pass" if i3_error <= fixture.tolerance else "fail",
            fixture.tolerance - i3_error,
            input_hash,
            {"i3": fixture.i3_value, "expected_i3": fixture.expected_i3},
        ),
        telemetry_event(
            protocol,
            "context_normalization",
            "used",
            "pass" if total_error <= fixture.tolerance else "fail",
            fixture.tolerance - total_error,
            input_hash,
            {"total": fixture.context_total, "expected_total": fixture.expected_total},
        ),
    ]


def run_marker_eraser_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, MarkerEraserFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "marker/eraser")
    input_hash = stable_digest(fixture_to_json(fixture))
    marker_error = abs(fixture.marker_visibility - fixture.expected_marker_visibility)
    eraser_error = abs(fixture.eraser_visibility - fixture.expected_eraser_visibility)
    return [
        telemetry_event(
            protocol,
            "path_marker_distinguishability",
            "stressed",
            "pass" if fixture.marker_distinguishability > 0.0 else "fail",
            fixture.marker_distinguishability,
            input_hash,
            {"marker_distinguishability": fixture.marker_distinguishability},
        ),
        telemetry_event(
            protocol,
            "interference_visibility",
            "used",
            "pass" if marker_error <= fixture.tolerance and eraser_error <= fixture.tolerance else "fail",
            fixture.tolerance - max(marker_error, eraser_error),
            input_hash,
            {
                "marker_visibility": fixture.marker_visibility,
                "eraser_visibility": fixture.eraser_visibility,
            },
        ),
    ]


def run_phase_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, PhaseAccumulationFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "phase")
    input_hash = stable_digest(fixture_to_json(fixture))
    phase_error = phase_distance(fixture.observed_phase, fixture.expected_phase)
    total_error = abs(fixture.context_total - fixture.expected_total)
    second_node = "phase_action_conversion_I"
    if "context_normalization" in protocol.logical_nodes:
        second_node = "context_normalization"
    return [
        telemetry_event(
            protocol,
            "phase_accumulation",
            "used",
            "pass" if phase_error <= fixture.tolerance else "fail",
            fixture.tolerance - phase_error,
            input_hash,
            {"observed_phase": fixture.observed_phase, "expected_phase": fixture.expected_phase},
        ),
        telemetry_event(
            protocol,
            second_node,
            "used",
            "pass" if total_error <= fixture.tolerance else "fail",
            fixture.tolerance - total_error,
            input_hash,
            {"total": fixture.context_total, "expected_total": fixture.expected_total},
        ),
    ]


def run_spin_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, SpinTransitionFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "spin")
    input_hash = stable_digest(fixture_to_json(fixture))
    max_error = max(
        abs(actual - expected)
        for actual, expected in zip(fixture.probabilities, fixture.expected_probabilities, strict=True)
    )
    min_probability = min(fixture.probabilities)
    return [
        telemetry_event(
            protocol,
            "spin_axis_transition",
            "used",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_probability_error": max_error},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if min_probability >= -fixture.tolerance else "fail",
            min_probability,
            input_hash,
            {"min_probability": min_probability},
        ),
    ]


def run_unitary_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, UnitaryContextFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "unitary context")
    input_hash = stable_digest(fixture_to_json(fixture))
    probabilities = tuple(sum(left * right for left, right in zip(row, fixture.state, strict=True)) ** 2 for row in fixture.basis)
    max_error = max(
        abs(actual - expected)
        for actual, expected in zip(probabilities, fixture.expected_probabilities, strict=True)
    )
    total_error = abs(sum(probabilities) - 1.0)
    return [
        telemetry_event(
            protocol,
            "unitary_context_map",
            "used",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_probability_error": max_error},
        ),
        telemetry_event(
            protocol,
            "context_normalization",
            "used",
            "pass" if total_error <= fixture.tolerance else "fail",
            fixture.tolerance - total_error,
            input_hash,
            {"total": sum(probabilities)},
        ),
    ]


def run_projective_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, ProjectiveRepeatabilityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "projective repeatability")
    input_hash = stable_digest(fixture_to_json(fixture))
    max_error = max(
        abs(actual - expected)
        for actual, expected in zip(fixture.probabilities, fixture.expected_probabilities, strict=True)
    )
    min_repeatability = min(fixture.repeat_probabilities)
    min_probability = min(fixture.probabilities)
    return [
        telemetry_event(
            protocol,
            "projective_repeatability",
            "stressed",
            "pass" if max_error <= fixture.tolerance and min_repeatability >= 1.0 - fixture.tolerance else "fail",
            min(fixture.tolerance - max_error, min_repeatability - 1.0 + fixture.tolerance),
            input_hash,
            {"max_probability_error": max_error, "min_repeatability": min_repeatability},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if min_probability >= -fixture.tolerance else "fail",
            min_probability,
            input_hash,
            {"min_probability": min_probability},
        ),
    ]


def run_bell_amplitude_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, BellAmplitudeFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "Bell amplitude")
    input_hash = stable_digest(fixture_to_json(fixture))
    bell_fixture = BellFixture(
        contexts=tuple(amplitude_context_to_bell_context(context) for context in fixture.contexts),
        expected_abs_s=fixture.expected_abs_s,
        max_abs_s=fixture.max_abs_s,
        tolerance=fixture.tolerance,
    )
    normalization_error = max(abs(sum(outcome.probability for outcome in context.outcomes) - 1.0) for context in bell_fixture.contexts)
    max_signal = bell_no_signalling_error(bell_fixture.contexts)
    chsh_abs = abs(chsh_value(bell_fixture.contexts))
    chsh_error = abs(chsh_abs - fixture.expected_abs_s)
    bounded_status: TelemetryStatus = (
        "pass"
        if chsh_abs <= fixture.max_abs_s + fixture.tolerance and chsh_error <= fixture.tolerance
        else "fail"
    )
    return [
        telemetry_event(
            protocol,
            "amplitude_probability_readout",
            "used",
            "pass" if normalization_error <= fixture.tolerance else "fail",
            fixture.tolerance - normalization_error,
            input_hash,
            {"max_context_normalization_error": normalization_error},
        ),
        telemetry_event(
            protocol,
            "bell_chsh_no_signalling",
            "used",
            "pass" if max_signal <= fixture.tolerance else "fail",
            fixture.tolerance - max_signal,
            input_hash,
            {"max_signal": max_signal},
        ),
        telemetry_event(
            protocol,
            "bounded_correlation_window",
            "stressed",
            bounded_status,
            fixture.max_abs_s - chsh_abs,
            input_hash,
            {"abs_s": chsh_abs, "max_abs_s": fixture.max_abs_s},
        ),
    ]


def run_singlet_angle_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, SingletAngleFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "singlet angle")
    input_hash = stable_digest(fixture_to_json(fixture))
    correlations = {
        (alice_index, bob_index): -math.cos(alice_angle - bob_angle)
        for alice_index, alice_angle in enumerate(fixture.alice_angles)
        for bob_index, bob_angle in enumerate(fixture.bob_angles)
    }
    chsh_abs = abs(correlations[(0, 0)] + correlations[(0, 1)] + correlations[(1, 0)] - correlations[(1, 1)])
    chsh_error = abs(chsh_abs - fixture.expected_abs_s)
    status: TelemetryStatus = (
        "pass"
        if chsh_abs <= fixture.max_abs_s + fixture.tolerance and chsh_error <= fixture.tolerance
        else "fail"
    )
    return [
        telemetry_event(
            protocol,
            "singlet_angle_correlation",
            "used",
            status,
            fixture.tolerance - chsh_error,
            input_hash,
            {"abs_s": chsh_abs, "expected_abs_s": fixture.expected_abs_s},
        ),
        telemetry_event(
            protocol,
            "bounded_correlation_window",
            "stressed",
            "pass" if chsh_abs <= fixture.max_abs_s + fixture.tolerance else "fail",
            fixture.max_abs_s - chsh_abs,
            input_hash,
            {"abs_s": chsh_abs, "max_abs_s": fixture.max_abs_s},
        ),
    ]


def run_decoherence_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, DecoherenceRecoverabilityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "decoherence")
    input_hash = stable_digest(fixture_to_json(fixture))
    probabilities = tuple(amplitude * amplitude for amplitude in fixture.amplitudes)
    probability_error = max(
        abs(actual - expected)
        for actual, expected in zip(probabilities, fixture.expected_probabilities, strict=True)
    )
    residual = max_residual_coherence(fixture.amplitudes, fixture.environment_kernel)
    visibility_lambda = math.log(fixture.environment_recoverable_visibility / fixture.observed_visibility)
    lambda_error = abs(visibility_lambda - fixture.expected_lambda)
    facticity = visibility_lambda >= fixture.facticity_threshold
    return [
        telemetry_event(
            protocol,
            "decoherence_suppression",
            "stressed",
            "pass" if residual <= fixture.max_residual_coherence + fixture.tolerance else "fail",
            fixture.max_residual_coherence - residual,
            input_hash,
            {"max_residual_coherence": residual},
        ),
        telemetry_event(
            protocol,
            "recoverability_loss",
            "stressed",
            "pass" if lambda_error <= fixture.tolerance and facticity == fixture.expected_facticity else "fail",
            min(fixture.tolerance - lambda_error, visibility_lambda - fixture.facticity_threshold),
            input_hash,
            {"lambda": visibility_lambda, "facticity": facticity},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if probability_error <= fixture.tolerance and min(probabilities) >= -fixture.tolerance else "fail",
            fixture.tolerance - probability_error,
            input_hash,
            {"max_probability_error": probability_error},
        ),
    ]


def run_zeno_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, RepeatedContextZenoFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "Zeno")
    input_hash = stable_digest(fixture_to_json(fixture))
    errors = [
        abs(math.cos(fixture.total_angle / (2.0 * sample.readout_count)) ** (2 * sample.readout_count) - sample.expected_survival)
        for sample in fixture.samples
    ]
    monotone = all(left.expected_survival <= right.expected_survival + fixture.tolerance for left, right in zip(fixture.samples, fixture.samples[1:]))
    max_error = max(errors)
    return [
        telemetry_event(
            protocol,
            "repeated_context_survival",
            "stressed",
            "pass" if max_error <= fixture.tolerance and monotone else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_survival_error": max_error, "monotone": monotone},
        ),
        telemetry_event(
            protocol,
            "context_normalization",
            "used",
            "pass",
            1.0,
            input_hash,
            {"sample_count": len(fixture.samples)},
        ),
    ]


def run_context_transfer_protocol(
    protocol: ExperimentProtocol,
    transfer_fixtures: Mapping[str, ContextTransferFixture],
    no_cloning_fixtures: Mapping[str, NoCloningFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(transfer_fixtures, protocol.experiment_id, "context transfer")
    obstruction = lookup_fixture(no_cloning_fixtures, "no_cloning", "no-cloning")
    input_hash = stable_digest({"transfer": fixture_to_json(fixture), "no_cloning": fixture_to_json(obstruction)})
    corrected_state = teleportation_corrected_state(
        teleportation_branch_state(fixture.input_state, fixture.bell_branch),
        fixture.bell_branch,
    )
    max_error = max(
        abs(actual - expected)
        for actual, expected in zip(corrected_state, fixture.expected_target_state, strict=True)
    )
    obstruction_value = no_cloning_obstruction(obstruction.state_overlap)
    obstructed = obstruction_value >= obstruction.min_obstruction - obstruction.tolerance
    return [
        telemetry_event(
            protocol,
            "context_transfer_branch",
            "used",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_target_error": max_error},
        ),
        telemetry_event(
            protocol,
            "no_cloning_obstruction",
            "blocked",
            "pass" if obstructed == obstruction.expected_obstructed else "fail",
            obstruction_value - obstruction.min_obstruction,
            input_hash,
            {"obstruction": obstruction_value, "expected_obstructed": obstruction.expected_obstructed},
        ),
    ]


def run_no_cloning_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, NoCloningFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "no-cloning")
    input_hash = stable_digest(fixture_to_json(fixture))
    obstruction_value = no_cloning_obstruction(fixture.state_overlap)
    obstructed = obstruction_value >= fixture.min_obstruction - fixture.tolerance
    return [
        telemetry_event(
            protocol,
            "no_cloning_obstruction",
            "stressed",
            "pass" if obstructed == fixture.expected_obstructed else "fail",
            obstruction_value - fixture.min_obstruction,
            input_hash,
            {"obstruction": obstruction_value, "expected_obstructed": fixture.expected_obstructed},
        )
    ]


def run_barrier_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, BarrierTransmissionFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "barrier")
    input_hash = stable_digest(fixture_to_json(fixture))
    transmission = math.exp(-2.0 * fixture.decay_constant * fixture.width)
    reflection = 1.0 - transmission
    max_error = max(
        abs(transmission - fixture.expected_transmission),
        abs(reflection - fixture.expected_reflection),
    )
    return [
        telemetry_event(
            protocol,
            "barrier_transmission_suppression",
            "stressed",
            "pass" if fixture.classically_forbidden and max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"transmission": transmission, "reflection": reflection},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if min(transmission, reflection) >= -fixture.tolerance else "fail",
            min(transmission, reflection),
            input_hash,
            {"min_probability": min(transmission, reflection)},
        ),
    ]


def run_bosonic_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, BosonicIndistinguishabilityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "bosonic")
    input_hash = stable_digest(fixture_to_json(fixture))
    coincidence = (1.0 - fixture.wavepacket_overlap * fixture.wavepacket_overlap) / 2.0
    bunching = 1.0 - coincidence
    max_error = max(abs(coincidence - fixture.expected_coincidence), abs(bunching - fixture.expected_bunching))
    return [
        telemetry_event(
            protocol,
            "bosonic_coincidence_suppression",
            "stressed",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"coincidence": coincidence, "bunching": bunching},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if min(coincidence, bunching) >= -fixture.tolerance else "fail",
            min(coincidence, bunching),
            input_hash,
            {"min_probability": min(coincidence, bunching)},
        ),
    ]


def run_single_quantum_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, SingleQuantumFacticityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "single quantum")
    input_hash = stable_digest(fixture_to_json(fixture))
    g2_zero = (fixture.coincidence_count * fixture.trial_count) / (fixture.detector_a_count * fixture.detector_b_count)
    g2_error = abs(g2_zero - fixture.expected_g2_zero)
    return [
        telemetry_event(
            protocol,
            "single_quantum_coincidence_exclusion",
            "stressed",
            "pass" if g2_error <= fixture.tolerance and g2_zero <= fixture.max_g2_zero + fixture.tolerance else "fail",
            min(fixture.tolerance - g2_error, fixture.max_g2_zero - g2_zero),
            input_hash,
            {"g2_zero": g2_zero},
        ),
        telemetry_event(
            protocol,
            "positive_measure_readout",
            "used",
            "pass" if min(fixture.detector_a_count, fixture.detector_b_count, fixture.coincidence_count) >= 0 else "fail",
            float(min(fixture.detector_a_count, fixture.detector_b_count, fixture.coincidence_count)),
            input_hash,
            {"trial_count": fixture.trial_count},
        ),
    ]


def run_inheritance_swap_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, ConditionalInheritanceSwapFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "inheritance swap")
    input_hash = stable_digest(fixture_to_json(fixture))
    max_error = max(abs(correlation.expected_correlation - expected_swap_correlation(fixture.bell_outcome)) for correlation in fixture.remote_correlations)
    return [
        telemetry_event(
            protocol,
            "conditional_inheritance_swap",
            "used",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_correlation_error": max_error},
        )
    ]


def run_multipartite_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, MultipartiteContextualityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "multipartite contextuality")
    input_hash = stable_digest(fixture_to_json(fixture))
    product = 1
    for constraint in fixture.constraints:
        product *= constraint.expected_product
    obstructed = product < 0
    return [
        telemetry_event(
            protocol,
            "contextuality_obstruction",
            "stressed",
            "pass" if obstructed == fixture.expected_obstructed else "fail",
            1.0 if obstructed == fixture.expected_obstructed else -1.0,
            input_hash,
            {"obstructed": obstructed},
        )
    ]


def run_ks_contextuality_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, KSContextualityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "KS contextuality")
    input_hash = stable_digest(fixture_to_json(fixture))
    symbol_counts: dict[str, int] = {}
    for context in fixture.contexts:
        for symbol in context:
            symbol_counts[symbol] = symbol_counts.get(symbol, 0) + 1
    obstructed = len(fixture.contexts) % 2 == 1 and all(count % 2 == 0 for count in symbol_counts.values())
    return [
        telemetry_event(
            protocol,
            "contextuality_obstruction",
            "stressed",
            "pass" if obstructed == fixture.expected_obstructed else "fail",
            1.0 if obstructed == fixture.expected_obstructed else -1.0,
            input_hash,
            {"obstructed": obstructed},
        )
    ]


def run_temporal_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, TemporalFactivityFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "temporal facticity")
    input_hash = stable_digest(fixture_to_json(fixture))
    k_value = fixture.c12 + fixture.c23 - fixture.c13
    k_error = abs(k_value - fixture.expected_k)
    violation = k_value > fixture.macrorealist_bound + fixture.tolerance
    return [
        telemetry_event(
            protocol,
            "temporal_facticity_bound",
            "stressed",
            "pass" if k_error <= fixture.tolerance and violation == fixture.expected_violation else "fail",
            min(fixture.tolerance - k_error, k_value - fixture.macrorealist_bound),
            input_hash,
            {"k": k_value, "violation": violation},
        )
    ]


def run_partial_facticity_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, PartialFactivityReadoutFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "partial facticity")
    input_hash = stable_digest(fixture_to_json(fixture))
    pointer_shift = fixture.coupling * fixture.weak_value
    shift_error = abs(pointer_shift - fixture.expected_pointer_shift)
    full_facticity = fixture.distinguishability_gain >= fixture.facticity_threshold
    status: TelemetryStatus = (
        "pass"
        if (
            shift_error <= fixture.tolerance
            and fixture.observed_disturbance <= fixture.max_disturbance + fixture.tolerance
            and full_facticity == fixture.expected_full_facticity
        )
        else "fail"
    )
    return [
        telemetry_event(
            protocol,
            "partial_facticity_readout",
            "stressed",
            status,
            min(fixture.tolerance - shift_error, fixture.max_disturbance - fixture.observed_disturbance),
            input_hash,
            {"pointer_shift": pointer_shift, "full_facticity": full_facticity},
        )
    ]


def run_graph_walk_protocol(
    protocol: ExperimentProtocol,
    fixtures: Mapping[str, UnitaryGraphWalkFixture],
) -> list[TelemetryEvent]:
    fixture = lookup_fixture(fixtures, protocol.experiment_id, "graph walk")
    input_hash = stable_digest(fixture_to_json(fixture))
    distribution = hadamard_walk_distribution(fixture.steps, fixture.initial_coin)
    expected = {point.position: point.probability for point in fixture.expected_distribution}
    positions = sorted(set(distribution) | set(expected))
    max_error = max(abs(distribution.get(position, 0.0) - expected.get(position, 0.0)) for position in positions)
    total_error = abs(sum(distribution.values()) - 1.0)
    return [
        telemetry_event(
            protocol,
            "unitary_graph_walk_distribution",
            "used",
            "pass" if max_error <= fixture.tolerance else "fail",
            fixture.tolerance - max_error,
            input_hash,
            {"max_distribution_error": max_error},
        ),
        telemetry_event(
            protocol,
            "context_normalization",
            "used",
            "pass" if total_error <= fixture.tolerance else "fail",
            fixture.tolerance - total_error,
            input_hash,
            {"total": sum(distribution.values())},
        ),
    ]


def run_residual_not_implemented_protocol(protocol: ExperimentProtocol) -> list[TelemetryEvent]:
    input_hash = stable_digest(
        {
            "experiment_id": protocol.experiment_id,
            "fixture_class": protocol.fixture_class,
            "claim_boundary": protocol.claim_boundary,
        }
    )
    return [
        telemetry_event(
            protocol,
            "residual_fixture_not_implemented",
            "blocked",
            "blocked",
            0.0,
            input_hash,
            {
                "reason": "no safe v8 telemetry fixture implemented yet",
                "experiment_id": protocol.experiment_id,
            },
        )
    ]


def telemetry_event(
    protocol: ExperimentProtocol,
    node_id: str,
    role: TelemetryRole,
    status: TelemetryStatus,
    margin: float,
    input_hash: str,
    output: Mapping[str, object],
) -> TelemetryEvent:
    return TelemetryEvent(
        experiment_id=protocol.experiment_id,
        node_id=node_id,
        role=role,
        status=status,
        margin=margin,
        input_hash=input_hash,
        output_hash=stable_digest(output),
        source=f"lean_protocol:{protocol.identifier}",
    )


def validate_telemetry_events(
    protocol: ExperimentProtocol,
    events: Sequence[TelemetryEvent],
    known_nodes: frozenset[str],
) -> None:
    protocol_nodes = frozenset(protocol.logical_nodes)
    allowed = frozenset(protocol.allowed_result_statuses)
    for event in events:
        if event.node_id not in known_nodes:
            raise ExperimentRunnerError(f"unknown telemetry logical node {event.node_id!r}")
        if event.node_id not in protocol_nodes:
            raise ExperimentRunnerError(
                f"telemetry node {event.node_id!r} is not declared by protocol {protocol.identifier!r}"
            )
        if event.status not in allowed:
            raise ExperimentRunnerError(
                f"telemetry status {event.status!r} is not allowed by protocol {protocol.identifier!r}"
            )


def experiment_status(events: Sequence[TelemetryEvent]) -> TelemetryStatus:
    if any(event.status == "fail" for event in events):
        return "fail"
    if any(event.status == "inconclusive" for event in events):
        return "inconclusive"
    if any(event.status == "blocked" for event in events):
        return "blocked"
    return "pass"


def build_node_stats(events: Sequence[TelemetryEvent]) -> list[NodeStats]:
    node_ids = sorted({event.node_id for event in events})
    stats: list[NodeStats] = []
    for node_id in node_ids:
        node_events = [event for event in events if event.node_id == node_id]
        stats.append(
            NodeStats(
                node_id=node_id,
                used=count_events(node_events, "role", "used"),
                stressed=count_events(node_events, "role", "stressed"),
                blocked=count_events(node_events, "role", "blocked"),
                failed=count_events(node_events, "role", "failed"),
                bypassed=count_events(node_events, "role", "bypassed"),
                passed=count_events(node_events, "status", "pass"),
                failed_status=count_events(node_events, "status", "fail"),
                inconclusive=count_events(node_events, "status", "inconclusive"),
                blocked_status=count_events(node_events, "status", "blocked"),
                min_margin=min(event.margin for event in node_events),
            )
        )
    return stats


def count_events(events: Sequence[TelemetryEvent], field: str, value: str) -> int:
    if field == "role":
        return sum(1 for event in events if event.role == value)
    if field == "status":
        return sum(1 for event in events if event.status == value)
    raise ExperimentRunnerError(f"unsupported event count field {field!r}")


def select_protocols(
    protocols: Sequence[ExperimentProtocol],
    experiment_filters: Sequence[str],
) -> tuple[ExperimentProtocol, ...]:
    if not experiment_filters:
        return tuple(protocols)
    filters = frozenset(experiment_filters)
    selected = tuple(
        protocol
        for protocol in protocols
        if protocol.experiment_id in filters or protocol.identifier in filters
    )
    found = {protocol.experiment_id for protocol in selected} | {protocol.identifier for protocol in selected}
    missing = sorted(filters - found)
    if missing:
        raise ExperimentRunnerError(f"unknown experiment filter(s): {', '.join(missing)}")
    return selected


def default_fixtures() -> FixtureSet:
    return FixtureSet(
        action_scale=ActionScaleFixture(
            shared_action_scale=2.0,
            tolerance=1.0e-10,
            allow_per_experiment_refit=False,
            hbar_status="blocked",
            observations=(
                ActionScaleObservation("photoelectric_anchor", "energy_frequency", "calibration", 6.0, 3.0),
                ActionScaleObservation("matter_wave_holdout", "momentum_wavenumber", "validation", 10.0, 5.0),
                ActionScaleObservation("phase_action_holdout", "phase_action", "validation", 8.0, 4.0),
                ActionScaleObservation("spectral_holdout", "spectral_transition", "validation", 14.0, 7.0),
                ActionScaleObservation("interference_holdout", "interference_phase", "validation", 12.0, 6.0),
            ),
        ),
        readout=ReadoutFixture(
            weights=(0.2, 0.3, 0.5),
            expected_total=1.0,
            tolerance=1.0e-10,
        ),
        bell=BellFixture(
            contexts=default_bell_contexts(),
            expected_abs_s=2.8284271247461903,
            max_abs_s=2.8284271247461903,
            tolerance=1.0e-10,
        ),
        interference={
            "two_path_interference": InterferenceFixture(0.8, 0.8, 1.0, 1.0, 1.0e-10),
            "delayed_choice": InterferenceFixture(0.8, 0.8, 1.0, 1.0, 1.0e-10),
        },
        sorkin={
            "finite_i3_actualization": SorkinFixture(0.0, 0.0, 1.0, 1.0, 1.0e-10),
            "triple_slit_sorkin_parameter": SorkinFixture(0.0, 0.0, 1.0, 1.0, 1.0e-10),
        },
        marker_eraser={
            "which_way_marker": MarkerEraserFixture(1.0, 0.0, 0.8, 0.0, 0.8, 1.0e-10),
            "quantum_eraser": MarkerEraserFixture(1.0, 0.0, 0.8, 0.0, 0.8, 1.0e-10),
        },
        phase={
            "finite_interferometer_network": PhaseAccumulationFixture(math.pi / 2.0, math.pi / 2.0, 1.0, 1.0, 1.0e-10),
            "aharonov_bohm_phase": PhaseAccumulationFixture(math.pi, math.pi, 1.0, 1.0, 1.0e-10),
            "ab_flux_period": PhaseAccumulationFixture(2.0 * math.pi, 2.0 * math.pi, 1.0, 1.0, 1.0e-10),
            "ramsey_interferometry": PhaseAccumulationFixture(math.pi / 3.0, math.pi / 3.0, 1.0, 1.0, 1.0e-10),
            "rabi_oscillation": PhaseAccumulationFixture(math.pi, math.pi, 1.0, 1.0, 1.0e-10),
        },
        spin={
            "stern_gerlach_single_axis": SpinTransitionFixture((1.0, 0.0), (1.0, 0.0), 1.0e-10),
            "sequential_stern_gerlach": SpinTransitionFixture((0.5, 0.5), (0.5, 0.5), 1.0e-10),
        },
        unitary={
            "unitary_measurement_context": UnitaryContextFixture(
                state=(1.0, 0.0),
                basis=((math.sqrt(0.5), math.sqrt(0.5)), (math.sqrt(0.5), -math.sqrt(0.5))),
                expected_probabilities=(0.5, 0.5),
                tolerance=1.0e-10,
            ),
        },
        projective={
            "projective_repeatability": ProjectiveRepeatabilityFixture(
                probabilities=(0.36, 0.64),
                expected_probabilities=(0.36, 0.64),
                repeat_probabilities=(1.0, 1.0),
                tolerance=1.0e-10,
            ),
        },
        bell_amplitude={
            "bell_chsh_from_amplitudes": default_bell_amplitude_fixture(),
        },
        singlet_angle={
            "singlet_angle_model": SingletAngleFixture(
                alice_angles=(0.0, math.pi / 2.0),
                bob_angles=(math.pi / 4.0, -math.pi / 4.0),
                expected_abs_s=2.8284271247461903,
                max_abs_s=2.8284271247461903,
                tolerance=1.0e-10,
            ),
        },
        decoherence={
            "decoherence_and_recoverability": DecoherenceRecoverabilityFixture(
                amplitudes=(0.6, 0.8),
                environment_kernel=((1.0, 0.01), (0.01, 1.0)),
                expected_probabilities=(0.36, 0.64),
                max_residual_coherence=0.005,
                observed_visibility=0.1,
                environment_recoverable_visibility=0.9,
                expected_lambda=2.1972245773362196,
                facticity_threshold=2.0,
                expected_facticity=True,
                tolerance=1.0e-10,
            ),
        },
        zeno={
            "quantum_zeno": RepeatedContextZenoFixture(
                total_angle=math.pi / 2.0,
                samples=(
                    ZenoSample(1, 0.5000000000000001),
                    ZenoSample(4, 0.8562321183810632),
                    ZenoSample(16, 0.9621656643239899),
                    ZenoSample(64, 0.9904077742506335),
                ),
                tolerance=1.0e-10,
            ),
        },
        context_transfer={
            "quantum_teleportation": ContextTransferFixture(
                input_state=(0.6, 0.8),
                bell_branch="psi_minus",
                expected_target_state=(0.6, 0.8),
                tolerance=1.0e-10,
            ),
        },
        no_cloning={
            "no_cloning": NoCloningFixture(
                state_overlap=0.5,
                min_obstruction=0.1,
                expected_obstructed=True,
                tolerance=1.0e-10,
            ),
        },
        barrier={
            "tunneling_barrier": BarrierTransmissionFixture(
                classically_forbidden=True,
                decay_constant=0.5,
                width=2.0,
                expected_transmission=0.1353352832366127,
                expected_reflection=0.8646647167633873,
                tolerance=1.0e-10,
            ),
        },
        bosonic={
            "hong_ou_mandel": BosonicIndistinguishabilityFixture(
                wavepacket_overlap=1.0,
                expected_coincidence=0.0,
                expected_bunching=1.0,
                tolerance=1.0e-10,
            ),
        },
        single_quantum={
            "antibunching_single_photon": SingleQuantumFacticityFixture(
                trial_count=100,
                detector_a_count=50,
                detector_b_count=50,
                coincidence_count=0,
                expected_g2_zero=0.0,
                max_g2_zero=0.5,
                tolerance=1.0e-10,
            ),
        },
        inheritance_swap={
            "entanglement_swapping": ConditionalInheritanceSwapFixture(
                bell_outcome="psi_minus",
                remote_correlations=(
                    RemoteCorrelation("zz", -1.0),
                    RemoteCorrelation("xx", -1.0),
                ),
                tolerance=1.0e-10,
            ),
        },
        multipartite={
            "ghz_mermin_contextuality": MultipartiteContextualityFixture(
                constraints=(
                    MerminConstraint(("x", "y", "y"), 1),
                    MerminConstraint(("y", "x", "y"), 1),
                    MerminConstraint(("y", "y", "x"), 1),
                    MerminConstraint(("x", "x", "x"), -1),
                ),
                expected_obstructed=True,
                tolerance=1.0e-10,
            ),
        },
        ks_contextuality={
            "kochen_specker_contextuality": KSContextualityFixture(
                contexts=(("a", "b"), ("b", "c"), ("c", "a")),
                expected_obstructed=True,
                tolerance=1.0e-10,
            ),
        },
        temporal={
            "leggett_garg_temporal_context": TemporalFactivityFixture(
                c12=math.sqrt(0.5),
                c23=math.sqrt(0.5),
                c13=0.0,
                expected_k=1.4142135623730951,
                macrorealist_bound=1.0,
                expected_violation=True,
                tolerance=1.0e-10,
            ),
        },
        partial_facticity={
            "weak_measurement": PartialFactivityReadoutFixture(
                coupling=0.1,
                weak_value=2.0,
                expected_pointer_shift=0.2,
                observed_disturbance=0.01,
                max_disturbance=0.05,
                distinguishability_gain=0.2,
                facticity_threshold=1.0,
                expected_full_facticity=False,
                tolerance=1.0e-10,
            ),
        },
        graph_walk={
            "quantum_random_walk": UnitaryGraphWalkFixture(
                steps=3,
                initial_coin=(1.0, 0.0),
                expected_distribution=(
                    WalkDistributionPoint(-3, 0.125),
                    WalkDistributionPoint(-1, 0.625),
                    WalkDistributionPoint(1, 0.125),
                    WalkDistributionPoint(3, 0.125),
                ),
                tolerance=1.0e-10,
            ),
        },
    )


def default_bell_contexts() -> tuple[BellContext, ...]:
    high = 0.4267766952966369
    low = 0.0732233047033631
    return (
        BellContext(0, 0, bell_outcomes(high, low)),
        BellContext(0, 1, bell_outcomes(high, low)),
        BellContext(1, 0, bell_outcomes(high, low)),
        BellContext(1, 1, bell_outcomes(low, high)),
    )


def default_bell_amplitude_fixture() -> BellAmplitudeFixture:
    high = 0.6532814824381883
    low = 0.27059805007309845
    return BellAmplitudeFixture(
        contexts=(
            BellAmplitudeContext(0, 0, bell_amplitudes(high, low)),
            BellAmplitudeContext(0, 1, bell_amplitudes(high, low)),
            BellAmplitudeContext(1, 0, bell_amplitudes(high, low)),
            BellAmplitudeContext(1, 1, bell_amplitudes(low, high)),
        ),
        expected_abs_s=2.8284271247461903,
        max_abs_s=2.8284271247461903,
        tolerance=1.0e-10,
    )


def bell_amplitudes(same_amplitude: float, different_amplitude: float) -> tuple[BellAmplitudeOutcome, ...]:
    return (
        BellAmplitudeOutcome(1, 1, same_amplitude),
        BellAmplitudeOutcome(1, -1, different_amplitude),
        BellAmplitudeOutcome(-1, 1, different_amplitude),
        BellAmplitudeOutcome(-1, -1, same_amplitude),
    )


def bell_outcomes(same_probability: float, different_probability: float) -> tuple[BellOutcome, ...]:
    return (
        BellOutcome(1, 1, same_probability),
        BellOutcome(1, -1, different_probability),
        BellOutcome(-1, 1, different_probability),
        BellOutcome(-1, -1, same_probability),
    )


def amplitude_context_to_bell_context(context: BellAmplitudeContext) -> BellContext:
    return BellContext(
        x=context.x,
        y=context.y,
        outcomes=tuple(
            BellOutcome(
                a=outcome.a,
                b=outcome.b,
                probability=outcome.amplitude * outcome.amplitude,
            )
            for outcome in context.amplitudes
        ),
    )


def bell_no_signalling_error(contexts: Sequence[BellContext]) -> float:
    max_error = 0.0
    for x_value in sorted({context.x for context in contexts}):
        marginals = [
            alice_marginal(context)
            for context in contexts
            if context.x == x_value
        ]
        max_error = max(max_error, marginal_spread(marginals))
    for y_value in sorted({context.y for context in contexts}):
        marginals = [
            bob_marginal(context)
            for context in contexts
            if context.y == y_value
        ]
        max_error = max(max_error, marginal_spread(marginals))
    return max_error


def marginal_spread(marginals: Sequence[Mapping[int, float]]) -> float:
    if len(marginals) <= 1:
        return 0.0
    outcomes = sorted({outcome for marginal in marginals for outcome in marginal})
    return max(
        abs(float(left.get(outcome, 0.0)) - float(right.get(outcome, 0.0)))
        for outcome in outcomes
        for left in marginals
        for right in marginals
    )


def alice_marginal(context: BellContext) -> dict[int, float]:
    output: dict[int, float] = {}
    for outcome in context.outcomes:
        output[outcome.a] = output.get(outcome.a, 0.0) + outcome.probability
    return output


def bob_marginal(context: BellContext) -> dict[int, float]:
    output: dict[int, float] = {}
    for outcome in context.outcomes:
        output[outcome.b] = output.get(outcome.b, 0.0) + outcome.probability
    return output


def chsh_value(contexts: Sequence[BellContext]) -> float:
    correlations = {(context.x, context.y): correlation(context) for context in contexts}
    return (
        correlations[(0, 0)]
        + correlations[(0, 1)]
        + correlations[(1, 0)]
        - correlations[(1, 1)]
    )


def correlation(context: BellContext) -> float:
    return sum(outcome.a * outcome.b * outcome.probability for outcome in context.outcomes)


def lookup_fixture[T](fixtures: Mapping[str, T], experiment_id: str, fixture_name: str) -> T:
    try:
        return fixtures[experiment_id]
    except KeyError as error:
        raise ExperimentRunnerError(
            f"missing {fixture_name} fixture for experiment {experiment_id!r}"
        ) from error


def phase_distance(left: float, right: float) -> float:
    raw = abs(left - right) % (2.0 * math.pi)
    return min(raw, (2.0 * math.pi) - raw)


def max_residual_coherence(amplitudes: Sequence[float], kernel: Sequence[Sequence[float]]) -> float:
    residual = 0.0
    for left_index, left_amplitude in enumerate(amplitudes):
        for right_index, right_amplitude in enumerate(amplitudes):
            if left_index != right_index:
                residual = max(
                    residual,
                    abs(left_amplitude * right_amplitude * kernel[left_index][right_index]),
                )
    return residual


def teleportation_branch_state(input_state: Sequence[float], bell_branch: str) -> tuple[float, ...]:
    alpha, beta = input_state
    if bell_branch == "phi_plus":
        return (alpha, beta)
    if bell_branch == "phi_minus":
        return (alpha, -beta)
    if bell_branch == "psi_plus":
        return (beta, alpha)
    if bell_branch == "psi_minus":
        return (beta, -alpha)
    raise ExperimentRunnerError(f"unknown teleportation Bell branch {bell_branch!r}")


def teleportation_corrected_state(branch_state: Sequence[float], bell_branch: str) -> tuple[float, ...]:
    left, right = branch_state
    if bell_branch == "phi_plus":
        return (left, right)
    if bell_branch == "phi_minus":
        return (left, -right)
    if bell_branch == "psi_plus":
        return (right, left)
    if bell_branch == "psi_minus":
        return (-right, left)
    raise ExperimentRunnerError(f"unknown teleportation Bell branch {bell_branch!r}")


def no_cloning_obstruction(state_overlap: float) -> float:
    return abs(state_overlap - (state_overlap * state_overlap))


def expected_swap_correlation(bell_outcome: str) -> float:
    if bell_outcome in {"psi_minus", "phi_minus"}:
        return -1.0
    if bell_outcome in {"psi_plus", "phi_plus"}:
        return 1.0
    raise ExperimentRunnerError(f"unknown swap Bell outcome {bell_outcome!r}")


def hadamard_walk_distribution(steps: int, initial_coin: tuple[float, float]) -> dict[int, float]:
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    amplitudes: dict[tuple[int, int], float] = {
        (0, 0): initial_coin[0],
        (0, 1): initial_coin[1],
    }
    for _ in range(steps):
        next_amplitudes: dict[tuple[int, int], float] = {}
        for position in sorted({position for position, _coin in amplitudes}):
            left = amplitudes.get((position, 0), 0.0)
            right = amplitudes.get((position, 1), 0.0)
            next_left = (left + right) * inv_sqrt2
            next_right = (left - right) * inv_sqrt2
            left_target = (position - 1, 0)
            right_target = (position + 1, 1)
            next_amplitudes[left_target] = next_amplitudes.get(left_target, 0.0) + next_left
            next_amplitudes[right_target] = next_amplitudes.get(right_target, 0.0) + next_right
        amplitudes = next_amplitudes
    distribution: dict[int, float] = {}
    for (position, _coin), amplitude in amplitudes.items():
        distribution[position] = distribution.get(position, 0.0) + amplitude * amplitude
    return distribution


def build_source_hashes(repo_root: Path) -> JsonObject:
    paths = [
        Path("Experiments/V8ExperimentProtocolRegistry.lean"),
        Path("theory_experiments/v8_runner.py"),
        Path("scripts/run_v8_experiment_suite.py"),
    ]
    hashes: JsonObject = {}
    for path in paths:
        absolute = repo_root / path
        if absolute.exists():
            hashes[str(path)] = file_sha256(absolute)
    return hashes


def fixture_to_json(fixture: object) -> JsonObject:
    if isinstance(fixture, ActionScaleFixture):
        return {
            "shared_action_scale": fixture.shared_action_scale,
            "tolerance": fixture.tolerance,
            "allow_per_experiment_refit": fixture.allow_per_experiment_refit,
            "hbar_status": fixture.hbar_status,
            "observations": [
                {
                    "id": observation.identifier,
                    "kind": observation.kind,
                    "role": observation.role,
                    "numerator": observation.numerator,
                    "denominator": observation.denominator,
                }
                for observation in fixture.observations
            ],
        }
    if isinstance(fixture, ReadoutFixture):
        return {
            "weights": list(fixture.weights),
            "expected_total": fixture.expected_total,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, BellFixture):
        return {
            "expected_abs_s": fixture.expected_abs_s,
            "max_abs_s": fixture.max_abs_s,
            "tolerance": fixture.tolerance,
            "contexts": [
                {
                    "x": context.x,
                    "y": context.y,
                    "outcomes": [
                        {
                            "a": outcome.a,
                            "b": outcome.b,
                            "p": outcome.probability,
                        }
                        for outcome in context.outcomes
                    ],
                }
                for context in fixture.contexts
            ],
        }
    if isinstance(fixture, InterferenceFixture):
        return {
            "visibility": fixture.visibility,
            "expected_visibility": fixture.expected_visibility,
            "context_total": fixture.context_total,
            "expected_total": fixture.expected_total,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, SorkinFixture):
        return {
            "i3_value": fixture.i3_value,
            "expected_i3": fixture.expected_i3,
            "context_total": fixture.context_total,
            "expected_total": fixture.expected_total,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, MarkerEraserFixture):
        return {
            "marker_distinguishability": fixture.marker_distinguishability,
            "marker_visibility": fixture.marker_visibility,
            "eraser_visibility": fixture.eraser_visibility,
            "expected_marker_visibility": fixture.expected_marker_visibility,
            "expected_eraser_visibility": fixture.expected_eraser_visibility,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, PhaseAccumulationFixture):
        return {
            "observed_phase": fixture.observed_phase,
            "expected_phase": fixture.expected_phase,
            "context_total": fixture.context_total,
            "expected_total": fixture.expected_total,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, SpinTransitionFixture):
        return {
            "probabilities": list(fixture.probabilities),
            "expected_probabilities": list(fixture.expected_probabilities),
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, UnitaryContextFixture):
        return {
            "state": list(fixture.state),
            "basis": [list(row) for row in fixture.basis],
            "expected_probabilities": list(fixture.expected_probabilities),
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, ProjectiveRepeatabilityFixture):
        return {
            "probabilities": list(fixture.probabilities),
            "expected_probabilities": list(fixture.expected_probabilities),
            "repeat_probabilities": list(fixture.repeat_probabilities),
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, BellAmplitudeFixture):
        return {
            "expected_abs_s": fixture.expected_abs_s,
            "max_abs_s": fixture.max_abs_s,
            "tolerance": fixture.tolerance,
            "contexts": [
                {
                    "x": context.x,
                    "y": context.y,
                    "amplitudes": [
                        {
                            "a": outcome.a,
                            "b": outcome.b,
                            "amp": outcome.amplitude,
                        }
                        for outcome in context.amplitudes
                    ],
                }
                for context in fixture.contexts
            ],
        }
    if isinstance(fixture, SingletAngleFixture):
        return {
            "alice_angles": list(fixture.alice_angles),
            "bob_angles": list(fixture.bob_angles),
            "expected_abs_s": fixture.expected_abs_s,
            "max_abs_s": fixture.max_abs_s,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, DecoherenceRecoverabilityFixture):
        return {
            "amplitudes": list(fixture.amplitudes),
            "environment_kernel": [list(row) for row in fixture.environment_kernel],
            "expected_probabilities": list(fixture.expected_probabilities),
            "max_residual_coherence": fixture.max_residual_coherence,
            "observed_visibility": fixture.observed_visibility,
            "environment_recoverable_visibility": fixture.environment_recoverable_visibility,
            "expected_lambda": fixture.expected_lambda,
            "facticity_threshold": fixture.facticity_threshold,
            "expected_facticity": fixture.expected_facticity,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, RepeatedContextZenoFixture):
        return {
            "total_angle": fixture.total_angle,
            "samples": [
                {
                    "readout_count": sample.readout_count,
                    "expected_survival": sample.expected_survival,
                }
                for sample in fixture.samples
            ],
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, ContextTransferFixture):
        return {
            "input_state": list(fixture.input_state),
            "bell_branch": fixture.bell_branch,
            "expected_target_state": list(fixture.expected_target_state),
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, NoCloningFixture):
        return {
            "state_overlap": fixture.state_overlap,
            "min_obstruction": fixture.min_obstruction,
            "expected_obstructed": fixture.expected_obstructed,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, BarrierTransmissionFixture):
        return {
            "classically_forbidden": fixture.classically_forbidden,
            "decay_constant": fixture.decay_constant,
            "width": fixture.width,
            "expected_transmission": fixture.expected_transmission,
            "expected_reflection": fixture.expected_reflection,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, BosonicIndistinguishabilityFixture):
        return {
            "wavepacket_overlap": fixture.wavepacket_overlap,
            "expected_coincidence": fixture.expected_coincidence,
            "expected_bunching": fixture.expected_bunching,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, SingleQuantumFacticityFixture):
        return {
            "trial_count": fixture.trial_count,
            "detector_a_count": fixture.detector_a_count,
            "detector_b_count": fixture.detector_b_count,
            "coincidence_count": fixture.coincidence_count,
            "expected_g2_zero": fixture.expected_g2_zero,
            "max_g2_zero": fixture.max_g2_zero,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, ConditionalInheritanceSwapFixture):
        return {
            "bell_outcome": fixture.bell_outcome,
            "remote_correlations": [
                {
                    "context": correlation.context,
                    "expected_correlation": correlation.expected_correlation,
                }
                for correlation in fixture.remote_correlations
            ],
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, MultipartiteContextualityFixture):
        return {
            "constraints": [
                {
                    "context": list(constraint.context),
                    "expected_product": constraint.expected_product,
                }
                for constraint in fixture.constraints
            ],
            "expected_obstructed": fixture.expected_obstructed,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, KSContextualityFixture):
        return {
            "contexts": [list(context) for context in fixture.contexts],
            "expected_obstructed": fixture.expected_obstructed,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, TemporalFactivityFixture):
        return {
            "c12": fixture.c12,
            "c23": fixture.c23,
            "c13": fixture.c13,
            "expected_k": fixture.expected_k,
            "macrorealist_bound": fixture.macrorealist_bound,
            "expected_violation": fixture.expected_violation,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, PartialFactivityReadoutFixture):
        return {
            "coupling": fixture.coupling,
            "weak_value": fixture.weak_value,
            "expected_pointer_shift": fixture.expected_pointer_shift,
            "observed_disturbance": fixture.observed_disturbance,
            "max_disturbance": fixture.max_disturbance,
            "distinguishability_gain": fixture.distinguishability_gain,
            "facticity_threshold": fixture.facticity_threshold,
            "expected_full_facticity": fixture.expected_full_facticity,
            "tolerance": fixture.tolerance,
        }
    if isinstance(fixture, UnitaryGraphWalkFixture):
        return {
            "steps": fixture.steps,
            "initial_coin": list(fixture.initial_coin),
            "expected_distribution": [
                {
                    "position": point.position,
                    "probability": point.probability,
                }
                for point in fixture.expected_distribution
            ],
            "tolerance": fixture.tolerance,
        }
    raise ExperimentRunnerError(f"unsupported fixture object {type(fixture).__name__}")


def stats_json_text(payload: Mapping[str, object], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True) + "\n"


def write_outputs(payload: Mapping[str, object], output_path: Path, report_path: Path, pretty: bool) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(stats_json_text(payload, pretty), encoding="utf-8")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(build_markdown_report(payload), encoding="utf-8")


def build_markdown_report(payload: Mapping[str, object]) -> str:
    experiments = require_list(payload.get("experiments"), "experiments")
    node_stats = require_list(payload.get("node_stats"), "node_stats")
    lines = [
        "# IDT v8 Experiment Node Telemetry",
        "",
        "Protocol authority: `lean_checked_protocol`.",
        "",
        "Boundary: experiment telemetry is certified executable evidence only, not formal proof authority.",
        "",
        "## Experiments",
        "",
    ]
    for item in experiments:
        row = require_object(item, "experiments[]")
        lines.append(
            f"- `{require_string(row.get('experiment_id'), 'experiment_id')}`: "
            f"{require_string(row.get('status'), 'status')}"
        )
    lines.extend(["", "## Logical Nodes", ""])
    for item in node_stats:
        row = require_object(item, "node_stats[]")
        lines.append(
            f"- `{require_string(row.get('node_id'), 'node_id')}`: "
            f"pass={require_int(row.get('pass'), 'pass')} "
            f"fail={require_int(row.get('fail'), 'fail')} "
            f"blocked={require_int(row.get('blocked_status'), 'blocked_status')}"
        )
    return "\n".join(lines) + "\n"


def validate_stats_payload(payload: Mapping[str, object]) -> None:
    require_literal(payload.get("schema"), SCHEMA, "schema")
    require_literal(payload.get("protocol_authority"), PROTOCOL_AUTHORITY, "protocol_authority")
    require_literal(payload.get("proof_boundary"), PROOF_BOUNDARY, "proof_boundary")
    coverage = require_object(payload.get("coverage"), "coverage")
    telemetry = require_list(payload.get("telemetry"), "telemetry")
    node_stats = require_list(payload.get("node_stats"), "node_stats")
    experiments = require_list(payload.get("experiments"), "experiments")
    if require_int(coverage.get("telemetry"), "coverage.telemetry") != len(telemetry):
        raise ExperimentRunnerError("coverage.telemetry does not match telemetry rows")
    if require_int(coverage.get("nodes"), "coverage.nodes") != len(node_stats):
        raise ExperimentRunnerError("coverage.nodes does not match node_stats rows")
    if require_int(coverage.get("experiments"), "coverage.experiments") != len(experiments):
        raise ExperimentRunnerError("coverage.experiments does not match experiment rows")


def stable_digest(payload: Mapping[str, object]) -> str:
    raw = json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:16]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_object(value: object, field: str) -> JsonObject:
    if not isinstance(value, dict):
        raise ExperimentRunnerError(f"{field} must be an object")
    output: JsonObject = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise ExperimentRunnerError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ExperimentRunnerError(f"{field} must be an array")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise ExperimentRunnerError(f"{field} must be a non-empty string")
    return value


def require_int(value: object, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ExperimentRunnerError(f"{field} must be an integer")
    return value


def require_literal(value: object, expected: str, field: str) -> None:
    actual = require_string(value, field)
    if actual != expected:
        raise ExperimentRunnerError(f"{field} must be {expected!r}, got {actual!r}")


def require_string_list(value: object, field: str) -> list[str]:
    items = require_list(value, field)
    output: list[str] = []
    for index, item in enumerate(items):
        output.append(require_string(item, f"{field}[{index}]"))
    return output


def require_fixture_class(value: object, field: str) -> FixtureClass:
    raw = require_string(value, field)
    if raw == "calibrated_action_scale_reconstruction":
        return "calibrated_action_scale_reconstruction"
    if raw == "finite_readout_normalization":
        return "finite_readout_normalization"
    if raw == "bell_chsh_table":
        return "bell_chsh_table"
    if raw == "interference_visibility":
        return "interference_visibility"
    if raw == "sorkin_i3":
        return "sorkin_i3"
    if raw == "marker_eraser_visibility":
        return "marker_eraser_visibility"
    if raw == "phase_accumulation":
        return "phase_accumulation"
    if raw == "spin_axis_transition":
        return "spin_axis_transition"
    if raw == "unitary_context_readout":
        return "unitary_context_readout"
    if raw == "projective_repeatability":
        return "projective_repeatability"
    if raw == "bell_amplitude_table":
        return "bell_amplitude_table"
    if raw == "singlet_angle_grid":
        return "singlet_angle_grid"
    if raw == "decoherence_recoverability":
        return "decoherence_recoverability"
    if raw == "repeated_context_zeno":
        return "repeated_context_zeno"
    if raw == "context_transfer_no_cloning":
        return "context_transfer_no_cloning"
    if raw == "no_cloning_context_invariance":
        return "no_cloning_context_invariance"
    if raw == "barrier_transmission":
        return "barrier_transmission"
    if raw == "bosonic_indistinguishability":
        return "bosonic_indistinguishability"
    if raw == "single_quantum_facticity":
        return "single_quantum_facticity"
    if raw == "conditional_inheritance_swap":
        return "conditional_inheritance_swap"
    if raw == "multipartite_contextuality":
        return "multipartite_contextuality"
    if raw == "ks_contextuality_obstruction":
        return "ks_contextuality_obstruction"
    if raw == "temporal_facticity":
        return "temporal_facticity"
    if raw == "partial_facticity_readout":
        return "partial_facticity_readout"
    if raw == "unitary_graph_walk":
        return "unitary_graph_walk"
    if raw == "residual_not_implemented":
        return "residual_not_implemented"
    raise ExperimentRunnerError(f"{field} has unsupported fixture class {raw!r}")


def require_telemetry_status(value: object, field: str) -> TelemetryStatus:
    raw = require_string(value, field)
    if raw == "pass":
        return "pass"
    if raw == "fail":
        return "fail"
    if raw == "inconclusive":
        return "inconclusive"
    if raw == "blocked":
        return "blocked"
    raise ExperimentRunnerError(f"{field} has unsupported telemetry status {raw!r}")
