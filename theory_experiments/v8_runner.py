from __future__ import annotations

import hashlib
import json
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
class FixtureSet:
    action_scale: ActionScaleFixture
    readout: ReadoutFixture
    bell: BellFixture


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


def bell_outcomes(same_probability: float, different_probability: float) -> tuple[BellOutcome, ...]:
    return (
        BellOutcome(1, 1, same_probability),
        BellOutcome(1, -1, different_probability),
        BellOutcome(-1, 1, different_probability),
        BellOutcome(-1, -1, same_probability),
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
