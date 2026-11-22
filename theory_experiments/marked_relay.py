"""Bounded return-language comparison for a supplied marked port graph.

The specification provides transitions, a detector partition, and an origin
quantifier. The observed return is endpoint membership in the chosen origin's
marker class, not state equality unless that class is a singleton. Alternating
port counts are only the comparison rule, never the relay's readout.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from functools import lru_cache
from itertools import pairwise, permutations, product
from pathlib import Path
from typing import Literal, TypeAlias

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    object_fields,
)

OriginContract: TypeAlias = Literal["fixed", "exists", "all"]
Program: TypeAlias = Literal["named_six", "through_six"]
PortRow: TypeAlias = tuple[int, int, int, int]
Word: TypeAlias = tuple[int, ...]
CanonicalRows: TypeAlias = tuple[tuple[bool, tuple[int, ...]], ...]
PORTS = tuple(range(4))
MAX_STATES = 128
# A caller can import this adapter before the pipeline takes its own snapshot.
LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def _signed_counts(word: Word) -> PortRow:
    counts = [0] * len(PORTS)
    for i, port in enumerate(word):
        counts[port] += 1 if i % 2 == 0 else -1
    return counts[0], counts[1], counts[2], counts[3]


@lru_cache(maxsize=2)
def _program_words(program: Program) -> tuple[tuple[Word, bool], ...]:
    if program == "named_six":
        return tuple((triple * 2, True) for triple in permutations(PORTS, 3)) + tuple(
            (pair * 3, False) for pair in permutations(PORTS, 2)
        )
    return tuple(
        (word, _signed_counts(word) == (0, 0, 0, 0))
        for length in range(1, 7)
        for word in product(PORTS, repeat=length)
        if all(a != b for a, b in pairwise(word))
    )


def _parse_origin_contract(value: object) -> OriginContract:
    if type(value) is str:
        if value == "fixed":
            return "fixed"
        if value == "exists":
            return "exists"
        if value == "all":
            return "all"
    raise ValueError("unsupported origin_contract")


def _parse_program(value: object) -> Program:
    if type(value) is str:
        if value == "named_six":
            return "named_six"
        if value == "through_six":
            return "through_six"
    raise ValueError("unsupported marked relay program")


@dataclass(frozen=True)
class MarkedRelay:
    id: str
    transitions: tuple[PortRow, ...]
    marker_classes: tuple[int, ...]
    origin_contract: OriginContract
    program: Program
    origin: int | None = None

    def __post_init__(self) -> None:
        candidate_id(self.id)
        _parse_origin_contract(self.origin_contract)
        _parse_program(self.program)
        if type(self.transitions) is not tuple:
            raise ValueError("immutable tuple of transition rows required")
        state_count = bounded_int(len(self.transitions), 1, MAX_STATES)
        for row in self.transitions:
            if type(row) is not tuple or len(row) != len(PORTS):
                raise ValueError("each transition row requires four immutable entries")
            for target in row:
                bounded_int(target, 0, state_count - 1)
        for source, row in enumerate(self.transitions):
            for port, target in enumerate(row):
                if self.transitions[target][port] != source:
                    raise ValueError("each port must be a reciprocal involution")
        if (
            type(self.marker_classes) is not tuple
            or len(self.marker_classes) != state_count
        ):
            raise ValueError("one immutable marker class entry per state required")
        for marker in self.marker_classes:
            bounded_int(marker, 0, MAX_STATES - 1)
        if self.origin_contract == "fixed":
            bounded_int(self.origin, 0, state_count - 1)
        elif self.origin is not None:
            raise ValueError("quantified origins must not supply a fixed origin")

    def specification(self) -> dict[str, object]:
        result: dict[str, object] = {
            "id": self.id,
            "family": "marked_relay",
            "transitions": [list(row) for row in self.transitions],
            "marker_classes": list(self.marker_classes),
            "origin_contract": self.origin_contract,
            "program": self.program,
        }
        if self.origin is not None:
            result["origin"] = self.origin
        return result


def parse_marked_relay(value: object) -> MarkedRelay:
    row = object_fields(value)
    contract = _parse_origin_contract(row.get("origin_contract"))
    fields = {
        "id",
        "family",
        "transitions",
        "marker_classes",
        "origin_contract",
        "program",
    }
    if contract == "fixed":
        fields.add("origin")
    object_fields(row, fields)
    if type(row["family"]) is not str or row["family"] != "marked_relay":
        raise ValueError("expected marked_relay family")
    raw_transitions = row["transitions"]
    if type(raw_transitions) is not list or not 1 <= len(raw_transitions) <= MAX_STATES:
        raise ValueError("transitions must be a JSON array of 1 to 128 rows")
    state_count = len(raw_transitions)
    transitions: list[PortRow] = []
    for raw_targets in raw_transitions:
        if type(raw_targets) is not list or len(raw_targets) != len(PORTS):
            raise ValueError("each transition row must be a four-entry JSON array")
        a, b, c, d = (bounded_int(target, 0, state_count - 1) for target in raw_targets)
        transitions.append((a, b, c, d))
    raw_markers = row["marker_classes"]
    if type(raw_markers) is not list or len(raw_markers) != state_count:
        raise ValueError("marker_classes must be a JSON array with one entry per state")
    return MarkedRelay(
        candidate_id(row["id"]),
        tuple(transitions),
        tuple(bounded_int(marker, 0, MAX_STATES - 1) for marker in raw_markers),
        contract,
        _parse_program(row["program"]),
        bounded_int(row["origin"], 0, state_count - 1) if contract == "fixed" else None,
    )


def _canonical_root(model: MarkedRelay, origin: int) -> CanonicalRows:
    """Number reachable states by BFS in fixed port order, rooting at zero.

    Exact row equality identifies each numbered state across roots. This
    bijection preserves ports and the root-relative marker predicate, so it
    preserves the observed result of every word from those roots. Other
    labels and unreachable states are not part of that observation.
    """
    origin_marker = model.marker_classes[origin]
    order = [origin]
    numbers = {origin: 0}
    rows: list[tuple[bool, tuple[int, ...]]] = []
    for source in order:
        targets: list[int] = []
        for target in model.transitions[source]:
            if target not in numbers:
                numbers[target] = len(order)
                order.append(target)
            targets.append(numbers[target])
        rows.append((model.marker_classes[source] == origin_marker, tuple(targets)))
    return tuple(rows)


ASSUMPTIONS = (
    "supplied_finite_transition_table_with_four_reciprocal_involutive_ports",
    "supplied_detector_partition_with_return_observed_relative_to_the_same_origin",
    "one_fixed_origin_for_the_entire_word_program_under_the_declared_quantifier",
    "one_complete_word_from_the_origin_per_charged_trajectory",
    "root_sharing_requires_equal_ordered_port_bfs_rows_with_root_relative_marker_bits",
    "conditional_bounded_model_language_comparison_not_a_physical_geometry_or_experiment",
)
PROGRAM_REQUIREMENTS = {
    "named_six": "abcabc_returns_for_distinct_a_b_c_and_ababab_does_not_for_distinct_a_b",
    "through_six": "marked_return_iff_alternating_signed_port_counts_all_zero_through_length_six",
}


def _first_mismatch(
    model: MarkedRelay, origin: int, word: Word, expected: bool
) -> dict[str, object] | None:
    states = [origin]
    for port in word:
        states.append(model.transitions[states[-1]][port])
    endpoint = states[-1]
    origin_marker = model.marker_classes[origin]
    endpoint_marker = model.marker_classes[endpoint]
    observed = origin_marker == endpoint_marker
    if observed == expected:
        return None
    return {
        "origin": origin,
        "word": list(word),
        "path": states,
        "endpoint": endpoint,
        "origin_marker_class": origin_marker,
        "endpoint_marker_class": endpoint_marker,
        "observed_return": observed,
        "expected_return": expected,
        "alternating_signed_port_counts": list(_signed_counts(word)),
    }


def evaluate_marked_relay(
    model: MarkedRelay, limits: Limits
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(model) is not MarkedRelay or type(limits) is not Limits:
        raise TypeError("expected a MarkedRelay specification and Limits")
    model.__post_init__()
    limits.__post_init__()
    words = _program_words(model.program)
    groups: dict[CanonicalRows, list[int]] = {}
    selected = (
        (model.origin,) if model.origin is not None else range(len(model.transitions))
    )
    for origin in selected:
        groups.setdefault(_canonical_root(model, origin), []).append(origin)

    classes: list[dict[str, object]] = []
    failures: list[dict[str, object]] = []
    status: Status = "inconclusive"
    stop_reason = "max_cases_exhausted"
    viable_origin: int | None = None
    witness: dict[str, object] | None = None
    checked = 0
    decided_classes = 0
    for canonical, origins in groups.items():
        representative = origins[0]
        before = checked
        failure: dict[str, object] | None = None
        if status == "inconclusive":
            for word, expected in words:
                if checked == limits.max_cases:
                    break
                failure = _first_mismatch(model, representative, word, expected)
                checked += 1
                if failure is not None:
                    break
        class_checked = checked - before
        if failure is not None:
            class_status = "eliminated"
            decided_classes += 1
            failures.append(failure)
            if model.origin_contract != "exists":
                status = "counterexample"
                stop_reason = "selected_origin_counterexample"
                witness = {
                    "inputs": failure,
                    "actual": str(int(failure["observed_return"] is True)),
                    "required": str(int(failure["expected_return"] is True)),
                }
        elif class_checked == len(words):
            class_status = "viable"
            decided_classes += 1
            if model.origin_contract == "exists":
                viable_origin = representative
                status = "no_counterexample_within_bounds"
                stop_reason = "existential_origin_witness"
        elif class_checked:
            class_status = "partial"
        else:
            class_status = "not_tested"
        classes.append(
            {
                "representative": representative,
                "origins": origins,
                "reachable_states": len(canonical),
                "status": class_status,
                "checked": class_checked,
                "first_failure": failure,
            }
        )

    if status == "inconclusive" and decided_classes == len(groups):
        if model.origin_contract == "exists":
            status = "counterexample"
            stop_reason = "all_origin_classes_eliminated"
            witness = {
                "inputs": {
                    "origin_contract": "exists",
                    "failed_representatives": failures,
                },
                "actual": "0",
                "required": "at_least_one_origin_satisfying_the_entire_program",
            }
        else:
            status = "no_counterexample_within_bounds"
            stop_reason = "all_selected_origin_classes_passed"

    planned = len(groups) * len(words)
    requirement = PROGRAM_REQUIREMENTS[model.program]
    check = Check(
        "marked_relay_return_language",
        status,
        checked,
        planned,
        requirement,
        ASSUMPTIONS
        + (f"origin_contract_{model.origin_contract}", f"program_{model.program}"),
        witness,
    )
    return (check,), {
        "adapter_status": "finite_marked_relay_language_screen",
        "scientific_status": "unassessed",
        "state_count": len(model.transitions),
        "origin_contract": model.origin_contract,
        "fixed_origin": model.origin,
        "viable_origin": viable_origin,
        "program": model.program,
        "words_per_origin": len(words),
        "word_order": "distinct_abc_lexicographic_then_distinct_ab_lexicographic"
        if model.program == "named_six"
        else "length_then_lexicographic_nonbacktracking_through_six",
        "backtrack_boundary": (
            "only_the_nominated_six_tick_words_are_compared"
            if model.program == "named_six"
            else "adjacent_equal_ports_cancel_in_both_models_including_reduction_to_the_empty_word"
        ),
        "origin_classes": classes,
        "origin_class_certificate": {
            "algorithm": "rooted_port_bfs_with_relative_marker_v1",
            "port_order": list(PORTS),
            "numbering": "root_zero_then_first_discovery_in_breadth_first_port_order",
            "rows": "ordered_numbered_targets_and_boolean_marker_equals_origins_marker",
            "soundness": "exact_row_equality_gives_a_port_and_predicate_preserving_bijection",
            "boundary": "sufficient_sharing_not_a_minimal_return_language_partition",
        },
        "budget_semantics": "max_cases_counts_whole_word_trajectories_actually_executed_once_per_representative",
        "trajectory_plan_exhausted": checked == planned,
        "all_origin_classes_decided": decided_classes == len(groups),
        "quantified_requirement_resolved": status != "inconclusive",
        "stop_reason": stop_reason,
        "rejection_boundary": "only_this_supplied_relay_detector_origin_quantifier_and_program",
        "untested": [
            "physical_geometry",
            "experiment",
            "universal_primitive_rejection",
            "QM_closure",
        ],
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }
