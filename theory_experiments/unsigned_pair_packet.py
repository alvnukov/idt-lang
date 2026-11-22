"""Exact packet-table screens under an explicit observation contract.

This is a finite supplied deterministic memoryless model, not experimental
evidence or a derivation of the exchange/readout requirements. Both contracts
admit all six individually addressed input packets. ``port_totals`` forgets
output rail identities, not input preparations. No pure-port-only contract is
silently substituted. Diagnostics never participate in candidate rejection.

The small pure core is shared with the optional exhaustive collision search;
evaluating one candidate never imports or executes that 46656-table search.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Literal, TypeAlias

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Trial,
    bounded_int,
    candidate_id,
    object_fields,
    run_probe,
)

Edge: TypeAlias = tuple[int, int]
Table: TypeAlias = tuple[int, ...]
ObservationContract: TypeAlias = Literal["resolved_packets", "port_totals"]
EDGES = tuple(combinations(range(4), 2))
INDEX = {edge: index for index, edge in enumerate(EDGES)}
INC = tuple(tuple(int(leg in edge) for leg in range(4)) for edge in EDGES)
COMP = tuple(
    next(index for index, other in enumerate(EDGES) if set(edge).isdisjoint(other))
    for edge in EDGES
)
MATCHES = tuple((index, other) for index, other in enumerate(COMP) if index < other)
BY_PORT = tuple(sum(row[:2]) for row in INC)
ID = tuple(range(6))
PAIRS = tuple(
    tuple(tuple(x + y for x, y in zip(left, right, strict=True)) for right in INC)
    for left in INC
)
OVER = tuple(
    tuple(sum(x * y for x, y in zip(left, right, strict=True)) for right in INC)
    for left in INC
)


def leg_table(permutation: tuple[int, ...]) -> Table:
    if sorted(permutation) != list(range(4)):
        raise ValueError("four-leg permutation required")
    return tuple(
        INDEX[min(permutation[a], permutation[b]), max(permutation[a], permutation[b])]
        for a, b in EDGES
    )


SWAP = leg_table((2, 3, 0, 1))
FIX = tuple(index for index, other in enumerate(SWAP) if index == other)


def after(left: Table, right: Table) -> Table:
    return tuple(left[index] for index in right)


def validate_table(table: Table) -> None:
    if len(table) != 6:
        raise ValueError("complete six-entry unsigned edge table required")
    for value in table:
        bounded_int(value, 0, 5)


def packet_diagnostics(table: Table) -> dict[str, bool]:
    """Fixed-size algebraic diagnostics only, never physical requirements."""
    validate_table(table)
    outputs = {PAIRS[table[a]][table[b]] for a, b in MATCHES}
    metric = all(
        OVER[a][b] == OVER[table[a]][table[b]] for a, b in combinations(range(6), 2)
    )
    return {
        "histogram_sufficient": len(outputs) == 1,
        "bijective": len(set(table)) == 6,
        "square_stock": metric,
    }


def check_table(table: Table) -> dict[str, bool]:
    """Full-table census helper; the bounded adapter uses run_probe instead."""
    diagnostics = packet_diagnostics(table)
    twice = after(table, table)
    raw_echo = twice == SWAP
    fixed = all(table[index] == index for index in FIX)
    coarse = all(BY_PORT[a] == BY_PORT[b] for a, b in zip(twice, SWAP, strict=True))
    coarse_fixed = all(BY_PORT[table[index]] == BY_PORT[index] for index in FIX)
    return {
        **diagnostics,
        "raw_echo": raw_echo,
        "transparent_root": raw_echo and fixed,
        "coarse_echo": coarse,
        "coarse_transparent": coarse and coarse_fixed,
    }


@dataclass(frozen=True)
class UnsignedPairPacket:
    id: str
    outputs: Table
    observation_contract: ObservationContract

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if not isinstance(self.outputs, tuple):
            raise TypeError("internal packet table must be an immutable tuple")
        validate_table(self.outputs)
        if self.observation_contract not in ("resolved_packets", "port_totals"):
            raise ValueError("observation_contract must be resolved_packets or port_totals")

    def specification(self) -> dict[str, object]:
        return {
            "id": self.id,
            "family": "unsigned_pair_packet",
            "outputs": list(self.outputs),
            "observation_contract": self.observation_contract,
        }


def parse_unsigned_pair_packet(value: object) -> UnsignedPairPacket:
    row = object_fields(value, {"id", "family", "outputs", "observation_contract"})
    if row["family"] != "unsigned_pair_packet":
        raise ValueError("expected unsigned_pair_packet family")
    outputs = row["outputs"]
    if not isinstance(outputs, list) or len(outputs) != 6:
        raise ValueError("outputs must be a six-entry JSON array")
    contract = row["observation_contract"]
    if contract not in ("resolved_packets", "port_totals"):
        raise ValueError("observation_contract must be resolved_packets or port_totals")
    return UnsignedPairPacket(
        candidate_id(row["id"]),
        tuple(bounded_int(value, 0, 5) for value in outputs),
        "resolved_packets" if contract == "resolved_packets" else "port_totals",
    )


ASSUMPTIONS = (
    "supplied_deterministic_memoryless_six_species_packet_table",
    "unordered_distinct_mark_pairs_on_four_fixed_addressed_legs",
    "all_six_input_packets_individually_preparable_including_tied_port_totals",
    "observed_ports_are_legs_01_and_23_with_two_marks_retained",
    "same_table_and_address_meaning_at_both_ticks",
    "supplied_two_tick_exchange_02_13_and_one_tick_equal_input_transparency",
    "finite_model_requirements_not_experimental_observations_or_Lean_proof",
)


def _observation(index: int, contract: ObservationContract) -> tuple[int, ...]:
    return (index,) if contract == "resolved_packets" else (BY_PORT[index], 2 - BY_PORT[index])


def _trials(model: UnsignedPairPacket, *, two_ticks: bool) -> Iterable[Trial]:
    outputs = after(model.outputs, model.outputs) if two_ticks else model.outputs
    required = SWAP if two_ticks else ID
    for index in ID if two_ticks else FIX:
        actual = _observation(outputs[index], model.observation_contract)
        target = _observation(required[index], model.observation_contract)
        yield Trial(
            {
                "input_packet": index,
                "input_legs": list(EDGES[index]),
                "ticks": 2 if two_ticks else 1,
                "observation_contract": model.observation_contract,
                "observed_actual": list(actual),
                "observed_required": list(target),
                "residual_meaning": "zero_iff_observed_values_equal",
            },
            Fraction(int(actual != target)),
        )


def evaluate_unsigned_pair_packet(
    model: UnsignedPairPacket, limits: Limits
) -> tuple[tuple[Check, ...], dict[str, object]]:
    prefix = "resolved" if model.observation_contract == "resolved_packets" else "port_total"
    assumptions = ASSUMPTIONS + (f"readout_contract_{model.observation_contract}",)
    checks = (
        run_probe(
            f"{prefix}_two_tick_exchange", _trials(model, two_ticks=True),
            6, "=0", assumptions, limits,
        ),
        run_probe(
            f"{prefix}_equal_input_transparency", _trials(model, two_ticks=False),
            2, "=0", assumptions, limits,
        ),
    )
    applicability = {
        f"{kind}_{requirement}": (
            "applicable" if kind == prefix
            else "not_applicable_unresolved_outputs" if kind == "resolved"
            else "not_selected_implied_by_resolved_checks"
        )
        for kind in ("resolved", "port_total")
        for requirement in ("two_tick_exchange", "equal_input_transparency")
    }
    coverage = {
        check.id: {
            "allowed_input_packets": list(indices),
            "tested_input_packets": list(indices[:check.checked]),
            "not_exercised_input_packets": list(indices[check.checked:]),
            "complete": check.checked == check.planned,
            "stop_reason": (
                "first_counterexample" if check.status == "counterexample"
                else "complete" if check.checked == check.planned else "max_cases"
            ),
        }
        for check, indices in zip(checks, (ID, FIX), strict=True)
    }
    return checks, {
        "adapter_status": "finite_unsigned_packet_screen",
        "scientific_status": "unassessed",
        "observation_contract": model.observation_contract,
        "packet_order": [list(edge) for edge in EDGES],
        "available_input_packets": list(ID),
        "input_scope": "all_six_addressable_packets_not_only_pure_port_preparations",
        "output_scope": "packet_index" if prefix == "resolved" else "two_aggregate_port_totals",
        "two_tick_leg_exchange": [2, 3, 0, 1],
        "transparent_input_packets": list(FIX),
        "requirement_applicability": applicability,
        "coverage": coverage,
        "budget_semantics": "max_cases_per_applicable_check_with_first_witness_stop",
        "diagnostics": packet_diagnostics(model.outputs),
        "diagnostic_scope": "fixed_size_full_table_algebra_not_rejection_criteria_or_physical_observations",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "missing_bridges": [
            "physical_packet_preparation_and_declared_output_resolution",
            "physical_two_tick_exchange_and_equal_input_transparency_calibration",
            "memorylessness_fixed_addresses_and_record_retention",
            "primitive_origin_of_packet_stock_clock_and_readout",
        ],
        "untested": [
            "pure_port_only_preparation_contract", "multi_packet_pairing_or_scheduler",
            "Born_rule", "QM_closure", "experimental_data",
        ],
    }
