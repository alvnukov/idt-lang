"""Exact rail-rate check for one submitted independently phased device pair.

Outputs are read at the current states, then both devices take one hop. Only
their cycles reachable from the two declared initial states enter the rate
contract; either phase on each such cycle may be chosen independently.

For signal period m, clock period n, and g = gcd(m, n), offset d compares
signal phase 0 with clock phase d (both from their first cycle entries).
Over one joint period the Chinese remainder condition j-i = d mod g is
necessary and sufficient for a pair of phases (i, j) to be visited, once.
Thus the counts are circular correlations of residue histograms, not a
simulation of the lcm(m, n) steps and not an average over offsets.

Each signal state has exactly one rail, even at untriggered steps. A true
clock bit selects that one contact; a false bit makes no observation.
The table and squared-current reference are supplied, not derived from
physics. This check says nothing about iid outcomes, detectors, or QM.
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    object_fields,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "periodic_contact_observer_rail_rates"
SCOPE = "only_submitted_periodic_devices_and_calibrated_reference"
ASSUMPTIONS = (
    "two_supplied_total_deterministic_tables_with_declared_initial_states",
    "one_signal_rail_and_one_clock_bit_read_before_synchronous_unit_hops",
    "trigger_selects_the_single_signal_rail_without_loss_or_feedback",
    "independent_unknown_phases_on_the_reachable_recurrent_cycles",
    "supplied_labelled_neutral_integer_current_and_squared_rail_share_reference",
)
MAX_CURRENT = 10**6
MAX_RAILS = 8
MAX_STATES = 16384
_PACKED_WORK_THRESHOLD = 65536

SignalTable = tuple[tuple[int, int], ...]
ClockTable = tuple[tuple[int, bool], ...]


def _sequence(value: object, kind: type, minimum: int, maximum: int):
    if type(value) is not kind or not minimum <= len(value) <= maximum:
        raise ValueError(f"expected {kind.__name__} of length {minimum}..{maximum}")
    return value


def _object(value: object, fields: set[str]) -> dict[str, object]:
    if type(value) is not dict:
        raise TypeError("expected JSON object")
    return object_fields(value, fields)


@dataclass(frozen=True)
class PeriodicContactObserver:
    id: str
    current: tuple[int, ...]
    signal_initial: int
    signal_transitions: SignalTable
    clock_initial: int
    clock_transitions: ClockTable

    def __post_init__(self) -> None:
        if type(self.id) is not str:
            raise ValueError("expected candidate id string")
        candidate_id(self.id)
        if sum(bounded_int(x, -MAX_CURRENT, MAX_CURRENT)
               for x in _sequence(self.current, tuple, 2, MAX_RAILS)) != 0:
            raise ValueError("current must be neutral")
        for initial, table, is_clock in (
            (self.signal_initial, self.signal_transitions, False),
            (self.clock_initial, self.clock_transitions, True),
        ):
            _sequence(table, tuple, 1, MAX_STATES)
            bounded_int(initial, 0, len(table) - 1)
            for row in table:
                successor, output = _sequence(row, tuple, 2, 2)
                bounded_int(successor, 0, len(table) - 1)
                if is_clock:
                    if type(output) is not bool:
                        raise ValueError("expected a Boolean clock trigger")
                else:
                    bounded_int(output, 0, len(self.current) - 1)

    def specification(self) -> dict[str, object]:
        return {
            "id": self.id, "family": "periodic_contact_observer",
            "current": list(self.current),
            "signal": {"initial": self.signal_initial,
                       "transitions": [list(row) for row in self.signal_transitions]},
            "clock": {"initial": self.clock_initial,
                      "transitions": [list(row) for row in self.clock_transitions]},
        }


def parse_periodic_contact_observer(value: object) -> PeriodicContactObserver:
    raw = _object(value, {"id", "family", "current", "signal", "clock"})
    if type(raw["family"]) is not str or raw["family"] != "periodic_contact_observer":
        raise ValueError("expected periodic_contact_observer family")
    signal = _object(raw["signal"], {"initial", "transitions"})
    clock = _object(raw["clock"], {"initial", "transitions"})

    def device_table(device):
        return tuple(tuple(_sequence(row, list, 2, 2))
                     for row in _sequence(device["transitions"], list, 1, MAX_STATES))

    return PeriodicContactObserver(
        raw["id"], tuple(_sequence(raw["current"], list, 2, MAX_RAILS)),
        signal["initial"], device_table(signal), clock["initial"], device_table(clock),
    )


class _Deadline(Exception):
    pass


def _cycle(table: SignalTable | ClockTable, initial: int,
           guard: Callable[[], None]) -> tuple[int, list[int]]:
    seen, states = {}, []
    state = initial
    while state not in seen:
        guard()
        seen[state] = len(states)
        states.append(state)
        state = table[state][0]
    start = seen[state]
    return start, states[start:]


def _pack(digits: list[int], width: int, guard: Callable[[], None]) -> int:
    encoded = bytearray()
    for digit in digits:
        guard()
        encoded.extend(digit.to_bytes(width, "little"))
    return int.from_bytes(encoded, "little")


def _packed_rows(signal_by_rail: list[list[int]], clock: list[int],
                 limit: int, guard: Callable[[], None]) -> Iterator[list[int]]:
    """Digit-packed linear convolution folded mod x**g - 1.

    Reverse the indices of the signal histogram cyclically, so convolution
    at d gives sum_i signal[i] * clock[(i+d) % g]. Each coefficient before
    folding is at most sum(signal) * max(clock); choose a byte-aligned base
    strictly larger so there is no carry between coefficients.
    """
    g = len(clock)
    max_digit = max(map(sum, signal_by_rail)) * max(clock)
    width = max(1, (max_digit.bit_length() + 7) // 8)
    clock_packed = _pack(clock, width, guard)
    products = []
    for rail in signal_by_rail:
        reverse = rail[:1] + rail[:0:-1]
        rail_packed = _pack(reverse, width, guard)
        guard()
        product = rail_packed * clock_packed  # bounded by MAX_STATES and digit width
        guard()
        # Pad through coefficient 2*g-1, which is always zero.
        products.append(product.to_bytes(2 * g * width, "little"))
    for offset in range(limit):
        guard()
        lo, hi = offset * width, (offset + g) * width
        yield [int.from_bytes(p[lo:lo+width], "little") +
               int.from_bytes(p[hi:hi+width], "little") for p in products]


def _sparse_rows(signal_by_rail: list[list[int]], clock_live: list[tuple[int, int]],
                 limit: int, guard: Callable[[], None]) -> Iterator[list[int]]:
    g = len(signal_by_rail[0])
    for offset in range(limit):
        row = [0] * len(signal_by_rail)
        for j, count in clock_live:
            guard()
            i = (j - offset) % g
            for rail, histogram in enumerate(signal_by_rail):
                row[rail] += histogram[i] * count
        yield row


def evaluate_periodic_contact_observer(
    candidate: PeriodicContactObserver, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not PeriodicContactObserver:
        raise TypeError("expected a PeriodicContactObserver")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be a finite absolute monotonic time")

    def guard() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise _Deadline

    squares = [a * a for a in candidate.current]
    norm = sum(squares)
    checked, planned = 0, 0
    # All checked offsets before the first mismatch have the same integer
    # counts. Retain that prefix losslessly without duplicating the vector.
    observed: dict[str, object] = {
        "matching_prefix_length": 0, "matching_rail_counts": None, "first_mismatch": None,
    }
    details: dict[str, object] = {
        "rejection_scope": SCOPE, "scientific_status": "unassessed",
        "empirical_status": "not_tested", "proof_status": "not_attempted",
        "reference_rail_shares": [str(Fraction(a, norm)) for a in squares] if norm else None,
        "all_recurrent_phase_rail_rates_certified": False,
        "planned_is_exact": False,
        "count_method": None,
        "expected_rail_counts_per_joint_period": None,
        "observed_phase_rail_counts": observed,
        "budget_semantics": "one_relative_recurrent_phase_class_all_rails;"
                            "cycle_discovery_and_exact_correlation_setup_not_cases",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }

    def result(status: Status, reason: str, witness: dict[str, object] | None = None):
        details["stop_reason"] = reason
        return (Check(CHECK_ID, status, checked, planned, "=0", ASSUMPTIONS, witness),), details

    try:
        signal_start, signal = _cycle(candidate.signal_transitions, candidate.signal_initial, guard)
        clock_start, clock = _cycle(candidate.clock_transitions, candidate.clock_initial, guard)
        m, n = len(signal), len(clock)
        g = gcd(m, n)
        details.update(signal_period=m, clock_period=n, relative_phase_classes=g,
                       joint_period_steps=(m // g) * n,
                       signal_transient_length=signal_start, clock_transient_length=clock_start,
                       signal_recurrent_entry_state=signal[0], clock_recurrent_entry_state=clock[0])
        clock_hist = [0] * g
        for j, state in enumerate(clock):
            guard()
            clock_hist[j % g] += candidate.clock_transitions[state][1]
        triggers = sum(clock_hist)
        joint_triggers = triggers * (m // g)
        planned = g if norm and triggers else 0
        details.update(trigger_count_per_clock_cycle=triggers,
                       trigger_count_per_joint_period=joint_triggers, planned_is_exact=True)
        guard()
        if not norm:
            return result("unsupported", "unsupported_zero_current")
        if not triggers:
            return result("unsupported", "unsupported_silent_recurrent_clock")

        targets = [joint_triggers * a for a in squares]
        expected_counts = [str(Fraction(a, norm)) for a in targets]
        details["expected_rail_counts_per_joint_period"] = expected_counts
        signal_hist = [[0] * g for _ in squares]
        for i, state in enumerate(signal):
            guard()
            signal_hist[candidate.signal_transitions[state][1]][i % g] += 1
        clock_live = []
        for j, count in enumerate(clock_hist):
            guard()
            if count:
                clock_live.append((j, count))
        limit = min(planned, limits.max_cases)
        if limit * len(clock_live) * len(squares) >= _PACKED_WORK_THRESHOLD:
            details["count_method"] = "packed_exact_circular"
            rows = _packed_rows(signal_hist, clock_hist, limit, guard)
        else:
            details["count_method"] = "sparse_exact_circular"
            rows = _sparse_rows(signal_hist, clock_live, limit, guard)
        for offset, counts in enumerate(rows):
            guard()
            checked += 1
            for rail, (count, target) in enumerate(zip(counts, targets)):
                residual = norm * count - target
                if residual:
                    observed["first_mismatch"] = {"relative_phase_offset": offset,
                                                  "rail_counts": counts}
                    witness = {
                        "relative_phase_offset": offset, "signal_phase": 0, "clock_phase": offset,
                        "signal_state": signal[0], "clock_state": clock[offset],
                        "signal_period": m, "clock_period": n, "joint_period_steps": (m // g) * n,
                        "trigger_count": joint_triggers, "observed_rail_counts": counts,
                        "expected_rail_counts": expected_counts, "mismatched_rail": rail,
                        "integer_residual": residual,
                    }
                    return result("counterexample", "first_counterexample",
                                  {"inputs": witness, "actual": str(residual), "required": "=0"})
            if not offset:
                observed["matching_rail_counts"] = counts
            observed["matching_prefix_length"] = checked
        guard()
        if checked != planned:
            return result("inconclusive", "max_cases")
        details["all_recurrent_phase_rail_rates_certified"] = True
        return result("no_counterexample_within_bounds", "complete")
    except _Deadline:
        return result("inconclusive", "deadline")
