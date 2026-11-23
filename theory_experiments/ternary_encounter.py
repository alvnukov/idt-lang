"""Predict exact tagged occupancies after one supplied three-packet command.

A vertex is an even five-bit record of comparisons with named root port
germs, not a spatial coordinate. The supplied marked pair are the two
small ports. A hop holds one bit and complements the other four. The
anchored rule and its reverse use the blank record; the relative rule
uses only the difference between two distinct records. Idle is an
explicit unchanged-command control. None of the rules reads a charge.

The independent demand is a count (0..3) at a tag, not a fired flag,
calculated score, probability, or frequency. Independence of its origin
is a premise, not authenticated here. A match concerns only supplied
rows; even a perfectly matched control does not establish a working
physical detector. Ordered packet labels have no meaning in this family.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from math import isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import Check, Limits, bounded_int, candidate_id

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SCOPE = "only_submitted_three_packet_tag_counts_after_one_command"
CHECK_ID = "ternary_encounter_one_command_tag_count"
ASSUMPTIONS = (
    "supplied_rooted_even_five_port_records_and_marked_small_pair",
    "three_indistinguishable_packets_and_exactly_one_selected_command",
    "a_hop_preserves_the_held_germ_and_flips_all_four_others",
    "reproducible_preparation_and_tagged_counts_supplied_independently_of_prediction",
)
RULES = ("anchored", "relative", "idle")
MAX_OBSERVATIONS = 64
ALL_BITS = 31
Packets = tuple[int, int, int]
Observation = tuple[Packets, int, int]


def _sequence(value, kind, minimum, maximum):
    if type(value) is not kind or not minimum <= len(value) <= maximum:
        raise ValueError(f"expected {kind.__name__} of length {minimum}..{maximum}")
    return value


def _object(value, fields):
    if type(value) is not dict or len(value) != len(fields) or set(value) != fields:
        raise ValueError(f"expected exactly {sorted(fields)}")
    return value


def _record(value):
    bounded_int(value, 0, ALL_BITS)
    if value.bit_count() % 2:
        raise ValueError("expected an even five-bit germ record")
    return value


@dataclass(frozen=True)
class TernaryEncounter:
    id: str
    marked_ports: tuple[int, int]
    rule: str
    observations: tuple[Observation, ...]

    def __post_init__(self):
        if type(self.id) is not str:
            raise ValueError("expected a plain candidate id")
        candidate_id(self.id)
        a, b = _sequence(self.marked_ports, tuple, 2, 2)
        if bounded_int(a, 0, 4) >= bounded_int(b, 0, 4):
            raise ValueError("expected two distinct sorted marked ports")
        if type(self.rule) is not str or self.rule not in RULES:
            raise ValueError("unsupported rule; this grammar admits anchored, relative or idle")
        last = None
        totals = {}
        for row in _sequence(self.observations, tuple, 1, MAX_OBSERVATIONS):
            packets, vertex, count = _sequence(row, tuple, 3, 3)
            for v in _sequence(packets, tuple, 3, 3):
                _record(v)
            if packets != tuple(sorted(packets)):
                raise ValueError("packet triple must be sorted")
            _record(vertex)
            bounded_int(count, 0, 3)
            key = (packets, vertex)
            if last is not None and key <= last:
                raise ValueError("expected one sorted observation per preparation and tag")
            last = key
            tags, total = totals.get(packets, (0, 0))
            totals[packets] = tags + 1, total + count
        if any(total > 3 or (tags == 16 and total != 3) for tags, total in totals.values()):
            raise ValueError("submitted counts for one preparation cannot describe three packets")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "ternary_encounter", "marked_ports": list(self.marked_ports),
                "rule": self.rule, "observations": [
                    {"packets": list(packets), "vertex": vertex, "count": count}
                    for packets, vertex, count in self.observations]}


def parse_ternary_encounter(value: object) -> TernaryEncounter:
    raw = _object(value, {"id", "family", "marked_ports", "rule", "observations"})
    if type(raw["family"]) is not str or raw["family"] != "ternary_encounter":
        raise ValueError("expected ternary_encounter family")
    ports = tuple(sorted(bounded_int(i, 0, 4) for i in _sequence(raw["marked_ports"], list, 2, 2)))
    rows = []
    for row in _sequence(raw["observations"], list, 1, MAX_OBSERVATIONS):
        row = _object(row, {"packets", "vertex", "count"})
        packets = tuple(sorted(_record(v) for v in _sequence(row["packets"], list, 3, 3)))
        rows.append((packets, _record(row["vertex"]), bounded_int(row["count"], 0, 3)))
    return TernaryEncounter(raw["id"], ports, raw["rule"], tuple(sorted(rows)))


def _step(packets: Packets, small_mask: int, rule: str) -> Packets:
    """Return the unordered output. Caller supplies validated, sorted records."""
    a, b, c = packets
    if rule == "idle" or a == c or (a != b and b != c):
        return packets
    # Exactly two packets share b, independent of the slot of the singleton.
    delta = (c if a == b else a) ^ b
    large = delta & (ALL_BITS ^ small_mask)
    if large.bit_count() != 1 or (delta & small_mask).bit_count() != 1:
        return packets
    flip = ALL_BITS ^ large
    # The inverse starts at the hopped blank, i.e. the repeated record flip.
    if rule == "anchored" and b not in (0, flip):
        return packets
    return tuple(sorted(v ^ flip for v in packets))


def evaluate_ternary_encounter(
    candidate: TernaryEncounter, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not TernaryEncounter or type(limits) is not Limits:
        raise TypeError("expected exact TernaryEncounter and Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be finite absolute monotonic time")
    small_mask = sum(1 << j for j in candidate.marked_ports)
    outputs = {}
    comparisons = []
    first_mismatch = None
    planned = len(candidate.observations)

    def finish(status, reason, witness=None):
        checked = len(comparisons)
        return (Check(CHECK_ID, status, checked, planned, "=0", ASSUMPTIONS, witness),), {
            "rejection_scope": SCOPE, "scientific_status": "unassessed",
            "proof_status": "not_attempted", "empirical_status": "not_tested",
            "finite_submitted_contract_only": True, "stop_reason": reason,
            "check_units": ["compared_tag_counts"], "budget_semantics": "one_unit_per_compared_tag_count",
            "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
            "marked_ports": list(candidate.marked_ports), "rule": candidate.rule,
            "observations_submitted": planned, "observations_compared": checked,
            "distinct_preparations_evaluated": len(outputs),
            "distinct_triggering_preparations": sum(p != q for p, q in outputs.items()),
            "comparisons": comparisons,
        }

    for packets, vertex, expected in candidate.observations:
        if deadline is not None and monotonic() >= deadline:
            return finish("inconclusive", "deadline")
        if len(comparisons) >= limits.max_cases:
            return finish("inconclusive", "max_cases")
        if packets not in outputs:
            outputs[packets] = _step(packets, small_mask, candidate.rule)
        after = outputs[packets]
        predicted = after.count(vertex)
        row = {"packets": list(packets), "after": list(after), "vertex": vertex,
               "predicted_count": predicted, "submitted_count": expected}
        comparisons.append(row)
        if predicted != expected and first_mismatch is None:
            first_mismatch = {"inputs": dict(row), "actual": str(predicted - expected), "required": "=0"}
    if deadline is not None and monotonic() >= deadline:
        return finish("inconclusive", "deadline")
    if first_mismatch is not None:
        return finish("counterexample", "submitted_tag_count_mismatch", first_mismatch)
    return finish("no_counterexample_within_bounds", "finite_submitted_counts_matched")
