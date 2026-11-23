"""Replay one explicitly prepared stream of signed unit arrivals.

Outputs are vectors of signed integer counter increments. They need not be
nonnegative or sum to one, and are not probabilities, click counts or wave
amplitudes. A step read compares the last increment; a prefix read compares
the integrated counters starting at zero. Expectations are supplied separately
from the update law, even if they contradict each other or all three laws.

The bucket has a scalar remainder and broadcasts whole blocks. The rotor
instead explicitly uses the named cyclic order 0,1,...,d-1; a negative
arrival rewinds before debiting the two slots. This order and initial phase
are supplied resources, not geometry recovered from anonymous ports. Idle
returns the signed input to its own port with no internal memory. None of
these models explains the physical origin of events or of a signed detector.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from math import isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    bounded_int,
    candidate_id,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "signed_contact_stream_raw_step_and_prefix_counters"
SCOPE = "only_submitted_signed_unit_arrivals_and_requested_port_counter_vectors"
RULES = ("anonymous_bucket", "ordered_pair_rotor", "idle_wire")
ASSUMPTIONS = ("submitted_ordered_signed_unit_inputs_and_stable_port_identifiers",
               "initially_zero_signed_counters_and_declared_initial_device_state",
               "step_or_prefix_counter_references_supplied_independently_of_prediction")
MAX_ITEMS = 64
MAX_COUNT = 10**6
Input = tuple[int, int]
Readout = tuple[int, str, tuple[int, ...]]


def _fields(x, keys):
    if type(x) is not dict or len(x) != len(keys) or set(x) != keys:
        raise ValueError(f"expected exactly {sorted(keys)}")
    return x


def _seq(x, kind, minimum, maximum):
    if type(x) is not kind or not minimum <= len(x) <= maximum:
        raise ValueError(f"expected {kind.__name__} of length {minimum}..{maximum}")
    return x


def _scope(x):
    if type(x) is not str or x not in ("step", "prefix"):
        raise ValueError("expected step or prefix readout")
    return x


def _sign(x):
    if bounded_int(x, -1, 1) == 0:
        raise ValueError("arrival sign must be -1 or +1")
    return x


@dataclass(frozen=True)
class SignedContactStream:
    id: str
    ports: int
    rule: str
    initial_phase: int
    inputs: tuple[Input, ...]
    readouts: tuple[Readout, ...]

    def __post_init__(self):
        if type(self.id) is not str:
            raise ValueError("expected a plain candidate id")
        candidate_id(self.id)
        d = bounded_int(self.ports, 2, 8)
        if type(self.rule) is not str or self.rule not in RULES:
            raise ValueError("unsupported signed contact rule")
        bounded_int(self.initial_phase, 0, 0 if self.rule == "idle_wire" else d-1)
        for row in _seq(self.inputs, tuple, 1, MAX_ITEMS):
            i, s = _seq(row, tuple, 2, 2)
            bounded_int(i, 0, d-1)
            _sign(s)
        last = None
        for row in _seq(self.readouts, tuple, 1, MAX_ITEMS):
            after, scope, counts = _seq(row, tuple, 3, 3)
            key = (bounded_int(after, 1, len(self.inputs)), _scope(scope))
            if last is not None and key <= last:
                raise ValueError("readouts must have unique sorted (after, scope) keys")
            for v in _seq(counts, tuple, d, d):
                bounded_int(v, -MAX_COUNT, MAX_COUNT)
            last = key

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "signed_contact_stream", "ports": self.ports, "rule": self.rule,
                "initial_phase": self.initial_phase, "inputs": [{"port": i, "sign": s} for i, s in self.inputs],
                "readouts": [{"after": k, "scope": scope, "counts": list(v)} for k, scope, v in self.readouts]}


def parse_signed_contact_stream(value: object) -> SignedContactStream:
    x = _fields(value, {"id", "family", "ports", "rule", "initial_phase", "inputs", "readouts"})
    if type(x["family"]) is not str or x["family"] != "signed_contact_stream":
        raise ValueError("expected signed_contact_stream family")
    d = bounded_int(x["ports"], 2, 8)
    ins, reads = [], []
    for row in _seq(x["inputs"], list, 1, MAX_ITEMS):
        _fields(row, {"port", "sign"})
        ins.append((bounded_int(row["port"], 0, d-1), _sign(row["sign"])))
    for row in _seq(x["readouts"], list, 1, MAX_ITEMS):
        _fields(row, {"after", "scope", "counts"})
        counts = tuple(bounded_int(v, -MAX_COUNT, MAX_COUNT) for v in _seq(row["counts"], list, d, d))
        reads.append((bounded_int(row["after"], 1, len(ins)), _scope(row["scope"]), counts))
    return SignedContactStream(x["id"], d, x["rule"], x["initial_phase"], tuple(ins), tuple(sorted(reads)))


def _step(rule, d, phase, i, sign):
    """One validated command; phase 0 is only a wire-format placeholder for idle."""
    if rule == "idle_wire":
        out = [0]*d
        out[i] = sign
        return 0, out
    if rule == "anonymous_bucket":
        q, phase = divmod(phase + 2*sign, d)
        out = [q]*d
    else:
        start = phase if sign == 1 else (phase-2) % d
        out = [0]*d
        out[start] += sign
        out[(start+1) % d] += sign
        phase = (phase + 2*sign) % d
    out[i] -= sign
    return phase, out


def evaluate_signed_contact_stream(
    candidate: SignedContactStream, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not SignedContactStream or type(limits) is not Limits:
        raise TypeError("expected exact SignedContactStream and Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be finite absolute monotonic time")
    d, rule = candidate.ports, candidate.rule
    phase = candidate.initial_phase
    prefix = [0]*d
    comparisons = []
    first = None
    consumed = 0
    reads = candidate.readouts
    resources = {"ordered_pair_rotor": "supplied_named_cyclic_order_0_to_d_minus_one_and_pointer",
                 "anonymous_bucket": "scalar_remainder_and_uniform_broadcast",
                 "idle_wire": "memoryless_same_port_return"}
    assumptions = (*ASSUMPTIONS, resources[rule])

    def finish(status, reason, witness=None):
        return (Check(CHECK_ID, status, len(comparisons), len(reads), "=0", assumptions, witness),), {
            "rejection_scope": SCOPE, "scientific_status": "unassessed", "empirical_status": "not_tested",
            "proof_status": "not_attempted", "finite_submitted_contract_only": True,
            "budget_semantics": "one_unit_per_consumed_signed_arrival_including_unobserved_steps",
            "check_units": ["compared_counter_vectors"], "unused_limits": ["coefficient_radius", "reference_radius",
                                                                         "max_copies"],
            "ports": d, "rule": rule, "rule_resource": resources[rule], "inputs_submitted": len(candidate.inputs),
            "inputs_consumed": consumed, "readouts_submitted": len(reads), "readouts_compared": len(comparisons),
            "model_phase_after_consumed_inputs": None if rule == "idle_wire" else phase,
            "model_prefix_after_consumed_inputs": prefix.copy(), "comparisons": comparisons, "stop_reason": reason}

    for i, sign in candidate.inputs:
        if deadline is not None and monotonic() >= deadline:
            return finish("inconclusive", "deadline")
        if consumed >= limits.max_cases:
            return finish("inconclusive", "max_cases")
        phase, delta = _step(rule, d, phase, i, sign)
        prefix = [a+b for a, b in zip(prefix, delta, strict=True)]
        consumed += 1
        while len(comparisons) < len(reads) and reads[len(comparisons)][0] == consumed:
            _, scope, ref = reads[len(comparisons)]
            actual = delta if scope == "step" else prefix
            row = {"after": consumed, "scope": scope, "predicted_counts": actual.copy(), "submitted_counts": list(ref)}
            comparisons.append(row)
            if first is None:
                for j, (a, b) in enumerate(zip(actual, ref, strict=True)):
                    if a != b:
                        first = {"inputs": {"after": consumed, "scope": scope, "port": j,
                                            "predicted_count": a, "submitted_count": b},
                                 "actual": str(a-b), "required": "=0"}
                        break
    if deadline is not None and monotonic() >= deadline:
        return finish("inconclusive", "deadline")
    if first is not None:
        return finish("counterexample", "submitted_counter_vector_mismatch", first)
    return finish("no_counterexample_within_bounds", "finite_submitted_counter_vectors_matched")
