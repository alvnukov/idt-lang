"""Compare raw ternary-network dark flags, never amplitudes, gains or probabilities.

Contacts act simultaneously on three distinct named wires; other wires pass
through. For mobile refinement, wire (n,k) carries the exact signed value
n/3^k. Align just the contacted wires, reflect, and cancel redundant powers
of three. This implements exact cancellation on the refinement quotient;
it does not retain histories of the individual marks.

The stationary alternative has one initially empty remainder bucket per
unordered support. Only its integer output wires are exposed to the null
detector; a remainder is not spread back over visible ports. The field
alternative instead cancels in the submitted prime field, so a nonzero
rational result can appear dark. In every family a read is only the Boolean
answer to 'is the selected wire zero just after this command?'.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from math import isfinite, isqrt
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    bounded_int,
    candidate_id,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "ternary_network_submitted_port_null_flags"
SCOPE = "only_submitted_ordered_ternary_contacts_and_visible_port_null_flags"
RULES = ("mobile_depth", "stationary_bucket", "residue_field", "idle_wire")
MAX_CONTACTS = 96
MAX_READOUTS = 64
ASSUMPTIONS = ("supplied_named_wires_initial_signed_inputs_and_ordered_three_port_contacts",
               "submitted_dark_flags_independent_of_model_updates_and_initial_private_stocks_zero",
               "ideal_zero_comparison_in_the_declared_visible_channel_only")
Support = tuple[int, int, int]
Readout = tuple[int, int, bool]


def _seq(x, kind, lo, hi):
    if type(x) is not kind or not lo <= len(x) <= hi:
        raise ValueError(f"expected {kind.__name__} of length {lo}..{hi}")
    return x


def _fields(x, names):
    if type(x) is not dict or len(x) != len(names) or set(x) != names:
        raise ValueError(f"expected exactly {sorted(names)}")
    return x


def _dark(v):
    if type(v) is not bool:
        raise ValueError("dark must be a Boolean observation")
    return v


@dataclass(frozen=True)
class TernaryNetworkNulls:
    id: str
    rule: str
    modulus: int | None
    initial: tuple[int, ...]
    contacts: tuple[Support, ...]
    readouts: tuple[Readout, ...]

    def __post_init__(self):
        if type(self.id) is not str:
            raise ValueError("expected a plain candidate id")
        candidate_id(self.id)
        if type(self.rule) is not str or self.rule not in RULES:
            raise ValueError("unsupported ternary network rule")
        if self.rule == "residue_field":
            p = bounded_int(self.modulus, 2, 997)
            if p == 3 or any(p % j == 0 for j in range(2, isqrt(p)+1)):
                raise ValueError("modulus must be prime and admit division by three")
        elif self.modulus is not None:
            raise ValueError("only residue_field takes a modulus; expected null")
        for v in _seq(self.initial, tuple, 3, 8):
            bounded_int(v, -32, 32)
        d = len(self.initial)
        for h in _seq(self.contacts, tuple, 1, MAX_CONTACTS):
            for i in _seq(h, tuple, 3, 3):
                bounded_int(i, 0, d-1)
            if not h[0] < h[1] < h[2]:
                raise ValueError("expected three sorted distinct ports")
        last = None
        for row in _seq(self.readouts, tuple, 1, MAX_READOUTS):
            k, j, dark = _seq(row, tuple, 3, 3)
            key = (bounded_int(k, 1, len(self.contacts)), bounded_int(j, 0, d-1))
            _dark(dark)
            if last is not None and key <= last:
                raise ValueError("expected unique sorted (after, port) observations")
            last = key

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "ternary_network_nulls", "rule": self.rule, "modulus": self.modulus,
                "initial": list(self.initial), "contacts": [list(h) for h in self.contacts],
                "readouts": [{"after": k, "port": j, "dark": dark} for k, j, dark in self.readouts]}


def parse_ternary_network_nulls(value: object) -> TernaryNetworkNulls:
    x = _fields(value, {"id", "family", "rule", "modulus", "initial", "contacts", "readouts"})
    if type(x["family"]) is not str or x["family"] != "ternary_network_nulls":
        raise ValueError("expected ternary_network_nulls family")
    initial = tuple(bounded_int(v, -32, 32) for v in _seq(x["initial"], list, 3, 8))
    d = len(initial)
    contacts = tuple(tuple(sorted(bounded_int(i, 0, d-1) for i in _seq(h, list, 3, 3)))
                     for h in _seq(x["contacts"], list, 1, MAX_CONTACTS))
    reads = []
    for r in _seq(x["readouts"], list, 1, MAX_READOUTS):
        _fields(r, {"after", "port", "dark"})
        reads.append((bounded_int(r["after"], 1, len(contacts)), bounded_int(r["port"], 0, d-1), _dark(r["dark"])))
    return TernaryNetworkNulls(x["id"], x["rule"], x["modulus"], initial, contacts, tuple(sorted(reads)))


def _mobile(wires, depth, h):
    level = max(depth[j] for j in h)
    same_depth = [wires[j]*3**(level-depth[j]) for j in h]
    twice = 2*sum(same_depth)
    for j, v in zip(h, same_depth, strict=True):
        num, k = twice-3*v, level+1
        if not num:
            k = 0
        else:
            while k and num % 3 == 0:
                num //= 3
                k -= 1
        wires[j], depth[j] = num, k


def evaluate_ternary_network_nulls(
    candidate: TernaryNetworkNulls, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not TernaryNetworkNulls or type(limits) is not Limits:
        raise TypeError("expected exact TernaryNetworkNulls and Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be finite absolute monotonic time")
    p, rule = candidate.modulus, candidate.rule
    wires = list(candidate.initial) if p is None else [v % p for v in candidate.initial]
    inv3 = None if p is None else pow(3, -1, p)
    depths = [0]*len(wires)
    stocks = {}
    consumed = 0
    first = None
    comparisons = []
    reads = candidate.readouts
    resources = {"mobile_depth": "wire_local_exact_ternary_cancellation",
                 "stationary_bucket": "one_initially_zero_remainder_per_unordered_support_not_visible_at_ports",
                 "residue_field": "prime_field_zero_after_modular_reduction",
                 "idle_wire": "unchanged_integer_wires"}
    assumptions = (*ASSUMPTIONS, resources[rule])

    def finish(status, reason, witness=None):
        return (Check(CHECK_ID, status, len(comparisons), len(reads), "=0", assumptions, witness),), {
            "rejection_scope": SCOPE, "finite_submitted_contract_only": True, "scientific_status": "unassessed",
            "proof_status": "not_attempted", "empirical_status": "not_tested", "rule": rule, "modulus": p,
            "visible_channel": resources[rule], "contacts_consumed": consumed, "contacts_submitted": len(candidate.contacts),
            "readouts_compared": len(comparisons), "readouts_submitted": len(reads), "comparisons": comparisons,
            "budget_semantics": "one_unit_per_completed_contact_including_unobserved_suffix",
            "check_units": ["compared_submitted_null_flags"], "stop_reason": reason,
            "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"]}

    for h in candidate.contacts:
        if deadline is not None and monotonic() >= deadline:
            return finish("inconclusive", "deadline")
        if consumed >= limits.max_cases:
            return finish("inconclusive", "max_cases")
        if rule == "mobile_depth":
            _mobile(wires, depths, h)
        elif rule == "stationary_bucket":
            q, stocks[h] = divmod(stocks.get(h, 0) + 2*sum(wires[j] for j in h), 3)
            for j in h:
                wires[j] = q-wires[j]
        elif rule == "residue_field":
            reflect = 2*inv3*sum(wires[j] for j in h)
            for j in h:
                wires[j] = (reflect-wires[j]) % p
        consumed += 1
        while len(comparisons) < len(reads) and reads[len(comparisons)][0] == consumed:
            _, j, expected = reads[len(comparisons)]
            dark = wires[j] == 0
            row = {"after": consumed, "port": j, "predicted_dark": dark, "submitted_dark": expected}
            comparisons.append(row)
            if dark != expected and first is None:
                first = {"inputs": dict(row), "actual": str(int(dark)-int(expected)), "required": "=0"}
    if deadline is not None and monotonic() >= deadline:
        return finish("inconclusive", "deadline")
    if first is not None:
        return finish("counterexample", "submitted_null_flag_mismatch", first)
    return finish("no_counterexample_within_bounds", "finite_submitted_null_flags_matched")
