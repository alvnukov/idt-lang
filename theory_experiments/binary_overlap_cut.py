"""Necessary dimension condition for a submitted rectangular binary event table.

Conditional on an input-independent shared classical seed, preparation i is a
normalized rho_i on <=D levels, setting y is a binary effect E_y (classical
D-state messages are the diagonal special case). No bypass, preshared quantum
resource or postselection. For each seed, d^2/D <= Tr[(sum rho_i)^2] and its
diagonal terms are <=1. Writing A=sqrt(rho_i), B=sqrt(rho_j), split AB at E_y
and I-E_y. Triangle and Frobenius submultiplicativity bound ||AB||_F by
sqrt(p*q)+sqrt((1-p)*(1-q)), where p,q are the two seed-specific responses.

The SQUARED binary affinity f(p,q) is jointly concave: set a=sqrt(p*(1-p)),
b=sqrt(q*(1-q)), u=1-2p and v=1-2q. Its interior Hessian has diagonal
-b/(2*a^3), -a/(2*b^3) and mixed entry (4*a*b+u*v)/(2*a*b). The numerator
4*a*b+u*v is an inner product of two unit vectors, so the Hessian is negative
semidefinite. Extend by continuity. Consequently f of the two *averaged*
responses bounds their seed-averaged state overlap. Minimize over settings for
each pair. This seed argument is binary-specific, not an arbitrary-output
fidelity claim. The overlap expression for a direct prepare/measure
factorization is given by Sikora, Varvitsiotis & Wei, Phys. Rev. A 94, 042125
(2016). Taking p=sin^2(theta), q=sin^2(phi), f=cos^2(theta-phi): its maximum
over two disjoint intervals is at their closest ends; it is 1 if they meet.

The output is conditional on the submitted *simultaneous* outer bounds, not a
statistical procedure, a realization, or rejection of a physical theory.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import isfinite, isqrt
from pathlib import Path
from time import monotonic

from theory_experiments.prepare_measure_cut import (
    EVENT_BASES, MAX_DIMENSION, MAX_FRACTION_COMPONENT, MAX_SETTINGS, MEMORY_MODELS,
    Intervals,
)
from theory_experiments.primitive_screen import (
    Check, Limits, Status, bounded_int, candidate_id, exact_fraction, object_fields,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SCOPE = "only_submitted_binary_event_intervals_and_declared_sufficient_cut_model"
CHECK_ID = "binary_overlap_cut_pair_affinity_dimension"
SCALE = 1 << 48
ASSUMPTIONS = (
    "one_fixed_binary_event_and_its_complement_per_setting_on_all_attempts",
    "declared_closed_intervals_cover_all_underlying_event_probabilities_simultaneously",
    "counted_memory_is_sufficient_including_any_prefix_dependent_output_flags",
    "normalized_classical_or_quantum_states_with_binary_effects",
    "shared_classical_seed_if_present_is_independent_of_all_inputs",
    "no_preshared_quantum_resource_or_additional_cross_cut_channel",
)


def _obj(value, fields):
    if type(value) is not dict:
        raise TypeError("expected JSON object")
    return object_fields(value, fields)


def _seq(value, kind, low, high):
    if type(value) is not kind or not low <= len(value) <= high:
        raise ValueError(f"expected {kind.__name__} of length {low}..{high}")
    return value


@dataclass(frozen=True)
class BinaryOverlapCut:
    id: str
    event: str
    event_basis: str
    memory_model: str
    dimension: int
    shared_classical_seed: bool
    intervals: Intervals

    def __post_init__(self) -> None:
        for label in (self.id, self.event):
            if type(label) is not str:
                raise ValueError("expected short fixed identifier")
            candidate_id(label)
        if type(self.event_basis) is not str or self.event_basis not in EVENT_BASES:
            raise ValueError("invalid event basis")
        if type(self.memory_model) is not str or self.memory_model not in MEMORY_MODELS:
            raise ValueError("invalid memory model")
        bounded_int(self.dimension, 1, MAX_DIMENSION)
        if type(self.shared_classical_seed) is not bool:
            raise ValueError("shared_classical_seed must be Boolean")
        rows = _seq(self.intervals, tuple, 2, MAX_SETTINGS)
        width = len(_seq(rows[0], tuple, 1, MAX_SETTINGS))
        for row in rows:
            for cell in _seq(row, tuple, width, width):
                lo, hi = _seq(cell, tuple, 2, 2)
                if any(type(x) is not Fraction or max(abs(x.numerator), x.denominator)
                       > MAX_FRACTION_COMPONENT for x in (lo, hi)) or not 0 <= lo <= hi <= 1:
                    raise ValueError("expected bounded closed rational probability interval")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "binary_overlap_cut", "event": self.event,
                "event_basis": self.event_basis,
                "memory": {"model": self.memory_model, "dimension": self.dimension,
                           "shared_classical_seed": self.shared_classical_seed},
                "intervals": [[[str(lo), str(hi)] for lo, hi in row] for row in self.intervals]}


def parse_binary_overlap_cut(value: object) -> BinaryOverlapCut:
    raw = _obj(value, {"id", "family", "event", "event_basis", "memory", "intervals"})
    if type(raw["family"]) is not str or raw["family"] != "binary_overlap_cut":
        raise ValueError("expected binary_overlap_cut family")
    mem = _obj(raw["memory"], {"model", "dimension", "shared_classical_seed"})
    table = _seq(raw["intervals"], list, 2, MAX_SETTINGS)
    width = len(_seq(table[0], list, 1, MAX_SETTINGS))

    def interval(cell):
        lo, hi = _seq(cell, list, 2, 2)
        if type(lo) is not str or type(hi) is not str:
            raise ValueError("endpoints must be rational strings")
        return exact_fraction(lo), exact_fraction(hi)

    rows = tuple(tuple(interval(cell) for cell in _seq(row, list, width, width)) for row in table)
    return BinaryOverlapCut(raw["id"], raw["event"], raw["event_basis"], mem["model"],
                            mem["dimension"], mem["shared_classical_seed"], rows)


def _affinity_ticks(left, right) -> int:
    """Least k with k/SCALE >= max binary squared affinity over these intervals."""
    if left[1] < right[0]:
        p, q = left[1], right[0]
    elif right[1] < left[0]:
        p, q = right[1], left[0]
    else:
        return SCALE
    z = p.denominator*q.denominator
    a = p.numerator*q.numerator
    b = (p.denominator-p.numerator)*(q.denominator-q.numerator)
    rad = 4*SCALE*SCALE*a*b
    k = isqrt(rad)
    # (a+b+2*sqrt(a*b))/z; k*z-SCALE*(a+b) in the defining ceiling is integer.
    num = SCALE*(a+b)+k+(k*k < rad)
    return (num+z-1)//z


def evaluate_binary_overlap_cut(
    candidate: BinaryOverlapCut, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not BinaryOverlapCut or type(limits) is not Limits:
        raise TypeError("expected a BinaryOverlapCut and exact Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be a finite absolute monotonic time")
    rows = candidate.intervals
    d, cols, dim = len(rows), len(rows[0]), candidate.dimension
    eligible = candidate.event_basis != "accepted_only" and dim < d
    planned = d*(d-1)//2 if eligible else 0
    certificate = []
    details = {
        "rejection_scope": SCOPE, "scientific_status": "unassessed", "empirical_status": "not_tested",
        "proof_status": "not_attempted", "necessary_conditions_only": True,
        "event": candidate.event, "event_basis": candidate.event_basis, "preparations": d, "settings": cols,
        "declared_dimension": dim, "memory_model": candidate.memory_model,
        "shared_classical_seed": candidate.shared_classical_seed,
        "interval_coverage_status": "declared_simultaneous_outer_bounds_not_verified",
        "cut_sufficiency_status": "declared_model_premise_not_verified",
        "affinity_tick_denominator": SCALE, "ordered_overlap_sum_upper": None,
        "scaled_upper_gap": None, "planned_pairs": planned,
        "budget_semantics": "one_completed_unordered_pair_including_all_settings;no_partial_verdict",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }

    def finish(status: Status, reason: str, witness=None):
        details.update(stop_reason=reason, checked_pairs=len(certificate))
        return (Check(CHECK_ID, status, len(certificate), planned, ">=0", ASSUMPTIONS, witness),), details

    def expired():
        return deadline is not None and monotonic() >= deadline

    if candidate.event_basis == "accepted_only":
        return finish("unsupported", "unsupported_accepted_only_event_ratio")
    if dim >= d:
        return finish("inconclusive", "dimension_cap_at_least_preparation_count")
    for i, j in combinations(range(d), 2):
        if len(certificate) >= limits.max_cases:
            return finish("inconclusive", "max_cases")
        best, best_setting = SCALE+1, 0
        for y in range(cols):
            if expired():
                return finish("inconclusive", "deadline")
            k = _affinity_ticks(rows[i][y], rows[j][y])
            if k < best:
                best, best_setting = k, y
        if expired():
            return finish("inconclusive", "deadline")
        certificate.append([best_setting, best])
    total_ticks = d*SCALE+2*sum(k for _, k in certificate)
    total = Fraction(total_ticks, SCALE)
    gap = dim*total-d*d
    if expired():
        return finish("inconclusive", "deadline")
    details.update(ordered_overlap_sum_upper=str(total), scaled_upper_gap=str(gap))
    if gap >= 0:
        return finish("inconclusive", "no_strict_binary_overlap_contradiction_certified")
    witness = {"inputs": {"preparations": d, "settings": cols, "dimension": dim,
                          "shared_classical_seed": candidate.shared_classical_seed,
                          "pair_order": "zero_based_lexicographic_i_less_than_j",
                          "pair_columns": ["first_minimizing_setting", "affinity_upper_ticks"],
                          "pair_certificate": certificate, "tick_denominator": SCALE,
                          "ordered_overlap_sum_upper": str(total)},
               "actual": str(gap), "required": ">=0"}
    return finish("counterexample", "binary_overlap_dimension_bound_violated", witness)
