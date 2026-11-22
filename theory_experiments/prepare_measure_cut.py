"""Necessary dimension tests for a submitted finite binary prepare–measure table.

The intervals are claimed outer bounds on the same event in every cell,
not confidence levels computed here. The counted cut must be sufficient:
prefix-dependent flags, timing and other persistent information cannot
bypass it. A declared shared classical seed must be independent of the
settings. The quantum model supplies no additional classical/quantum
memory and no preshared entanglement.

Without the seed, classical H_ij = p_i · e_j has rank <= s, and quantum
H_ij = Tr(rho_i E_j) has real rank <= D². Strict interval row dominance
certifies full rank for every table in the box. An arbitrary mixture may
increase rank, so neither of these rank tests applies to a shared seed.

If H_ii = 1, each quantum effect E_i is identity on the support of rho_i,
hence E_i >= rho_i. With d matched pairs, sum_ij H_ij >=
Tr((sum_i rho_i)²) >= d² / D. The same proof works for diagonal classical
states of dimension s. With an independent shared classical seed all d
saturated diagonals hold almost surely per seed, so this bound survives
averaging. Upper bounds on all cells suffice to certify a violation.

Click-normalized conditional ratios are unsupported. A jointly recorded
accept-and-event numerator is an ordinary binary all-attempt probability.
These are finite table tests, not a physical rejection, a realization
algorithm, an analysis of statistical significance or a Lean proof.
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from math import isfinite, lcm, prod
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    exact_fraction,
    object_fields,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SCOPE = "only_submitted_prepare_measure_intervals_and_declared_sufficient_cut_model"
RANK_CHECK_ID = "prepare_measure_cut_rank"
TRACE_CHECK_ID = "prepare_measure_cut_saturated_diagonal_dimension"
EVENT_BASES = ("unconditional", "accepted_only", "joint_accepted_event")
MEMORY_MODELS = ("classical", "quantum")
MAX_SETTINGS = 24
MAX_DIMENSION = 1024
MAX_FRACTION_COMPONENT = 10**12 - 1
BASE_ASSUMPTIONS = (
    "one_fixed_binary_event_per_cell_under_the_declared_event_convention",
    "declared_closed_intervals_are_safe_outer_bounds_not_inferred_here",
    "counted_memory_is_sufficient_and_no_prefix_dependent_side_channel_bypasses_the_cut",
    "normalized_classical_distributions_or_quantum_states_and_binary_effects",
    "no_preshared_entanglement_or_additional_cross_cut_channel",
)
RANK_ASSUMPTIONS = (*BASE_ASSUMPTIONS, "no_shared_classical_seed_bypasses_the_counted_cut")
TRACE_ASSUMPTIONS = (
    *BASE_ASSUMPTIONS, "every_matched_diagonal_probability_is_exactly_one",
    "declared_shared_classical_seed_if_any_is_independent_of_the_settings",
)
Intervals = tuple[tuple[tuple[Fraction, Fraction], ...], ...]
ExactTable = tuple[tuple[Fraction, ...], ...]


def _sequence(value: object, kind: type, low: int, high: int):
    if type(value) is not kind or not low <= len(value) <= high:
        raise ValueError(f"expected {kind.__name__} of length {low}..{high}")
    return value


def _object(value: object, fields: set[str]) -> dict[str, object]:
    if type(value) is not dict:
        raise TypeError("expected JSON object")
    return object_fields(value, fields)


@dataclass(frozen=True)
class PrepareMeasureCut:
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
                raise ValueError("expected a short fixed identifier")
            candidate_id(label)
        if type(self.event_basis) is not str or self.event_basis not in EVENT_BASES:
            raise ValueError("invalid event basis")
        if type(self.memory_model) is not str or self.memory_model not in MEMORY_MODELS:
            raise ValueError("invalid memory model")
        bounded_int(self.dimension, 1, MAX_DIMENSION)
        if type(self.shared_classical_seed) is not bool:
            raise ValueError("shared_classical_seed must be Boolean")
        table = _sequence(self.intervals, tuple, 2, MAX_SETTINGS)
        for row in table:
            for cell in _sequence(row, tuple, len(table), len(table)):
                lo, hi = _sequence(cell, tuple, 2, 2)
                if any(type(x) is not Fraction or max(abs(x.numerator), x.denominator) > MAX_FRACTION_COMPONENT
                       for x in (lo, hi)):
                    raise ValueError("expected bounded exact rational endpoints")
                if not 0 <= lo <= hi <= 1:
                    raise ValueError("expected a nonempty closed interval inside [0,1]")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "prepare_measure_cut", "event": self.event,
                "event_basis": self.event_basis,
                "memory": {"model": self.memory_model, "dimension": self.dimension,
                           "shared_classical_seed": self.shared_classical_seed},
                "intervals": [[[str(lo), str(hi)] for lo, hi in row] for row in self.intervals]}


def parse_prepare_measure_cut(value: object) -> PrepareMeasureCut:
    raw = _object(value, {"id", "family", "event", "event_basis", "memory", "intervals"})
    if type(raw["family"]) is not str or raw["family"] != "prepare_measure_cut":
        raise ValueError("expected prepare_measure_cut family")
    memory = _object(raw["memory"], {"model", "dimension", "shared_classical_seed"})
    table = _sequence(raw["intervals"], list, 2, MAX_SETTINGS)

    def interval(cell):
        lo, hi = _sequence(cell, list, 2, 2)
        if type(lo) is not str or type(hi) is not str:
            raise ValueError("probability endpoints must be rational strings")
        return exact_fraction(lo), exact_fraction(hi)

    intervals = tuple(tuple(interval(cell) for cell in _sequence(row, list, len(table), len(table)))
                      for row in table)
    return PrepareMeasureCut(raw["id"], raw["event"], raw["event_basis"], memory["model"],
                             memory["dimension"], memory["shared_classical_seed"], intervals)


class _Deadline(Exception):
    pass


def _exact_text(value: int | Fraction) -> str:
    value = Fraction(value)
    if max(value.numerator.bit_length(), value.denominator.bit_length()) <= 2000:
        return str(value)
    # Conversion of a large exact aggregate must not depend on Python's
    # configurable integer-to-decimal digit limit.
    return f"{value.numerator:#x}/{value.denominator:#x}"


def _rank_or_minor(table: ExactTable, bound: int, guard: Callable[[], None]
                   ) -> tuple[int, dict[str, object] | None]:
    """Stop at an indexed nonzero (bound+1)-minor, or finish computing rank."""
    n = len(table)
    scales = []
    work = []
    for row in table:
        guard()
        scale = lcm(*(x.denominator for x in row))
        scales.append(scale)
        work.append([x.numerator * (scale // x.denominator) for x in row])
    rows, columns = list(range(n)), list(range(n))
    previous = 1
    for k in range(n):
        guard()
        at = next(((i, j) for j in range(k, n) for i in range(k, n) if work[i][j]), None)
        if at is None:
            return k, None
        i, j = at
        if i != k:
            rows[k], rows[i] = rows[i], rows[k]
            work[k], work[i] = work[i], work[k]
        if j != k:
            columns[k], columns[j] = columns[j], columns[k]
            for row in work:
                row[k], row[j] = row[j], row[k]
        pivot = work[k][k]
        if k == bound:
            chosen_rows, chosen_columns = rows[:k+1], columns[:k+1]
            determinant = Fraction(pivot, prod(scales[a] for a in chosen_rows))
            return k+1, {"rows": chosen_rows, "columns": chosen_columns,
                         "determinant_in_listed_order": _exact_text(determinant)}
        for a in range(k+1, n):
            guard()
            for b in range(k+1, n):
                numerator = pivot * work[a][b] - work[a][k] * work[k][b]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("non-exact fraction-free elimination")
                work[a][b] = quotient
            work[a][k] = 0
        previous = pivot
    return n, None


def evaluate_prepare_measure_cut(
    candidate: PrepareMeasureCut, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not PrepareMeasureCut or type(limits) is not Limits:
        raise TypeError("expected a PrepareMeasureCut and exact Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be a finite absolute monotonic time")

    def guard() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise _Deadline

    d = len(candidate.intervals)
    accepted_only = candidate.event_basis == "accepted_only"
    point_exact = all(lo == hi for row in candidate.intervals for lo, hi in row)
    rank_bound = candidate.dimension if candidate.memory_model == "classical" else candidate.dimension**2
    rank_eligible = not accepted_only and not candidate.shared_classical_seed and rank_bound < d
    trace_eligible = not accepted_only and all(candidate.intervals[i][i][0] == 1 for i in range(d))
    rank_detail: dict[str, object] = {
        "eligible": rank_eligible, "point_exact": point_exact,
        "rank_bound": None if accepted_only or candidate.shared_classical_seed else rank_bound,
        "rank_lower_bound": None, "exact_rank": None, "method": None,
    }
    trace_detail: dict[str, object] = {
        "eligible": trace_eligible, "entry_upper_sum": None, "scaled_upper_gap": None,
    }
    details: dict[str, object] = {
        "rejection_scope": SCOPE, "scientific_status": "unassessed",
        "empirical_status": "not_tested", "proof_status": "not_attempted",
        "necessary_conditions_only": True,
        "interval_coverage_status": "declared_outer_bounds_not_verified",
        "cut_sufficiency_status": "declared_model_premise_not_verified",
        "event": candidate.event, "event_basis": candidate.event_basis, "settings_per_side": d,
        "memory_model": candidate.memory_model, "declared_dimension": candidate.dimension,
        "shared_classical_seed": candidate.shared_classical_seed,
        "rank": rank_detail, "saturated_diagonal": trace_detail,
        "exact_aggregate_encoding": "decimal rational or signed hexadecimal numerator/denominator",
        "budget_semantics": "one_eligible_whole_table_necessary_test;rank_then_saturated_diagonal",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }
    done = 0
    stalled: str | None = None

    def budget() -> str | None:
        nonlocal stalled
        if stalled is None:
            if done >= limits.max_cases:
                stalled = "max_cases"
            else:
                try:
                    guard()
                except _Deadline:
                    stalled = "deadline"
        return stalled

    def result(check_id: str, status: Status, planned: int, checked: int, reason: str,
               detail: dict[str, object], assumptions: tuple[str, ...],
               witness: dict[str, object] | None = None) -> Check:
        detail["stop_reason"] = reason
        return Check(check_id, status, checked, planned, ">=0", assumptions, witness)

    def rank_check() -> Check:
        nonlocal done, stalled

        def finish(status, reason, *, checked=0, witness=None):
            return result(RANK_CHECK_ID, status, int(rank_eligible), checked, reason,
                          rank_detail, RANK_ASSUMPTIONS, witness)

        if accepted_only:
            return finish("unsupported", "unsupported_accepted_only_event_ratio")
        if candidate.shared_classical_seed:
            return finish("unsupported", "rank_not_applicable_with_shared_classical_seed")
        if not rank_eligible:
            return finish("inconclusive", "rank_cap_at_least_number_of_settings")
        stop = budget()
        if stop:
            return finish("inconclusive", stop)
        try:
            if point_exact:
                rank_detail["method"] = "fraction_free_exact_rank"
                exact_table = tuple(tuple(lo for lo, _ in row) for row in candidate.intervals)
                lower, certificate = _rank_or_minor(exact_table, rank_bound, guard)
            else:
                rank_detail["method"] = "strict_row_dominance_of_all_interval_realizations"
                margins = []
                for i, row in enumerate(candidate.intervals):
                    guard()
                    margins.append(row[i][0] - sum(hi for j, (_, hi) in enumerate(row) if j != i))
                lower = d if all(margin > 0 for margin in margins) else None
                certificate = ({"diagonal_lower_minus_off_diagonal_upper_sums": list(map(_exact_text, margins))}
                               if lower is not None else None)
            guard()
        except _Deadline:
            stalled = "deadline"
            return finish("inconclusive", stalled)
        done += 1
        rank_detail["rank_lower_bound"] = lower
        if point_exact and (certificate is None or lower == d):
            rank_detail["exact_rank"] = lower
        if certificate is None:
            return finish("inconclusive", "no_rank_contradiction_certified", checked=1)
        certificate.update(rank_bound=rank_bound, certified_rank_lower_bound=lower, method=rank_detail["method"])
        return finish("counterexample", "rank_bound_violated", checked=1,
                      witness={"inputs": certificate, "actual": str(rank_bound - lower), "required": ">=0"})

    def trace_check() -> Check:
        nonlocal done, stalled

        def finish(status, reason, *, checked=0, witness=None):
            return result(TRACE_CHECK_ID, status, int(trace_eligible), checked, reason,
                          trace_detail, TRACE_ASSUMPTIONS, witness)

        if accepted_only:
            return finish("unsupported", "unsupported_accepted_only_event_ratio")
        if not trace_eligible:
            return finish("inconclusive", "not_all_diagonals_certified_exactly_one")
        stop = budget()
        if stop:
            return finish("inconclusive", stop)
        try:
            upper_sum = Fraction(0)
            for row in candidate.intervals:
                guard()
                upper_sum += sum(hi for _, hi in row)
            gap = candidate.dimension * upper_sum - d*d
            gap_text = _exact_text(gap)
            upper_sum_text = _exact_text(upper_sum)
            guard()
        except _Deadline:
            stalled = "deadline"
            return finish("inconclusive", stalled)
        done += 1
        trace_detail.update(entry_upper_sum=upper_sum_text, scaled_upper_gap=gap_text)
        if gap >= 0:
            return finish("inconclusive", "no_saturated_diagonal_contradiction_certified", checked=1)
        witness = {"inputs": {"matched_pairs": d, "dimension": candidate.dimension,
                              "entry_upper_sum": upper_sum_text, "required_minimum_sum": _exact_text(
                                  Fraction(d*d, candidate.dimension)),
                              "shared_classical_seed": candidate.shared_classical_seed},
                   "actual": gap_text, "required": ">=0"}
        return finish("counterexample", "saturated_diagonal_dimension_bound_violated", checked=1, witness=witness)

    checks = (rank_check(), trace_check())
    details.update(checked_necessary_tests=done, planned_necessary_tests=sum(c.planned for c in checks))
    if any(c.status == "counterexample" for c in checks):
        details["stop_reason"] = "conditional_dimension_contradiction"
    elif accepted_only:
        details["stop_reason"] = "unsupported_accepted_only_event_ratio"
    else:
        details["stop_reason"] = stalled or "necessary_conditions_only_no_contradiction"
    return checks, details
