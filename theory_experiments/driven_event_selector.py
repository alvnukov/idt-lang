"""Exact conditional-rate checker for one supplied deterministic event selector.

Knob indices are available before the event; even two identical current/fixed
entries are distinct supplied input labels. Each transition emits one bit
(1 = minus). On a nonzero neutral current v with fixed rail i, the supplied
quadratic stock and transposition splitter give the reference minus fraction
(v_j-v_k)^2/(2 sum(v_l^2)). No reference distribution exists at zero.

For EACH input c on a loop assign an integer residual q_c*y-a_c to coordinate
c, zero elsewhere (target = a_c/q_c reduced). A reachable closed walk with
nonzero total can be driven forever after a finite prefix. Conversely, if on
each reachable strongly connected component every internal edge vector is
the difference of its endpoint potentials, its cycles sum to zero. Every
trajectory changes component only finitely often; within each component
the residual telescopes. Thus each context's count discrepancy is bounded,
and its limiting conditional rate is correct whenever it recurs infinitely
often, even under feedback. No rate is imposed on a finitely visited input.
This decides the eventually-periodic-drive contract (and implies the stated
extension) only for this table and reference. Not iid, observed statistics,
a derivation of the table, or a formal physics proof.
"""

from __future__ import annotations

import hashlib
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    bounded_int,
    candidate_id,
    object_fields,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "driven_event_selector_context_rates"
SCOPE = "only_submitted_finite_transducer_and_calibrated_reference"
ASSUMPTIONS = (
    "total_time_homogeneous_deterministic_table_and_specified_initial_state",
    "one_registered_minus_or_plus_event_per_step_no_losses_or_external_clock",
    "setting_index_available_in_advance_even_when_two_reference_contexts_coincide",
    "supplied_labelled_neutral_current_quadratic_stock_and_transposition_reference",
    "all_setting_words_drivable_after_any_reachable_prefix",
)
Context = tuple[tuple[int, int, int], int]
Transitions = tuple[tuple[tuple[int, int], ...], ...]
Parents = dict[int, tuple[int, int] | None]
MAX_CURRENT = 10**6


def _seq(value: object, kind: type, lo: int, hi: int):
    if type(value) is not kind or not lo <= len(value) <= hi:
        raise ValueError(f"expected {kind.__name__} of length {lo}..{hi}")
    return value


@dataclass(frozen=True)
class DrivenEventSelector:
    id: str
    contexts: tuple[Context, ...]
    initial: int
    transitions: Transitions

    def __post_init__(self):
        candidate_id(self.id)
        for context in _seq(self.contexts, tuple, 1, 8):
            current, fixed = _seq(context, tuple, 2, 2)
            if sum(bounded_int(x, -MAX_CURRENT, MAX_CURRENT)
                   for x in _seq(current, tuple, 3, 3)) != 0:
                raise ValueError("current must be neutral")
            bounded_int(fixed, 0, 2)
        table = _seq(self.transitions, tuple, 1, 128)
        bounded_int(self.initial, 0, len(table)-1)
        for row in table:
            for edge in _seq(row, tuple, len(self.contexts), len(self.contexts)):
                dest, bit = _seq(edge, tuple, 2, 2)
                bounded_int(dest, 0, len(table)-1)
                bounded_int(bit, 0, 1)

    def specification(self):
        return {"id": self.id, "family": "driven_event_selector", "initial": self.initial,
                "contexts": [{"current": list(v), "fixed": i} for v, i in self.contexts],
                "transitions": [[list(edge) for edge in row] for row in self.transitions]}


def parse_driven_event_selector(value: object) -> DrivenEventSelector:
    raw = object_fields(value, {"id", "family", "contexts", "initial", "transitions"})
    if raw["family"] != "driven_event_selector":
        raise ValueError("expected driven_event_selector family")
    contexts = []
    for entry in _seq(raw["contexts"], list, 1, 8):
        ctx = object_fields(entry, {"current", "fixed"})
        contexts.append((tuple(_seq(ctx["current"], list, 3, 3)), ctx["fixed"]))
    k = len(contexts)
    table = tuple(tuple(tuple(_seq(edge, list, 2, 2)) for edge in _seq(row, list, k, k))
                  for row in _seq(raw["transitions"], list, 1, 128))
    return DrivenEventSelector(candidate_id(raw["id"]), tuple(contexts), raw["initial"], table)


def _reference(context: Context) -> Fraction | None:
    v, i = context
    norm = sum(x*x for x in v)
    return Fraction((v[(i+1) % 3] - v[(i+2) % 3])**2, 2*norm) if norm else None


def _parents(table, start, allow, guard) -> Parents:
    parents: Parents = {start: None}
    queue = deque([start])
    while queue:
        guard()
        s = queue.popleft()
        for c, (t, _) in enumerate(table[s]):
            if t not in parents and (allow is None or t in allow):
                parents[t] = (s, c)
                queue.append(t)
    return parents


def _word(parents: Parents, state: int) -> list[int]:
    rev = []
    while (step := parents[state]) is not None:
        state, c = step
        rev.append(c)
    return rev[::-1]


def _components(table, reachable, guard):
    """Kosaraju on the reachable subgraph, including non-bottom components."""
    reverse = {s: [] for s in reachable}
    for s in reachable:
        guard()
        for t, _ in table[s]:
            reverse[t].append(s)
    seen, finish = set(), []

    def visit(s):
        guard()
        seen.add(s)
        for t, _ in table[s]:
            if t not in seen:
                visit(t)
        finish.append(s)

    visit(next(iter(reachable)))  # reachability BFS starts with initial state
    components = []
    while finish:
        guard()
        root = finish.pop()
        if root not in seen:
            continue
        seen.remove(root)
        comp, todo = {root}, [root]
        while todo:
            s = todo.pop()
            for t in reverse[s]:
                if t in seen:
                    seen.remove(t)
                    comp.add(t)
                    todo.append(t)
        components.append(comp)
    return sorted(components, key=min)


class _Deadline(Exception):
    pass


def evaluate_driven_event_selector(candidate: DrivenEventSelector, limits: Limits, *,
                                   deadline: float | None = None
                                   ) -> tuple[tuple[Check, ...], dict[str, object]]:
    if deadline is not None and (type(deadline) not in (int, float) or not isfinite(deadline)):
        raise ValueError("deadline must be a finite absolute monotonic time")

    def guard():
        if deadline is not None and monotonic() >= deadline:
            raise _Deadline

    table = candidate.transitions
    refs = tuple(_reference(context) for context in candidate.contexts)
    k = len(refs)
    planned, checked = len(table)*k, 0
    details = {
        "rejection_scope": SCOPE, "scientific_status": "unassessed",
        "empirical_status": "not_tested", "proof_status": "not_attempted",
        "reference_minus_rates": [str(p) if p is not None else None for p in refs],
        "all_eventually_periodic_context_rates_certified": False,
        "planned_is_exact": False, "potential_certificate": None,
        "budget_semantics": "one_reachable_internal_edge_all_context_coordinates;"
                            "bounded_graph_setup_and_witness_replay_not_cases",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }

    def result(status, reason, witness=None):
        details["stop_reason"] = reason
        return (Check(CHECK_ID, status, checked, planned, "=0", ASSUMPTIONS, witness),), details

    if None in refs:
        planned = 0
        details["planned_is_exact"] = True
        return result("unsupported", "unsupported_zero_current")
    rates = tuple((p.numerator, p.denominator) for p in refs)

    def advance(values, c, bit):
        a, q = rates[c]
        return values[:c] + (values[c] + q*bit-a,) + values[c+1:]

    try:
        reachable = _parents(table, candidate.initial, None, guard)
        components = _components(table, reachable, guard)
        planned = sum(t in comp for comp in components for s in comp for t, _ in table[s])
        details.update(planned_is_exact=True, reachable_states=len(reachable),
                       reachable_components=len(components))
        certificate = []
        for comp in components:
            base = min(comp)
            parents = _parents(table, base, comp, guard)
            values = {base: (0,)*k}
            for t, step in parents.items():  # BFS parent precedes its child
                if step is not None:
                    s, c = step
                    values[t] = advance(values[s], c, table[s][c][1])
            for s in sorted(comp):
                guard()
                for c, (t, bit) in enumerate(table[s]):
                    if t not in comp:
                        continue
                    guard()
                    if checked >= limits.max_cases:
                        return result("inconclusive", "max_cases")
                    checked += 1
                    if advance(values[s], c, bit) == values[t]:
                        continue
                    # Competing paths to t disagree, hence after the SAME
                    # return path to base at least one closed walk is biased.
                    suffix = _word(_parents(table, t, comp, guard), base)
                    for path in (_word(parents, s) + [c], _word(parents, t)):
                        loop = path + suffix
                        counts, minus, end = [0]*k, [0]*k, base
                        for knob in loop:
                            guard()
                            end, y = table[end][knob]
                            counts[knob] += 1
                            minus[knob] += y
                        if end != base:
                            raise RuntimeError("invalid return path")
                        for j, (a, q) in enumerate(rates):
                            residual = q*minus[j] - a*counts[j]
                            if residual:
                                w = {"initial_state": candidate.initial, "prefix": _word(reachable, base),
                                     "loop_state": base, "loop": loop, "final_state": end,
                                     "context_index": j, "context_counts": counts, "minus_counts": minus,
                                     "target_minus_rate": str(refs[j]),
                                     "actual_minus_rate": str(Fraction(minus[j], counts[j])),
                                     "integer_residual": residual}
                                guard()
                                return result("counterexample", "first_counterexample",
                                              {"inputs": w, "actual": str(residual), "required": "=0"})
                    raise RuntimeError("inconsistent potentials without a closed witness")
            certificate.append({"base": base, "state_potentials":
                                [[s, list(values[s])] for s in sorted(comp)]})
        guard()
        details.update(all_eventually_periodic_context_rates_certified=True,
                       potential_certificate=certificate)
        return result("no_counterexample_within_bounds", "complete")
    except _Deadline:
        return result("inconclusive", "deadline")
