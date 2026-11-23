"""Exact finite feasibility of submitted operational probability requirements.

Each setting declares a complete, mutually exclusive row (including loss or
other outcomes where needed). Each event is a union of outcomes within ONE
row. Equalities up to tolerance across settings are supplied assumptions,
never inferred from outcome names or wave identity. Conditional rows with
different acceptance denominators cannot support an unconditional transfer.
No joint hidden distribution, Hilbert model, sampling inference or
experimental validation is constructed here.

Rows of Ax<=b, x>=0, in canonical order: normalization (+,-) per setting,
upper then negated lower per bound, left-minus-right then reverse per link.
Columns follow settings then outcomes in lexical order. The feasibility-only
dual simplex starts with objective zero, basic slacks and a possibly negative
RHS. Bland's rule on the dual chooses the least-index negative basic, then the
least-index eligible entering variable (all reduced costs are zero). Either
an exact primal vector or a nonnegative Farkas combination is checked against
the original inequalities before a verdict. A stopped search decides nothing.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from fractions import Fraction
from math import isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    candidate_id,
    exact_fraction,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "operational_probability_ledger_exact_feasibility"
SCOPE = "only_submitted_exhaustive_operational_rows_interval_bounds_and_declared_event_links"
ASSUMPTIONS = ("mutually_exclusive_exhaustive_outcomes_in_each_submitted_setting",
               "submitted_bounds_and_event_links_are_assumptions_not_inferred_identities",
               "all_attempts_including_losses_or_explicit_separate_conditioning")
MAX_RELATIONS = 96
MAX_BITS = 256
MAX_UPDATES = 250_000
Event = tuple[str, tuple[str, ...]]
Setting = tuple[str, tuple[str, ...]]
Bound = tuple[Event, Fraction, Fraction]
Link = tuple[Event, Event, Fraction]


def _seq(x, kind, low, high):
    if type(x) is not kind or not low <= len(x) <= high:
        raise ValueError(f"expected {kind.__name__} of length {low}..{high}")
    return x


def _fields(x, *names):
    if type(x) is not dict or len(x) != len(names) or set(x) != set(names):
        raise ValueError(f"expected exactly {names}")
    return x


def _name(x):
    if type(x) is not str:
        raise ValueError("expected a plain identifier")
    return candidate_id(x)


def _fraction(x):
    if type(x) is not str or len(x) > 25:
        raise ValueError("expected bounded probability string")
    v = exact_fraction(x)
    if not 0 <= v <= 1:
        raise ValueError("probability or tolerance outside [0,1]")
    return v


def _check_fraction(v):
    if type(v) is not Fraction or not 0 <= v <= 1 or max(v.numerator, v.denominator) >= 10**12:
        raise ValueError("expected bounded exact probability")


def _sorted_unique(seq):
    if tuple(sorted(set(seq))) != seq:
        raise ValueError("expected unique entries in canonical order")


def _event_wire(e):
    return {"setting": e[0], "outcomes": list(e[1])}


@dataclass(frozen=True)
class OperationalProbabilityLedger:
    id: str
    basis: str
    settings: tuple[Setting, ...]
    bounds: tuple[Bound, ...]
    links: tuple[Link, ...]

    def __post_init__(self):
        _name(self.id)
        if type(self.basis) is not str or self.basis not in ("all_attempts", "separately_postselected"):
            raise ValueError("unrecognized basis")
        universe = {}
        for row in _seq(self.settings, tuple, 1, 16):
            key, outcomes = _seq(row, tuple, 2, 2)
            _name(key)
            for name in _seq(outcomes, tuple, 1, 8):
                _name(name)
            _sorted_unique(outcomes)
            if key in universe:
                raise ValueError("duplicate setting")
            universe[key] = outcomes
        _sorted_unique(tuple(universe))
        if sum(map(len, universe.values())) > 64:
            raise ValueError("too many outcomes")

        def event(e):
            key, names = _seq(e, tuple, 2, 2)
            _name(key)
            for v in _seq(names, tuple, 1, 8):
                _name(v)
            _sorted_unique(names)
            if key not in universe or not set(names) <= set(universe[key]):
                raise ValueError("event references undeclared setting or outcome")

        _seq(self.bounds, tuple, 0, MAX_RELATIONS)
        _seq(self.links, tuple, 0, MAX_RELATIONS)
        if len(self.bounds) + len(self.links) > MAX_RELATIONS:
            raise ValueError("too many bounds plus links")
        for row in self.bounds:
            e, lo, hi = _seq(row, tuple, 3, 3)
            event(e)
            _check_fraction(lo)
            _check_fraction(hi)
            if lo > hi:
                raise ValueError("reversed probability interval")
        for row in self.links:
            a, b, eps = _seq(row, tuple, 3, 3)
            event(a)
            event(b)
            _check_fraction(eps)
            if b < a:
                raise ValueError("link not in canonical orientation")
        _sorted_unique(self.bounds)
        _sorted_unique(self.links)

    def specification(self):
        return {"id": self.id, "family": "operational_probability_ledger", "basis": self.basis,
                "settings": [{"id": s, "outcomes": list(o)} for s, o in self.settings],
                "bounds": [{"event": _event_wire(e), "lower": str(lo), "upper": str(hi)} for e, lo, hi in self.bounds],
                "links": [{"left": _event_wire(a), "right": _event_wire(b), "tolerance": str(eps)}
                          for a, b, eps in self.links]}


def parse_operational_probability_ledger(value: object) -> OperationalProbabilityLedger:
    x = _fields(value, "id", "family", "basis", "settings", "bounds", "links")
    if type(x["family"]) is not str or x["family"] != "operational_probability_ledger":
        raise ValueError("unexpected family")
    settings, bounds, links = [], [], []

    def names(xs):
        return tuple(sorted(_name(v) for v in _seq(xs, list, 1, 8)))

    def event(e):
        _fields(e, "setting", "outcomes")
        return _name(e["setting"]), names(e["outcomes"])

    for row in _seq(x["settings"], list, 1, 16):
        _fields(row, "id", "outcomes")
        settings.append((_name(row["id"]), names(row["outcomes"])))
    for row in _seq(x["bounds"], list, 0, MAX_RELATIONS):
        _fields(row, "event", "lower", "upper")
        bounds.append((event(row["event"]), _fraction(row["lower"]), _fraction(row["upper"])))
    for row in _seq(x["links"], list, 0, MAX_RELATIONS):
        _fields(row, "left", "right", "tolerance")
        a, b = sorted((event(row["left"]), event(row["right"])))
        links.append((a, b, _fraction(row["tolerance"])))
    return OperationalProbabilityLedger(x["id"], x["basis"], tuple(sorted(settings)), tuple(sorted(bounds)),
                                        tuple(sorted(links)))


def _system(c):
    cols = {(s, o): j for j, (s, o) in enumerate((s, o) for s, names in c.settings for o in names)}
    rows = []

    def interval(terms, lo, hi):
        rows.append((terms, hi))
        rows.append(({j: -a for j, a in terms.items()}, -lo))

    def vec(e):
        return {cols[e[0], o]: 1 for o in e[1]}

    for e in c.settings:
        interval(vec(e), 1, 1)
    for e, lo, hi in c.bounds:
        interval(vec(e), lo, hi)
    for left, right, eps in c.links:
        v = vec(left)
        for j in vec(right):
            if j in v:
                del v[j]
            else:
                v[j] = -1
        interval(v, -eps, eps)
    return len(cols), rows


def _conditioned_transfer(c):
    return c.basis == "separately_postselected" and any(a[0] != b[0] for a, b, _ in c.links)


def _small(x):
    return x.numerator.bit_length() <= MAX_BITS and x.denominator.bit_length() <= MAX_BITS


def verify_ledger_certificate(candidate: OperationalProbabilityLedger, certificate: object) -> bool:
    """Rebuild the original constraints, never trust solver tableaux or cached verdicts."""
    if type(candidate) is not OperationalProbabilityLedger or _conditioned_transfer(candidate):
        return False
    n, rows = _system(candidate)
    if type(certificate) is not dict or len(certificate) != 2 or type(certificate.get("kind")) is not str:
        return False
    kind = certificate["kind"]
    if kind not in ("primal", "farkas"):
        return False
    key, size = ("values", n) if kind == "primal" else ("weights", len(rows))
    raw = certificate.get(key)
    if type(raw) is not list or len(raw) != size:
        return False
    values = []
    for s in raw:
        if type(s) is not str or len(s) > 157 or not re.fullmatch(r"[0-9]{1,78}(/[1-9][0-9]{0,77})?", s):
            return False
        v = Fraction(s)
        if not _small(v) or str(v) != s:
            return False
        values.append(v)
    if kind == "primal":
        return all(sum(a*values[j] for j, a in terms.items()) <= b for terms, b in rows)
    # lambda >= 0 follows from the wire grammar. Ax<=b and x>=0 require
    # lambda.b>=0 whenever lambda.A>=0, so strict negativity contradicts feasibility.
    lhs = [Fraction(0)] * n
    rhs = Fraction(0)
    for w, (terms, b) in zip(values, rows, strict=True):
        rhs += w*b
        for j, a in terms.items():
            lhs[j] += w*a
    return min(lhs) >= 0 and rhs < 0


def evaluate_operational_probability_ledger(
    candidate: OperationalProbabilityLedger, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    if type(candidate) is not OperationalProbabilityLedger or type(limits) is not Limits:
        raise TypeError("expected exact OperationalProbabilityLedger and Limits")
    if deadline is not None and (type(deadline) not in (int, float) or
                                 (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be finite absolute monotonic time")
    n, original = _system(candidate)
    m = len(original)
    pivots = updates = 0

    def expired():
        return deadline is not None and monotonic() >= deadline

    def finish(status, reason, cert=None, contradiction=None):
        details = {"rejection_scope": SCOPE, "finite_submitted_contract_only": True,
                   "scientific_status": "unassessed", "proof_status": "not_attempted",
                   "empirical_status": "not_tested", "basis": candidate.basis, "variables": n, "inequalities": m,
                   "stop_reason": reason, "checked_certificate": cert, "completed_pivots": pivots,
                   "coefficient_updates_charged": updates, "max_coefficient_updates": MAX_UPDATES,
                   "max_rational_bits": MAX_BITS, "max_pivots": limits.max_cases,
                   "budget_semantics": "max_cases_counts_complete_simplex_pivots",
                   "check_units": ["independently_verified_feasibility_decision"],
                   "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"]}
        witness = None if contradiction is None else {"inputs": {"certificate": cert},
                                                     "actual": str(contradiction), "required": ">=0"}
        return (Check(CHECK_ID, status, int(cert is not None), 1, ">=0", ASSUMPTIONS, witness),), details

    if _conditioned_transfer(candidate):
        return finish("unsupported", "cross_setting_transfer_across_separately_postselected_rows")
    # Dictionary equalities in full column form: slack columns always retain
    # the exact row multipliers against the original inequality system.
    tab = [{**terms, n+i: 1} for i, (terms, _) in enumerate(original)]
    rhs = [Fraction(b) for _, b in original]
    basic = list(range(n, n+m))
    while not expired():
        bad = min((i for i in range(m) if rhs[i] < 0), key=basic.__getitem__, default=None)
        if bad is None:
            x = [Fraction(0)] * n
            for i, j in enumerate(basic):
                if j < n:
                    x[j] = rhs[i]
            cert = {"kind": "primal", "values": list(map(str, x))}
            status, reason, contradiction = "no_counterexample_within_bounds", "verified_feasible_assignment", None
        else:
            enter = min((j for j, a in tab[bad].items() if a < 0), default=None)
            if enter is None:
                cert = {"kind": "farkas", "weights": [str(tab[bad].get(n+i, 0)) for i in range(m)]}
                status, reason, contradiction = "counterexample", "verified_farkas_contradiction", rhs[bad]
            else:
                if pivots >= limits.max_cases:
                    return finish("inconclusive", "max_cases")
                inv = Fraction(1, 1) / tab[bad][enter]
                row = {k: inv*v for k, v in tab[bad].items()}
                b = rhs[bad]*inv
                if not _small(b) or not all(map(_small, row.values())):
                    return finish("inconclusive", "rational_size_limit")
                cost = (len(row)+1) * (1 + sum(i != bad and enter in t for i, t in enumerate(tab)))
                if updates + cost > MAX_UPDATES:
                    return finish("inconclusive", "coefficient_work_limit")
                updates += cost
                for i, t in enumerate(tab):
                    if expired():
                        return finish("inconclusive", "deadline")
                    factor = t.get(enter)
                    if i == bad or not factor:
                        continue
                    rhs[i] -= b*factor
                    if not _small(rhs[i]):
                        return finish("inconclusive", "rational_size_limit")
                    for j, a in row.items():
                        v = t.get(j, 0) - a*factor
                        if not _small(v):
                            return finish("inconclusive", "rational_size_limit")
                        if v:
                            t[j] = v
                        else:
                            t.pop(j, None)
                tab[bad], rhs[bad], basic[bad] = row, b, enter
                pivots += 1
                continue
        if not verify_ledger_certificate(candidate, cert):
            raise ArithmeticError("solver produced an invalid exact certificate")
        if not expired():
            return finish(status, reason, cert, contradiction)
        break
    return finish("inconclusive", "deadline")
