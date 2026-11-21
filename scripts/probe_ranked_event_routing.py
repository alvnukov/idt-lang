"""Exact, lazy addressing of the finite tagged-pair cancellation router.

The supplied count vector encodes a normalized cloud in rail-major order;
within a rail its live IDs are 0..abs(q[i])-1. Counts do not encode an
arbitrary interleaving of different parent rails. No event probabilities are
consulted, and neither children nor the ordered pairs of children are listed.
Gate copy-pairs are row intervals: even h diagonal seeds need no h-entry list.

For m rows and d columns, Gram validation costs O(m d^2) integer operations.
Row intervals take O(m d) storage; a column-pair index takes O(m) time/space
on its first use and is cached (at most d^2 such indexes). A traversed edge
uses O(log(1+m)+log(1+d)) rank/select work on a warm cache. These are
operation counts, not bit-complexity bounds: very large ranks require
correspondingly many bits. The mean edge bound below is not a time limit.

Let N = sum_o (sum_i |A[o,i] q[i]|)^2 be the raw pair universe and
E = h sum_i q[i]^2 the ticket count. R and C are involutions on that finite
universe; their nontrivial edges reverse sign, and their fixed points are
positive. Each C-fixed ticket starts an alternating path (possibly isolated),
not a cycle. Its other end is R-fixed: after an R step the sign is negative,
so C cannot fix that point. Distinct starts occupy disjoint paths. Thus
total traversed edges over all E tickets <= N-E (cycles are unused). Under a
uniform ticket, mean edges <= N/E-1 <= s-1 for E>0, where s is the maximum
number of occupied, nonzero parent rails feeding a row (Cauchy-Schwarz,
then A^t A=hI). This is not a worst-case constant. A user-supplied edge
budget raises an exception on exhaustion; it is not an emission filter.
"""

from __future__ import annotations

import sys
from bisect import bisect_right
from collections.abc import Sequence
from itertools import product
from pathlib import Path
from typing import NamedTuple

Event = tuple[int, int, int]  # rail, left local ID, right local ID; IDs may coincide
Matrix = tuple[tuple[int, ...], ...]


class EdgeBudgetExceeded(RuntimeError):
    """No result was returned; retry the same ticket with a higher limit."""


class _Pool(NamedTuple):
    ends: tuple[int, ...]
    indices: tuple[int, ...]

    def select(self, k: int) -> tuple[int, int]:
        j = bisect_right(self.ends, k)
        return self.indices[j], k - (self.ends[j - 1] if j else 0)

    @property
    def size(self) -> int:
        return self.ends[-1] if self.ends else 0


class _Layout:
    """Concatenated positive/negative runs, in reference enumeration order."""

    def __init__(self, weights: Sequence[int]) -> None:
        starts: list[int] = []
        ends: tuple[list[int], list[int]] = ([], [])
        indices: tuple[list[int], list[int]] = ([], [])
        totals = [0, 0]
        for i, w in enumerate(weights):
            sign = int(w < 0)
            starts.append(totals[sign])
            if w:
                totals[sign] += abs(w)
                ends[sign].append(totals[sign])
                indices[sign].append(i)
        self.starts = tuple(starts)
        self.pool = tuple(_Pool(tuple(e), tuple(ix)) for e, ix in zip(ends, indices))


class _Child(NamedTuple):
    rail: int  # parent input rail
    rank: int  # parent ID local to that rail
    copy: int


class _Point(NamedTuple):
    out: int
    left: _Child
    right: _Child


class RankedGate:
    """One fixed integer gate acting on one fixed canonical signed cloud."""

    def __init__(
        self, q: Sequence[int], gate: Sequence[Sequence[int]], reverse_matching: bool
    ) -> None:
        self.q = tuple(q)
        self.gate: Matrix = tuple(tuple(row) for row in gate)
        if (
            not self.q
            or not self.gate
            or any(len(row) != len(self.q) for row in self.gate)
        ):
            raise ValueError("nonempty rectangular gate must have len(q) columns")
        if any(type(v) is not int for v in self.q) or any(
            type(v) is not int for row in self.gate for v in row
        ):
            raise ValueError("counts and gate coefficients must be integers")
        self.gain = sum(row[0] ** 2 for row in self.gate)
        if self.gain == 0 or any(
            sum(row[i] * row[j] for row in self.gate) != (self.gain if i == j else 0)
            for i in range(len(self.q))
            for j in range(i + 1)
        ):
            raise ValueError("gate must satisfy A^t A=hI with h>0")
        self.reverse_matching = reverse_matching
        self._rows = tuple(
            _Layout(tuple(a * v for a, v in zip(row, self.q))) for row in self.gate
        )
        self.q_out = tuple(row.pool[0].size - row.pool[1].size for row in self._rows)
        self.raw_children = sum(sum(p.size for p in row.pool) for row in self._rows)
        self.raw_pairs = sum(sum(p.size for p in row.pool) ** 2 for row in self._rows)
        self.tickets = self.gain * sum(v * v for v in self.q)
        self._columns: dict[tuple[int, int], _Layout] = {}

    def _column(self, i: int, j: int) -> _Layout:
        key = i, j
        if key not in self._columns:
            # Parent signs may swap these two pools. Both ordinary zip and
            # reverse-rank zip define the same involution when pools swap.
            self._columns[key] = _Layout(tuple(row[i] * row[j] for row in self.gate))
        return self._columns[key]

    def _from_column(self, i: int, u: int, j: int, v: int, sign: int, k: int) -> _Point:
        o, local = self._column(i, j).pool[sign].select(k)
        a, b = divmod(local, abs(self.gate[o][j]))
        return _Point(o, _Child(i, u, a), _Child(j, v, b))

    def _column_rank(self, p: _Point) -> int:
        o, (i, _, a), (j, _, b) = p
        return self._column(i, j).starts[o] + a * abs(self.gate[o][j]) + b

    def _c(self, p: _Point) -> _Point:
        o, (i, u, _), (j, v, _) = p
        if i == j:
            return p
        other_sign = int(self.gate[o][i] * self.gate[o][j] > 0)
        k = self._column_rank(p)
        if self.reverse_matching:
            k = self._column(i, j).pool[other_sign].size - 1 - k
        return self._from_column(i, u, j, v, other_sign, k)

    def _from_row(self, o: int, sign: int, k: int) -> _Child:
        i, local = self._rows[o].pool[sign].select(k)
        rank, copy = divmod(local, abs(self.gate[o][i]))
        return _Child(i, rank, copy)

    def _row_rank(self, o: int, child: _Child) -> int:
        i, rank, copy = child
        return self._rows[o].starts[i] + rank * abs(self.gate[o][i]) + copy

    def _partner(self, o: int, child: _Child) -> _Child | None:
        sign = int(self.gate[o][child.rail] * self.q[child.rail] < 0)
        pools = self._rows[o].pool
        k = self._row_rank(o, child)
        if self.reverse_matching and sign:
            k = pools[sign].size - 1 - k
        other = 1 - sign
        if k >= pools[other].size:
            return None
        if self.reverse_matching and other:
            k = pools[other].size - 1 - k
        return self._from_row(o, other, k)

    def _r(self, p: _Point) -> _Point:
        o, a, b = p
        partner = self._partner(o, a)
        if partner is not None:
            return _Point(o, partner, b)
        partner = self._partner(o, b)
        return p if partner is None else _Point(o, a, partner)

    def _survivor_offset(self, o: int) -> int:
        negative = self.q_out[o] < 0
        if negative and self.reverse_matching:
            return 0
        return self._rows[o].pool[int(not negative)].size

    @staticmethod
    def _validate(event: Event, q: tuple[int, ...], max_edges: int | None) -> None:
        i, u, v = event
        if (
            any(type(k) is not int for k in event)
            or not 0 <= i < len(q)
            or not 0 <= u < abs(q[i])
            or not 0 <= v < abs(q[i])
        ):
            raise ValueError("event outside normalized signed cloud")
        if max_edges is not None and (type(max_edges) is not int or max_edges < 0):
            raise ValueError("edge budget must be a nonnegative integer")

    def _walk(self, p: _Point, reverse: bool, limit: int | None) -> tuple[_Point, int]:
        first, second = (self._c, self._r) if reverse else (self._r, self._c)
        edges = 0
        while True:
            n = first(p)
            if n == p:
                return p, edges
            if limit is not None and edges + 2 > limit:
                raise EdgeBudgetExceeded(f"next alternating step exceeds {limit} edges")
            p = second(n)
            edges += 2
            if p == n or edges > self.raw_pairs - self.tickets:
                raise RuntimeError("finite alternating-path invariant violated")

    def route_with_cost(
        self, event: Event, seed: int, *, max_edges: int | None = None
    ) -> tuple[Event, int]:
        self._validate(event, self.q, max_edges)
        if type(seed) is not int or not 0 <= seed < self.gain:
            raise ValueError("seed outside 0..gain-1")
        i, u, v = event
        start = self._from_column(i, u, i, v, 0, seed)
        (o, a, b), edges = self._walk(start, False, max_edges)
        offset = self._survivor_offset(o)
        return (o, self._row_rank(o, a) - offset, self._row_rank(o, b) - offset), edges

    def route(self, event: Event, seed: int, *, max_edges: int | None = None) -> Event:
        return self.route_with_cost(event, seed, max_edges=max_edges)[0]

    def unroute(
        self, output_event: Event, *, max_edges: int | None = None
    ) -> tuple[Event, int]:
        self._validate(output_event, self.q_out, max_edges)
        o, u, v = output_event
        offset, sign = self._survivor_offset(o), int(self.q_out[o] < 0)
        end = _Point(
            o, self._from_row(o, sign, offset + u), self._from_row(o, sign, offset + v)
        )
        p, _ = self._walk(end, True, max_edges)
        return (p.left.rail, p.left.rank, p.right.rank), self._column_rank(p)


def ranked_gate(
    q: Sequence[int], gate: Sequence[Sequence[int]], reverse_matching: bool = False
) -> RankedGate:
    return RankedGate(q, gate, reverse_matching)


def route(
    block: RankedGate, event: Event, seed: int, *, max_edges: int | None = None
) -> Event:
    return block.route(event, seed, max_edges=max_edges)


def _need(condition: bool, reason: str) -> None:
    if not condition:
        raise AssertionError(reason)


def main() -> None:
    # The expanded reference is a check only, never a dependency of routing.
    if not __package__:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from scripts.probe_cancellation_event_router import H, route_block

    phase: Matrix = ((2, -1, 0, 0), (1, 2, 0, 0), (0, 0, 1, 2), (0, 0, -2, 1))
    cases = tickets = longest = 0
    budget_checked = False
    for gate, q, rev in product(
        (H, phase), product(range(-2, 3), repeat=4), (False, True)
    ):
        block = ranked_gate(q, gate, rev)
        cloud = tuple(
            (i, 1 if x > 0 else -1) for i, x in enumerate(q) for _ in range(abs(x))
        )
        in_ids = tuple((i, u) for i, x in enumerate(q) for u in range(abs(x)))
        out, routes, gain, expected_max = route_block(cloud, gate, rev)
        oracle = tuple(sum(a * b for a, b in zip(row, q)) for row in gate)
        _need(
            block.q_out == oracle and block.gain == gain,
            "incorrect count balance or gain",
        )
        out_ids = tuple((o, u) for o, x in enumerate(oracle) for u in range(abs(x)))
        _need(
            tuple((o, 1 if oracle[o] > 0 else -1) for o, _ in out_ids) == out,
            "output cloud order",
        )
        edge_sum = max_seen = 0
        for ((a, b), seed), (x, y) in routes.items():
            i, u = in_ids[a]
            event = i, u, in_ids[b][1]
            o, v = out_ids[x]
            expected = o, v, out_ids[y][1]
            actual, cost = block.route_with_cost(event, seed)
            _need(
                actual == expected and block.unroute(actual) == (event, seed),
                "ticket/inverse mismatch",
            )
            edge_sum += cost
            max_seen = max(max_seen, cost)
            if cost and not budget_checked:
                try:
                    block.route(event, seed, max_edges=cost - 1)
                except EdgeBudgetExceeded:
                    _need(
                        block.route(event, seed, max_edges=cost) == expected,
                        "budget boundary",
                    )
                    budget_checked = True
                else:
                    raise AssertionError("edge budget silently ignored")
        support = max(sum(bool(a * x) for a, x in zip(row, q)) for row in gate)
        _need(
            max_seen == expected_max and len(routes) == block.tickets,
            "edge or ticket count",
        )
        _need(
            edge_sum <= block.raw_pairs - block.tickets
            and block.raw_pairs <= support * block.tickets,
            "uniform cost bound",
        )
        cases += 1
        tickets += len(routes)
        longest = max(longest, max_seen)
    _need(budget_checked, "no positive length path tested")
    print(
        f"{cases} canonical signed clouds/gates/matchings; {tickets} individual tickets match the enumerator and invert, longest {longest} edges."
    )
    scale = 10**20
    large = ranked_gate((scale,) * 4, H)
    for seed in range(large.gain):
        # Endpoints and distinct ranks are fixed before routing, not sampled.
        for event in (
            (0, 0, scale - 1),
            (2, scale // 2, scale // 3),
            (3, scale - 1, scale - 1),
        ):
            output = large.route(event, seed, max_edges=128)
            _need(
                large.unroute(output, max_edges=128) == (event, seed),
                "large deterministic inverse",
            )
    print(
        f"q=(10^20,)*4: 12 preselected tickets inverted. {large.raw_children} raw children, {large.raw_pairs} raw ordered pairs, neither expanded."
    )


if __name__ == "__main__":
    main()
