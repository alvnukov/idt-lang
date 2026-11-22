"""A single finite port machine for short spatial echoes AND an active six-pulse row.

Assumptions: four labeled reciprocal ports; abc=cba everywhere on COMPLETE
states. Put r_i=T_i T_0. Then r_i r_j=r_j r_i, and T_0 r_i T_0=r_i^-1.
Even words are commuting translations; odd words are involutions. In
particular two native words of order six MUST commute. Agreement merely
on positions is weaker, as demonstrated by the link-bit lift below.

Conditional size bound: on a finite A3/L endpoint quotient with four
globally permutable ports and two distinct roles, let m be the common
order of e_i-e_j. They generate A3/L, hence its exponent is exactly m.
Actual order six needs 6|m (fitting six observations does not). For v in L,
v-(ij)v=(v_i-v_j)(e_i-e_j) is in L, so v_i=v_j modulo m. Thus L/mA3
lies in the diagonal, of size gcd(4,m), inside the m^3-element A3/mA3.
At m=6 the bound is 108 per role; m>=12 already gives >=12^3/4.
The two-element diagonal at six attains the bound. This quotient is a
specified identification, NOT a new local interaction selected by IDT.

On the old four-cycle shuttle, every native permutation has order dividing
four. A time-homogeneous stochastic mixture of those permutation matrices
cannot have a primitive sixth-root peripheral eigenvalue: if Kv=zv, |z|=1,
the average of equal-norm P_g v has that same norm, hence every positively
weighted P_g v=zv. None admits z. Thus no exact, indefinitely persistent
sixth harmonic of a fixed linear readout, not a bound from six samples,
nor a ban on time-dependent control, extra memory or a different machine.

One mixed-pulse test separates machines matching BOTH single-axis rows:
the plain relay returns probability 1, an explicit reciprocal link-bit
lift 3/4, and separately supplied orthogonal 60-degree rotations 29/32.
The lift detects phase plus a carried polarity; its mark pattern, preferred
ports and analyzer are additional structure. With four equiprobable histories
and a deterministic readout, every probability is a multiple of 1/4 anyway.
The reference response cannot exclude other source or detection mechanisms.

The six-cycle actuator, specific words, fair preparation choices and
two-cell relative-symbol analyzer are inputs; no native local comparator,
spatial axes, Hilbert amplitudes, Born law, or experimental result follows.
All counts below are finite computations. The general arguments are not
machine-checked theorems.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations, product
from math import gcd, lcm
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_shuttle_local_reunions import (
    PORTS,
    TRIPLES,
    Ports,
    Word,
    components,
    exact_ball,
    need,
    ring,
    tables,
    walk,
)

A = (0, 1)
B = (2, 1)
B_DISJOINT = (2, 3)
BRIGHT = frozenset((5, 0, 1))
ROW = (4, 3, 1, 0, 1, 3)  # numerators for four equiprobable histories


@dataclass(frozen=True)
class Model:
    ports: Ports
    q: int
    reps: tuple[int, ...]  # full configuration representatives, 0 is the origin

    def role(self, s: int) -> int:
        return self.reps[s] // self.q**4

    def symbol(self, s: int, p: int) -> int:
        return self.reps[s] // (1, self.q, self.q**2, self.q**3)[p] % self.q

    def phase(self, s: int) -> int:
        return (self.symbol(s, 0) - self.symbol(s, 2)) % self.q


def model(q: int, identify: bool) -> Model:
    raw = tables(q, ring(q))
    orbit = next(part for part in components(raw) if 0 in part)
    need(len(orbit) == 2 * q**3, "wrong full-state shuttle orbit")

    def mate(s: int) -> int:
        if not identify:
            return s
        need(q == 6, "only the six-symbol diagonal identification is requested")
        return s // q**4 * q**4 + sum(
            ((s // stride + 3) % q) * stride for stride in (1, q, q**2, q**3)
        )

    need(all(mate(s) in orbit and mate(mate(s)) == s for s in orbit), "bad equivalence")
    need(
        all(raw[p][mate(s)] == mate(raw[p][s]) for p in PORTS for s in orbit),
        "port transition not well-defined on quotient",
    )
    reps = tuple(sorted({min(s, mate(s)) for s in orbit}))
    idx = {s: i for i, s in enumerate(reps)}
    ports = tuple(tuple(idx[min(t[s], mate(t[s]))] for s in reps) for t in raw)
    need(
        reps[0] == 0 and all(t[t[s]] == s for t in ports for s in range(len(reps))),
        "bad registered origin or reciprocal step",
    )
    return Model(ports, q, reps)


def action(ports: Ports, w: Word) -> tuple[int, ...]:
    return tuple(walk(ports, s, w) for s in range(len(ports[0])))


def order(perm: tuple[int, ...]) -> int:
    todo = set(range(len(perm)))
    result = 1
    while todo:
        s = next(iter(todo))
        length = 0
        while s in todo:
            todo.remove(s)
            length += 1
            s = perm[s]
        result = lcm(result, length)
    return result


def word_group(m: Model) -> dict[int, int]:
    identity = tuple(range(len(m.reps)))
    seen, todo = {identity}, [identity]
    while todo:
        g = todo.pop()
        for t in m.ports:
            h = tuple(t[x] for x in g)
            if h not in seen:
                seen.add(h)
                todo.append(h)
    return dict(sorted(Counter(order(g) for g in seen).items()))


def compass(m: Model) -> None:
    n, q = len(m.reps), m.q
    idx = {s: i for i, s in enumerate(m.reps)}
    for perm in permutations(PORTS):
        relabel = []
        for s in range(n):
            h = m.role(s) * q**4
            vals = [m.symbol(s, p) for p in PORTS]
            direct = h + sum(vals[p] * q ** perm[p] for p in PORTS)
            shifted = h + sum(((vals[p] + 3) % q) * q ** perm[p] for p in PORTS)
            relabel.append(idx[min(direct, shifted)])
        need(
            len(set(relabel)) == n
            and all(
                relabel[t[s]] == m.ports[perm[p]][relabel[s]]
                for p, t in enumerate(m.ports)
                for s in range(n)
            ),
            "lost full port symmetry",
        )


def size_controls() -> None:
    need(6**3 // gcd(4, 6) == 108 and 12**3 // 4 > 108, "bound arithmetic")
    # The minimum l1 norm of a nonzero kernel vector is 12. Diagonal
    # residues are all 0 or all 3; checking a ball of radius 12 includes an
    # attained minimizer and all possible shorter candidates.
    shortest = 13
    for a, b, c in product(range(-12, 13), repeat=3):
        v = (a, b, c, -a - b - c)
        length = sum(map(abs, v))
        if 0 < length <= 12 and {x % 6 for x in v} in ({0}, {3}):
            shortest = min(shortest, length)
    need(shortest == 12, "a short diagonal relation was missed")


def commutator(second: Word) -> Word:
    return A + second + A[::-1] + second[::-1]


def prepared(m: Model) -> tuple[int, ...]:
    return tuple(
        walk(m.ports, 0, A[::-1] + A * (a + b)) for a, b in product(range(2), repeat=2)
    )


def fringe(m: Model) -> tuple[int, ...]:
    prep = prepared(m)
    need(tuple(m.phase(s) for s in prep) == (5, 0, 0, 1), "two fair choices")
    row = tuple(
        sum(m.phase(walk(m.ports, s, A * n)) in BRIGHT for s in prep) for n in range(6)
    )
    need(row == ROW, "shared relay did not reproduce the active phase row")
    need(
        tuple(
            sum(m.phase(walk(m.ports, s, B * n)) in BRIGHT for s in prep)
            for n in range(6)
        )
        == ROW,
        "shared relay failed the independent second-axis calibration",
    )
    # p(0)=1 for an actual single-site marker forces a source concentrated
    # at that site. A deterministic fixed-word pulse then reads only 0 or 1.
    literal = tuple(sum(walk(m.ports, 0, A * n) == 0 for _ in prep) for n in range(6))
    need(literal == (4, 0, 0, 0, 0, 0), "one marked site mistaken for a phase analyzer")
    return row


def coordinate_control(m: Model) -> None:
    # An absolute-cell response on a quotient must be invariant under common
    # +3; every such one-cell Boolean function has period <=3 along A.
    masks = [
        d
        for d in range(64)
        if all(((d >> i) ^ (d >> ((i + 3) % 6))) & 1 == 0 for i in range(6))
    ]
    need(len(masks) == 8, "wrong one-cell invariant functions")
    need(
        all(
            ((d >> m.symbol(s, p)) ^ (d >> m.symbol(walk(m.ports, s, A * 3), p))) & 1
            == 0
            for d in masks
            for s in range(len(m.reps))
            for p in PORTS
        ),
        "absolute-symbol detector separated antipodal phases",
    )


def link_lift(m: Model, two_axes: bool) -> Ports:
    # No schedule or global path label: a bit changes only on a marked
    # undirected port-2 link, using its unique role-0 endpoint to set the mark.
    def step(p: int, full: int) -> int:
        s, bit = divmod(full, 2)
        t = m.ports[p][s]
        base = s if m.role(s) == 0 else t
        phi = m.phase(base)
        eta = (m.symbol(base, 0) - m.symbol(base, 3)) % 6
        zeta = (eta + phi) % 6
        # The one-axis decoy marks two phase levels. The two-axis control
        # marks a rectangle in two relative-symbol readings. It deliberately
        # breaks compass symmetry on the fiber, not on the projected relay.
        mark = (eta in (2, 3) and zeta in (3, 4)) if two_axes else phi in (0, 1)
        return 2 * t + (bit ^ int(p == 2 and mark))

    return tuple(tuple(step(p, s) for s in range(2 * len(m.reps))) for p in PORTS)


def fiber_controls(m: Model, two_axes: bool) -> dict[str, object]:
    lift = link_lift(m, two_axes)
    full = range(len(lift[0]))

    # The same fixed relative-symbol analyzer on every run; a set bit
    # interchanges its bright/dark outputs (adds half a rotation).
    def bright(s: int) -> bool:
        site, bit = divmod(s, 2)
        return (m.phase(site) + 3 * bit) % 6 in BRIGHT

    prep = tuple(
        walk(lift, 0, A[::-1] + A * (a + b)) for a, b in product(range(2), repeat=2)
    )
    need(all(t[t[s]] == s for t in lift for s in full), "link lift not reciprocal")
    need(
        all(len(part) == len(full) for part in components(lift)),
        "disconnected spectator bit",
    )
    need(
        all(lift[p][s] // 2 == m.ports[p][s // 2] for s in full for p in PORTS),
        "lift changed the position relay",
    )
    changed = []
    for second, subgroup in ((B, 36), (B_DISJOINT, 18)):
        word = commutator(second)
        need(
            len(
                {
                    walk(m.ports, 0, A * i + second * j)
                    for i, j in product(range(6), repeat=2)
                }
            )
            == subgroup,
            "misidentified overlapping translation directions",
        )
        need(
            order(action(lift, A)) == order(action(lift, second)) == 6,
            "actuator order on full lift",
        )
        need(
            all(walk(m.ports, s, word) == s for s in range(len(m.reps))),
            "base commutator",
        )
        need(
            all(walk(lift, s, word) // 2 == s // 2 for s in full),
            "fiber commutator changed position",
        )
        # Role 0: A raises phi, second lowers it. The two bit marks compare
        # g(phi+1) and g(phi); their XOR is one precisely at 1 and 5.
        if not two_axes:
            need(
                all(
                    (walk(lift, s, word) != s) == (m.phase(s // 2) in (1, 5))
                    for s in full
                    if m.role(s // 2) == 0
                ),
                "link-local commutator phase",
            )
        changed.append(sum(walk(lift, 2 * s, word) != 2 * s for s in prepared(m)))
        need(
            sum(bright(walk(lift, s, word)) for s in prep) == (3 if two_axes else 2),
            "same analyzer did not separate the lifted commutator",
        )
    need(
        changed == ([1, 1] if two_axes else [2, 2]),
        "moved bit on the same four preparation histories",
    )
    failed = sum(
        any(walk(lift, s, w) != walk(lift, s, w[::-1]) for w in TRIPLES) for s in full
    )
    need(
        failed == (276 if two_axes else 360),
        "scope of the complete-state abc=cba failure",
    )
    # The identical preparation and position analyzer still yield the same
    # clean phase row when actually executed on the bit-carrying update.
    need(
        tuple(
            sum(m.phase(walk(lift, s, A * n) // 2) in BRIGHT for s in prep)
            for n in range(6)
        )
        == ROW
        == tuple(sum(bright(walk(lift, s, A * n)) for s in prep) for n in range(6)),
        "fiber rival lost one-axis fringe",
    )
    b_row = tuple(sum(bright(walk(lift, s, B * n)) for s in prep) for n in range(6))
    # B changes phi by -1 but preserves eta. In the calibrated case none of
    # the prepared B-lines (eta = 5,0,1) is marked. Moving through A first
    # changes eta: the formerly bright +1 history alone picks up a bit.
    need(
        (b_row == ROW) == two_axes, "second-axis calibration did not separate the decoy"
    )
    return {
        "full_states": len(full),
        "commutator_bit_changes_of_four": changed,
        "second_axis_quarter_numerators": b_row,
        "same_analyzer_commutator_return": str(F(4 - changed[0], 4)),
        "full_state_origins_violating_some_abc": failed,
    }


def reference(protocol: tuple[tuple[str, int], ...]) -> F:
    # An independent, SUPPLIED benchmark, not the meaning of named ports.
    # Cartesian Bloch vector is (sqrt(3)*u, sqrt(3)*v, z). Use +/-60-degree
    # rotations about orthogonal x,y and a north preparation / north analyzer.
    u, v, z = F(0), F(0), F(1)
    for axis, sign in protocol:
        if axis == "x":
            v, z = (v - sign * z) / 2, (sign * 3 * v + z) / 2
        else:
            u, z = (u + sign * z) / 2, (-sign * 3 * u + z) / 2
        need(3 * u * u + 3 * v * v + z * z == 1, "reference rotation norm")
    return (1 + z) / 2


def reference_control() -> F:
    for axis in ("x", "y"):
        need(
            tuple(reference(((axis, 1),) * n) for n in range(6))
            == tuple(F(k, 4) for k in ROW),
            "reference did not pass both separate calibrations",
        )
    answer = reference((("x", 1), ("y", 1), ("x", -1), ("y", -1)))
    need(
        answer == F(29, 32) and (4 * answer).denominator != 1,
        "reference commutator or four-history granularity",
    )
    return answer


def main() -> None:
    old, raw, m = model(4, False), model(6, False), model(6, True)
    size_controls()
    compass(m)
    need(
        tuple(len(x.reps) for x in (old, raw, m)) == (128, 432, 216),
        "connected site counts",
    )
    for x in (old, raw, m):
        need(
            all(exact_ball(x.ports, s) for s in range(len(x.reps))), "six-tick language"
        )
    old_orders, orders = word_group(old), word_group(m)
    need(old_orders == {1: 1, 2: 71, 4: 56}, "four-symbol full word group")
    need(orders == {1: 1, 2: 111, 3: 26, 6: 78}, "216-site full word group")
    need(fringe(raw) == fringe(m), "loss from diagonal identification")
    coordinate_control(m)
    print(
        json.dumps(
            {
                "connected_sites": [len(x.reps) for x in (old, raw, m)],
                "q4_word_orders": old_orders,
                "q6_quotient_word_orders": orders,
                "quarter_numerators": ROW,
                "plain_relay_commutator_return": "1",
                "one_axis_link_bit_decoy": fiber_controls(m, False),
                "two_axis_link_bit_rival": fiber_controls(m, True),
                "supplied_orthogonal_reference_return": str(reference_control()),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
