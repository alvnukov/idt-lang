"""Pre-setting exchange of two independently issued triangle-edge packets.

Only the two signed edges enter the preparation. The two branches of one
co-located exchange are recorded before either analyzer setting is supplied.
Both continue through both analyzers, using their actual prior event addresses.
This supplies a shared identification of the three labels, signed branching,
paired rails, quadratic ordered-pair readout and uniform seeds. It neither
derives these resources nor implements a Bell-local detector or physical 3D.

Run: python3 -O -m scripts.probe_heralded_triangle_factory
"""

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_triangle_exchange_source import (
    AB,
    BA,
    BITS,
    D,
    Stock,
    V,
    comparator,
    edge,
    initialize,
    local_swap,
    need,
    outer,
    pairs,
    signed_vector,
    split,
)


def independent(x: V, y: V) -> Stock:
    left, right = initialize(x), initialize(y)
    cloud = tuple((3 * a + b, s * t) for a, s in left.cloud for b, t in right.cloud)
    n = len(right.cloud)
    tickets = {
        (u, v): (a * n + c, b * n + d)
        for (u,), (a, b) in left.tickets.items()
        for (v,), (c, d) in right.tickets.items()
    }
    need(
        len(tickets) == len(set(tickets.values()))
        and set(tickets.values()) == pairs(cloud),
        "independent event addresses",
    )
    s = Stock(cloud, tickets)
    need(signed_vector(s, 9) == outer(x, y), "independent source currents")
    return s


def factory(x: V, y: V) -> Stock:
    return comparator(independent(x, y), 1)


def outcome(s: Stock, address: tuple[int, int]) -> int:
    i, j = address
    rail = s.cloud[i][0]
    need(rail == s.cloud[j][0], "cross-rail output event")
    return rail


def read_settings(hstock: Stock, order=AB, reverse=False, micro=False):
    """All settings reuse this pre-setting stock; no branch reinitialization."""
    herald = {t: outcome(hstock, addr) // 9 for t, addr in hstock.tickets.items()}
    totals = Counter(herald.values())
    tables, histories = {}, {}
    for k, l in product(D, repeat=2):
        s = hstock
        for stage, side in enumerate(order):
            s = split(s, local_swap((k, l)[side], side, 2 << stage), 9, reverse)
        table, records = Counter(), {}
        for ticket, addr in s.tickets.items():
            rail = outcome(s, addr)
            h, first, last = (rail // scale % 2 for scale in (9, 18, 36))
            a, b = (first, last) if order == AB else (last, first)
            need(
                h == herald[ticket[:-2]], "settings changed the earlier ticket's herald"
            )
            table[h, a, b, rail % 9] += 1
            if micro:
                records[ticket] = (h, a, b)
        need(
            Counter(t[:-2] for t in s.tickets) == Counter({t: 16 for t in herald}),
            "a factory history lost or duplicated descendants",
        )
        for h in BITS:
            need(
                sum(n for (v, _, _, _), n in table.items() if v == h) == 16 * totals[h],
                "herald denominator changed",
            )
        tables[k, l] = table
        if micro:
            histories[k, l] = records
    for h, side, own in product(BITS, BITS, D):
        marginals = set()
        for remote in D:
            table = tables[(own, remote) if side == 0 else (remote, own)]
            marginals.add(
                sum(
                    n
                    for (v, a, b, _), n in table.items()
                    if v == h and (a, b)[side] == 0
                )
            )
        need(len(marginals) == 1, "conditional marginal signals")
    if micro:
        for side in order:
            witness = None
            for own, lo, hi in product(D, repeat=3):
                if lo >= hi:
                    continue
                u, v = ((own, lo), (own, hi)) if side == 0 else ((lo, own), (hi, own))
                for t, raw in histories[u].items():
                    later = histories[v][t]
                    if raw[0] == 1 and raw[1 + side] != later[1 + side]:
                        witness = (u, v, t, raw[1 + side], later[1 + side])
                        break
                if witness:
                    break
            need(
                (witness is None) == (side == order[0]),
                "microscopic setting dependence",
            )
            if witness:
                print(
                    "later party",
                    side,
                    "changes at (settings,settings,ticket,old,new):",
                    witness,
                )
    return tables


def witness(tables, h):
    def eq(k, l):
        table = tables[k, l]
        total = sum(n for (v, _, _, _), n in table.items() if h is None or h == v)
        same = sum(
            n for (v, a, b, _), n in table.items() if (h is None or h == v) and a == b
        )
        return F(same, total)

    return sum(eq(k, (k + 1) % 3) - eq(k, k) for k in D)


def main():
    # This target pattern is checked only after the complete stock has routed.
    target = (0, 1, -1, -1, 0, 1, 1, -1, 0)
    base = factory(edge(0), edge(1))
    raw = signed_vector(base, 18)
    need(raw[9:] == target, "antisymmetric output is not the unit circulation")
    swapped = signed_vector(factory(edge(1), edge(0)), 18)
    need(
        swapped[:9] == raw[:9] and swapped[9:] == tuple(-v for v in raw[9:]),
        "swapped source order",
    )
    ref = read_settings(base, micro=True)
    need(
        ref == read_settings(base, BA, micro=True) == read_settings(base, reverse=True),
        "analyzer order or matching changed counts",
    )
    need(
        [witness(ref, h) for h in (1, 0, None)] == [F(9, 4), F(-9, 20), F(9, 16)],
        "conditional or unconditional cycle witness",
    )
    # A setting-independent herald only reweights the deterministic local
    # assignments. Hence their maximum also bounds any such positive mixture.
    bound = max(
        sum((a[k] == b[(k + 1) % 3]) - (a[k] == b[k]) for k in D)
        for a in product(BITS, repeat=3)
        for b in product(BITS, repeat=3)
    )
    need(bound == 2, "deterministic local assignments")
    pooled = {kl: Counter() for kl in ref}
    for p in permutations(D):
        x, y = (tuple(edge(k)[p[i]] for i in D) for k in (0, 1))
        for sx, sy in product((-1, 1), repeat=2):
            s = factory(tuple(sx * v for v in x), tuple(sy * v for v in y))
            need(
                signed_vector(s, 18)
                == tuple(
                    sx * sy * raw[9 * h + 3 * p[a] + p[b]]
                    for h in BITS
                    for a in D
                    for b in D
                ),
                "frame/orientation current",
            )
        tables = read_settings(factory(x, y))
        for (k, l), table in tables.items():
            renamed = Counter(
                {
                    (h, a, b, 3 * p[r // 3] + p[r % 3]): n
                    for (h, a, b, r), n in table.items()
                }
            )
            need(renamed == ref[p[k], p[l]], "anonymous-frame fine counts")
    for i, j in product(D, repeat=2):
        s = factory(edge(i), edge(j))
        counts = Counter(outcome(s, addr) // 9 for addr in s.tickets.values())
        need(
            (counts[1], counts[0]) == ((0, 16) if i == j else (6, 10)),
            "factory denominator",
        )
        tables = read_settings(s)
        if i != j:
            need(witness(tables, 1) == F(9, 4), "conditional singlet cycle")
            for (k, l), table in tables.items():
                branch = tuple(
                    sum(table[1, a, b, r] for r in range(9)) for a in BITS for b in BITS
                )
                need(
                    branch == ((0, 48, 48, 0) if k == l else (36, 12, 12, 36)),
                    "singlet table",
                )
        for kl, table in tables.items():
            pooled[kl].update(table)  # positive mixture, not coherent addition
    need(
        sum(n for (h, _, _, _), n in pooled[0, 0].items() if h) == 576
        and sum(pooled[0, 0].values()) == 2304,
        "independent uniform edge mixture",
    )
    need(
        [witness(pooled, h) for h in (1, 0, None)] == [F(9, 4), F(-3, 4), F(0)],
        "positive mixture conditioning",
    )
    # In an arbitrary positive independent edge mixture with index laws p,q,
    # the nine checked rows give P(anti)=3/8 * (1-sum_i p_i q_i). Every
    # contributing row has the same anti table; a zero-rate herald is undefined.
    print(
        "e0 x e1: pre-setting antisymmetric/symmetric 6/16,10/16;"
        " after settings 96/256,160/256. Cycles (anti,sym,all): 9/4,-9/20,9/16; local bound 2."
    )
    print(
        "9 edge pairs; parallel null, swapped raw sign; 6 shared frames x 4 sign choices;"
        " all 9 setting pairs. Independent uniform edge mixture: 576/2304 anti;"
        " cycles 9/4,-3/4,0."
    )


if __name__ == "__main__":
    main()
