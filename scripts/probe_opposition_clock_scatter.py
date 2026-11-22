"""A selected four-leg mixer from an ordered pair of uncolored opposition marks.

Start with six partial records in three opposite pairs. A controller carries
two successive marks on DIFFERENT pairs. The next mark must change pair,
must not immediately retrace its previous edge, and must be deterministic
and equivariant under every relabeling preserving opposition. These are
actual dynamics assumptions. There is exactly one such successor: the
opposite of the older mark. No external direction or assigned cyclic order
is needed once an admissible initial ordered pair exists.

Applying the selected permutation to ALL records is a separate data/control
coupling. Two opposition-preserving bijections extend this clock; only the
one transparent on the unused pair induces the four-leg mixing reflection.
No readout/clock synchronization of remote vertices or probabilities follow.
"""

from __future__ import annotations

from itertools import permutations, product

from scripts.probe_three_opposition_origin import (
    DUAL,
    SHEET,
    TupleI,
    X,
    hist,
    need,
    raw,
)


def group() -> tuple[TupleI, ...]:
    return tuple(
        tuple(2 * p[x // 2] + ((x & 1) ^ f[x // 2]) for x in X)
        for p, f in product(permutations(range(3)), product(range(2), repeat=3))
    )


G = group()
FLAGS = tuple((u, v) for u in X for v in X if u // 2 != v // 2)


def extend(u: int, v: int, flip: bool) -> TupleI:
    if (u, v) not in FLAGS:
        raise ValueError("ordered successive marks on different pairs required")
    route = {u: v, v: u ^ 1, u ^ 1: v ^ 1, v ^ 1: u}
    return tuple(route.get(x, x ^ int(flip)) for x in X)


def advance(stock: TupleI, perm: TupleI) -> TupleI:
    return tuple(stock[perm.index(i)] for i in range(len(stock)))


def chart(perm: TupleI) -> tuple[bool, TupleI]:
    image = tuple(tuple(sorted(perm[x] for x in v)) for v in SHEET)
    dual = set(image) == set(DUAL)
    vertices = DUAL if dual else SHEET
    return dual, tuple(vertices.index(v) for v in image)


def run_controls() -> None:
    routes = set()
    for x in X:
        fixed = {y for y in X if all(p[y] == y for p in G if p[x] == x)}
        need(fixed == {x, x ^ 1}, "one-mark natural alternative")
    for u, v in FLAGS:
        stab = tuple(p for p in G if p[u] == u and p[v] == v)
        allowed = {
            w for w in X if w // 2 != v // 2 and w != u and all(p[w] == w for p in stab)
        }
        need(allowed == {u ^ 1}, "unique second-order successor")
        on, off = extend(u, v, False), extend(u, v, True)
        need(
            {p for p in G if p[u] == v and p[v] == u ^ 1} == {on, off},
            "extension class",
        )
        need(extend(v, u ^ 1, False) == on, "unintended controller precession")
        need(
            extend(v, u, False) == tuple(on.index(i) for i in X),
            "time reversal not an inverse",
        )
        routes.add(on)
        for p in G:
            ren = extend(p[u], p[v], False)
            need(all(ren[p[i]] == p[on[i]] for i in X), "frame-dependent chronology")
        for op, transparent in ((on, True), (off, False)):
            swaps, ports = chart(op)
            need(swaps == transparent, "wrong chart response")
            for i in range(4):
                need(
                    ports[ports[i]] != i and ports[ports[ports[ports[i]]]] == i,
                    "not a four-cycle",
                )
            for i in X:
                stock = tuple(int(x == i) for x in X)
                h = hist(stock, SHEET)
                need(
                    hist(advance(stock, op), SHEET)
                    == advance(raw(h) if transparent else h, ports),
                    "raw response from record transport",
                )
    need(len(routes) == 6, "orientation count")
    # One supplied test input demonstrates the difference after choosing the
    # SAME probe flag. The bypass species themselves discriminate immediately.
    u, v = FLAGS[0]
    spare = next(x for x in X if x // 2 not in (u // 2, v // 2))
    s = tuple(int(x == spare) for x in X)
    need(
        hist(advance(s, extend(u, v, False)), SHEET)
        != hist(advance(s, extend(u, v, True)), SHEET),
        "bypass control",
    )


def main() -> None:
    run_controls()
    print(
        "Three opposite pairs + two ordered marks: equivariance, changing pair and no immediate retrace select (u,v)→(v,opposite u). The 24 flags induce exactly six transparent quarter-turns (three bypass pairs, two time orientations). One mark cannot naturally leave its own pair."
    )
    print(
        "Exactly two bijective opposition-preserving data extensions agree on the entire controller orbit. A transparent spare yields the previous G times a port four-cycle; flipping the spare yields a pure port permutation. A spare-preparation test separates these identical-clock rivals."
    )
    print(
        "Controller chronology, recordwise coupling, bypass transparency and actual fixed-chart detection are assumptions. A passive chart change or a randomized symmetric successor does not establish the same apparatus."
    )


if __name__ == "__main__":
    main()
