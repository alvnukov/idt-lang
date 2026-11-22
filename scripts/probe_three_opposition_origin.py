"""A smaller record primitive: three unlabeled binary oppositions, not four wired legs.

The numbers below label an implementation, not preferred bit signs/axes.
Aut of a fixed-point-free involution with three orbits has order 48.
Its eight transversals are one-from-each-pair completions. Even/odd Hamming
distance defines an *unordered* pair of sheets, independent of orientations.
Each port value on either sheet counts partial records compatible with one
of four completions. This is a candidate operational readout, not an event
probability, and switching passive charts alone is no physical dynamics.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product
from math import comb

TupleI = tuple[int, ...]
X = tuple(range(6))
WORDS = tuple(
    tuple(2 * i + u for i, u in enumerate(v)) for v in product(range(2), repeat=3)
)
SHEET = tuple(v for v in WORDS if sum(x & 1 for x in v) % 2 == 0)
DUAL = tuple(tuple(x ^ 1 for x in v) for v in SHEET)
EDGES = tuple(tuple(i for i, v in enumerate(SHEET) if x in v) for x in X)


def need(ok: bool, msg: str) -> None:
    if not ok:
        raise ArithmeticError(msg)


def hist(stock: TupleI, vertices: tuple[TupleI, ...]) -> TupleI:
    return tuple(sum(stock[x] for x in v) for v in vertices)


def op(stock: TupleI) -> TupleI:
    return tuple(stock[x ^ 1] for x in X)


def raw(h: TupleI) -> TupleI:
    if sum(h) % 2:
        raise ValueError("off the integral pair lattice")
    return tuple(sum(h) // 2 - n for n in h)


def realize(h: TupleI) -> TupleI:
    if len(h) != 4 or min(h) < 0 or sum(h) % 2 or 2 * max(h) > sum(h):
        raise ValueError("not a loopless two-leg stock")
    counts = list(h)
    stock = [0] * 6
    while any(counts):
        i, j = sorted(range(4), key=counts.__getitem__, reverse=True)[:2]
        need(counts[j] > 0, "unpaired excess degree")
        stock[EDGES.index(tuple(sorted((i, j))))] += 1
        counts[i] -= 1
        counts[j] -= 1
        need(2 * max(counts) <= sum(counts), "degree induction")
    return tuple(stock)


def geometric_controls() -> None:
    need(
        len(SHEET) == len(DUAL) == 4 and set(SHEET) | set(DUAL) == set(WORDS),
        "parity sheets",
    )
    need(
        set(EDGES) == set(combinations(range(4), 2)),
        "six abstract records not tetrahedral edges",
    )
    need(
        all(set(EDGES[x ^ 1]) == set(range(4)) - set(EDGES[x]) for x in X),
        "edge complement",
    )
    # Without even naming the cube coordinates, classify transversals by
    # parity of their distance from any one. Another basepoint may swap sheets.
    for w in WORDS:
        near = {
            v for v in WORDS if sum(a != b for a, b in zip(v, w, strict=True)) % 2 == 0
        }
        need(near in (set(SHEET), set(DUAL)), "basepoint ambiguity")
    keep, swap = set(), set()
    perms = []
    for p, f in product(permutations(range(3)), product(range(2), repeat=3)):
        a = tuple(2 * p[x // 2] + ((x & 1) ^ f[x // 2]) for x in X)
        perms.append(a)
        image = tuple(tuple(sorted(a[x] for x in v)) for v in SHEET)
        if set(image) == set(SHEET):
            keep.add(tuple(SHEET.index(w) for w in image))
        else:
            need(set(image) == set(DUAL), "broken parity")
            swap.add(tuple(DUAL.index(w) for w in image))
    need(
        len(set(perms)) == 48 and len(keep) == len(swap) == 24,
        "oriented sheet stabilizer",
    )
    # Any deterministic single-record operation natural under every relabel
    # commutes with the automorphism group. No bijectivity assumed here.
    possibilities = [y for y in X if all(p[y] == y for p in perms if p[0] == 0)]
    need(possibilities == [0, 1], "a preferred turn cannot be selected naturally")
    # Ambiguity from a passive chart AND an active operation on each record:
    # any local single-leg readout of the dual chart equals the complement
    # acting in the first chart (both involutions). A co-record distinguishes.
    one = (1, 0, 0, 0, 0, 0)
    need(
        hist(one, DUAL) == hist(op(one), SHEET) and one != op(one), "passive vs active"
    )


def stock_controls() -> None:
    for s in product(range(4), repeat=6):
        h = hist(s, SHEET)
        need(hist(s, DUAL) == hist(op(s), SHEET) == raw(h), "half-sum map")
        need(
            raw(raw(h)) == h and sum(x * x for x in raw(h)) == sum(x * x for x in h),
            "reflection stock",
        )
    for h in product(range(7), repeat=4):
        if sum(h) % 2 == 0 and 2 * max(h) <= sum(h):
            need(hist(realize(h), SHEET) == h, "histogram realization")
    # Three distinct opposite-pair balanced stocks have the same two chart
    # readouts, so the chart choice does not reveal the hidden two dimensions.
    balanced = tuple(tuple(int(k // 2 == j) for k in X) for j in range(3))
    need(
        len(set(balanced)) == 3
        and {hist(s, v) for s in balanced for v in (SHEET, DUAL)} == {(1, 1, 1, 1)},
        "hidden correlations",
    )


def graph_rivals() -> None:
    # For connected simple unsigned graphs the rank of edge->vertex incidence
    # is v-1 in the bipartite case and v otherwise: a left kernel vector must
    # switch sign along each edge. Fixed total removes one visible direction.
    # Therefore (visible, hidden)=(3,2) needs (v,e)=(4,6) or (5,6).
    rivals: Counter[tuple[int, ...]] = Counter()
    for v in (4, 5):
        for edges in combinations(combinations(range(v), 2), 6):
            parity = {0: 0}
            todo = [0]
            bip = True
            while todo:
                i = todo.pop()
                for e in edges:
                    if i not in e:
                        continue
                    j = e[0] + e[1] - i
                    if j not in parity:
                        parity[j] = 1 - parity[i]
                        todo.append(j)
                    else:
                        bip = bip and parity[j] != parity[i]
            if len(parity) != v:
                continue
            rank = v - int(bip)
            if (rank - 1, 6 - rank) == (3, 2):
                degrees = tuple(sorted(sum(i in e for e in edges) for i in range(v)))
                rivals[degrees] += 1
    need(rivals == {(3, 3, 3, 3): 1, (2, 2, 2, 3, 3): 10}, "complete bipartite rival")
    need(
        all(sum(not set(e) & set(q) for q in EDGES) == 1 for e in EDGES),
        "unique disjoint edge",
    )
    k23 = tuple(product((0, 1), (2, 3, 4)))
    need(
        all(sum(not set(e) & set(q) for q in k23) == 2 for e in k23),
        "rival disjoint ambiguity",
    )
    # For m>=2, a literal fixed by one choice occurs in 2^(m-2)
    # completions on each sheet; exactly TWO such vertices means m=3.
    need(2 ** (3 - 2) == 2 and comb(2 ** (3 - 1), 2) == 2 * 3, "edge interpretation")


def main() -> None:
    geometric_controls()
    stock_controls()
    graph_rivals()
    print(
        "Three unoriented opposite pairs produce eight transversals, two interchangeable tetrahedra, and all six edge-complement types. Their two compatibility histograms satisfy h'=sum(h)/2-h exactly; the involutive change preserves squared stock."
    )
    print(
        "The 48 label symmetries exchange the sheets; 24 preserve one and induce all tetrahedral leg permutations. A natural unary record rule is only identity or complement. No selected four-cycle, clock, click law, positive frequency or quantum state follows."
    )
    print(
        "Among connected simple six-edge populations the same visible/hidden ranks 3+2 also occur on K(2,3); its edges have two disjoint partners, not one. Keeping both charts fails to distinguish the two hidden correlation directions."
    )


if __name__ == "__main__":
    main()
