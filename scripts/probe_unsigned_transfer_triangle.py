"""Can a signed triangle current be the boundary of unsigned transfers?

A raw transfer has two roles: start and end. Local splicing joins an arriving
and a departing transfer; a loop may disappear. Raw paths and pairing choices
can be different even when all endpoint-only experiments agree. The router
below keeps branch populations, not identities of earlier detector tickets.
Its count of ordered pairs and its split/reverse wiring are still supplied.
"""

from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product

from scripts.probe_affine_pulse_holdouts import need

Arc = tuple[int, int]
Stock = tuple[Arc, ...]
D = range(3)


def boundary(g: Stock, n: int):
    # Audit observable only. No signed mark is an input to a rewrite.
    return tuple(sum(int(v == i) - int(u == i) for u, v in g) for i in range(n))


def one_step(g):
    for i, (u, v) in enumerate(g):
        if u == v:
            yield g[:i] + g[i + 1 :]
        else:
            for j, (k, w) in enumerate(g):
                if i != j and v == k and k != w:
                    rest = tuple(e for l, e in enumerate(g) if l not in (i, j))
                    yield tuple(sorted(rest + (((u, w),) if u != w else ())))


def reduce(g, rev=False):
    g = tuple(sorted(g))
    while True:
        if not rev:
            dest = next(one_step(g), None)
        else:
            dest = next((tuple(sorted(t)) for t in one_step(g[::-1])), None)
        if dest is None:
            return g
        need(len(dest) < len(g), "splice did not shorten the stock")
        g = dest


@cache
def terminals(g):
    nxt = set(one_step(g))
    return {g} if not nxt else set.union(*(terminals(t) for t in nxt))


def count(g, n):
    # A reduced endpoint has only arrivals or only departures. Count ordered
    # pairs WITH replacement of incident ends on that mark (not pairs of arcs
    # arriving on different rails, not unsigned path lengths).
    degrees = Counter(x for arc in g for x in arc)
    return tuple(degrees[i] ** 2 for i in range(n))


def visible_stock():
    arcs = tuple(product(D, repeat=2))
    for k in range(5):
        for g in combinations_with_replacement(arcs, k):
            v = boundary(g, 3)
            for t in terminals(g):
                need(
                    boundary(t, 3) == v and count(t, 3) == tuple(x * x for x in v),
                    "splice endpoint law",
                )
    shared = tuple(sorted(((0, 4), (1, 4), (4, 2), (4, 3))))
    finals = terminals(shared)
    need(
        len(finals) == 2
        and len({count(t, 5) for t in finals}) == 1
        and {((0, 2) in t) for t in finals} == {True, False},
        "pair-sensitive countercontrol",
    )
    # A closed directed cycle has visible raw transfers before splicing.
    loop = ((0, 1), (1, 2), (2, 0))
    need(reduce(loop) == () and len(loop) == 3, "loop erasure is a physical assumption")


def turn(g, p):
    return tuple((p[u], p[v]) for u, v in g)


def split(g, p, rev):
    h = turn(g, p)
    return reduce(g + h, rev), reduce(g + tuple((v, u) for u, v in h), rev)


def product_arcs(g, h, n, rev):
    raw = []
    for (u, v), (a, b) in product(g, h):
        opposite = (u * n + b, v * n + a)
        alike = (u * n + a, v * n + b)
        raw.extend(product(opposite, alike))
    return reduce(tuple(raw), rev)


def symmetries():
    # Character on antisymmetric integer net flows: swap input ports fixes
    # flow; reversing either input is REQUIRED here to reverse raw net flow.
    # Every equivariant integral solution, not just a bounded list of flows,
    # is propagated orbit by orbit on the six unoriented edges.
    es = tuple(combinations(range(4), 2))
    gens = (((0, 2, 1, 3), 1), ((2, 3, 0, 1), -1), ((1, 0, 3, 2), -1))
    todo = set(es)
    solutions = []
    while todo:
        seed = min(todo)
        values = {seed: 1}
        queue = [seed]
        forced_zero = False
        while queue:
            a, b = queue.pop()
            for p, c in gens:
                x, y = p[a], p[b]
                e = tuple(sorted((x, y)))
                v = values[a, b] * c * (1 if x < y else -1)
                if e in values:
                    forced_zero |= values[e] != v
                else:
                    values[e] = v
                    queue.append(e)
        todo -= set(values)
        if not forced_zero:
            solutions.append(values)
    need(len(solutions) == 1, "unexpected raw-flow invariant")
    net = tuple((a, b) if v > 0 else (b, a) for (a, b), v in solutions[0].items())
    base = (1, -1, -1, 1)
    need(
        len(net) == 4
        and boundary(net, 4)
        in (tuple(2 * x for x in base), tuple(-2 * x for x in base)),
        "symmetric product scale",
    )
    # Exchange alone, WITHOUT the raw reversal rule, permits a 3-arrow
    # shortcut; two preferred horizontal arrows are cheaper still.
    three = ((1, 0), (2, 0), (0, 3))
    two = ((1, 0), (2, 3))
    need(
        boundary(three, 4) == boundary(two, 4) == base
        and sorted(turn(three, gens[0][0])) == sorted(three)
        and sorted(turn(two, gens[0][0])) != sorted(two),
        "which covariance costs the factor two?",
    )


def edge(k):
    return (((k + 2) % 3, (k + 1) % 3),)


def refl(k):
    return tuple((2 * k - i) % 3 for i in D)


def joint(i, j, rev):
    g = product_arcs(edge(i), edge(j), 3, rev)
    swap = tuple(3 * b + a for a, b in product(D, repeat=2))
    pop = split(g, swap, rev)
    out = {}
    for k, l in product(D, repeat=2):
        localA = tuple(3 * refl(k)[a] + b for a, b in product(D, repeat=2))
        localB = tuple(3 * a + refl(l)[b] for a, b in product(D, repeat=2))
        cells = []
        for branch in pop:
            row = []
            for u in split(branch, localA, rev):
                row.extend(sum(count(v, 9)) for v in split(u, localB, rev))
            cells.append(tuple(row))
        need(sum(sum(c) for c in cells) == 1024, "all issued events")
        out[k, l] = tuple(cells)
    return tuple(sum(count(x, 9)) for x in pop), out


def main():
    visible_stock()
    symmetries()
    for a, b in product(D, repeat=2):
        flags, tab = joint(a, b, False)
        need(
            (flags, tab) == joint(a, b, True), "endpoint effects depend on splice order"
        )
        need(flags == ((64, 0) if a == b else (40, 24)), "joint herald stock")
        if a != b:
            need(
                all(
                    anti == ((0, 192, 192, 0) if k == l else (144, 48, 48, 144))
                    for (k, l), (_, anti) in tab.items()
                ),
                "trine correlations from transfers",
            )
        for p in permutations(D):
            x, y = turn(edge(a), p), turn(edge(b), p)
            z = product_arcs(x, y, 3, False)
            relabel = tuple(3 * p[u] + p[v] for u, v in product(D, repeat=2))
            need(
                boundary(z, 9)
                == boundary(turn(product_arcs(edge(a), edge(b), 3, False), relabel), 9),
                "anonymous product mismatch",
            )
    print(
        "Unsigned transfers, reversal and local splices realize neutral currents; "
        "all triangle inputs through four arcs and all splice orders checked."
    )
    print(
        "Microscopic two-input reversal plus exchange covariance forces an even boundary; "
        "four unsigned arrows attain twice the unit checkerboard. A weaker convention allows unit scale."
    )
    print(
        "Distinct independent edges: antisymmetric joint herald 24/64, symmetric 40/64; "
        "384+640=1024 terminal ordered-pair events per setting. Parallel herald is empty."
    )
    print(
        "Direction, splicing, split routing, Cartesian corner roles and ordered-pair readout "
        "are supplied. Endpoint equivalence does not hide pairing-sensitive detectors."
    )


if __name__ == "__main__":
    main()
