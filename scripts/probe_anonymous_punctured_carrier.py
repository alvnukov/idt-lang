"""Read the minimally punctured active five-slot carrier as an uncolored graph.

Given only its 16-by-16 adjacency, what can still be reconstructed? No
vertex bit string, direction, slot name, charge, vacuum or metric is passed
to the reconstruction. The preceding sparse-pencil rank criterion selected
this graph conditionally; neither the rank criterion nor its physical
implementation is derived here. The little cube below is a relation, not
a cube embedded in physical space.
"""

from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations, permutations, product

from scripts.probe_affine_pulse_holdouts import need


def edge(x, y):
    return tuple(sorted((x, y)))


def edges(g):
    return frozenset((x, y) for x, ns in enumerate(g) for y in ns if x < y)


def graph(n, es):
    tab = [set() for _ in range(n)]
    for x, y in es:
        need(x != y, "loop")
        tab[x].add(y)
        tab[y].add(x)
    return tuple(frozenset(ns) for ns in tab)


def distances(g, x):
    out = {x: 0}
    q = deque([x])
    while q:
        u = q.popleft()
        for v in g[u]:
            if v not in out:
                out[v] = 1 + out[u]
                q.append(v)
    return out


def read_graph(g):
    high = [x for x, ns in enumerate(g) if len(ns) == 5]
    low = [x for x, ns in enumerate(g) if len(ns) == 2]
    need(len(high) == len(low) == 8, "two valence classes")
    crown = {x: g[x] & set(high) for x in high}
    ds = {x: distances(crown, x) for x in high}
    charts = []
    for origin in high:
        for ns in permutations(crown[origin]):
            ch = {
                x: sum(1 << j for j, n in enumerate(ns) if ds[n][x] < ds[origin][x])
                for x in high
            }
            need(
                len(set(ch.values())) == 8
                and all(
                    (v in crown[u]) == ((ch[u] ^ ch[v]).bit_count() == 1)
                    for u, v in combinations(high, 2)
                ),
                "not a three-direction cube",
            )
            charts.append(ch)
    # Vertices of degree two come in pairs with precisely the same unordered
    # antipodal neighbors. There is no preferred member in any such pair.
    pairs = sorted({tuple(sorted(g[x])) for x in low})
    twins = [sorted(x for x in low if g[x] == set(p)) for p in pairs]
    need(
        len(charts) == 48
        and len(pairs) == 4
        and all(len(t) == 2 for t in twins)
        and all(ds[a][b] == 3 for a, b in pairs),
        "antipodal twin links",
    )
    return high, low, pairs, twins, charts


def completions(g):
    high, _, hs, ls, charts = read_graph(g)
    ch = charts[0]
    inverse = {b: a for a, b in ch.items()}
    raw = edges(g)
    outputs = {}
    for bits in product((0, 1), repeat=4):
        first = {
            u: ls[i][j ^ bits[i]] for i, p in enumerate(hs) for j, u in enumerate(p)
        }
        second = {
            u: ls[i][1 ^ j ^ bits[i]] for i, p in enumerate(hs) for j, u in enumerate(p)
        }
        extra = frozenset(
            edge(first[u], first[v]) for u, v in raw if u in ch and v in ch
        )
        full = graph(16, raw | extra)
        need(
            all(len(ns) == 5 for ns in full)
            and all(
                len(full[u] & full[v]) == (0 if v in full[u] else 2)
                for u, v in combinations(range(16), 2)
            ),
            "completion not the even five-mask graph",
        )
        ports = []
        for j in range(3):
            t = {u: inverse[x ^ (1 << j)] for u, x in ch.items()}
            ports.append(t | {first[u]: first[v] for u, v in t.items()})
        for route in (first, second):
            ports.append(route | {v: u for u, v in route.items()})
        masks = {high[0]: 0}
        q = deque([high[0]])
        while q:
            x = q.popleft()
            for j, t in enumerate(ports):
                v = t[x]
                m = masks[x] ^ 31 ^ (1 << j)
                need(t[v] == x and v in full[x], "not a reciprocal port")
                if v in masks:
                    need(masks[v] == m, "chart holonomy")
                else:
                    masks[v] = m
                    q.append(v)
        need(
            set(masks.values()) == {m for m in range(32) if m.bit_count() % 2 == 0},
            "even-mask chart",
        )
        outputs[extra] = masks
    need(len(outputs) == 8, "eight addressed completions up to global interchange")
    candidates = Counter(e for extra in outputs for e in extra)
    need(
        len(candidates) == 24 and set(candidates.values()) == {4},
        "ambiguous transitions",
    )
    questions = [edge(ls[0][0], t[0]) for t in ls[1:]]
    need(
        len({tuple(e in extra for e in questions) for extra in outputs}) == 8,
        "three extra yes/no tests",
    )
    # Every automorphism of the high cube lifts independently across each
    # low twin pair; every graph automorphism must preserve valence. Check
    # all relabelings from this construction and the full orbit of each node.
    autos = set()
    for co in charts:
        mp = {x: inverse[co[x]] for x in high}
        for bits in product((0, 1), repeat=4):
            lift = mp.copy()
            for i, (a, b) in enumerate(hs):
                j = hs.index(edge(mp[a], mp[b]))
                for s in (0, 1):
                    lift[ls[i][s]] = ls[j][s ^ bits[i]]
            p = tuple(lift[x] for x in range(16))
            need(frozenset(edge(p[x], p[y]) for x, y in raw) == raw, "not a lift")
            autos.add(p)
    need(
        len(autos) == 768 and all(len({p[x] for p in autos}) == 8 for x in range(16)),
        "invariant scalars need extra structure",
    )
    return next(iter(outputs.values()))


def charge_control(masks):
    # GIVEN a chosen chart/vacuum and centered additive slot charges,
    # block permutations leave TWO parameters c,w. Neutrality of the
    # chosen empty mask would impose 3c+2w=0. The graph did not impose it.
    def values(c, w):
        return tuple(
            c * ((m & 7).bit_count() - F(3, 2)) + w * ((m >> 3).bit_count() - 1)
            for m in masks.values()
        )

    need(
        Counter(values(-2, 3)) == {-4: 3, -3: 2, 0: 1, 1: 6, 2: 3, 6: 1},
        "conditional one-family multiplicities",
    )
    for c, w in ((0, 1), (1, 0), (1, 1), (-2, 3), (7, -2)):
        ys = values(c, w)
        need(sum(ys) == sum(y**3 for y in ys) == 0, "trace anomaly control")
    # A chart-independent scalar would be constant on each of only two
    # graph orbits, so these six charge values cannot be assigned that way.
    need(len(set(values(1, 1))) == 3, "different admissible charge table")


def fixture(slots, side):
    ev = [m for m in range(32) if not m.bit_count() % 2]
    rich = {m for m in ev if (m & slots).bit_count() % 2 == side}
    # Replace bit masks by unrelated IDs before passing adjacency on.
    name = {m: (13 * j + 7) % 16 for j, m in enumerate(ev)}
    return graph(
        16,
        (
            edge(name[a], name[b])
            for a, b in combinations(ev, 2)
            if (a ^ b).bit_count() == 4 and (a in rich or b in rich)
        ),
    )


def main():
    for i, j in combinations(range(5), 2):
        for side in (0, 1):
            g = fixture((1 << i) | (1 << j), side)
            need(len(edges(g)) == 28, "wrong puncture")
            charge_control(completions(g))
    print(
        "20 minimal all-active punctures: unlabeled 8-vertex cube, each antipodal pair with two twin bridges."
    )
    print(
        "48 cube charts; 768 graph automorphisms, two vertex orbits. No intrinsic six-valued charge."
    )
    print(
        "16 cross-port assignments give eight addressed five-port completions. "
        "Three extra binary adjacency queries separate them, if an extra transition probe exists."
    )
    print(
        "Block-symmetric centered additive charges leave two weights; a chosen neutral vacuum "
        "conditionally gives six one-family multiplicities, not charge normalization, gauge or generations."
    )


if __name__ == "__main__":
    main()
