"""Recover the five-tag relation without supplying field labels.

Each of five anonymous centers holds a matching of the OTHER four marks.
If a claimed pair is also claimed by another center, a center may re-pair
its four marks. A configuration is collision-free iff every distinct pair
has exactly one center. Uniform fair proposals are one supplied schedule,
not a consequence of the rewrite. The local four-other-mark inventory and
access to duplicate claims are real inputs; physical interactions, blanks,
timing and choice of arity have not been derived.

At order five all collision-free tables are relabelings of the same
midpoint quasigroup. Given a center m one may reflect x about m, or take
the midpoint of x,m, by lookup in this incidence, without modular
arithmetic in the update. The two resulting inverse pair rotations supply
the existing five-tag spectator gate. Its six-setting instrument does
not identify the global alphabet: a transitive anonymous 21-mark rival
reproduces EVERY circuit starting from two tag values, including its first
and second records. A third source outside their five-mark line matters.
"""

from __future__ import annotations

from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations, permutations, product

from scripts.probe_affine_pulse_holdouts import need
from scripts.probe_midpoint_spectator_instrument import rule

Pair = tuple[int, int]
Matching = tuple[Pair, Pair]
Stock = tuple[int, ...]
Table = tuple[tuple[int, ...], ...]
Q = tuple(range(5))


def choices(center: int) -> tuple[Matching, ...]:
    a, b, c, d = [k for k in Q if k != center]
    return (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c)))


BANK = tuple(choices(i) for i in Q)


def count(s: Stock) -> Counter[Pair]:
    return Counter(pair for i, k in enumerate(s) for pair in BANK[i][k])


def transform(s: Stock, p: Stock) -> Stock:
    out = [0] * 5
    for i, k in enumerate(s):
        (a, b), (c, d) = BANK[i][k]
        edge1, edge2 = sorted(
            (tuple(sorted((p[a], p[b]))), tuple(sorted((p[c], p[d]))))
        )
        out[p[i]] = BANK[p[i]].index(((edge1[0], edge1[1]), (edge2[0], edge2[1])))
    return tuple(out)


def incidence(s: Stock) -> Table:
    m = [[i if i == j else -1 for j in Q] for i in Q]
    for c, k in enumerate(s):
        for x, y in BANK[c][k]:
            need(m[x][y] == -1, "ambiguous center")
            m[x][y] = m[y][x] = c
    return tuple(tuple(row) for row in m)


def other(mid: Table, center: int, one: int) -> int:
    """Other endpoint of a centered pair, defined also on the diagonal."""
    return mid[one].index(center)


def contact(mid: Table, spectator: int, x: int, y: int) -> Pair:
    m = mid[x][y]
    if spectator == m:
        # x is the center of the pair (m,left), hence left=2x-m in
        # a field presentation. Likewise for y. The rule only uses incidence.
        return other(mid, x, m), other(mid, y, m)
    return mid[x][m], mid[y][m]


def distances(
    states: list[Stock], sinks: set[Stock], edges: dict[Stock, list[Stock]]
) -> dict[Stock, int]:
    back: dict[Stock, list[Stock]] = {s: [] for s in states}
    for s, targets in edges.items():
        for t in targets:
            back[t].append(s)
    dist = {s: 0 for s in sinks}
    queue = deque(sorted(sinks))
    while queue:
        t = queue.popleft()
        for s in back[t]:
            if s not in dist:
                dist[s] = dist[t] + 1
                queue.append(s)
    return dist


def solve(a: list[list[F]]) -> list[F]:
    n = len(a)
    for j in range(n):
        pivot = next(k for k in range(j, n) if a[k][j])
        a[pivot], a[j] = a[j], a[pivot]
        p = a[j][j]
        a[j] = [v / p for v in a[j]]
        for k in range(n):
            if k != j:
                q = a[k][j]
                a[k] = [x - q * y for x, y in zip(a[k], a[j], strict=True)]
    return [row[-1] for row in a]


def factory() -> tuple[set[Stock], F, F]:
    states = list(product(range(3), repeat=5))
    counts = {s: count(s) for s in states}
    energy = {s: 10 - len(c) for s, c in counts.items()}
    sinks = {s for s in states if not energy[s]}
    need(
        Counter(energy.values()) == {0: 6, 2: 90, 3: 60, 4: 75, 5: 12}, "overlap census"
    )
    edges: dict[Stock, list[Stock]] = {}
    strict: dict[Stock, list[Stock]] = {}
    for s in states:
        row = []
        for i, k in enumerate(s):
            conflict = any(counts[s][p] > 1 for p in BANK[i][k])
            for h in range(3):
                if h != k:
                    row.append(s[:i] + (h,) + s[i + 1 :] if conflict else s)
        edges[s] = row
        strict[s] = [t for t in row if energy[t] < energy[s]]
    need(
        any(energy[t] > energy[s] for s, row in edges.items() for t in row),
        "simple rule secretly greedy",
    )
    d = distances(states, sinks, edges)
    need(len(d) == 243 and max(d.values()) <= 3, "unreachable collision-free incidence")
    need(
        len(distances(states, sinks, strict)) == 198
        and sum(not strict[s] and s not in sinks for s in states) == 30,
        "strict descent countercontrol",
    )
    # A nontrivial directed cycle can be repeated under a poor scheduler.
    need(
        any(t != s and s in edges[t] for s in states for t in edges[s]),
        "unfair scheduler control",
    )
    # A uniform choice out of 5 centers x 2 alternatives gives a path to
    # absorption of probability at least 10^-3 in each three proposals;
    # stalled proposals still count. Compute exact expectations, independently
    # checking the first-step equations on all 243 labeled configurations.
    rep: dict[Stock, Stock] = {}
    for s in states:
        if s not in rep:
            orbit = {transform(s, p) for p in permutations(Q)}
            for t in orbit:
                rep[t] = min(orbit)
    classes = sorted(set(rep.values()))
    need(
        len(classes) == 7
        and sorted(Counter(rep.values()).values()) == [6, 12, 15, 30, 60, 60, 60],
        "frame classes",
    )
    a = []
    for s in classes:
        targets = Counter(rep[t] for t in edges[s])
        a.append(
            [
                F(k == s) - (F(targets[k], 10) if s not in sinks else F(0))
                for k in classes
            ]
            + [F(s not in sinks)]
        )
    et = dict(zip(classes, solve(a), strict=True))
    need(
        all(
            et[rep[s]]
            == (
                1 + sum((et[rep[t]] for t in edges[s]), F(0)) / 10
                if s not in sinks
                else 0
            )
            for s in states
        ),
        "first-step hitting-time equations",
    )
    need(len({rep[s] for s in sinks}) == 1, "distinct terminal physics")
    return (
        sinks,
        max(et.values()),
        sum((et[rep[s]] for s in states), F(0)) / len(states),
    )


def lookup(sinks: set[Stock]) -> None:
    # Five is the first nontrivial odd size for the centered matching
    # plus a square root of reversal within each center's endpoint fiber:
    # (n-1)/2 endpoint transpositions must have even sign. At n=3 the
    # two off-center endpoints cannot be turned halfway. n=1 is vacuous.
    need(
        all(tuple(p[p[i]] for i in (0, 1)) != (1, 0) for p in permutations((0, 1))),
        "three-tag control",
    )
    for s in sinks:
        m = incidence(s)
        charts = [
            p
            for p in permutations(Q)
            if all(
                2 * p[m[x][y]] % 5 == (p[x] + p[y]) % 5 for x, y in product(Q, repeat=2)
            )
        ]
        need(len(charts) == 20, "anonymous chart multiplicity")
        for p in charts:
            for c, x, y in product(Q, repeat=3):
                a, b = contact(m, c, x, y)
                need(
                    (p[a], p[b]) == rule(p[c], p[x], p[y]),
                    "incidence circuit did not recover existing rule",
                )
        need(
            all(
                m[m[w][x]][m[y][z]] == m[m[w][y]][m[x][z]]
                for w, x, y, z in product(Q, repeat=4)
            ),
            "five-mark mediality",
        )


def counterworld() -> tuple[int, int, int, int]:
    # A concrete cyclic difference set. Check, rather than assume, that
    # each unordered pair is in just one five-mark line. Relative roles
    # move with the line under all 21 translations, so no preferred mark.
    n = 21
    labels = (0, 1, 4, 14, 16)
    need(
        sorted((a - b) % n for a, b in permutations(labels, 2)) == list(range(1, n)),
        "unique differences",
    )
    lines = [tuple((a + t) % n for a in labels) for t in range(n)]
    counts = Counter(
        tuple(sorted(pair)) for line in lines for pair in combinations(line, 2)
    )
    need(
        len(counts) == 210 and set(counts.values()) == {1},
        "two points do not select a unique line",
    )
    m = [[i if i == j else -1 for j in range(n)] for i in range(n)]
    for line in lines:
        for i, j in product(Q, repeat=2):
            m[line[i]][line[j]] = line[3 * (i + j) % 5]
    table = tuple(tuple(row) for row in m)
    need(
        all(sorted(row) == list(range(n)) for row in table),
        "not a global midpoint matching",
    )
    need(
        all(
            table[(x + 1) % n][(y + 1) % n] == (table[x][y] + 1) % n
            for x, y in product(range(n), repeat=2)
        ),
        "not transitive under cyclic translations",
    )
    for x, y, c in product(range(n), repeat=3):
        a, b = contact(table, c, x, y)
        need(contact(table, c, a, b) == (y, x), "global square-to-swap")
    for line in lines:
        for c, x, y in product(Q, repeat=3):
            a, b = rule(c, x, y)
            need(
                contact(table, line[c], line[x], line[y]) == (line[a], line[b]),
                "an operation leaves its prepared five-mark line",
            )
    # So every circuit, also a data-dependent circuit restricted to these
    # two tag types and their descendants, stays on that line by induction.
    # An independent third tag can reveal a different line. Five pair probes
    # all use the same contact primitive with distinct prepared comparison
    # wires. A nonmatching comparison changes neither target after two visits.
    for line in lines:
        hits = []
        for c in range(n):
            flags = []
            for i in Q:
                x, y = line[(i - 1) % 5], line[(i + 1) % 5]
                a, b = contact(table, c, x, y)
                out = contact(table, line[i], a, b)
                need(
                    out == ((y, x) if c == line[i] else (x, y)),
                    "external-tag comparator",
                )
                flags.append(out == (y, x))
            hits.append(sum(flags))
        need(Counter(hits) == {0: 16, 1: 5}, "third-source control")
    witness = next(
        (w, x, y, z)
        for w, x, y, z in product(range(n), repeat=4)
        if table[table[w][x]][table[y][z]] != table[table[w][y]][table[x][z]]
    )
    return witness


def main() -> None:
    sinks, worst, mean = factory()
    lookup(sinks)
    failed = counterworld()
    print(
        "Five centers, three anonymous matchings each: 6 of 243 have no duplicate claims, all related by renaming."
    )
    print(
        f"Any initial choice admits a <=3-repair path. Under uniform proposals, mean time from uniform start {mean}, worst expected {worst} proposals. Strict descent strands 30 nonterminal configurations."
    )
    print(
        "The incidence alone computes the known ternary rule in all 20 charts of every valid table; order five is minimal under a centered half-turn requirement."
    )
    print(
        f"A transitive 21-tag rival passes every two-tag-source circuit, but fails the global midpoint interchange law at {failed}."
    )
    print(
        "An independently uniform third tag hits the old five-mark line in 5/21 of trials vs 1; uniform fresh tags are NOT derived."
    )


if __name__ == "__main__":
    main()
