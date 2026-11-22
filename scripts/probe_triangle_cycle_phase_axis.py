"""A co-located cycle comparison for two neutral signed triangle currents.

Four *supplied* settings (three current exchanges and one joint cycle test)
herald eight preparations. Count every descendant of the independent source
tickets, without replacing a prepared branch by a newly normalized stock.
Three coherent paths, three identity copies on the complementary port, the
reference, orientation conventions, paired rails, and the existing signed
cloud/ordered-pair/uniform-seed router are resources. No complex phase,
probability table or coordinates are inputs to the router. This finite real
extension does not derive a single-triangle phase, a physical detector,
independent remote frames, complex QM, or the full set of qubit states.

Run: python3 -B -O -m scripts.probe_triangle_cycle_phase_axis
"""

import sys
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_heralded_triangle_factory import independent, outcome
from scripts.probe_triangle_exchange_source import (
    BITS,
    D,
    Matrix,
    Stock,
    V,
    edge,
    local_swap,
    need,
    outer,
    pairs,
    route_block,
    signed_vector,
    split,
    transposition,
)

K = 3
SETTINGS = (*D, K)
LABELS = tuple(product(SETTINGS, BITS))
WINDS = tuple(product((1, -1), repeat=2))


@cache
def cycle_paths(histories: int, winds: tuple[int, int]) -> Matrix:
    """Upper B=I+T+T² and lower 3I−B, from individual signed children."""
    need(histories > 0 and winds in WINDS, "invalid cycle convention")
    width = 9 * histories
    columns = []
    u, v = winds
    for h, a, b in product(range(histories), D, D):
        orbit = tuple(9 * h + 3 * ((a + j * u) % 3) + (b + j * v) % 3 for j in D)
        raw = (
            [(i, 1) for i in orbit]
            + [(width + orbit[0], 1)] * 3
            + [(width + i, -1) for i in orbit]
        )
        col = [0] * (2 * width)
        for i, sign in raw:
            col[i] += sign
        need(len(raw) == 9 and sum(map(abs, col)) == 7, "same-parent cancellation")
        columns.append(col)
    return tuple(zip(*columns, strict=True))


def read(s: Stock, setting: int, histories: int, winds=(1, 1), reverse=False) -> Stock:
    if setting in D:
        return split(s, local_swap(setting, 0, histories), 9, reverse)
    need(setting == K, "unknown setting")
    cloud, routes, gain, _ = route_block(
        s.cloud, cycle_paths(histories, winds), reverse
    )
    need(gain == 9, "joint cycle gain")
    tickets = {}
    for ticket, pair in s.tickets.items():
        for seed in range(gain):
            dest = routes[pair, seed]
            need(
                cloud[dest[0]][0] // 9 % histories == outcome(s, pair) // 9,
                "changed old herald",
            )
            tickets[(*ticket, seed)] = dest
    need(
        len(tickets) == len(set(tickets.values()))
        and set(tickets.values()) == pairs(cloud),
        "cycle tickets are not a bijection",
    )
    return Stock(cloud, tickets)


def gain(setting: int) -> int:
    return 9 if setting == K else 4


def extend(s: Stock, setting: int, histories: int, winds=(1, 1), reverse=False):
    """Compare recorded parent addresses, not merely the two marginal totals."""
    before = {t: outcome(s, p) // 9 for t, p in s.tickets.items()}
    after = read(s, setting, histories, winds, reverse)
    counts = Counter()
    multiplicity = Counter()
    for ticket, addr in after.tickets.items():
        prior, fired = before[ticket[:-1]], outcome(after, addr) // 9
        need(fired % histories == prior and fired // histories in BITS, "stale address")
        multiplicity[ticket[:-1]] += 1
        counts[prior, fired // histories] += 1
    need(
        multiplicity == Counter({t: gain(setting) for t in before}), "lost descendants"
    )
    return after, counts


def observed_table(reverse=False):
    table = {}
    for k in SETTINGS:
        # The adjacent edge gives both heralds of each trine setting.
        source = independent(edge((k + 1) % 3 if k in D else 0), edge(0))
        need(len(source.tickets) == 4, "two independent two-ticket edges")
        prep, emitted = extend(source, k, 1, reverse=reverse)
        need(
            tuple(emitted[0, b] for b in BITS) == ((12, 4) if k in D else (18, 18)),
            "unexpected preparation resources",
        )
        for l in SETTINGS:
            _, counts = extend(prep, l, 2, reverse=reverse)
            for a, b in product(BITS, repeat=2):
                table[k, a, l, b] = F(counts[a, b], emitted[0, a] * gain(l))
    return table


def rank(rows) -> int:
    a = [list(map(F, row)) for row in rows]
    r = 0
    for j in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        pivot = [e / a[r][j] for e in a[r]]
        for i in range(r + 1, len(a)):
            a[i] = [x - a[i][j] * y for x, y in zip(a[i], pivot, strict=True)]
        r += 1
    return r


def rotate(x: V, u: int) -> V:
    return tuple(x[(i - u) % 3] for i in D)


def delta(x: V) -> V:
    return tuple(a - b for a, b in zip(rotate(x, 1), rotate(x, -1), strict=True))


def act(m, x):
    return tuple(sum(a * b for a, b in zip(row, x, strict=True)) for row in m)


def algebra():
    """Exact linear diagnostics; no matrix below supplies the routed events."""
    gate = cycle_paths(1, (1, 1))
    for j in range(9):
        col = tuple(int(i == j) for i in range(9))
        pos, neg = act(gate[:9], col), act(gate[9:], col)
        need(act(gate[:9], pos) == tuple(3 * z for z in pos), "B²≠3B on all nine rails")
        need(act(gate[:9], neg) == (0,) * 9, "noncomplementary branches")
    axes = (edge(0), edge(1))
    for x, y in product(axes, repeat=2):  # a basis of neutral × neutral
        w = outer(x, y)
        pos, neg = act(gate[:9], w), act(gate[9:], w)
        triple_k = tuple(a - b for a, b in zip(pos, neg, strict=True))
        need(triple_k == outer(delta(x), delta(y)), "signed winding identity")

    # Basis on each factor has top coordinates (1,0),(0,1); the last is forced.
    basis = ((1, 0, -1), (0, 1, -1))

    def m2(f):
        return tuple(zip(*(f(w)[:2] for w in basis), strict=True))

    I = ((1, 0), (0, 1))
    J = m2(delta)
    P = [m2(lambda w, k=k: tuple(w[i] for i in transposition(k))) for k in D]

    def kron(A, B):
        return tuple(
            tuple(A[i][k] * B[j][l] for k, l in product(range(2), repeat=2))
            for i, j in product(range(2), repeat=2)
        )

    def equations(generators, sign):
        # Coefficients of G X − sign X G, with every matrix entry X free.
        n = len(generators[0])
        return [
            tuple(
                (g[i][u] if j == v else 0) - sign * (g[v][j] if i == u else 0)
                for u, v in product(range(n), repeat=2)
            )
            for g in generators
            for i, j in product(range(n), repeat=2)
        ]

    anti = equations(P, -1)

    def flat(m):
        return tuple(x for row in m for x in row)

    need(
        rank(anti) == 3 and not any(act(anti, flat(J))), "single triangle anticommutant"
    )
    # The neutral-plane metric in these coordinates is [[2,1],[1,2]].
    # Metric symmetry (GX)01=(GX)10, excluding skew J from real effects.
    need(rank([*anti, (-1, 2, -2, 1)]) == 4, "unexpected self-adjoint fourth axis")
    # J²=−3I makes (J⊗J)/3 an involution; J skew on the actual neutral plane.
    need(all(act(J, act(J, v)) == tuple(-3 * x for x in v) for v in I), "J²")
    need(
        all(
            sum(
                x * y + z * t
                for x, y, z, t in zip(delta(u), v, u, delta(v), strict=True)
            )
            == 0
            for u, v in product(basis, repeat=2)
        ),
        "not skew on the whole plane",
    )
    gen = [*(kron(p, I) for p in P), kron(J, J)]
    comm = equations(gen, 1)
    scalars = [flat(kron(I, I)), flat(kron(I, J))]
    need(
        rank(comm) == 14
        and rank(scalars) == 2
        and not any(any(act(comm, x)) for x in scalars),
        "reference commutant differs from span(I,I⊗J)",
    )


def controls():
    source = independent(edge(0), edge(0))
    # Reversing both cycles retraces the SAME paths. Relative winding matters.
    for u, v in WINDS:
        need(cycle_paths(1, (u, v)) == cycle_paths(1, (-u, -v)), "common reversal")
    # On any real product input the K expectation factors into two zero
    # skew quadratic forms (checked on bilinear basis pairs above). Also
    # exercise all nine independent edge inputs through the actual router.
    for a, b in product(D, repeat=2):
        _, emitted = extend(independent(edge(a), edge(b)), K, 1)
        need(emitted[0, 0] == emitted[0, 1] == 18, "product source has cycle bias")
    for prep_winds in WINDS:
        prep, emitted = extend(source, K, 1, winds=prep_winds)
        vec = signed_vector(prep, 18)
        for packet in (vec[:9], vec[9:]):
            need(
                rank([packet[3 * i : 3 * i + 3] for i in D]) == 2,
                "product heralded packet",
            )
        comparison = {}
        for read_winds in WINDS:
            _, counts = extend(prep, K, 2, winds=read_winds)
            aligned = prep_winds[0] * prep_winds[1] == read_winds[0] * read_winds[1]
            for a, b in product(BITS, repeat=2):
                f = F(counts[a, b], emitted[0, a] * 9)
                need(f == int((a == b) == aligned), "relative winding inversion")
                comparison[read_winds, a, b] = f
        need(
            all(
                sum(comparison[w, a, b] for w in WINDS) / 4 == F(1, 2)
                for a, b in product(BITS, repeat=2)
            ),
            "unrevealed independent fair windings",
        )
    prep, _ = extend(source, K, 1)
    for k in D:
        middle, _ = extend(prep, k, 2)
        final, counts = extend(middle, K, 4)
        need(
            len(final.tickets) == 1296
            and all(counts[h, b] == 162 for h, b in product(range(4), BITS)),
            "stale K recorded across trine",
        )


def main():
    tab = observed_table()
    need(observed_table(reverse=True) == tab, "matching changed frequencies")
    rows = [[tab[k, a, l, b] for l, b in LABELS] for k, a in LABELS]
    for k, a, l, b in product(SETTINGS, BITS, SETTINGS, BITS):
        same = k == l
        expect = (
            F(a == b) if same else F(1, 2) if K in (k, l) else F(1 if a == b else 3, 4)
        )
        need(tab[k, a, l, b] == expect, "eight preparation/effect table")
    need(
        rank(rows) == 4 and rank([r[:6] for r in rows]) == 3, "operational linear rank"
    )
    algebra()
    controls()
    print("Preparations (rows) and effects (columns): P0+ P0- P1+ P1- P2+ P2- K+ K-")
    for row in rows:
        print(" ".join(str(x).rjust(3) for x in row))
    print("4 independent source tickets; heralds P=(12,4) or K=(18,18); gains 4 or 9.")
    print(
        "Two matchings agree. K–trine–K: 162 tickets per (h,m,b), 1296 total, no discards."
    )
    print(
        "Common winding reversal preserves; relative reversal swaps; independent fair signs erase."
    )
    print(
        "Table linear rank 3→4 (normalized affine dimension 2→3); commutant span(I,I⊗J)."
    )
    print(
        "Real product inputs have zero K bias. The two heralded packets have matrix rank 2."
    )
    print(
        "A co-located reference and joint comparison are supplied; not full complex QM."
    )


if __name__ == "__main__":
    main()
