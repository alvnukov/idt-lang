"""One finite exchange rule on neutral signed currents; no ambient geometry.

An oriented difference of two anonymous labels supplies the preparation motif.
A chosen transposition P sends each carrier through stay and exchange paths,
with a relative minus in the second output. Same-parent opposite paths cancel
before the integer-column event router; that router cancels cross-parent paths
and transports the entire stock of ordered same-rail pairs and uniform seeds.
The six readings, two-party source, and whole-packet comparator below use no
angle, hand-entered entangling gate, or target frequency as routing input.

Supplied: three labels, integer orientation/neutrality, linear signed branching,
coherent merging by designated rail, quadratic event stock in the router,
uniform tickets, herald registers, independent product preparation when used,
or a joint antisymmetric divergence-free current when used. Composite carriers
have ordered paired-label rails; a local permutation on one label does not
make the cancellation/ordered-pair router Bell local. The comparison of both
payloads is a co-located operation, not a remote or nondisturbing measurement.
This finite construction is not detector dynamics, complex QM, or physical 3D.

Run: python3 -O -m scripts.probe_triangle_exchange_source
"""

import sys
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import permutations, product
from pathlib import Path
from typing import NamedTuple

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_cancellation_event_router import (
    Cloud,
    Matrix,
    Pair,
    need,
    pairs,
    route_block,
)

V = tuple[int, ...]
Ticket = tuple[int, ...]
D = range(3)
BITS = (0, 1)  # 0 = symmetric (stay + exchange), 1 = antisymmetric (stay - exchange)
AB, BA = (0, 1), (1, 0)
RAYS = ((0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1))


def norm(x: V) -> int:
    return sum(a * a for a in x)


def outer(x: V, y: V) -> V:
    return tuple(a * b for a in x for b in y)


def transposition(fixed: int) -> V:
    return tuple((2 * fixed - i) % 3 for i in D)


def edge(k: int) -> V:
    return tuple((0, 1, -1)[(i - k) % 3] for i in D)


def median(k: int) -> V:
    return tuple(2 if i == k else -1 for i in D)


@cache
def signed_split(p: V) -> Matrix:
    """Construct the integer columns from four signed children per source."""
    n = len(p)
    need(all(p[p[i]] == i for i in range(n)), "not an exchange involution")
    columns = []
    for i, exchanged in enumerate(p):
        raw = ((i, 1), (exchanged, 1), (n + i, 1), (n + exchanged, -1))
        col = [0] * (2 * n)
        for endpoint, sign in raw:
            col[endpoint] += sign
        # The fixed-label antisymmetric null is an actual same-parent pair.
        need(sum(map(abs, col)) == (2 if i == exchanged else 4), "column contraction")
        columns.append(tuple(col))
    return tuple(zip(*columns, strict=True))


class Stock(NamedTuple):
    cloud: Cloud
    tickets: dict[Ticket, Pair]


def initialize(v: V) -> Stock:
    cloud = tuple(
        (i, 1 if a > 0 else -1) for i, a in enumerate(v) for _ in range(abs(a))
    )
    return Stock(cloud, {(k,): pair for k, pair in enumerate(sorted(pairs(cloud)))})


def split(s: Stock, p: V, width: int, reverse: bool = False) -> Stock:
    """Route every input ticket, retaining prior heralds (blocks of width)."""
    n = len(p)
    need(all(i // width == p[i] // width for i in range(n)), "exchange moved a herald")
    cloud, routes, gain, _ = route_block(s.cloud, signed_split(p), reverse)
    need(gain == 4, "split gain")
    out = {}
    for ticket, pair in s.tickets.items():
        history = s.cloud[pair[0]][0] // width
        for seed in range(gain):
            dest = routes[pair, seed]
            need(
                cloud[dest[0]][0] % n // width == history,
                "ticket changed earlier herald",
            )
            out[(*ticket, seed)] = dest
    need(
        len(out) == len(set(out.values())) and set(out.values()) == pairs(cloud),
        "tickets do not biject onto all emitted events",
    )
    return Stock(cloud, out)


def rails(s: Stock) -> Counter[int]:
    return Counter(s.cloud[a][0] for a, _ in s.tickets.values())


def signed_vector(s: Stock, size: int) -> V:
    v = [0] * size
    for i, sign in s.cloud:
        v[i] += sign
    return tuple(v)


def prepare_rays() -> dict[tuple[int, int], V]:
    rays = {}
    for k in D:
        # edge(0), edge(1) span every integer neutral triple. On this basis
        # (I+P)x=x_k median(k); (I-P)x=(x_{k+1}-x_{k+2}) edge(k). Both
        # extend by linearity. Dividing by 2 gives complementary projectors;
        # no such division or normalization is fed into the event router.
        for basis in (edge(0), edge(1)):
            v = signed_vector(split(initialize(basis), transposition(k), 3), 6)
            need(
                v[:3] == tuple(basis[k] * z for z in median(k))
                and v[3:]
                == tuple(
                    (basis[(k + 1) % 3] - basis[(k + 2) % 3]) * z for z in edge(k)
                ),
                "neutral eigenline factorization",
            )
        prep = split(initialize(edge((k + 1) % 3)), transposition(k), 3)
        v = signed_vector(prep, 6)
        for b, direction in enumerate((median(k), edge(k))):
            branch = v[3 * b : 3 * b + 3]
            need(
                branch in (direction, tuple(-a for a in direction)),
                "not the derived eigenray",
            )
            need(
                sum(n for i, n in rails(prep).items() if i // 3 == b) == (6, 2)[b],
                "preparation herald stock",
            )
            rays[k, b] = branch
    table = []
    for label in RAYS:
        v = rays[label]
        measured = [rails(split(initialize(v), transposition(k), 3)) for k in D]
        table.append(
            tuple(
                F(sum(n for i, n in measured[k].items() if i // 3 == b), norm(v))
                for k, b in RAYS
            )
        )  # four times the conditional frequency
    first = (4, 3, 1, 0, 1, 3)
    need(
        all(
            row == tuple(first[(j - i) % 6] for j in range(6))
            for i, row in enumerate(table)
        ),
        "six-state analyzer row",
    )
    print(
        "single-packet: preparation herald stocks (+,-)=6,2 of 8; 4 × conditional rows:",
        [tuple(map(int, r)) for r in table],
    )
    return rays


def circulation() -> V:
    # Three skew edge currents u=J01, v=J12, w=J20 give row sums
    # (u-w,v-u,w-v). Thus zero divergence forces u=v=w, for every scale.
    j = tuple((0, 1, -1)[(b - a) % 3] for a in D for b in D)
    need(
        all(sum(j[3 * a : 3 * a + 3]) == 0 and sum(j[a::3]) == 0 for a in D),
        "divergence",
    )
    need(
        all(j[3 * a + b] == -j[3 * b + a] for a in D for b in D), "exchange orientation"
    )
    need(j[0] * j[4] - j[1] * j[3] == 1, "source is a product current")
    for p in permutations(D):
        transported = tuple(j[3 * p[a] + p[b]] for a in D for b in D)
        parity = (-1) ** sum(p[a] > p[b] for a in D for b in D if a < b)
        need(
            transported == tuple(parity * t for t in j), "orientation under relabeling"
        )
    return j


def local_swap(k: int, party: int, histories: int) -> V:
    p = transposition(k)
    return tuple(
        9 * h + (3 * p[a] + b if party == 0 else 3 * a + p[b])
        for h in range(histories)
        for a in D
        for b in D
    )


def analyze(
    v: V, settings: tuple[int, int], order: tuple[int, int], reverse: bool = False
) -> Stock:
    s = initialize(v)
    for stage, party in enumerate(order):
        s = split(s, local_swap(settings[party], party, 2**stage), 9, reverse)
    return s


def decode(i: int, order: tuple[int, int]) -> tuple[int, int, int]:
    first, second = i // 9 % 2, i // 18
    return (first, second, i % 9) if order == AB else (second, first, i % 9)


def freq(s: Stock, order: tuple[int, int]) -> Counter[tuple[int, int, int]]:
    return Counter({decode(i, order): n for i, n in rails(s).items()})


def branch_counts(s: Stock, order: tuple[int, int]) -> V:
    f = freq(s, order)
    return tuple(sum(f[a, b, r] for r in range(9)) for a in BITS for b in BITS)


def source_test(j: V) -> None:
    expected = {}
    matches = {}
    for order in (AB, BA):
        runs = {}
        for a, b in product(D, repeat=2):
            s = analyze(j, (a, b), order)
            counts = branch_counts(s, order)
            need(
                counts == ((0, 48, 48, 0) if a == b else (36, 12, 12, 36)),
                "joint trine law",
            )
            fine = freq(s, order)
            if order == AB:
                expected[a, b] = fine
            need(
                fine
                == expected[a, b]
                == freq(analyze(j, (a, b), order, True), order)
                == freq(analyze(tuple(-t for t in j), (a, b), order), order),
                "order/matching/orientation changed observable counts",
            )
            matches[a, b] = F(counts[0] + counts[3], sum(counts))
            outcomes = {}
            for (t, x, y), (i, _) in s.tickets.items():
                key = (
                    (t, x, y) if order == AB else (t, y, x)
                )  # fixed (source,A-seed,B-seed)
                outcomes[key] = decode(s.cloud[i][0], order)[:2]
            runs[a, b] = outcomes
        witness = None
        for party in BITS:
            for k, lo, hi in product(D, repeat=3):
                if lo >= hi:
                    continue
                u, v = ((k, lo), (k, hi)) if party == 0 else ((lo, k), (hi, k))
                changes = [t for t in runs[u] if runs[u][t][party] != runs[v][t][party]]
                if party == order[0]:
                    need(not changes, "later setting changed first outcome")
                elif changes and witness is None:
                    t = min(changes)
                    witness = (party, u, v, t, runs[u][t][party], runs[v][t][party])
        need(witness is not None, "no microscopic remote-setting witness")
        print(
            "order",
            "AB" if order == AB else "BA",
            "later-party remote-setting witness (party,settings,settings,ticket,old,new):",
            witness,
        )
    # Each local deterministic assignment satisfies the cycle bound, also with
    # imperfect same-setting anticorrelation. Positive mixtures preserve it.
    for a0, a1, a2, b0, b1, b2 in product(BITS, repeat=6):
        a, b = (a0, a1, a2), (b0, b1, b2)
        need(
            sum(a[k] == b[(k + 1) % 3] for k in D) <= 2 + sum(a[k] == b[k] for k in D),
            "local ticket bound",
        )
    score = sum(matches[k, (k + 1) % 3] - matches[k, k] for k in D)
    need(score == F(9, 4) > 2, "singlet three-setting separation")
    # Erasing orientation also erases neutrality; this control keeps the same
    # occupied input rails and tag stock, not the full preparation law.
    need(
        branch_counts(analyze(tuple(map(abs, j)), (0, 0), AB), AB) == (80, 0, 0, 16),
        "unsigned occupancy accidentally emulates the signed source",
    )
    # A genuinely neutral factorized input, with exactly the same exchanges,
    # separates the source from the apparatus; equal settings can now agree.
    need(
        branch_counts(analyze(outer(edge(0), edge(1)), (2, 2), AB), AB)
        == (36, 12, 12, 4),
        "neutral product source control",
    )
    print(
        "joint: 96/96 tickets per setting; (++,+-,-+,--) same=0,48,48,0;",
        "different=36,12,12,36; unbiased marginals; local cycle bound 2, routed",
        score,
    )


def comparator(s: Stock, histories: int) -> Stock:
    return split(
        s, tuple(9 * h + 3 * b + a for h in range(histories) for a in D for b in D), 9
    )


def comparison_rate(x: V, y: V) -> F:
    inner = sum(a * b for a, b in zip(x, y, strict=True))
    return (1 - F(inner**2, norm(x) * norm(y))) / 2


def independent_test(rays: dict[tuple[int, int], V]) -> None:
    checked = 0
    for a, b in product(D, repeat=2):
        # Two independent edge sources; both preparation heralds stay separate.
        x, y = edge((a + 1) % 3), edge((b + 1) % 3)
        prepared = analyze(outer(x, y), (a, b), AB)
        counts = rails(comparator(prepared, 4))
        bins = []
        for u, v in product(BITS, repeat=2):
            h = u + 2 * v
            both = tuple(
                sum(counts[36 * k + 9 * h + r] for r in range(9)) for k in BITS
            )
            total = sum(both)
            need(
                total == 4 * (6, 2)[u] * (6, 2)[v],
                "preparation heralds not independent",
            )
            measured = F(both[1], total)
            i, j = RAYS.index((a, u)), RAYS.index((b, v))
            need(
                measured
                == comparison_rate(rays[a, u], rays[b, v])
                == F((0, 1, 3, 4, 3, 1)[(j - i) % 6], 8),
                "conditional whole-packet comparison",
            )
            bins.append((both[1], total))
            checked += 1
        if a == b == 0:
            need(
                bins == [(0, 144), (24, 48), (24, 48), (0, 16)], "postselection control"
            )
            print(
                "independent preparations: raw antiswap clicks/issued by (++,+-,-+,--):",
                bins,
                "unselected 48/256=3/16; opposite heralds alone 48/96=1/2",
            )
    # General product formula: branch vectors are x⊗y ± y⊗x; their squared
    # norms are 2||x||²||y||² ± 2(x·y)². No target frequencies drive the split.
    for x, y in (
        ((1, 2, -3), (2, -1, -1)),
        ((1, -1, 0), (1, -1, 0)),
        ((1, 0, -1), (0, -1, 1)),
    ):
        s = comparator(initialize(outer(x, y)), 1)
        need(
            F(sum(n for i, n in rails(s).items() if i >= 9), len(s.tickets))
            == comparison_rate(x, y),
            "non-normalized product comparator",
        )
    print(
        "co-located comparator:",
        checked,
        "conditional ray pairs; cyclic click row",
        "(0,1,3,4,3,1)/8 = (1-cos Δ)/4 on these six operational directions",
    )


def global_test(j: V) -> None:
    # Cyclic relabelings on Alice versus the other coset (one transposition).
    # These are positive classical mixtures of preparations, never sums of amplitudes.
    local, clicks = [], []
    for handedness in (1, -1):
        components = [
            tuple(j[3 * ((handedness * a + k) % 3) + b] for a in D for b in D)
            for k in D
        ]
        local.append({})
        for a, b in product(D, repeat=2):
            pooled = sum(
                (freq(analyze(v, (a, b), AB), AB) for v in components), Counter()
            )
            local[-1][a, b] = pooled
            need(
                all(
                    sum(pooled[u, w, r] for r in range(9)) == 72
                    for u, w in product(BITS, repeat=2)
                ),
                "mixture product-trine marginals",
            )
        rates = []
        for v in components:
            s = comparator(initialize(v), 1)
            rates.append(
                F(sum(n for i, n in rails(s).items() if i >= 9), len(s.tickets))
            )
        clicks.append(sum(rates) / 3)
    need(
        local[0] == local[1] and clicks == [F(1, 2), F(0)], "global coordinate control"
    )
    print(
        "two 1:1:1 positive mixtures: all nine joint local trine tables equal down to rails;",
        "whole-packet antiswap rates, reflected vs unreflected: 0 vs 1/2",
    )


def quadratic_control() -> None:
    """Conditional weight rigidity on all integers (algebra; not a Lean artifact).

    Assume a nonzero identical sign-even additive per-rail law w with w(0)=0,
    and the same gain g for all neutral triples. Exchanging a,b in (a,b,-s),
    s=a+b, gives 2w(s)+w(2s)+2w(a-b)=g[w(a)+w(b)+w(s)]. Substituting b=-a
    yields w(2a)=g w(a). Eliminate w(2s), then put b=0: 4w(a)=g w(a).
    Nonzero w forces g=4. Thus w(a+b)+w(a-b)=2w(a)+2w(b). Taking b=1 gives
    constant second difference 2w(1), hence w(n)=n²w(1) by induction and
    evenness. Neither uniform gain nor additive weights follow from bare tags.
    """
    for power in (1, 2, 3):
        gains = set()
        for a, b in product(range(-4, 5), repeat=2):
            if a == b == 0:
                continue
            v = (a, b, -a - b)
            out = signed_vector(split(initialize(v), (1, 0, 2), 3), 6)
            gains.add(
                F(sum(abs(z) ** power for z in out), sum(abs(z) ** power for z in v))
            )
        need((gains == {F(4)}) if power == 2 else len(gains) > 1, "weight control")
    print(
        "conditional weight rigidity: g=4, w(n)=n²w(1); |n| and |n|³ fail constant gain"
    )


def main() -> None:
    rays = prepare_rays()
    j = circulation()
    source_test(j)
    independent_test(rays)
    global_test(j)
    quadratic_control()


if __name__ == "__main__":
    main()
