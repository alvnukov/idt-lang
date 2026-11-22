"""Lossless finite tagged-event routing with a separately propagated signed cloud.

An integer gate A with A^t A = h I supplies signed children, not a target
probability table. Match opposite children within each outgoing rail. Two
sign-reversing involutions route h seeds for every same-rail ordered live
input pair bijectively to all same-rail ordered surviving output pairs.
Addresses may coincide. This is neither blind iid sampling nor a gate on a
lone particle: the local cloud, complete matching information, uniform seeds
and access to all rails of each mixer are explicit resources.
"""

from collections import Counter, defaultdict
from itertools import product
from typing import NamedTuple

Matrix = tuple[tuple[int, ...], ...]
Cloud = tuple[tuple[int, int], ...]  # rail and sign, position is the live ID
Pair = tuple[int, int]
H: Matrix = ((1, -1, 1, 1), (1, 1, -1, 1), (1, 1, 1, -1), (-1, 1, 1, 1))
PLATE: Matrix = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, -1), (0, 0, 1, 0))


def need(b: bool, reason: str) -> None:
    if not b:
        raise AssertionError(reason)


class Child(NamedTuple):
    rail: int
    parent: int
    sign: int


def pairs(cloud: Cloud) -> set[Pair]:
    return {
        (u, v)
        for u, (i, _) in enumerate(cloud)
        for v, (j, _) in enumerate(cloud)
        if i == j
    }


def dot(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return sum(x * y for x, y in zip(a, b, strict=True))


def route_block(
    cloud: Cloud, gate: Matrix, reverse_matching: bool = False
) -> tuple[Cloud, dict[tuple[Pair, int], Pair], int, int]:
    """Build both involutions from raw gate children; never read output probabilities."""
    cols = tuple(zip(*gate, strict=True))
    gain = dot(cols[0], cols[0])
    need(gain > 0, "zero gain")
    for i, col_i in enumerate(cols):
        for j, col_j in enumerate(cols):
            need(
                dot(col_i, col_j) == (gain if i == j else 0),
                "unequal/nonorthogonal columns",
            )
    for i, _ in cloud:
        need(0 <= i < len(cols), "bad input rail")
    need(all(s in (-1, 1) for _, s in cloud), "bad sign")
    need(all(cloud[u][1] == cloud[v][1] for u, v in pairs(cloud)), "uncancelled input")
    children = [
        Child(o, u, s if row[i] > 0 else -s)
        for o, row in enumerate(gate)
        for u, (i, s) in enumerate(cloud)
        for _ in range(abs(row[i]))
    ]
    partner: dict[int, int] = {}
    columns: dict[Pair, list[Pair]] = defaultdict(list)
    for o in range(len(gate)):
        where = [a for a, child in enumerate(children) if child.rail == o]
        plus = [a for a in where if children[a].sign > 0]
        minus = [a for a in where if children[a].sign < 0]
        if reverse_matching:
            minus.reverse()
        for a, b in zip(plus, minus):
            partner[a], partner[b] = b, a
        for a, b in product(where, repeat=2):
            columns[children[a].parent, children[b].parent].append((a, b))

    alive = [a for a in range(len(children)) if a not in partner]
    rank = {a: k for k, a in enumerate(alive)}
    out = tuple((children[a].rail, children[a].sign) for a in alive)

    def r(p: Pair) -> Pair:
        a, b = p
        if a in partner:
            return partner[a], b
        return a, partner.get(b, b)

    def sign(p: Pair) -> int:
        return children[p[0]].sign * children[p[1]].sign

    c: dict[Pair, Pair] = {}
    seeds: dict[tuple[Pair, int], Pair] = {}
    for inp, choices in columns.items():
        if cloud[inp[0]][0] == cloud[inp[1]][0]:
            need(len(choices) == gain, "input pair has wrong ticket stock")
            for seed, p in enumerate(choices):
                seeds[inp, seed] = p
                c[p] = p
        else:
            positive = [p for p in choices if sign(p) > 0]
            negative = [p for p in choices if sign(p) < 0]
            if reverse_matching:
                negative.reverse()
            for p, q in zip(positive, negative, strict=True):
                c[p], c[q] = q, p

    omega = set(c)
    need(omega == {p for values in columns.values() for p in values}, "missing branch")
    for p in omega:
        for q, back in ((r(p), r(r(p))), (c[p], c[c[p]])):
            need(back == p, "not involutive")
            need(sign(p) == (1 if p == q else -sign(q)), "bad signed pairing")

    result: dict[tuple[Pair, int], Pair] = {}
    longest = 0
    path_edges = 0
    for ticket, start in seeds.items():
        p = start
        steps = 0
        while r(p) != p:
            neg = r(p)
            need(c[neg] != neg, "negative endpoint")
            p = c[neg]
            steps += 2
            need(steps < len(omega), "failed to reach a surviving output")
        end = p
        backwards = 0
        while c[p] != p:
            p = r(c[p])
            backwards += 2
            need(backwards <= steps, "inverse failed to terminate")
        need(backwards == steps, "inverse skipped edges")
        need(p == start, "reverse walk cannot recover original ticket")
        result[ticket] = rank[end[0]], rank[end[1]]
        longest = max(longest, steps)
        path_edges += steps
    need(len(result) == gain * len(pairs(cloud)), "input ticket count")
    need(set(result.values()) == pairs(out), "missed surviving output")
    need(len(set(result.values())) == len(result), "multiple tickets reach one event")
    need(
        path_edges + len(result) <= len(omega),
        "overlapping or oversized accepted paths",
    )
    return out, result, gain, longest


def run(
    cloud: Cloud, gates: tuple[Matrix, ...], reverse: bool = False
) -> tuple[int, ...]:
    tracked = Counter({p: 1 for p in pairs(cloud)})
    oracle = tuple(sum(s for j, s in cloud if i == j) for i in range(len(gates[0][0])))
    measured: tuple[int, ...] = ()
    for g in gates:
        out, routing, gain, _ = route_block(cloud, g, reverse)
        nxt: Counter[Pair] = Counter()
        for p, n in tracked.items():
            for seed in range(gain):
                nxt[routing[p, seed]] += n
        need(nxt == Counter({p: 1 for p in pairs(out)}), "emission lost or duplicated")
        oracle = tuple(dot(row, oracle) for row in g)
        counts = Counter(out[a][0] for a, _ in nxt.elements())
        measured = tuple(counts[i] for i in range(len(g)))
        need(measured == tuple(z * z for z in oracle), "external oracle")
        cloud, tracked = out, nxt
    return measured


def embedded(offset: int, bypass: int) -> Matrix:
    return tuple(
        tuple(
            H[i - offset][j - offset]
            if offset <= i < offset + 4 and offset <= j < offset + 4
            else bypass * int(i == j)
            for j in range(6)
        )
        for i in range(6)
    )


def independent_history_capture() -> tuple[int, int]:
    """Two independent raw path addresses drawn from 16 fixed histories each.

    Even an annihilated address remains in the denominator. Row cancellation
    removes a positive and a negative path at a time; surviving addresses at
    different output rails do not count as one same-rail event.
    """
    live: list[tuple[int, int]] = []
    for end in range(4):
        plus: list[tuple[int, int]] = []
        minus: list[tuple[int, int]] = []
        for middle in range(4):
            dest = plus if H[end][middle] * H[middle][0] > 0 else minus
            dest.append((middle, end))
        n = min(len(plus), len(minus))
        live.extend(plus[n:] + minus[n:])
    terminal = sum(x[1] == y[1] for x, y in product(live, repeat=2))
    every_stage = sum(x == y for x, y in product(live, repeat=2))
    need(len(live) == 4 and terminal == 16 and every_stage == 4, "raw pairing control")
    return terminal, every_stage


def main() -> None:
    initial: Cloud = ((0, 1),)
    for rev in (False, True):
        need(run(initial, (H,), rev) == (1, 1, 1, 1), "first split")
        need(run(initial, (H, H), rev) == (0, 0, 16, 0), "swap echo")
        need(run(initial, (H, PLATE, H), rev) == (4, 4, 4, 4), "quarter phase")
        # (1,1,1,-1) -> (1,1,-1,1) -> (0,4,0,0): same port, other quadrature.
        need(run(initial, (H, PLATE, PLATE, H), rev) == (0, 16, 0, 0), "half phase")
        three = run(initial, (embedded(0, 2), embedded(2, 2)), rev)
        need(
            tuple(three[i] + three[i + 1] for i in (0, 2, 4)) == (8, 4, 4),
            "three-port holdout",
        )
    cases = 0
    longest = 0
    rerouted = 0
    for amplitudes in product((-1, 0, 1), repeat=4):
        if not any(amplitudes):
            continue
        cloud = tuple((i, a) for i, a in enumerate(amplitudes) if a)
        for extra in ((), cloud):  # repeated physical IDs, including self-coincidences
            source = cloud + extra
            out, routes, _, length = route_block(source, H)
            other, r2, _, _ = route_block(source, H, True)
            need(Counter(out) == Counter(other), "matching changed output law")
            rerouted += int(
                any(out[v[0]][0] != other[r2[k][0]][0] for k, v in routes.items())
            )
            longest = max(longest, length)
            cases += 1
    need(
        rerouted > 0, "matching independence of readout was not independently exercised"
    )
    try:
        route_block(((0, 1), (4, 1)), embedded(0, 1))
    except AssertionError as e:
        need(str(e) == "unequal/nonorthogonal columns", "wrong padding diagnostic")
    else:
        raise AssertionError("unscaled bypass escaped common gain check")
    print(
        f"{cases} signed clouds, two matchings each; {rerouted} changed individual ticket destinations."
    )
    print(
        f"All routings bijective and invertible; longest observed alternating walk: {longest} edges."
    )
    print(
        "One initial pair, 4 tickets after first splitter, 16 after second; zero rejected."
    )
    terminal, every_stage = independent_history_capture()
    print(
        f"Independent raw histories: final-only capture {terminal}/256; both stages {every_stage}/256."
    )
    print(
        "Three ports with equal gain including bypass: (8,4,4)/16; unpadded bypass rejected."
    )
    print(
        "Conditional construction: signed wave cloud, addressed pairs with replacement, uniform gate seeds, local matching and clock resources supplied."
    )


if __name__ == "__main__":
    main()
