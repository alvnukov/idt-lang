"""Recover a coefficient-sign class by a held-out rank, without CAR as a filter.

Fix the 16 even masks and ten symmetric channel supports from the five-slot
pair probe. On each of the 40 undirected nonzero entries choose an independent
sign (fixed unit magnitude). A vertex sign acts on BOTH indices of a bilinear;
each named channel may also be rephased. The inverse question is: which signs
allow a complex linear span ("pencil") with NO rank-10 matrix? This new
selection rule is conditional, not an observed experimental law. It needs
coherent combination of channels; a charge census cannot implement it.

All three-axis tests are chosen by support alone. Doublets of reciprocal
axes have disjoint support on vertices, hence rank 16 if both coefficients
are nonzero. Every other pair splits into four two-edge stars (rank 8).
For each of the 80 triples avoiding reciprocal pairs, the graph has two
three-edge stars, two isolated vertices and a hexagon. The stars contribute
four to rank. In the hexagon the two perfect matchings each use all three
channel coefficients once. Their determinant terms have equal permutation
sign, so cancellation at (1,1,1) is cancellation for *all* nonzero complex
weights. Hexagon rank is four on cancellation and six otherwise. Thus a
rank-10 counterexample is exact over Q and C, not a finite-field artefact.

Solve the hexagon sign conditions over GF(2), not the matrix rank over GF(2).
Their rank 20 exhausts the quotient of 40 sign bits by 20 independent gauge
bits. The 20 independent triple tests span all 80 (not a claim of minimality
among arbitrary more complicated pencil tests). The alternating matching
ratio cancels individual vertex/channel phases even over U(1), so the quotient
of these SIGN assignments is not further collapsed by complex diagonal phases.
General complex edge amplitudes, support changes and arbitrary basis orbits
of nonwinning classes are not classified.

Only AFTER this inverse calculation, reconstruct the exterior witness. Its
matrix is J D_even with an invertible odd-to-even top pairing J and
D=sum_i(x_i c_i + y_i a_i) on the full space. Check every pairwise CAR
identity on all masks. Then D²=q I, q=sum_i x_i y_i. If q!=0 both parity
restrictions are invertible. If q=0 but D is nonzero, pick a reciprocal
letter H scaled by the inverse of a nonzero coefficient, so DH+HD=I.
DH has image im D and acts there as identity; it is a parity-preserving
projection. Both parity traces are eight (all distinct-slot terms have zero
trace; the occupied or vacant projector has eight on each parity). Thus
D_even has rank eight. This is an algebraic argument for arbitrary complex
coefficients, with its finite identities checked below, not a bounded grid.
In a rephased representative q has correspondingly rephased coordinates.

No spacetime spin, fermionic exchange statistics, generation count, field,
rank measurement or physical accessibility of this pencil is established.
Run: python3 -B -O -m scripts.probe_chiral_pencil_signs
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product

SLOTS = tuple(range(5))
EVEN = tuple(m for m in range(32) if m.bit_count() % 2 == 0)
AXES = tuple(product(SLOTS, (True, False)))
Axis = tuple[int, bool]
Edge = tuple[int, int, Axis]
EDGES = tuple(
    (m, n, (i, c))
    for i, c in AXES
    for m in EVEN
    if bool(m >> i & 1) != c and m < (n := m ^ 31 ^ (1 << i))
)


def need(ok: bool, msg: str) -> None:
    if not ok:
        raise ArithmeticError(msg)


def parity(x: int) -> int:
    return x.bit_count() % 2


def basis(rows: list[int]) -> dict[int, int]:
    piv: dict[int, int] = {}
    for v in rows:
        while v:
            j = v.bit_length() - 1
            if j not in piv:
                piv[j] = v
                break
            v ^= piv[j]
    return piv


def rank_q(matrix: list[list[int]]) -> int:
    a = [[Fraction(x) for x in row] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        p = next((r for r in range(rank, len(a)) if a[r][col]), None)
        if p is None:
            continue
        a[rank], a[p] = a[p], a[rank]
        for r in range(rank + 1, len(a)):
            if a[r][col]:
                c = a[r][col] / a[rank][col]
                a[r] = [x - c * y for x, y in zip(a[r], a[rank], strict=True)]
        rank += 1
    return rank


def pencil_rank(signs: int, coefficients: dict[Axis, int]) -> int:
    pos = {m: j for j, m in enumerate(EVEN)}
    a = [[0] * 16 for _ in EVEN]
    for j, (m, n, k) in enumerate(EDGES):
        a[pos[m]][pos[n]] = a[pos[n]][pos[m]] = coefficients.get(k, 0) * (
            1 - 2 * ((signs >> j) & 1)
        )
    return rank_q(a)


def gauges() -> list[int]:
    return [
        sum(1 << j for j, (a, b, _) in enumerate(EDGES) if m in (a, b)) for m in EVEN
    ] + [sum(1 << j for j, (_, _, axis) in enumerate(EDGES) if k == axis) for k in AXES]


def components(keys: tuple[Axis, ...]) -> list[dict[int, set[int]]]:
    adj: dict[int, set[int]] = {m: set() for m in EVEN}
    for a, b, k in EDGES:
        if k in keys:
            adj[a].add(b)
            adj[b].add(a)
    left = set(EVEN)
    parts: list[dict[int, set[int]]] = []
    while left:
        q = [min(left)]
        visited = set(q)
        while q:
            x = q.pop()
            for y in adj[x] - visited:
                q.append(y)
                visited.add(y)
        parts.append({m: adj[m] for m in visited})
        left -= visited
    return parts


def shape(parts: list[dict[int, set[int]]]) -> Counter[tuple[int, ...]]:
    return Counter(tuple(sorted(len(ns) for ns in part.values())) for part in parts)


def triple_checks() -> dict[tuple[Axis, ...], int]:
    """Extract the signed determinant ratio from the two hexagon matchings."""
    partners: set[frozenset[Axis]] = set()
    for k, l in combinations(AXES, 2):
        shapes = shape(components((k, l)))
        if shapes == {(1, 1): 8}:
            partners.add(frozenset((k, l)))
        else:
            need(shapes == {(1, 1, 2): 4, (0,): 4}, "distinct pair support")
    need(
        partners == {frozenset(((i, True), (i, False))) for i in SLOTS},
        "recover partners",
    )
    rows: dict[tuple[Axis, ...], int] = {}
    for keys in combinations(AXES, 3):
        if any(pair.issubset(keys) for pair in partners):
            continue
        parts = components(keys)
        need(shape(parts) == {(1, 1, 1, 3): 2, (0,): 2, (2,) * 6: 1}, "triple support")
        hexagon = next(p for p in parts if len(p) == 6)
        start = min(hexagon)
        cycle = [start, min(hexagon[start])]
        while len(cycle) < 6:
            (x,) = hexagon[cycle[-1]] - {cycle[-2]}
            cycle.append(x)
        need(len(set(cycle)) == 6 and start in hexagon[cycle[-1]], "simple hexagon")
        colored_edges = [
            (j, k) for j, (a, b, k) in enumerate(EDGES) if k in keys and a in hexagon
        ]
        ordered = [
            next(
                (j, k)
                for j, k in colored_edges
                if set(EDGES[j][:2]) == {cycle[n], cycle[(n + 1) % 6]}
            )
            for n in range(6)
        ]
        # Each of the two matchings contains each vertex once and exactly
        # one edge of each named channel: the alternating ratio is invariant
        # even under arbitrary independent nonzero complex diagonal rescalings.
        need(
            all({k for _, k in ordered[o::2]} == set(keys) for o in (0, 1)),
            "distinct determinant terms have the same channel monomial",
        )
        # For the 3x3 biadjacency block, enumerate its determinant terms,
        # confirm equal permutation signs and a 2x2 triangular minor. Hence
        # its rank is >=2 for arbitrary nonzero coefficients, not just generic.
        left, right = cycle[::2], cycle[1::2]
        perms = [
            p
            for p in permutations(range(3))
            if all(right[p[r]] in hexagon[left[r]] for r in range(3))
        ]
        det_signs = [sum(a > b for a, b in combinations(p, 2)) % 2 for p in perms]
        need(len(perms) == 2 and len(set(det_signs)) == 1, "hexagon determinant signs")
        need(
            any(
                sum(
                    all(c in hexagon[r] for c, r in zip(order, lr, strict=True))
                    for order in permutations(rr)
                )
                == 1
                for lr in combinations(left, 2)
                for rr in combinations(right, 2)
            ),
            "nonzero two by two minor",
        )
        rows[keys] = sum(1 << j for j, _ in ordered)
    need(len(EDGES) == 40 and len(rows) == 80, "support census")
    return rows


def solve(rows: list[int]) -> int:
    # Augment on the LOW bit so bit_length elimination preserves variables.
    piv = basis([(row << 1) | 1 for row in rows])
    need(0 not in piv, "inconsistent determinant requirements")
    x = 0
    for j, row in sorted(piv.items()):
        v = row >> 1
        x |= ((row & 1) ^ parity(x & v)) << (j - 1)
    need(all(parity(x & r) == 1 for r in rows), "recovered representative")
    return x


def inverse(rows: dict[tuple[Axis, ...], int]) -> tuple[int, int]:
    checks = list(rows.values())
    actions = gauges()
    need(len(basis(actions)) == len(basis(checks)) == 20, "full gauge quotient")
    need(all(not parity(v & r) for v in actions for r in checks), "gauge invariance")
    recovered = solve(checks)
    for create, rank in ((True, 5), (False, 6)):
        local = [r for keys, r in rows.items() if all(c == create for _, c in keys)]
        mask = sum(1 << j for j, (_, _, k) in enumerate(EDGES) if k[1] == create)
        need(len(local) == 10 and len(basis(local)) == rank, "pure triple tests")
        need(
            mask.bit_count() - len(basis([v & mask for v in actions])) == rank,
            "all signs within either pure support are exhausted independently",
        )
    pure = [r for ks, r in rows.items() if len({c for _, c in ks}) == 1]
    need(len(basis(pure)) == 11, "nine undetermined relative-frame signs in quotient")
    # Change a single state sign in just the creation half. Pure pencils
    # stay equivalent for ALL coefficients, but a mixed triple can see it.
    plus = sum(1 << j for j, (_, _, k) in enumerate(EDGES) if k[1])
    delta = actions[EVEN.index(0b00011)] & plus
    need(delta.bit_count() == 3, "partial state rephasing on three edges")
    rival = recovered ^ delta
    need(all(parity(rival & r) for r in pure), "pure-passing mixed rival")
    witness = ((0, True), (1, False), (2, True))
    need(
        not parity(rival & rows[witness])
        and pencil_rank(rival, dict.fromkeys(witness, 1)) == 10
        and pencil_rank(recovered, dict.fromkeys(witness, 1)) == 8,
        "constructive mixed rank-ten witness",
    )
    return recovered, rival


def step(m: int, k: Axis) -> tuple[int, int] | None:
    i, create = k
    if bool(m >> i & 1) == create:
        return None
    return m ^ (1 << i), 1 - 2 * parity(m & ((1 << i) - 1))


def exterior_witness() -> int:
    def entry(a: int, b: int, k: Axis) -> int:
        act = step(b, k)
        if act is None or act[0] != 31 ^ a:
            return 0
        m, s = act
        n = a.bit_count()
        crossings = sum((m & ((1 << j) - 1)).bit_count() for j in SLOTS if a >> j & 1)
        return s * (1 - 2 * ((n * (n - 1) // 2 + crossings) % 2))

    # J[a,m] is a signed permutation pairing a with its odd complement.
    # Check the full support (including actual zeros) as well as symmetry.
    indexes = {(a, b, k): j for j, (a, b, k) in enumerate(EDGES)}
    signs = 0
    for a, b, k in product(EVEN, EVEN, AXES):
        s = entry(a, b, k)
        j = indexes.get((min(a, b), max(a, b), k))
        need(bool(s) == (j is not None) and s == entry(b, a, k), "top CAR witness")
        if s < 0 and j is not None:
            signs |= 1 << j
    return signs


def car_certificate() -> None:
    def compose(m: int, k: Axis, l: Axis) -> tuple[int, int] | None:
        u = step(m, l)
        if u is None:
            return None
        v = step(u[0], k)
        return None if v is None else (v[0], v[1] * u[1])

    for k, l in product(AXES, repeat=2):
        dual = int(k[0] == l[0] and k[1] != l[1])
        traces = [0, 0]
        for m in range(32):
            kl, lk = compose(m, k, l), compose(m, l, k)
            if kl is not None and kl[0] == m:
                traces[parity(m)] += kl[1]
            column: Counter[int] = Counter()
            for act in (kl, lk):
                if act is not None:
                    column[act[0]] += act[1]
            need(
                {n: s for n, s in column.items() if s} == ({m: 1} if dual else {}),
                "full CAR anticommutator",
            )
        need(traces == [8 * dual, 8 * dual], "parity-specific trace of each product")


def main() -> None:
    rows = triple_checks()
    recovered, rival = inverse(rows)
    car = exterior_witness()
    need(all(parity(car & r) == 1 for r in rows.values()), "exterior is a solution")
    need(len(basis([*gauges(), car ^ recovered])) == 20, "same signed gauge orbit")
    car_certificate()
    need(pencil_rank(car, {}) == 0, "zero pencil element")
    for signs, expected_prefix in ((car, [8, 8, 8, 8, 8]), (0, [8, 8, 10, 10, 12])):
        need(
            [pencil_rank(signs, {(i, True): 1 for i in range(n)}) for n in range(1, 6)]
            == expected_prefix,
            "one-orientation prefixes",
        )
    # Explicit rational ranks independently check the graph formula across
    # all triples for the recovered, unsigned and mixed-rival assignments.
    for keys, row in rows.items():
        coeffs = dict(zip(keys, (2, -3, 5), strict=True))
        for signs in (recovered, 0, rival):
            need(
                pencil_rank(signs, coeffs) == (8 if parity(signs & row) else 10),
                "exact triple rank",
            )
    unit = dict(zip(AXES, (1, 2, 3, -1, -2, 3, 0, 1, 1, 7), strict=True))
    for y, expected in ((0, 16), (6, 16), (7, 8)):
        unit[4, False] = y
        q = sum(unit[i, True] * unit[i, False] for i in SLOTS)
        need(
            (q != 0) == (expected == 16) and pencil_rank(car, unit) == expected,
            "mixed complex-locus rational control",
        )
    print(
        "40 sign bits, 20 gauge bits: 1,048,576 diagonal sign classes on the supplied support."
    )
    print(
        "80 rank tests, 20 independent hexagons: exactly one class has no rank 10 in its complex pencil."
    )
    print(
        "Creation-only leaves 32,768 classes; both pure pencils leave 512. Flip creation edges at mask 00011: c0+a1+c2 rank 8 -> 10."
    )
    print(
        "Recovered class equals the exterior witness; complex ranks 0, 8, 16 only. No physical rank law established."
    )


if __name__ == "__main__":
    main()
