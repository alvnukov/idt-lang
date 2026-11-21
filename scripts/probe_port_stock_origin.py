"""Raw two-port stocks, without a supplied metric or a polynomial fit.

Inputs: an additive rank-two integer lattice, J²=-I, the supplied raw mixer
M with diagonal blocks A=I+J and off-diagonal blocks B=I-J, a universal gain
h>0, and separate nonnegative port stocks vanishing at zero, not both zero.
This executable checks finite consequences and controls, not physical laws or
a machine proof of the universal statement. Run: python3 -O -m scripts.probe_port_stock_origin
"""

from collections import Counter
from collections.abc import Iterable
from itertools import product
from math import comb
from typing import NamedTuple

Vec = tuple[int, int]
Ports = tuple[Vec, Vec]
ZERO: Vec = (0, 0)


def check(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def add(x: Vec, y: Vec) -> Vec:
    return x[0] + y[0], x[1] + y[1]


def scale(k: int, x: Vec) -> Vec:
    return k * x[0], k * x[1]


def det(x: Vec, y: Vec) -> int:
    return x[0] * y[1] - x[1] * y[0]


class Quarter(NamedTuple):
    a: int
    b: int
    c: int

    def j(self, x: Vec) -> Vec:
        a, b, c = self
        return a * x[0] + b * x[1], c * x[0] - a * x[1]

    def branch(self, x: Vec, cross: bool) -> Vec:
        return add(x, scale(-1 if cross else 1, self.j(x)))

    def mix(self, x: Vec, y: Vec) -> Ports:
        return (
            add(self.branch(x, False), self.branch(y, True)),
            add(self.branch(x, True), self.branch(y, False)),
        )

    def stock(self, x: Vec) -> int:
        # For nonzero x this is the sublattice index [Z² : Zx + ZJx].
        return abs(det(x, self.j(x)))


def grid(radius: int) -> list[Vec]:
    return [
        (x, y) for x in range(-radius, radius + 1) for y in range(-radius, radius + 1)
    ]


def rank_mod_101(rows: Iterable[dict[int, int]]) -> int:
    """A nonzero minor mod 101 gives at least the same rank over Q and R."""
    basis: dict[int, dict[int, int]] = {}
    for source in rows:
        row = {i: v % 101 for i, v in source.items() if v % 101}
        while row:
            i = min(row)
            coeff = row[i]
            if i not in basis:
                inv = pow(coeff, -1, 101)
                basis[i] = {j: v * inv % 101 for j, v in row.items()}
                break
            for j, v in basis[i].items():
                entry = (row.get(j, 0) - coeff * v) % 101
                if entry:
                    row[j] = entry
                else:
                    row.pop(j, None)
    return len(basis)


def orbit_check(root: Quarter) -> None:
    """Independently replay the four choices; compare with the binomial kernel."""
    x: Vec = (1, 0)
    phases = [x]
    for _ in range(3):
        phases.append(root.j(phases[-1]))
    check(len(set(phases)) == 4 and root.j(phases[-1]) == x, "quarter orbit")
    # M²=4*swap on generators => W_p(4x)=h² W_other(x).
    for v in ((1, 0), (0, 1)):
        for pair in ((v, ZERO), (ZERO, v)):
            check(
                root.mix(*root.mix(*pair)) == (scale(4, pair[1]), scale(4, pair[0])),
                "raw square",
            )
    rows: list[dict[int, int]] = []
    for p, j in product(range(2), range(4)):
        replay: Counter[int] = Counter()
        for word in product((0, 1), repeat=4):
            w, port = phases[j], p
            for cross in word:
                w = root.branch(w, bool(cross))
                port ^= cross
            check(w[0] % 4 == w[1] % 4 == 0, "four-step divisibility")
            phase = phases.index((w[0] // 4, w[1] // 4))
            replay[4 * (port ^ 1) + phase] += 1
        predicted: Counter[int] = Counter()
        for k in range(5):
            target = 4 * (p ^ (k % 2) ^ 1) + (j + 2 + 3 * k) % 4
            predicted[target] += comb(4, k)
        check(replay == predicted, "four actual branch moves vs orbit identity")
        rows.append(dict(replay))
    check(all(sum(row.values()) == 16 for row in rows), "orbit row sums")
    check(
        all(sum(row.get(j, 0) for row in rows) == 16 for j in range(8)),
        "orbit column sums",
    )
    # h²*w=K*w and some orbit has positive total -> h²=16, then h=4.
    seen = {0}
    for _ in range(7):
        seen |= {j for i in seen for j in rows[i]}
    check(seen == set(range(8)), "orbit is connected")
    harmonic = [
        {j: 16 * int(i == j) - row.get(j, 0) for j in range(8)}
        for i, row in enumerate(rows)
    ]
    check(
        rank_mod_101(harmonic) == 7, "constant is the only harmonic port/phase vector"
    )


def inverse_check(root: Quarter) -> tuple[int, int, int]:
    """Unknown W_p(z) per actual argument touched, including all output-only z."""
    labels: dict[tuple[int, Vec], int] = {}
    witness: list[int] = []
    rows: list[dict[int, int]] = []
    for x, y in product(grid(2), repeat=2):
        u, v = root.mix(x, y)
        row: Counter[int] = Counter()
        for port, z, coef in ((0, x, -4), (1, y, -4), (0, u, 1), (1, v, 1)):
            if z == ZERO:
                continue  # separate vacuum conditions only
            label = port, z
            if label not in labels:
                labels[label] = len(witness)
                witness.append(root.stock(z))
            row[labels[label]] += coef
        rows.append(dict(row))
    check(any(witness), "nonzero candidate")
    check(
        all(sum(c * witness[i] for i, c in row.items()) == 0 for row in rows),
        "integer null witness",
    )
    rank = rank_mod_101(rows)
    check(
        rank == len(labels) - 1,
        "raw equations must leave exactly one stock scale on these arguments",
    )
    return len(rows), len(labels), rank


def shortest_check(root: Quarter) -> None:
    a, b, c = root
    check(a * a + b * c == -1, "not a quarter turn")
    # |c|Q(x,y)=(cx-ay)^2+y^2; Q(1,0)=|c| bounds this entire shortest-vector search.
    box = [
        (x, y)
        for x in range(-abs(a) - 1, abs(a) + 2)
        for y in range(-abs(c), abs(c) + 1)
        if (x, y) != ZERO
    ]
    v = min(box, key=root.stock)
    jv = root.j(v)
    unit = det(v, jv)
    check(abs(unit) == 1, "shortest cyclic basis is not unimodular")
    for z in grid(2):
        check(
            abs(c) * root.stock(z) == (c * z[0] - a * z[1]) ** 2 + z[1] ** 2,
            "search certificate",
        )
        m, n = det(z, jv) // unit, det(v, z) // unit
        check(
            add(scale(m, v), scale(n, jv)) == z and root.stock(z) == m * m + n * n,
            "reduced lattice stock",
        )
    for x, y in product(grid(1), repeat=2):
        u, w = root.mix(x, y)
        check(
            root.stock(u) + root.stock(w) == 4 * (root.stock(x) + root.stock(y)),
            "sheared stock gain",
        )


def gamma(root: Quarter, pair: Ports) -> int:
    """Context multiplier invariant under M because M^4 is scalar dilation."""
    for _ in range(4):
        if ZERO in pair:
            return 2
        pair = root.mix(*pair)
    return 1


def controls(root: Quarter) -> None:
    def contextual(pair: Ports) -> tuple[int, int]:
        multiplier = gamma(root, pair)
        return multiplier * root.stock(pair[0]), multiplier * root.stock(pair[1])

    def rank_four(x: Vec, z: Vec, weight: int) -> int:
        return root.stock(x) + weight * root.stock(z)

    for x, y in product(grid(1), repeat=2):
        pair = x, y
        out = root.mix(x, y)
        check(gamma(root, out) == gamma(root, pair), "context gain is orbit invariant")
        sx, sy = root.stock(x), root.stock(y)
        cx, cy = contextual(pair)
        check(sum(contextual(out)) == 4 * (cx + cy), "contextual stock gain")
        if sx + sy:
            check(
                cx * (sx + sy) == sx * (cx + cy),
                "contextual normalized share",
            )
    v: Vec = (1, 0)
    check(
        gamma(root, (v, v)) == 1
        and gamma(root, (v, ZERO)) == gamma(root, (ZERO, v)) == 2,
        "axes vs pair",
    )
    check(
        sum(contextual((v, v)))
        != sum(contextual((v, ZERO))) + sum(contextual((ZERO, v))),
        "axis sums fail for contextual stock",
    )

    # Two independent copies make the port rank four. A spectator may be invisible,
    # or a distinct positive scale can survive; both satisfy the SAME gain.
    for x, y, z, w in product((ZERO, (1, 0), (0, 1)), repeat=4):
        u, v1 = root.mix(x, y)
        s, t = root.mix(z, w)
        for weight in (0, 1, 2):
            before = rank_four(x, z, weight) + rank_four(y, w, weight)
            after = rank_four(u, s, weight) + rank_four(v1, t, weight)
            check(after == 4 * before, "rank-four independent weights")
    check(
        [rank_four(ZERO, v, k) for k in (0, 1, 2)]
        == [0, root.stock(v), 2 * root.stock(v)]
        and root.stock(v) > 0,
        "spectator distinguishes zero and two positive weights",
    )


def main() -> None:
    standard = Quarter(0, -1, 1)
    roots = (standard, Quarter(1, -2, 1), Quarter(3, -10, 1), Quarter(7, 5, -10))
    for root in roots:
        orbit_check(root)
        shortest_check(root)
    counts = inverse_check(standard)
    check(counts == (625, 184, 183), "unexpected inverse dimensions")
    controls(standard)
    print(
        "Four raw branch steps: all 8 port/phase states connected, harmonic rank 7; positive orbit sum forces gain 4."
    )
    print(
        "625 raw equations, 184 independent port values, exact rank 183: one stock scale on the touched states."
    )
    print(
        "Four integral charts: the subgroup index |det(x,Jx)| becomes m²+n² in a shortest cyclic basis."
    )
    print(
        "Contextual multiplier preserves gain and normalized shares but fails port additivity."
    )
    print(
        "Rank four admits independent weights, including an invisible spectator. No physical readout is derived."
    )


if __name__ == "__main__":
    main()
