"""Joint selection of a minimal raw mixer and a separable nonnegative stock.

This is a conditional research probe; the universal argument is in
ROUTED_EVENT_CANDIDATE.md. The finite inverse check below does not assume the
four rail functions agree, are even, or are polynomials. It solves for all
their positive AND negative arguments independently (overdetermined equations
with an exact modular rank certificate and a rational null witness).
"""

from collections import Counter
from collections.abc import Callable, Iterable, Iterator
from itertools import combinations, product
from math import gcd

Vector = tuple[int, ...]
Matrix = tuple[Vector, ...]
Stock = Callable[[Vector], int]


def require(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


def table(a: int, b: int, c: int) -> Matrix:
    require(a * a + b * c == -1, "not an integral quarter-turn")
    j = ((a, b), (c, -a))
    return tuple(
        tuple(
            int(i % 2 == k % 2) + (1 if i // 2 == k // 2 else -1) * j[i % 2][k % 2]
            for k in range(4)
        )
        for i in range(4)
    )


def act(m: Matrix, q: Vector) -> Vector:
    return tuple(sum(a * b for a, b in zip(row, q, strict=True)) for row in m)


def norm(q: Vector) -> int:
    return sum(x * x for x in q)


def sources(radius: int) -> Iterator[Vector]:
    for i in range(4):
        for n in range(-radius, radius + 1):
            if n:
                yield tuple(n * int(i == j) for j in range(4))
    for i, k in combinations(range(4), 2):
        for x in range(-radius, radius + 1):
            for y in (-1, 1):
                if x:
                    yield tuple(x * int(i == j) + y * int(k == j) for j in range(4))


def equations(m: Matrix, radius: int) -> Iterator[Vector]:
    labels = [(j, x) for j in range(4) for x in range(-radius, radius + 1) if x]
    for q in sources(radius):
        out = act(m, q)
        if max(map(abs, out)) > radius:
            continue
        row = Counter(enumerate(out))
        row.subtract({(i, n): 4 for i, n in enumerate(q)})
        yield tuple(row[label] for label in labels)


def modular_rank(rows: Iterable[Vector], prime: int = 101) -> int:
    pivots: dict[int, list[int]] = {}
    for row in rows:
        x = [v % prime for v in row]
        for i, v in enumerate(x):
            if v == 0:
                continue
            if i not in pivots:
                inv = pow(v, -1, prime)
                pivots[i] = [w * inv % prime for w in x]
                break
            saved = pivots[i]
            for k in range(i, len(x)):
                x[k] = (x[k] - v * saved[k]) % prime
    return len(pivots)


def homogeneous(stock: Stock, m: Matrix, inputs: Iterable[Vector], gain: int) -> bool:
    return all(stock(act(m, q)) == gain * stock(q) for q in inputs)


def periodic_controls() -> None:
    # In the putative sheared case nonnegative stocks would be periodic.
    # Fix any input coordinate and uniformly average the remaining three:
    # each output coordinate is uniform modulo an odd period, even when an
    # individual matrix entry vanishes modulo that period. Multiplicity, not
    # independence between distinct output coordinates, is what we check.
    cases = 0
    for a in range(-7, 8):
        if not a:
            continue
        t = 1 + a * a
        for b in range(-t, t + 1):
            if not b or t % b:
                continue
            rows = table(a, b, -t // b)
            for row in rows:
                for ignore in range(4):
                    coeffs = row[:ignore] + row[ignore + 1 :]
                    require(2 % gcd(*coeffs) == 0, "conditional gcd")
                    for m in (3, 5, 9, 15, 25):
                        require(gcd(m, *coeffs) == 1, "odd-period averaging")
                    cases += 1
    for mod in (5, 15):
        for row in table(2, -5, 1):
            for j in range(4):
                v = row[:j] + row[j + 1 :]
                counts = Counter(
                    (v[0] * x + v[1] * y + v[2] * z) % mod
                    for x, y, z in product(range(mod), repeat=3)
                )
                require(
                    len(counts) == mod and set(counts.values()) == {mod**2},
                    "explicit residue average",
                )
    # A supplied periodic function invariant under doubling descends to the odd part.
    for period in (8, 30, 60):
        odd = period
        while odd % 2 == 0:
            odd //= 2
        w = [int(gcd(n, odd) > 1) for n in range(period)]
        require(
            all(
                w[n] == w[(2 * n) % period] == w[(n + odd) % period]
                for n in range(period)
            ),
            "odd part reduction",
        )
    # Symmetric calibration alone misses an actual periodic response.
    blind = table(7, 5, -10)

    def residue_stock(q: Vector) -> int:
        return sum(int(n % 5 != 0) for n in q)

    for x, y in product(range(5), repeat=2):
        for sign in (-1, 1):
            q = (x, y, sign * x, sign * y)
            require(
                residue_stock(act(blind, q)) == residue_stock(q),
                "mod-five symmetric control",
            )
    require(
        residue_stock(act(blind, (1, 0, 0, 0))) == 2,
        "single-port mod-five discriminator",
    )
    print(
        f"{cases} possible missing-coordinate gcds tested; odd-modulus averages uniform even with vanishing coefficients."
    )


def main() -> None:
    r = 10
    points = list(product(range(-2, 3), repeat=4))
    for j, m in enumerate((table(0, -1, 1), table(0, 1, -1))):
        for q in points:
            require(act(m, act(m, q)) == tuple(4 * x for x in q[2:] + q[:2]), "square")
        rows = list(equations(m, r))
        witness = [n * n for _ in range(4) for n in range(-r, r + 1) if n]
        require(
            all(
                sum(x * y for x, y in zip(row, witness, strict=True)) == 0
                for row in rows
            ),
            "rational null vector",
        )
        rank = modular_rank(rows)
        require(rank == len(witness) - 1, "unexpected other rail response")
        print(
            f"Orientation {j}: {len(rows)} equations, {len(witness)} unknown stocks, rank {rank}; only a multiple of n^2."
        )
        require(homogeneous(norm, m, points, 4), "four-rail holdout")
        require(
            homogeneous(lambda q: norm(q) ** 2, m, points, 16), "global quartic control"
        )
        require(
            not homogeneous(lambda q: sum(x**4 for x in q), m, points, 4),
            "separable quartic should fail",
        )
        require(
            not homogeneous(lambda q: sum(abs(x) for x in q), m, points, 4),
            "linear count should fail",
        )

    # Integral shear P=[[1,1],[0,1]] of the internal frame. PJP^-1 has
    # (a,b,c)=(1,-2,1). The positive alternative cost couples raw rail pairs.
    crooked = table(1, -2, 1)

    def sheared(q: Vector) -> int:
        x, y, z, w = q
        return (x - y) ** 2 + y * y + (z - w) ** 2 + w * w

    require(homogeneous(sheared, crooked, points, 4), "mixed stock forgery")
    require(not homogeneous(norm, crooked, points, 4), "ordinary stock should separate")
    require(homogeneous(sum, crooked, points, 2), "signed linear control at gain two")
    for root in (crooked, table(0, -1, 1)):

        def two_times(q: Vector, gate: Matrix = root) -> int:
            return 2 * sum(map(abs, q)) + sum(map(abs, act(gate, q)))

        require(
            homogeneous(two_times, root, points, 2), "two-time positive nonsquare stock"
        )
        require(
            two_times((1, 1, 0, 0))
            != two_times((1, 0, 0, 0)) + two_times((0, 1, 0, 0)),
            "two-time nonseparability",
        )
    require(
        sheared((1, 1, 0, 0)) != sheared((1, 0, 0, 0)) + sheared((0, 1, 0, 0)),
        "internal cross term",
    )

    # Quantify the cost of restricting a square readout to a *bounded* prefix.
    def tail(q: Vector) -> int:
        return sum(x * x + int(abs(x) > r) for x in q)

    m = table(0, -1, 1)
    require(
        all(
            tail(act(m, q)) == 4 * tail(q)
            for q in sources(r)
            if max(map(abs, act(m, q))) <= r
        ),
        "finite lookup control",
    )
    require(not homogeneous(tail, m, [(r, 1, 0, 0)], 4), "first unseen rail amplitude")
    periodic_controls()
    print(
        "625 four-rail holdouts per orientation. Departures: coherent shear, global quartic, and prefix-only decoder."
    )
    print(
        "No probability, address pairing, equal ticket sampling, laboratory detector, or physical swap law inferred."
    )


if __name__ == "__main__":
    main()
