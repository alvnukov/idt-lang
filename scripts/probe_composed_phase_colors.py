"""Exact integer controls on composed, orthogonal signed phase colors.

Supplied: bilinear unital serial composition, orthogonal unit axes, and a
common-gain weight N(x)=sum(x_i**2) on signed superpositions. Serial
factorization asks for N(x*y)=N(x)N(y). A sign-sensitive comparison also
supplies common output alignment and the ability to join the two orders.
Neither preparation, factorization, alignment, nor readout is derived here.

For three orthogonal axes (1,a,b), if ab=ba and the squares have norm one,
the three sum/difference products are 1-a^2, 1-b^2 and a^2-b^2. Each asks
for squared norm 4. Writing u=1, v=a^2, w=b^2, the sum of the three squared
distances is 9-N(u+v+w) <= 9, not 12. This identity is independent of the
table enumeration. For the two-axis signed table, the first mask singles
out a^2=-1 from the four signed axes, hence Gaussian-integer multiplication
on the generated lattice.

Four-axis enumeration is restricted to the specified XOR routing; nine
nonidentity basis-product signs are free. Neither commutativity nor
associativity is assumed. Factorization residuals are homogeneous quadratic
in each input.
In each slot the unit axes and all pair sums determine such a quadratic
by polarization, so their Cartesian product suffices for this table test.
Basis triples similarly suffice to check each survivor's associator because
it is trilinear. Neither observation selects the XOR model or its rank.

This is a finite executable fixture with algebraic explanations, not a
formal proof artifact, a physical realization, a Born-rule derivation, or
a Hilbert/composite reconstruction.
"""

from collections.abc import Callable
from itertools import combinations, product

Vector = tuple[int, ...]
Pair = tuple[Vector, Vector]
Signs = tuple[int, ...]
Multiply = Callable[[Vector, Vector], Vector]


def require(condition: bool, description: str) -> None:
    if not condition:
        raise RuntimeError(description)


def add(x: Vector, y: Vector) -> Vector:
    return tuple(a + b for a, b in zip(x, y, strict=True))


def neg(x: Vector) -> Vector:
    return tuple(-a for a in x)


def sub(x: Vector, y: Vector) -> Vector:
    return add(x, neg(y))


def norm(x: Vector) -> int:
    return sum(a * a for a in x)


def basis(rank: int) -> tuple[Vector, ...]:
    return tuple(tuple(int(i == j) for j in range(rank)) for i in range(rank))


def test_vectors(units: tuple[Vector, ...]) -> tuple[Vector, ...]:
    return units + tuple(add(x, y) for x, y in combinations(units, 2))


def xor_table(rank: int, signs: Signs) -> Multiply:
    require(rank in (2, 4), "the fixture uses rank two or four")
    require(len(signs) == (rank - 1) ** 2, "wrong number of free table signs")
    require(all(s in (-1, 1) for s in signs), "basis products must be signed axes")
    table = tuple(
        tuple(
            1 if i == 0 or j == 0 else signs[(i - 1) * (rank - 1) + (j - 1)]
            for j in range(rank)
        )
        for i in range(rank)
    )

    def multiply(x: Vector, y: Vector) -> Vector:
        out = [0] * rank
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                out[i ^ j] += a * b * table[i][j]
        return tuple(out)

    return multiply


def preserves_norm(mul: Multiply, pair: Pair) -> bool:
    x, y = pair
    return norm(mul(x, y)) == norm(x) * norm(y)


def sum_difference(x: Vector, y: Vector) -> Pair:
    return add(x, y), sub(x, y)


def distance_budget() -> int:
    units = basis(4)
    signed_axes = units + tuple(neg(x) for x in units)
    u = units[0]
    masks = tuple(sum_difference(x, y) for x, y in combinations(units[:3], 2))
    target = sum(norm(x) * norm(y) for x, y in masks)
    require(target == 12, "three orthogonal masks demand total weight 12")
    largest = 0
    for v, w in product(signed_axes, repeat=2):
        distances = sum(norm(sub(x, y)) for x, y in combinations((u, v, w), 2))
        require(distances == 9 - norm(add(add(u, v), w)), "distance budget identity")
        require(distances <= 9 < target, "commuting budget cannot meet the demand")
        largest = max(largest, distances)
    require(largest == 8, "sharp maximum on signed coordinate axes")
    return largest


def rank_two_table(square: Vector) -> Multiply:
    square_real, square_axis = square

    def multiply(x: Vector, y: Vector) -> Vector:
        a, b = x
        c, d = y
        return a * c + b * d * square_real, a * d + b * c + b * d * square_axis

    return multiply


def rank_two() -> None:
    units = basis(2)
    one, a = units
    probe_vectors = test_vectors(units)
    mask = sum_difference(one, a)
    passed = []
    for square in (one, neg(one), a, neg(a)):
        mul = rank_two_table(square)
        require(mul(a, a) == square, "supplied signed square")
        require(
            preserves_norm(mul, mask) == (square == neg(one)), "single-mask selection"
        )
        count = sum(
            preserves_norm(mul, (x, y)) for x, y in product(probe_vectors, repeat=2)
        )
        if count == len(probe_vectors) ** 2:
            passed.append(square)
    require(passed == [neg(one)], "only the Gaussian-integer table should pass")


def commutes(mul: Multiply, units: tuple[Vector, ...]) -> bool:
    return all(mul(x, y) == mul(y, x) for x, y in combinations(units, 2))


def rank_four() -> tuple[dict[tuple[int, int], int], dict[int, int]]:
    units = basis(4)
    one, a, b, c = units
    probe_vectors = test_vectors(units)
    require(len(set(probe_vectors)) == 10, "four unit axes plus six distinct sums")
    masks = tuple(sum_difference(x, y) for x, y in combinations((one, a, b), 2))
    require(all(norm(x) * norm(y) == 4 for x, y in masks), "orthogonal mask gains")
    pair_support = dict.fromkeys(combinations(range(len(masks)), 2), 0)
    orientations: dict[int, int] = {}
    survivors: dict[int, Multiply] = {}
    table_count = 0
    for signs in product((-1, 1), repeat=9):
        mul = xor_table(4, signs)
        table_count += 1
        match_count = sum(
            preserves_norm(mul, (x, y)) for x, y in product(probe_vectors, repeat=2)
        )
        if commutes(mul, units):
            mask_passes = tuple(preserves_norm(mul, mask) for mask in masks)
            require(not all(mask_passes), "commuting table passed all three masks")
            for pair in pair_support:
                i, j = pair
                pair_support[pair] += int(mask_passes[i] and mask_passes[j])
            forward, reverse = mul(a, b), mul(b, a)
            require(
                norm(forward) == norm(reverse) == 1,
                "commuting individual order weights",
            )
            require(norm(add(forward, reverse)) == 4, "commuting order sum")
        if match_count == 100:
            require(not commutes(mul, units), "surviving table commutes")
            require(
                all(
                    mul(mul(x, y), z) == mul(x, mul(y, z))
                    for x, y, z in product(units, repeat=3)
                ),
                "surviving table has a basis associator",
            )
            require(all(mul(x, x) == neg(one) for x in (a, b, c)), "quaternion squares")
            orientation = mul(a, b)[3]
            require(
                orientation in (-1, 1) and orientation not in survivors, "orientation"
            )
            for x, y, z in ((a, b, c), (b, c, a), (c, a, b)):
                forward = mul(x, y)
                reverse = mul(y, x)
                signed_z = z if orientation == 1 else neg(z)
                require(
                    forward == signed_z and reverse == neg(signed_z), "quaternion cycle"
                )
                require(norm(forward) == norm(reverse) == 1, "individual order weights")
                require(norm(add(forward, reverse)) == 0, "reversed-order sum")
            orientations[orientation] = norm(add(mul(a, b), mul(b, a)))
            survivors[orientation] = mul
    require(table_count == 512, "wrong XOR-table population")
    require(set(survivors) == {-1, 1}, "expected exactly two quaternion orientations")
    require(
        all(
            survivors[-1](x, y) == survivors[1](y, x)
            for x, y in product(units, repeat=2)
        ),
        "the two tables must be opposite products",
    )
    require(all(count == 16 for count in pair_support.values()), "two-mask minimality")
    return pair_support, orientations


def boundary_controls() -> None:
    one, a = basis(2)
    split = rank_two_table(one)
    gaussian = rank_two_table(neg(one))
    plus, minus = sum_difference(one, a)
    zero = (0, 0)
    require(
        plus != zero and minus != zero and split(plus, minus) == zero,
        "split zero divisors",
    )
    require(
        norm(plus) * norm(minus) == 4,
        "split violates positive orthogonal factorization",
    )
    residues = tuple(product((0, 1), repeat=2))
    for x, y in product(residues, repeat=2):
        require(
            all(d % 2 == 0 for d in sub(split(x, y), gaussian(x, y))),
            "modulo two hides the sign-table difference",
        )
        require(
            (norm(split(x, y)) - norm(x) * norm(y)) % 2 == 0,
            "wrapped norm masks failure",
        )

    # Eisenstein multiplication in the basis 1,w with w^2=-1-w.
    def eisenstein(x: Vector, y: Vector) -> Vector:
        a, b = x
        c, d = y
        return a * c - b * d, a * d + b * c - b * d

    def hexagonal_norm(v: Vector) -> int:
        a, b = v
        return a * a - a * b + b * b

    require(hexagonal_norm(one) == hexagonal_norm(a) == 1, "Eisenstein unit lengths")
    require(
        hexagonal_norm(plus) == 1 != norm(plus), "Eisenstein axes are not orthogonal"
    )
    # These points determine the homogeneous quadratic residual in each slot.
    for x, y in product(test_vectors((one, a)), repeat=2):
        require(
            hexagonal_norm(eisenstein(x, y)) == hexagonal_norm(x) * hexagonal_norm(y),
            "Eisenstein norm factorization",
        )


def main() -> None:
    largest = distance_budget()
    rank_two()
    pair_support, orientations = rank_four()
    boundary_controls()
    print(
        f"commuting rank>=3 masks: demand 12, budget <=9 (signed-axis probe max {largest})"
    )
    print("rank 2: only a^2=-1 passes; Gaussian integers on the generated lattice")
    print(
        "rank 4 XOR: 512 sign tables x 100 pairs; 2 associative noncommuting opposite tables"
    )
    print(
        f"commuting survivors by mask pair (zero-based): {pair_support}; all three: 0"
    )
    print(
        f"per order N=1; relative N(ab+ba): {orientations} by orientation, commuting 4"
    )
    print(
        "controls: split zero divisors, mod-2 sign/failure erasure, nonorthogonal Eisenstein norm"
    )
    print(
        "finite model only; rank, serial factorization, relative alignment and readout supplied"
    )


if __name__ == "__main__":
    main()
