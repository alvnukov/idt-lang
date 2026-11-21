"""What transparent square-swap selects on a supplied signed-token lattice.

A context-independent substitution of a positive token specifies one integer
column of M: concatenation adds counts, and cancelling an input pair must not
change the output net counts, so a negative token has the opposite column.
These are model assumptions, not deductions about physical events.

For d>0 internal rails and a positive integer amplitude scale r (tag gain
r² when the metric law holds), impose M²=r²S and M(x,x)=r(x,x). The RAW
square is not S unless r=1. Only T=M/r is a normalized transparent swap root.
Proofs/QMClosure/TransparentSwapRoot.lean already proves normalized additive
reconstruction on its specified carrier, and gives the nontransparent natural
routing counterexample. The following integer refinement is elementary:

M commutes with its square, hence with S. Its blocks are [A B; B A],
A+B=rI. On differences C=A-B=2A-rI has C²=-r²I. Expanding gives
2A²-2rA+r²I=0, whose diagonal modulo 2 forces r even. Determinants give
det(C/r)²=(-1)^d, forcing d even. Thus r=d=2 is the first possible pair;
J=A-I then satisfies J²=-I. The additional uniform tag law MᵗM=4I
imposes JᵗJ=I on differences; every integer unit column is a signed basis
vector. Exhausting those columns is a classification, not a search cutoff.

For N paired ports, consider ALL embeddings of ONE oriented normalized table
with identity bypass. Squared gates swap ports; the processed matrices are
real and the calculations below use integers with denominators kept outside.
The construction selects a quarter-turn on port differences, not on uniform
inputs. No gate laws, metric, density, detector, or physical complex scalar
field are derived. The N=2..5 commutant calculations are finite checks.

Run: python3 -O -m scripts.probe_raw_gate_reconstruction
"""

import sys
from collections.abc import Callable, Iterable, Iterator
from itertools import combinations, permutations, product
from math import gcd
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_cancellation_event_router import H, Matrix, need

Vector = tuple[int, ...]


def matrix(n: int, f: Callable[[int, int], int]) -> Matrix:
    return tuple(tuple(f(i, j) for j in range(n)) for i in range(n))


def eye(n: int) -> Matrix:
    return matrix(n, lambda i, j: int(i == j))


def tr(a: Matrix) -> Matrix:
    return tuple(zip(*a, strict=True))


def scale(k: int, a: Matrix) -> Matrix:
    return tuple(tuple(k * x for x in row) for row in a)


def plus(a: Matrix, b: Matrix, sign: int = 1) -> Matrix:
    return matrix(len(a), lambda i, j: a[i][j] + sign * b[i][j])


def mul(a: Matrix, b: Matrix) -> Matrix:
    cols = tr(b)
    return tuple(
        tuple(sum(x * y for x, y in zip(row, col, strict=True)) for col in cols)
        for row in a
    )


def commutes(a: Matrix, b: Matrix) -> bool:
    return mul(a, b) == mul(b, a)


def wires(order: tuple[int, ...]) -> Matrix:
    return matrix(len(order), lambda i, j: int(order[i] == j))


def from_turn(j: Matrix) -> Matrix:
    a, b = plus(eye(2), j), plus(eye(2), j, -1)
    return matrix(4, lambda u, v: (a if u // 2 == v // 2 else b)[u % 2][v % 2])


def raw_selection() -> tuple[Matrix, Matrix]:
    ident, swap = eye(2), wires((2, 3, 0, 1))
    expected_square = scale(4, swap)
    diagonal: Matrix = ((1, 0), (0, 1), (1, 0), (0, 1))
    turns = [
        tuple(tuple(signs[j] * int(p[j] == i) for j in range(2)) for i in range(2))
        for p in permutations(range(2))
        for signs in product((-1, 1), repeat=2)
    ]
    selected = [j for j in turns if mul(j, j) == scale(-1, ident)]
    need(len(turns) == 8 and len(selected) == 2, "complete signed-permutation class")
    j: Matrix = ((0, -1), (1, 0))
    need(set(selected) == {j, scale(-1, j)}, "the two orientations")
    h = from_turn(j)
    reflect: Matrix = ((1, 0), (0, -1))
    need(mul(mul(reflect, j), reflect) == scale(-1, j), "rail-sign conjugacy")
    need(h == H and from_turn(scale(-1, j)) == tr(h), "compare existing router tables")
    # A non-orthogonal integral change of basis retains both structural laws.
    shear: Matrix = ((1, 1), (0, 1))
    undo: Matrix = ((1, -1), (0, 1))
    crooked = from_turn(mul(mul(shear, j), undo))
    for a in (h, tr(h), crooked):
        need(mul(a, a) == expected_square, "raw square = 4*S")
        need(mul(a, diagonal) == scale(2, diagonal), "raw diagonal gain = 2")
        need(commutes(a, swap), "swap commutation")
    need(mul(tr(h), h) == scale(4, eye(4)), "uniform stock")
    gram = mul(tr(crooked), crooked)
    need(len({gram[i][i] for i in range(4)}) > 1, "unequal single-rail stocks")
    routing = wires((1, 2, 3, 0))
    need(mul(routing, routing) == swap and mul(tr(routing), routing) == eye(4), "r=1")
    need(mul(routing, diagonal) != diagonal, "r=1 square root is not transparent")
    return h, j


def embed(n: int, pair: tuple[int, int], h: Matrix) -> Matrix:
    ix = {2 * p + t: 2 * k + t for k, p in enumerate(pair) for t in range(2)}
    return matrix(
        2 * n,
        lambda i, j: h[ix[i]][ix[j]] if i in ix and j in ix else 2 * int(i == j),
    )


def rank(rows: Iterable[Vector]) -> int:
    """Exact streaming Gaussian elimination over Q, using primitive integer rows."""
    pivots: dict[int, Vector] = {}
    for src in rows:
        row = src
        while any(row):
            col = next(i for i, x in enumerate(row) if x)
            if col not in pivots:
                pivots[col] = row
                break
            p = pivots[col]
            a, b = p[col], row[col]
            nxt = tuple(a * x - b * y for x, y in zip(row, p, strict=True))
            g = gcd(*nxt) or 1
            row = tuple(x // g for x in nxt)
    return len(pivots)


def commutator_rows(gates: Iterable[Matrix]) -> Iterator[Vector]:
    """Coefficients of every (XG-GX)[i,j] in row-major unknowns X."""
    for g in gates:
        m = len(g)
        for i, j in product(range(m), repeat=2):
            row = [0] * (m * m)
            for k in range(m):
                row[m * i + k] += g[k][j]
                row[m * k + j] -= g[i][k]
            yield tuple(row)


def fixed_rows(gates: Iterable[Matrix]) -> Iterator[Vector]:
    for twice_t in gates:
        yield from plus(twice_t, scale(-2, eye(len(twice_t))))


def port_classes(squares: list[Matrix]) -> set[frozenset[int]]:
    """Unlabelled squared-gate family: group addresses by moved/not-moved profile."""
    signatures: dict[tuple[bool, ...], set[int]] = {}
    for i in range(len(squares[0])):
        key = tuple(square[i][i] == 0 for square in squares)
        signatures.setdefault(key, set()).add(i)
    return {frozenset(rails) for rails in signatures.values()}


def network(n: int, h: Matrix, j: Matrix, expected_rank: int) -> None:
    m = 2 * n
    pairings = list(combinations(range(n), 2))
    gates = [embed(n, pair, h) for pair in pairings]  # twice each normalized gate
    squares = [mul(g, g) for g in gates]
    for (u, v), g, g2 in zip(pairings, gates, squares, strict=True):
        mapping = {u: v, v: u}
        order = tuple(2 * mapping.get(i // 2, i // 2) + i % 2 for i in range(m))
        need(g2 == scale(4, wires(order)), "square identifies an ordinary port swap")
        need(mul(tr(g), g) == scale(4, eye(m)), "transpose is scaled inverse")
    # Hide the supplied port order before recovering the rail partition.
    new_order = tuple(range(1, m, 2)) + tuple(reversed(range(0, m, 2)))
    scramble = wires(new_order)
    classes = port_classes([mul(mul(scramble, s), tr(scramble)) for s in squares])
    planted = {
        frozenset((new_order.index(2 * p), new_order.index(2 * p + 1)))
        for p in range(n)
    }
    need(
        classes == (planted if n >= 3 else {frozenset(range(m))}),
        "port identifiability",
    )

    # D/(2N) = sum(T-T^-1)/N. P/N projects off the two uniform modes.
    d = scale(0, eye(m))
    for g in gates:
        d = plus(d, plus(g, tr(g), -1))
    p = matrix(m, lambda u, v: (n * int(u // 2 == v // 2) - 1) * int(u % 2 == v % 2))
    j_all = matrix(m, lambda u, v: int(u // 2 == v // 2) * j[u % 2][v % 2])
    need(mul(p, p) == scale(n, p), "centered projection")
    need(d == scale(2, mul(j_all, p)), "oriented centered reconstruction")
    need(mul(d, d) == scale(-4 * n, p), "J_center² = -P_center")
    need(all(commutes(d, g) for g in gates), "common centered quarter-turn")
    need(rank(d) == m - 2, "quarter-turn kernel = uniform plane")
    # Extend by +/- the same quarter-turn on the invisible uniform plane.
    # Both extensions scaled by N; the observable centered term is unchanged.
    uniform_turn = mul(j_all, plus(scale(n, eye(m)), p, -1))
    centered_turn = mul(j_all, p)
    for sign in (-1, 1):
        ext = plus(centered_turn, uniform_turn, sign)
        need(mul(ext, ext) == scale(-n * n, eye(m)), "distinct global extensions")
        need(mul(ext, p) == scale(n, centered_turn), "same centered restriction")
        need(all(commutes(ext, g) for g in gates), "invisible extension")
    need(rank(uniform_turn) == 2, "extensions differ on uniform plane")
    # Transposing all gates leaves all squares intact and reverses the turn.
    need(
        all(mul(tr(g), tr(g)) == s for g, s in zip(gates, squares, strict=True)),
        "inverse squares",
    )
    inverse_d = scale(0, eye(m))
    for g in gates:
        inverse_d = plus(inverse_d, plus(tr(g), g, -1))
    need(inverse_d == scale(-1, d), "orientation is not fixed by squares")

    commute_rank = rank(commutator_rows(gates))
    fixed_dim = m - rank(fixed_rows(gates))
    need(
        (commute_rank, fixed_dim) == (expected_rank, 2),
        "finite commutant and fixed space",
    )

    # Four maps R²→R² on the uniform plane and two centered directions:
    # independence plus the measured nullity rules out additional directions.
    def uniform_unit(a: int, b: int) -> Matrix:
        return matrix(m, lambda i, k: int(i % 2 == a and k % 2 == b))

    basis = [uniform_unit(a, b) for a, b in product(range(2), repeat=2)] + [p, d]
    need(all(commutes(x, g) for x in basis for g in gates), "commutant witnesses")
    need(
        rank(tuple(v for row in x for v in row) for x in basis) == m * m - commute_rank,
        "uniform matrix algebra plus the two centered directions exhaust the commutant",
    )
    # Adjacent *raw rail* swaps generate all address permutations. A commuting
    # global complex structure must preserve the common real fixed space; on
    # a one-dimensional real line its square cannot be minus the identity.
    free = []
    for i in range(m - 1):
        raw_order = list(range(m))
        raw_order[i], raw_order[i + 1] = raw_order[i + 1], raw_order[i]
        free.append(scale(2, wires(tuple(raw_order))))
    free_gates = gates + free
    free_fixed_dim = m - rank(fixed_rows(free_gates))
    need(free_fixed_dim == 1, "unrestricted permutations leave a fixed line")
    need(any(not commutes(d, f) for f in free), "free permutations break centered turn")
    print(
        f"N={n}: commutator rank={commute_rank}/{m * m}, commutant dim={m * m - commute_rank}, "
        f"fixed dim={fixed_dim}, centered rank={rank(d)}, moved-profile classes={len(classes)}, "
        f"free-permutation fixed dim={free_fixed_dim}"
    )


def main() -> None:
    h, j = raw_selection()
    print("Raw integer root: minimum r=2, d=2; with uniform tag gain h=4: H and Hᵗ.")
    print(
        "Controls: a shear loses equal tag stock; a gain-one routing loses transparency."
    )
    for n, expected in enumerate((10, 30, 58, 94), start=2):
        network(n, h, j, expected)
    print(
        "Centered turn only; inversion reverses orientation; uniform-mode extension is ambiguous."
    )
    print(
        "Conditional finite reconstruction, not density, physical complex scalars, or full QM."
    )


if __name__ == "__main__":
    main()
