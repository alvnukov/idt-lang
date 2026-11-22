"""Can simply changing six-packet pairings generate an internal connection?

The original tetrahedron has ONE natural packet complement. Here an extra
local structure is deliberately tested: neighboring junctions can assign
different perfect matchings to the same six persistent addresses. Transport
by averaging with the NEW complement is compared with identifying labeled
frames and with adding a norm-correcting filter. No gauge field is assumed.
"""

from __future__ import annotations

from collections import deque
from fractions import Fraction as F
from itertools import combinations, permutations, product

from scripts import probe_balanced_phase_composition as b
from scripts.gaussian_dyadic_words import g as gaussian
from scripts.probe_native_rational_pentagon import retry

Pair = tuple[int, int]
Match = tuple[Pair, ...]
Matrix = b.Matrix
I3 = b.identity(3)
ONES = b.matrix(((1, 1, 1),) * 3)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def matchings(ports: tuple[int, ...]) -> tuple[Match, ...]:
    if not ports:
        return ((),)
    h, *tail = ports
    return tuple(
        ((h, x), *other)
        for x in tail
        for other in matchings(tuple(y for y in tail if y != x))
    )


MATCHES = matchings(tuple(range(6)))


def overlap(left: Match, right: Match, sign: int) -> Matrix:
    """Rows at destination left, columns at source right; normalized pair basis."""
    return b.matrix(
        tuple(
            tuple(
                sum(
                    F((sign ** (i + j)) * int(x == y), 2)
                    for i, x in enumerate(l)
                    for j, y in enumerate(r)
                )
                for r in right
            )
            for l in left
        )
    )


def reduced_plus(left: Match, right: Match) -> Matrix:
    # For disjoint matchings each destination pair misses exactly one source
    # pair. On centered triples the sum of the other two is its negative.
    return b.matrix(
        tuple(tuple(-int(not set(l) & set(r)) for r in right) for l in left)
    )


def polar(left: Match, right: Match) -> Matrix:
    m = overlap(left, right, -1)
    g = b.multiply(b.transpose(m), m)
    # g=(I+3P)/4 with P the rank-one common alternating line. The inverse
    # square root is 2I-P, where P=(4g-I)/3.
    p = b.scale(F(1, 3), b.add(b.scale(4, g), b.scale(-1, I3)))
    need(b.multiply(p, p) == p and b.trace(p) == 1, "wrong principal line")
    return b.multiply(m, b.add(b.scale(2, I3), b.scale(-1, p)))


def links() -> tuple[dict[tuple[int, int], Matrix], dict[tuple[int, int], Matrix]]:
    plus, minus = {}, {}
    cent = b.add(I3, b.scale(F(-1, 3), ONES))
    for i, j in permutations(range(15), 2):
        a, c = MATCHES[i], MATCHES[j]
        common = len(set(a) & set(c))
        raw = overlap(a, c, -1)
        if common:
            need(common == 1 and b.determinant(raw) == 0, "shared-pair contraction")
            continue
        op = reduced_plus(a, c)
        need(
            b.multiply(b.scale(2, overlap(a, c, 1)), cent) == b.multiply(op, cent),
            "half permutation on plus",
        )
        need(abs(b.determinant(raw)) == F(1, 4), "minus determinant")
        z = b.scale(2, raw)
        support = tuple(tuple(int(t) % 2 for t in row) for row in z)
        need(
            all(x in (0, 1) for r in support for x in r)
            and all(sum(r) == 2 for r in support)
            and all(sum(c) == 2 for c in zip(*support, strict=True)),
            "mod-two transfer pattern",
        )
        v = polar(a, c)
        need(b.multiply(b.transpose(v), v) == I3, "polar reference not orthogonal")
        plus[j, i], minus[j, i] = op, v
    need(len(plus) == 120, "wrong disjoint matching graph")
    return plus, minus


def loop_generators(
    edges: dict[tuple[int, int], Matrix],
) -> tuple[tuple[tuple[int, ...], Matrix], ...]:
    frames = {0: I3}
    paths: dict[int, tuple[int, ...]] = {0: (0,)}
    queue = deque((0,))
    loops = []
    while queue:
        j = queue.popleft()
        for i in range(15):
            if (j, i) not in edges:
                continue
            t = b.multiply(edges[j, i], frames[j])
            if i not in frames:
                frames[i] = t
                paths[i] = (*paths[j], i)
                queue.append(i)
            else:
                loop = b.multiply(b.transpose(frames[i]), t)
                loops.append(((*paths[j], i, *reversed(paths[i][:-1])), loop))
    need(len(frames) == 15, "disconnected matching graph")
    return tuple(loops)


def plus_group(gs: tuple[Matrix, ...]) -> set[Matrix]:
    start = {I3}
    queue = deque((I3,))
    while queue:
        x = queue.popleft()
        for g in gs:
            y = b.multiply(g, x)
            if y not in start:
                need(len(start) < 12, "not a signed coordinate permutation")
                start.add(y)
                queue.append(y)
    return start


def parity_wall() -> None:
    # Over F2 every twice-overlap matrix is J+P for a permutation P; it
    # acts as P on the even-sum plane E and vanishes on the all-ones line.
    e = {(0, 1, 1), (1, 0, 1), (1, 1, 0)}
    for p in permutations(range(3)):
        need(
            {tuple((sum(v) + v[p[j]]) % 2 for j in range(3)) for v in e} == e,
            "lost nonzero parity",
        )
    # For n nontrivial disjoint projections their integer numerator B has
    # |det|=2^n. B^t B=d I needs d^3=2^(2n), hence 3|n and d=4^(n/3).
    # In a sum of three integer squares, divisibility by four forces EVERY
    # coordinate even. Thus B=0 (mod 2), contradicting invertibility on E.
    need(
        all(
            sum(x * x for x in v) % 4 or v == (0, 0, 0)
            for v in product(range(2), repeat=3)
        ),
        "three-square residue",
    )


def axis(u: Matrix) -> tuple[F, ...]:
    return (u[2][1] - u[1][2], u[0][2] - u[2][0], u[1][0] - u[0][1])


def full_polar_sample() -> tuple[F, int]:
    # R=NM consists of two three-cycles. For eigenvalues omega,bar(omega),
    # |1+omega|=1; only the fixed vectors of R need gain 1/2 in I+R.
    # Thus polar(I+R)=I+R-(I+R+R²)/3 is a rational, invertible bridge.
    # This supplies an independent norm criterion NOT present in the pair
    # labels. A physical group-mixing compiler also needs extra resources.
    def reflect(m: Match) -> Matrix:
        p = {x: y for l in m for x, y in (l, tuple(reversed(l)))}
        return b.matrix(
            tuple(tuple(int(i == p[j]) for j in range(6)) for i in range(6))
        )

    m, n = reflect(MATCHES[0]), reflect(MATCHES[4])
    eye6 = b.identity(6)
    r = b.multiply(n, m)
    r2 = b.multiply(r, r)
    need(b.multiply(r, r2) == eye6, "not a disjoint six-cycle")
    f = b.add(b.scale(F(2, 3), b.add(eye6, r)), b.scale(F(-1, 3), r2))
    need(
        b.multiply(b.transpose(f), f) == eye6
        and b.multiply(f, f) == r
        and b.multiply(n, f) == b.multiply(f, m),
        "not the canonical polar intertwiner",
    )
    need(all(sum(row) == 1 for row in f), "uniform reference changed")
    need(f != r2 and b.multiply(r2, r2) == r, "long-arc permutation competitor")
    word = retry((tuple(tuple(gaussian(x) for x in row) for row in f),))
    need(word.success == F(9, 16), "incorrect retry law")
    return word.success, word.physical_mixers


def main() -> None:
    plus, minus = links()
    group = plus_group(tuple({g for _, g in loop_generators(plus)}))
    loc = loop_generators(minus)
    inf = [
        (p, g)
        for p, g in loc
        if b.determinant(g) == 1 and (b.trace(g) - 1).denominator != 1
    ]
    independent = next(
        (
            (p, q)
            for p, g in inf
            for q, h in inf
            if any(
                axis(g)[i] * axis(h)[j] != axis(g)[j] * axis(h)[i]
                for i, j in combinations(range(3), 2)
            )
        ),
        None,
    )
    parity_wall()
    need(len(group) == 12, "hexagonal holonomy group drift")
    need(
        independent is not None and len(inf) == 20,
        "nonparallel infinite-order loop witnesses",
    )
    success, mixers = full_polar_sample()
    print(
        "Matching graph: 15 frames, 60 undirected disjoint-pair links. Centered plus transport is exactly one half a signed permutation; loop group size",
        len(group),
    )
    print(
        "Any changing sequence in the three-dimensional minus sector is state-selective: shared pairs lose rank, disjoint sequences cannot be a nonzero scalar times an isometry (integer parity wall)."
    )
    print(
        f"Explicitly added polar rebalancing gives {len(inf)} non-torsion SO(3) fundamental loop records; independent axes paths: {independent}. A real rotation is not a derived SU(3) gauge field."
    )
    print(
        f"One complete six-address polar intertwiner = (2I+2NM-(NM)^2)/3, exact native compiled retry p={success}, {mixers} paired-rail mixers per isolated attempt. The equally reversible permutation (NM)^2 needs no norm compensation and gives different holonomy."
    )


if __name__ == "__main__":
    main()
