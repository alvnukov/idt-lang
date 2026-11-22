"""Which natural square roots transport one disjoint pairing into another?

No inner product, shortest-turn criterion or probability rule is assumed in
the root selection. Supply six linear signed record coordinates, a fixed
ordered pair of disjoint opposition matchings M,N, equivariance under every
relabel preserving them, U M=N U, U²=NM on the FULL carrier, and transparent
uniform stock. The echo is two uses of the *same* device, not its inverse.
Two ideal zero/nonzero response tests pick out a non-permutation root. The
stock interpretation and the case for a physical device are stated separately.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_balanced_phase_composition as b
from scripts.probe_matching_transport import MATCHES, Match, links, loop_generators

I6 = b.identity(6)
P0 = b.scale(F(1, 6), b.matrix(((1,) * 6,) * 6))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def perm(p: tuple[int, ...]) -> b.Matrix:
    return b.matrix(tuple(tuple(int(y == p[x]) for x in range(6)) for y in range(6)))


def matching(m: Match) -> tuple[int, ...]:
    lookup = {x: y for a, c in m for x, y in ((a, c), (c, a))}
    return tuple(lookup[x] for x in range(6))


def comp(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[x] for x in q)


def classify() -> tuple[b.Matrix, b.Matrix, b.Matrix, b.Matrix]:
    m, n = matching(MATCHES[0]), matching(MATCHES[4])
    M, N = perm(m), perm(n)
    rotation = comp(n, m)
    r = perm(rotation)
    r2 = b.multiply(r, r)
    fixed = b.scale(F(1, 3), b.add(b.add(I6, r), r2))
    pa = b.add(fixed, b.scale(-1, P0))
    other = b.add(I6, b.scale(-1, fixed))
    need(
        tuple(b.trace(x) for x in (P0, pa, other)) == (F(1), F(1), F(4)),
        "wrong central ranks",
    )
    group = tuple(
        p
        for p in permutations(range(6))
        if comp(p, m) == comp(m, p) and comp(p, n) == comp(n, p)
    )
    need(len(group) == 6, "ordered matching stabilizer")
    # U commutes with R from U²=R; R² itself intertwines M and N.
    # Therefore Y=R^(-2)U commutes with M,N and the common relabelings.
    # The dimension of that commutant is the number of ordered-cell orbits.
    gen = (*group, m, n)
    unseen = set(product(range(6), repeat=2))
    sizes = []
    while unseen:
        todo = [min(unseen)]
        orbit = set(todo)
        while todo:
            i, j = todo.pop()
            for p in gen:
                v = p[i], p[j]
                if v not in orbit:
                    orbit.add(v)
                    todo.append(v)
        unseen -= orbit
        sizes.append(len(orbit))
    need(len(sizes) == 3, "noncentral root not covered")
    ps = (P0, pa, other)
    for i, j in product(range(3), repeat=2):
        need(
            b.multiply(ps[i], ps[j]) == (ps[i] if i == j else b.scale(0, I6)),
            "not complementary idempotents",
        )
    for p in gen:
        need(
            all(b.multiply(perm(p), v) == b.multiply(v, perm(p)) for v in ps),
            "not a commutant basis",
        )
    # Thus Y^2=I gives independent signs on three summands. Uniform fixed
    # sets the first sign positive: four roots, without assuming orthogonality.
    orbit0 = {0, rotation[0], rotation[rotation[0]]}
    chosen = []
    signatures = set()
    for s, t in product((1, -1), repeat=2):
        y = b.add(P0, b.add(b.scale(s, pa), b.scale(t, other)))
        u = b.multiply(r2, y)
        need(
            b.multiply(u, u) == r and b.multiply(u, M) == b.multiply(N, u),
            "wrong echo/intertwiner",
        )
        need(b.multiply(b.transpose(u), u) == I6, "orthogonality did not follow")
        dark = all(u[k][0] == 0 for k in range(6) if k not in orbit0)
        stay = u[0][0]
        signatures.add((s, t, stay, dark))
        if dark and stay:
            chosen.append(u)
    need(
        signatures
        == {
            (1, 1, F(0), True),
            (1, -1, F(2, 3), True),
            (-1, 1, F(-1, 3), False),
            (-1, -1, F(1, 3), False),
        },
        "same-site/cross-orbit witnesses",
    )
    target = b.scale(F(1, 3), b.add(b.scale(2, b.add(I6, r)), b.scale(-1, r2)))
    need(chosen == [target], "unique retained root")
    return M, N, r, target


def stock_controls(m: b.Matrix, n: b.Matrix, r: b.Matrix, u: b.Matrix) -> None:
    r2 = b.multiply(r, r)
    # A signed -R² contribution becomes a positive opposite record as seen
    # in the target odd contrast. The other two terms each make two copies.
    five = b.add(b.scale(2, b.add(I6, r)), b.multiply(n, r2))
    nine = b.add(b.scale(3, u), b.scale(6, P0))
    for x, c in ((five, 5), (nine, 9)):
        need(
            all(z >= 0 and z.denominator == 1 for row in x for z in row)
            and all(sum(col) == c for col in zip(*x, strict=True)),
            "not a positive branching law",
        )
    anti_m = b.add(I6, b.scale(-1, m))
    anti_n = b.add(I6, b.scale(-1, n))
    center = b.add(I6, b.scale(-1, P0))
    need(
        b.multiply(anti_n, five) == b.scale(3, b.multiply(u, anti_m)),
        "odd unsigned implementation",
    )
    need(
        b.multiply(five, center) != b.scale(3, b.multiply(u, center)),
        "five-branch false positive on all centered modes",
    )
    need(
        b.multiply(center, nine) == b.scale(3, b.multiply(u, center)),
        "centered unsigned implementation",
    )
    # Signed stock grows by 3 in amplitude; raw counts grow by 5 or 9.
    # Normalizing by physical count would NOT give the normalized rotation.


def relative_stock_control() -> None:
    _, ms = links()
    loops = dict(loop_generators(ms))
    a, c = loops[(0, 5, 6, 4, 0)], loops[(0, 7, 11, 4, 0)]
    need(
        b.trace(a) == b.trace(c) == F(115, 81) and b.multiply(a, c) != b.multiply(c, a),
        "continuous rotation witnesses",
    )
    x = tuple(row[0] for row in a)
    need(
        sum(v * v for v in x) == 1 and sum(v**4 for v in x) != 1,
        "quartic count survived dense rotation",
    )


def main() -> None:
    m, n, r, u = classify()
    stock_controls(m, n, r, u)
    relative_stock_control()
    print(
        "All real natural uniform-preserving linear echo intertwiners on the six labels: four. Same-orbit darkness plus nonzero addressed return uniquely gives (2I+2NM−(NM)²)/3, without assuming a metric. Each candidate in this class is orthogonal as a consequence."
    )
    print(
        "Five positive descendants per record implement the selected map with gain 3 on the three odd contrasts; nine do so on ALL centered six-record differences with a uniform background. Counts grow: this is not a six-particle lossless microscopic gate."
    )
    print(
        "Two explicit odd-sector loops have rotation trace 115/81 and nonparallel axes, generating dense SO(3) in closure. Quadratic stock survives; an additive quartic control fails. Continuity and additivity over independently readable components are further premises, not a single-event probability law."
    )


if __name__ == "__main__":
    main()
