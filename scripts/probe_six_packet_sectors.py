"""Five directions from six distinct-pair species; what the 3+2 split does and does not give.

A tetrahedral junction has six unordered two-leg packet types. At fixed
total population their differences span five real dimensions. Complement
splits these into a three-dimensional minus sector V and two-dimensional
centered plus sector W. W is EXACTLY the kernel of counting the four
individual leg populations. The fixed-total integral lattice is not the
direct sum of integral sector lattices: the latter has index four.

There is no five-slot occupation postulate here. Quantizing the real
directions, identifying amplitudes on packet species, making a single
mode addressable, and taking exterior powers are different operations.
The related five-slot representation is a conditional comparison only.
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import ONE, ZERO, Gaussian, I, Matrix, apply, eye, g

PACKETS = ((0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2))
IVec = tuple[int, ...]
UNITS = (ONE, I, g(-1), g(0, -1))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def complement(v: IVec) -> IVec:
    return tuple(v[i ^ 1] for i in range(6))


def legs(v: IVec) -> IVec:
    return tuple(sum(v[i] for i, p in enumerate(PACKETS) if j in p) for j in range(4))


def basis_vectors() -> tuple[IVec, ...]:
    rows = [tuple(int(i == r) - int(i == (r ^ 1)) for i in range(6)) for r in (0, 2, 4)]
    rows.extend(
        tuple(int(i // 2 == j) - int(i // 2 == 2) for i in range(6)) for j in (0, 1)
    )
    return tuple(rows)


def centralizer_orbits() -> tuple[int, ...]:
    moves = tuple(
        tuple(PACKETS.index(tuple(sorted((p[i], p[j])))) for i, j in PACKETS)
        for p in permutations(range(4))
    )
    cells = set(product(range(6), repeat=2))
    sizes = []
    while cells:
        x, y = min(cells)
        orbit = {(f[x], f[y]) for f in moves}
        sizes.append(len(orbit))
        cells -= orbit
    return tuple(sorted(sizes))


def lattice_controls() -> None:
    vecs = basis_vectors()
    need(all(sum(v) == 0 for v in vecs), "not fixed total")
    need(all(complement(v) == tuple(-x for x in v) for v in vecs[:3]), "minus rank")
    need(
        all(complement(v) == v and legs(v) == (0, 0, 0, 0) for v in vecs[3:]),
        "hidden plus",
    )
    minor = sum(
        (-1) ** sum(p[i] > p[j] for i, j in combinations(range(5), 2))
        * prod(vecs[i][p[i]] for i in range(5))
        for p in permutations(range(5))
    )
    need(abs(minor) == 4, "index in A5")
    need(
        centralizer_orbits() == (6, 6, 24),
        "diagonal, opposite and overlapping packet orbits",
    )
    glued = tuple(int(i == 0) - int(i == 2) for i in range(6))
    q = tuple(F(a + 5 * b, 2) for a, b in zip(glued, complement(glued), strict=True))
    need(
        any(x.denominator == 2 for x in q),
        "traceless primitive weight is not an integral endomorphism",
    )
    for v, w in zip(vecs, (-2, -2, -2, 3, 3), strict=True):
        need(
            tuple(x + 5 * y for x, y in zip(v, complement(v), strict=True))
            == tuple(2 * w * x for x in v),
            "block weight",
        )
    weights = (-2, -2, -2, 3, 3)
    exterior = Counter(
        sum(weights[i] for i in a) for k in (0, 2, 4) for a in combinations(range(5), k)
    )
    need(
        exterior == {0: 1, 1: 6, -4: 3, 2: 3, -3: 2, 6: 1},
        "conditional even exterior comparison",
    )


def blocks(u: Matrix) -> tuple[Matrix, Matrix]:
    """Represent the operator before discarding the uniform plus coordinate."""
    d = len(u) // 2
    if not d or len(u) != 2 * d or any(len(r) != 2 * d for r in u):
        raise ValueError("square even carrier required")
    out = []
    for sign in (-1, 1):
        a = tuple(
            tuple(u[2 * i][2 * j] + g(sign) * u[2 * i][2 * j + 1] for j in range(d))
            for i in range(d)
        )
        if any(
            u[2 * i + 1][2 * j] + g(sign) * u[2 * i + 1][2 * j + 1] != g(sign) * a[i][j]
            for i, j in product(range(d), repeat=2)
        ):
            raise ValueError("operation mixes complement eigenspaces")
        out.append(a)
    return out[0], out[1]


def det3(a: Matrix) -> Gaussian:
    need(len(a) == 3 and all(len(r) == 3 for r in a), "three pairs required")
    return sum(
        (
            a[0][i]
            * (
                a[1][(i + 1) % 3] * a[2][(i + 2) % 3]
                - a[1][(i + 2) % 3] * a[2][(i + 1) % 3]
            )
            for i in range(3)
        ),
        ZERO,
    )


def lift_controls() -> None:
    phases = set()
    for k, l in product(range(4), repeat=2):
        u = eye(6)
        for _ in range(k):
            u = apply(u, ("T", 0, 1))
        for _ in range(l):
            u = apply(apply(u, ("T", 0, 2)), ("T", 1, 3))
        a, b = blocks(u)
        need(all(sum(r, ZERO) == ONE for r in b), "uniform plus direction changed")
        phases.add((det3(a), det3(b)))
    need(phases == set(product(UNITS, repeat=2)), "independent determinant cosets")
    for i in range(3):
        a, b = blocks(apply(eye(6), ("T", 2 * i, 2 * i + 1)))
        need(a == apply(eye(3), ("i", i, i)) and b == eye(3), "within-pair phase")
    for i, j in combinations(range(3), 2):
        u = apply(apply(eye(6), ("T", 2 * i, 2 * j)), ("T", 2 * i + 1, 2 * j + 1))
        need(blocks(u) == (apply(eye(3), ("T", i, j)),) * 2, "matched collision layer")
    one = apply(eye(6), ("T", 0, 2))
    # Opposite-sector vector (e0-e2-e1+e3)/2 leaks half its squared
    # norm under a single unmatched addressed mixer, none under its mate.
    x = (g(F(1, 2)), g(F(-1, 2)), g(F(-1, 2)), g(F(1, 2)), ZERO, ZERO)
    y = tuple(sum((z * w for z, w in zip(r, x, strict=True)), ZERO) for r in one)
    plus = tuple(g(F(1, 2)) * (v + y[i ^ 1]) for i, v in enumerate(y))
    need(sum(v.norm2() for v in plus) == F(1, 2), "substep leakage")
    # A pure phase mu on the centered PLUS plane with its uniform axis
    # fixed has diagonal (1+2mu)/3, offdiagonal (1-mu)/3.
    need(
        {mu for mu in UNITS if (g(F(1, 3)) * (ONE - mu)).dyadic()} == {ONE},
        "inert-three return obstruction",
    )
    # Projective ambiguity on the centered five modes: within-pair phases
    # on all three pairs enact every common mu4 relative phase exactly.
    for k in range(4):
        ops = tuple(("T", 2 * j, 2 * j + 1) for j in range(3) for _ in range(k))
        u = eye(6)
        for _, a0, b0 in ops:
            u = apply(u, ("T", a0, b0))
        a, b = blocks(u)
        need(
            b == eye(3) and a == tuple(tuple(UNITS[k] * v for v in r) for r in eye(3)),
            "relative phase control",
        )


def main() -> None:
    lattice_controls()
    lift_controls()
    print(
        "Six unordered packet types at fixed total: complement gives 3 visible + 2 histogram-invisible directions. Integral sector sublattice index 4; primitive traceless weights (-2,-2,-2,3,3) do not preserve the whole integer lattice as an infinitesimal endomorphism."
    )
    print(
        "On a SUPPLIED coherent second level, within-pair and synchronized addressed mixers preserve complement. Connected norm closure SU(3) x SU(2); 16 independent fourth-root determinant cosets; no continuous relative U(1) in this always-preserving gate class."
    )
    print(
        "For the pure weight circle, an exact raw finite word fixing the uniform reference has only the identity point. With an unobserved common phase on the five centered modes, four relative phases are available exactly. Addressing, exterior occupation, continuous gauging and particle dynamics not derived."
    )


if __name__ == "__main__":
    main()
