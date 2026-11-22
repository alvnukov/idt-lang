"""Where do Weyl-like cones occur in a spatially wired unsigned-junction model?

Supply a diamond lattice, a two-sublattice clock, linear wave amplitudes
(or sufficient background/resolution to enact a finite deviation circuit),
and a fixed cyclic rewiring R after every four-leg complementary junction
G=11^T/2-I. The Fourier transform is a mathematical analysis of these
spatial translations, not a separately supplied complex scalar particle.
The reduced two-tick Bloch action on sublattice A is
  F(k) = D(k) C_B D(k)^* C_A , C_*=G R_* .
Coordinates kappa_j are the three independent phase differences from leg 0.
All arithmetic below is exact at the eight REAL phase corners of the torus.
It is not a search of the continuous Brillouin zone or an experimental fit.
"""

from __future__ import annotations

import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_balanced_phase_composition import (
    Matrix,
    add,
    determinant,
    identity,
    matrix,
    multiply,
    scale,
    trace,
    transpose,
)

I4 = identity(4)
G = matrix(tuple(tuple(F(1, 2) - int(i == j) for j in range(4)) for i in range(4)))
TETRA = matrix(((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)))
JAC = matrix(
    tuple(tuple(TETRA[i][j] - TETRA[0][j] for j in range(3)) for i in (1, 2, 3))
)
WALSH = scale(F(1, 2), matrix(tuple((1, *r) for r in TETRA)))


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def sub(a: Matrix, b: Matrix) -> Matrix:
    return add(a, scale(-1, b))


def conjugate(v: Matrix, a: Matrix) -> Matrix:
    return multiply(multiply(v, a), transpose(v))


def diag(values: tuple[int, ...]) -> Matrix:
    return matrix(
        tuple(
            tuple(x if i == j else 0 for j in range(len(values)))
            for i, x in enumerate(values)
        )
    )


def rotations() -> tuple[Matrix, ...]:
    out = []
    for order in permutations(range(4)):
        r = tuple(I4[i] for i in order)
        r2 = multiply(r, r)
        if r2 != I4 and multiply(r2, r2) == I4:
            out.append(r)
    return tuple(out)


AXES = tuple(diag(tuple(int(i == j) for i in range(4))) for j in range(1, 4))


def derivatives(v: Matrix) -> tuple[Matrix, ...]:
    return tuple(sub(x, conjugate(v, x)) for x in AXES)


@dataclass(frozen=True)
class Cone:
    grams: Matrix
    spatial: Matrix
    tilt: tuple[F, ...]
    signed_trace: F


def double_sector(f: Matrix, v: Matrix) -> Cone | None:
    k = sub(scale(2, f), I4)
    if multiply(k, k) != scale(-3, I4):
        return None
    need(transpose(k) == scale(-1, k), "orthogonal complex structure")
    # For eigenvalue exp(+/-i pi/3), the real operator commuting with K
    # has exactly the two compressed complex blocks. No eigenvector phase
    # or floating-point band sort is needed.
    linear = tuple(
        scale(F(1, 2), sub(h, scale(F(1, 3), multiply(multiply(k, h), k))))
        for h in derivatives(v)
    )
    tilt = tuple(trace(h) / 4 for h in linear)
    axes = tuple(sub(h, scale(t, I4)) for h, t in zip(linear, tilt, strict=True))
    gram = matrix(tuple(tuple(trace(multiply(x, y)) / 4 for y in axes) for x in axes))
    for i, j in product(range(3), repeat=2):
        x, y = axes[i], axes[j]
        need(
            add(multiply(x, y), multiply(y, x)) == scale(2 * gram[i][j], I4),
            "projected Clifford metric",
        )
    need(all(multiply(k, x) == multiply(x, k) for x in axes), "mixed opposite carriers")
    comm = sub(multiply(axes[1], axes[2]), multiply(axes[2], axes[1]))
    value = trace(multiply(k, multiply(axes[0], comm)))
    # (1/(4i))tr_+(H1[H2,H3]) = -value/(8 sqrt(3)); the minus
    # branch is conjugate. Its square equals det g.
    need(value**2 / 192 == determinant(gram) > 0, "rank or chirality magnitude")
    return Cone(gram, multiply(multiply(transpose(JAC), gram), JAC), tilt, value)


def gamma_controls(rs: tuple[Matrix, ...]) -> None:
    counts: Counter[int] = Counter()
    for b in rs:
        vb = multiply(G, b)
        hs = derivatives(vb)
        for h in hs:
            hh = conjugate(transpose(WALSH), h)
            need(all(hh[i][i] == 0 for i in range(4)), "shared hollow basis")
        for a in rs:
            f = multiply(vb, multiply(G, a))
            need(f == multiply(b, a), "Gamma permutation")
            fixed = int(trace(f))
            counts[fixed] += 1
            # An arbitrary later Gamma permutation sends the Walsh
            # coordinates to signed permutations, preserving hollowness.
            p = conjugate(transpose(WALSH), f)
            need(all(sum(z != 0 for z in row) == 1 for row in p), "Walsh routing")
    need(counts == {4: 6, 0: 6, 1: 24}, "Gamma classes not separated")


def census() -> dict[tuple[tuple[F, ...], F], int]:
    rs = rotations()
    need(len(rs) == 6, "four-cycles")
    gamma_controls(rs)
    rows: Counter[tuple[tuple[F, ...], F]] = Counter()
    for a, b in product(rs, repeat=2):
        ca, cb = multiply(G, a), multiply(G, b)
        for signs in product((1, -1), repeat=3):
            v = conjugate(diag((1, *signs)), cb)
            cone = double_sector(multiply(v, ca), v)
            if cone is not None:
                need(all(t == 0 for t in cone.tilt), "unexpected first-order tilt")
                gram = cone.spatial
                need(
                    all(
                        gram[i][j] == 0
                        for i, j in product(range(3), repeat=2)
                        if i != j
                    ),
                    "nondiagonal spatial cone",
                )
                key = tuple(gram[i][i] for i in range(3))
                need(
                    sorted(key) == [F(2, 3), F(2, 3), F(4, 3)], "wrong principal speeds"
                )
                rows[key, cone.signed_trace] += 1
    need(len(rows) == 6 and set(rows.values()) == {8}, "real-corner census")
    return dict(rows)


def main() -> None:
    rows = census()
    print(
        "36 oriented two-sublattice wirings x eight real phase corners. Exactly",
        sum(rows.values()),
        "corner/wiring pairs pass F^2-F+I=0 and have full three-dimensional linear Weyl cones of both chiralities at eigenphases +/-pi/3.",
    )
    print(
        "Each cone is untilted with physical momentum metric a permutation of diag(4,2,2)/3 per two ticks (tetrahedral step coordinates +/-1). Distinct choices of the distinguished axis need not share a conformal metric."
    )
    print(
        "At Gamma a finite periodic word of these junctions with identity return has a common zero-diagonal basis for all three derivatives. A positive-rank-three real Clifford triple in four real dimensions cannot have such a basis. This Gamma wall does not rule out the finite-momentum hits."
    )
    print(
        "No particle counts, spin-statistics, electromagnetic gauge transversality, common metric, expanding background, or measured data follow from this walk."
    )


if __name__ == "__main__":
    main()
