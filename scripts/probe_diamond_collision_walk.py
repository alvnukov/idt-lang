"""Untwisted complementary-junction walk: a scalar cone, not photon dynamics.

SUPPLIED RESOURCES. Put G4=J4/2-I4 on both sublattices of an already arranged
diamond graph, with a synchronized collision/flip-flop clock and NO cyclic
outgoing-wire turn. Use a normalized signed/deviation wave and the ordinary
squared norm. Fourier complexification is a calculation on this real walk,
not a derived physical complex amplitude. The unsigned rule still requires
exhaustive unlike pairing at each event; a background and a finite common
integer scale supply that domain in the exact replay below. Spatial layout,
distance, time unit, signal preparation and detection are not derived.

SPECTRUM. Let s=(1,1,1,1)/2, E embed one uniform coin line per sublattice,
C=2EE*-I, and S(k)=[[0,Z],[Z*,0]], Z=diag(exp(i k.d_j)). Thus S*=S, S^2=I
and U=SC. The discriminant E*SE=[[0,gamma],[gamma*,0]] has eigenvalues +/-r,
gamma=sum_j exp(i k.d_j)/4, r=|gamma|. Each discriminant eigenvalue mu lifts
on span(Ev,SEv) to lambda^2-2mu*lambda+1=0. For r<1 the complementary
four-dimensional sector has C=-I, U=-S, with two flat +1 and two flat -1
modes. Hence
  det(lambda I-U)=(lambda^2-1)^2[lambda^4+(2-4r^2)lambda^2+1].
The dispersive eigenvalues are exp(+/-i theta), -exp(+/-i theta), cos(theta)=r.
At r=1 the invariant-plane dimension drops: +1 and -1 each have multiplicity
four. At r=0 the dispersive +/-i eigenvalues each have multiplicity two.
Finite rational-phase characteristic polynomials below test these degeneracies.

REGULAR TETRAHEDRON. d=(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1) gives
gamma=cos(kx)cos(ky)cos(kz)-i sin(kx)sin(ky)sin(kz). Near zero,
  theta^2=|k|^2-(kx^2 ky^2+ky^2 kz^2+kz^2 kx^2)/3+O(|k|^6).
The leading cone is isotropic, but fourth-order terms are not. Along a
coordinate axis theta=|k| locally, exactly. Along unit face/body diagonals
the fourth-order coefficients in theta^2 are -1/12 and -1/9. Coordinate
speed is one per tick; if physical edge length is a and tick time tau, this
means a/(sqrt(3)*tau), only after supplying that Euclidean embedding/clock.

MODE CONTENT. At quasienergy zero the +1 eigenspace at k=0 has basis
(1_4,1_4) and (d_x,-d_x),(d_y,-d_y),(d_z,-d_z), all divided by sqrt(8).
Projection of (dU/dk)/i gives the four-dimensional star matrix
  H(k)=[[0,k^T],[k,0_3]]
up to the overall quasienergy sign convention. H^3=|k|^2 H: one positive
and one negative dispersive mode, and two transverse flat directions.
The propagating vector component is LONGITUDINAL. This is the scalar/acoustic
first-order pattern, not Maxwell's two propagating transverse polarizations.
There is another cone at quasienergy pi, not a second degenerate polarization
near zero. Squaring U aliases the two cones and doubles bands across the two
decoupled sublattices; that is a clock/sublattice duplication, not a derived
polarization. A cone alone is not Weyl either: the leading matrices are not
Pauli/Clifford matrices, and the zero-frequency crossing includes flat bands.
No topological/helicity classification is inferred from the finite controls.

FLAT LOOPS. A six-edge directed circulation has opposite amplitudes on reversed
arcs, zero sum at each vertex and S=-1; therefore U=+1. Alternating edge signs
with equal amplitudes on reversed arcs give S=+1 and U=-1. Both have squared
norm 12 in the integer convention below. A vertex-sum detector misses them,
but a leg-resolved deviation detector does not: darkness is not gauge. A local
single-arc preparation overlaps a loop; a vertex-uniform preparation does not.
Distributed loop preparation is an additional resource, not claimed to follow
from one mark. An unsigned background realizes these unnormalized contrasts;
no exact normalized single-source preparation is asserted. Removing the sector
requires an actual operational quotient or preparation/readout restriction.

GEOMETRY WALL. For any zero-mean four-direction frame the leading quadratic
form is Q=sum_j d_j d_j^T/4. Equal lengths and zero drift alone do not make Q
isotropic: (±1,±2,±2) with even minus parity has Q=diag(1,4,4), equal length3.
A singular frame can even remove a propagation dimension; it is then not a
faithful three-dimensional spatial embedding. Changing a supplied
metric can whiten a nonsingular Q, so isotropy cannot select physical geometry
without independent distance/clock calibration. Four legs do not derive 3D.
Cheap distinguishing controls are branch multiplicity and longitudinal versus
transverse response, with that geometric interpretation supplied. No emergent
spacetime, gauge invariance, Maxwell/Weyl equation, Born rule or QM claim follows.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    Matrix,
    eye,
    g,
    unitary,
)
from scripts.probe_complement_collision_mixer import collide, counts, pairing

Vector3 = tuple[int, int, int]
Arc = tuple[int, Vector3, int]
State = dict[Arc, F]
DIRECTIONS: tuple[Vector3, ...] = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
OFFSETS: tuple[Vector3, ...] = ((0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1))
G4: Matrix = tuple(tuple(g(F(1, 2) - int(i == j)) for j in range(4)) for i in range(4))


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(ar, br, strict=True))
        for ar, br in zip(a, b, strict=True)
    )


def scale(c: Gaussian, a: Matrix) -> Matrix:
    return tuple(tuple(c * x for x in row) for row in a)


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def coin() -> Matrix:
    return tuple(
        tuple(G4[i % 4][j % 4] if i // 4 == j // 4 else ZERO for j in range(8))
        for i in range(8)
    )


def shift(phases: tuple[Gaussian, ...]) -> Matrix:
    need(
        len(phases) == 4 and all(z.norm2() == 1 for z in phases),
        "four unit edge phases",
    )
    return tuple(
        tuple(
            phases[i]
            if i < 4 and j == i + 4
            else phases[j].star()
            if j < 4 and i == j + 4
            else ZERO
            for j in range(8)
        )
        for i in range(8)
    )


def characteristic(a: Matrix) -> tuple[Gaussian, ...]:
    """Exact descending Faddeev-LeVerrier coefficients, no numeric eigenvalues."""
    n, identity = len(a), eye(len(a))
    b, coefficients = identity, [ONE]
    for k in range(1, n + 1):
        ab = mm(a, b)
        c = g(F(-1, k)) * sum((ab[i][i] for i in range(n)), ZERO)
        coefficients.append(c)
        b = add(ab, scale(c, identity))
    need(all(z == ZERO for row in b for z in row), "exact Cayley-Hamilton check")
    return tuple(coefficients)


def spectral_controls() -> int:
    phase_sets = [
        (ONE, *tuple(g(v) for v in signs)) for signs in product((-1, 1), repeat=3)
    ]
    z = g(F(3, 5), F(4, 5))
    phase_sets.extend(
        (
            (ONE, g(0, 1), ONE, g(0, 1)),
            (g(0, 1),) * 4,
            (ONE, g(0, 1), g(-1), g(0, -1)),
            (ONE, ONE, ONE, z),
            (z, z, z.star(), z.star()),
        )
    )
    xyz = (z, g(F(5, 13), F(12, 13)), g(F(8, 17), F(15, 17)))
    physical_phases = tuple(
        (xyz[0] if d[0] == 1 else xyz[0].star())
        * (xyz[1] if d[1] == 1 else xyz[1].star())
        * (xyz[2] if d[2] == 1 else xyz[2].star())
        for d in DIRECTIONS
    )
    gamma = g(F(1, 4)) * sum(physical_phases, ZERO)
    need(
        gamma
        == g(xyz[0].re * xyz[1].re * xyz[2].re, -xyz[0].im * xyz[1].im * xyz[2].im),
        "exact tetrahedral Fourier symbol",
    )
    phase_sets.append(physical_phases)
    for phases in phase_sets:
        s = shift(phases)
        u = mm(s, coin())
        need(
            mm(s, s) == eye(8) and unitary(u), "flip-flop reflection and lossless walk"
        )
        gamma = g(F(1, 4)) * sum(phases, ZERO)
        r2 = gamma.norm2()
        expected = tuple(g(v) for v in (1, 0, -4 * r2, 0, 8 * r2 - 2, 0, -4 * r2, 0, 1))
        need(
            characteristic(u) == expected,
            "full flat/dispersive characteristic polynomial",
        )
    need(
        (g(F(1, 4)) * (z + z + z.star() + z.star())).norm2() == z.re**2,
        "exact axis dispersion",
    )
    # The eight +/-1 triples are the complete Bloch cells of the size-two torus.
    exceptional = sum(
        all(v == 1 for v in signs) for signs in product((-1, 1), repeat=3)
    )
    need(
        exceptional == 1 and 4 * exceptional + 2 * (8 - exceptional) == 18,
        "each +/-1 eigenspace has torus multiplicity18 including the Gamma crossing",
    )
    return len(phase_sets)


def moment_controls() -> None:
    for v in ((1, 0, 0), (1, 1, 0), (1, 1, 1), (1, 2, 3)):
        dots = [sum(a * b for a, b in zip(v, d, strict=True)) for d in DIRECTIONS]
        m2, m4 = sum(F(x * x, 4) for x in dots), sum(F(x**4, 4) for x in dots)
        pairs = sum(v[i] ** 2 * v[j] ** 2 for i in range(3) for j in range(i + 1, 3))
        need(
            sum(dots) == 0 and m2 == sum(x * x for x in v),
            "zero drift and regular leading metric",
        )
        need(
            (m2 * m2 - m4) / 12 == -F(pairs, 3),
            "exact fourth-order dispersion coefficient",
        )
    for v, expected in (
        ((1, 0, 0), F(0)),
        ((1, 1, 0), F(-1, 12)),
        ((1, 1, 1), F(-1, 9)),
    ):
        q = sum(x * x for x in v)
        pairs = sum(v[i] ** 2 * v[j] ** 2 for i in range(3) for j in range(i + 1, 3))
        need(-F(pairs, 3 * q * q) == expected, "unit-direction quartic anisotropy")
    for stretches, diagonal in (((1, 2, 2), (1, 4, 4)), ((1, 1, 0), (1, 1, 0))):
        frame = tuple(tuple(d[i] * stretches[i] for i in range(3)) for d in DIRECTIONS)
        need(
            all(sum(d[i] for d in frame) == 0 for i in range(3)),
            "nonregular zero drift",
        )
        need(len({sum(x * x for x in d) for d in frame}) == 1, "equal leg lengths")
        covariance = tuple(
            tuple(sum(F(d[i] * d[j], 4) for d in frame) for j in range(3))
            for i in range(3)
        )
        need(
            covariance
            == tuple(
                tuple(F(diagonal[i] if i == j else 0) for j in range(3))
                for i in range(3)
            ),
            "anisotropic or singular supplied frame",
        )


def tangent_controls() -> None:
    basis = ((1,) * 8,) + tuple(
        tuple(d[a] for d in DIRECTIONS) + tuple(-d[a] for d in DIRECTIONS)
        for a in range(3)
    )
    u0 = mm(shift((ONE,) * 4), coin())
    for vector in basis:
        column = tuple((g(x),) for x in vector)
        need(
            mm(u0, column) == column and sum(x * x for x in vector) == 8,
            "Gamma positive-sector basis",
        )
    generators = []
    for axis in range(3):
        derivative = tuple(
            tuple(
                g(DIRECTIONS[i][axis])
                if i < 4 and j == i + 4
                else g(-DIRECTIONS[j][axis])
                if j < 4 and i == j + 4
                else ZERO
                for j in range(8)
            )
            for i in range(8)
        )
        du = mm(derivative, coin())
        projected = tuple(
            tuple(
                sum(
                    (
                        g(F(left[i] * right[j], 8)) * du[i][j]
                        for i in range(8)
                        for j in range(8)
                    ),
                    ZERO,
                )
                for right in basis
            )
            for left in basis
        )
        wanted = tuple(
            tuple(
                g(int((i == 0 and j == axis + 1) or (j == 0 and i == axis + 1)))
                for j in range(4)
            )
            for i in range(4)
        )
        need(
            projected == wanted, "longitudinal star generator, not Weyl Pauli matrices"
        )
        generators.append(projected)
    need(mm(generators[0], generators[0]) != eye(4), "no Clifford-square identity")
    for v in ((1, 0, 0), (1, 2, 3)):
        h = scale(ZERO, eye(4))
        for value, generator in zip(v, generators, strict=True):
            h = add(h, scale(g(value), generator))
        need(
            mm(mm(h, h), h) == scale(g(sum(x * x for x in v)), h),
            "one dispersive pair plus two flat directions",
        )
        transverse = ((ZERO,), (g(-v[1]),), (g(v[0]),), (ZERO,))
        need(
            mm(h, transverse) == ((ZERO,),) * 4,
            "transverse response is flat at leading order",
        )


def cells(size: int) -> tuple[Vector3, ...]:
    return tuple((x, y, z) for x, y, z in product(range(size), repeat=3))


def arcs(size: int) -> tuple[Arc, ...]:
    return tuple(
        (side, cell, j) for side in (0, 1) for cell in cells(size) for j in range(4)
    )


def shifted(arc: Arc, size: int) -> Arc:
    side, cell, j = arc
    sign = 1 if side == 0 else -1
    x, y, z = ((cell[i] + sign * OFFSETS[j][i]) % size for i in range(3))
    return 1 - side, (x, y, z), j


def step(state: State, size: int) -> State:
    out = {}
    for side, cell in product((0, 1), cells(size)):
        values = tuple(state.get((side, cell, j), F(0)) for j in range(4))
        half = sum(values, F(0)) / 2
        for j, value in enumerate(values):
            if half != value:
                out[shifted((side, cell, j), size)] = half - value
    return out


def loop_states(size: int) -> tuple[State, State]:
    vertices = (
        (0, (0, 0, 0)),
        (1, (0, 0, 0)),
        (0, (-1, 0, 0)),
        (1, (-1, 1, 0)),
        (0, (-1, 1, 0)),
        (1, (0, 1, 0)),
    )
    circulation: State = {}
    alternating: State = {}
    for i, j in enumerate((0, 1, 2, 0, 1, 2)):
        source, dest = vertices[i], vertices[(i + 1) % 6]
        cell0 = tuple(x % size for x in source[1])
        cell1 = tuple(x % size for x in dest[1])
        arc: Arc = (source[0], (cell0[0], cell0[1], cell0[2]), j)
        reverse: Arc = (dest[0], (cell1[0], cell1[1], cell1[2]), j)
        need(shifted(arc, size) == reverse, "closed six-edge diamond loop")
        circulation[arc], circulation[reverse] = F(1), F(-1)
        alternating[arc] = alternating[reverse] = F((-1) ** i)
    return circulation, alternating


def unsigned_step(histogram: dict[Arc, int], size: int) -> dict[Arc, int]:
    out = {}
    for side, cell in product((0, 1), cells(size)):
        n = tuple(histogram[(side, cell, j)] for j in range(4))
        actual = counts(
            tuple(collide(i, j) for i, j in pairing((n[0], n[1], n[2], n[3])))
        )
        need(
            actual == tuple(sum(n) // 2 - x for x in n),
            "actual unturned complementary-pair coin",
        )
        for j, value in enumerate(actual):
            out[shifted((side, cell, j), size)] = value
    return out


def torus_controls() -> None:
    for size in (2, 3):
        domain = arcs(size)
        need(
            len({shifted(a, size) for a in domain}) == len(domain)
            and all(shifted(shifted(a, size), size) == a for a in domain),
            "nearest-neighbor flip-flop permutation",
        )
        for eigenvalue, loop in zip((1, -1), loop_states(size), strict=True):
            need(
                len(loop) == 12 and sum(x * x for x in loop.values()) == 12,
                "nonzero compact loop norm",
            )
            need(
                all(
                    sum(loop.get((side, cell, j), F(0)) for j in range(4)) == 0
                    for side, cell in product((0, 1), cells(size))
                ),
                "coarse vertex sums are dark",
            )
            need(
                step(loop, size) == {a: eigenvalue * x for a, x in loop.items()},
                "exact flat eigenstate",
            )
            need(
                loop.get((0, (0, 0, 0), 0)) == 1,
                "leg-resolved contrast and single-arc preparation overlap remain nonzero",
            )
            histogram = {a: 2 + int(loop.get(a, F(0))) for a in domain}
            evolved = unsigned_step(histogram, size)
            need(
                evolved == {a: 2 + eigenvalue * int(loop.get(a, F(0))) for a in domain},
                "integer-background physical-domain loop replay",
            )
    size, horizon = 2, 3
    common_scale = 2**horizon
    background = 2 * common_scale
    domain = arcs(size)
    wave: State = {domain[0]: F(1)}
    histogram = {a: background + int(common_scale * wave.get(a, F(0))) for a in domain}
    initial_total = sum(histogram.values())
    for _ in range(horizon):
        wave, histogram = step(wave, size), unsigned_step(histogram, size)
        need(
            sum(x * x for x in wave.values()) == 1, "signed/deviation norm conservation"
        )
        need(
            all(
                F(histogram[a]) == background + common_scale * wave.get(a, F(0))
                for a in domain
            ),
            "finite common-scale unsigned walk replay",
        )
        need(
            sum(histogram.values()) == initial_total and min(histogram.values()) >= 0,
            "unsigned count conservation",
        )


def main() -> None:
    need(
        mm(G4, G4) == eye(4) and all(sum(row, ZERO) == ONE for row in G4),
        "untwisted junction reflection",
    )
    count = spectral_controls()
    moment_controls()
    tangent_controls()
    torus_controls()
    print(
        f"Untwisted diamond walk: {count} exact rational-phase characteristic polynomials; generic flat +1/-1 multiplicity2 each and two dispersive pairs, with Gamma degeneracy checked."
    )
    print(
        "Regular-frame cone speed1 per coordinate tick; quartic axis/face/body coefficients 0,-1/12,-1/9. Equal-length zero-drift anisotropic and singular frames remain alternatives."
    )
    print(
        "Low-frequency tangent: one longitudinal dispersive pair plus two transverse flat directions; scalar/acoustic pattern, not Maxwell polarizations or a Weyl identification."
    )
    print(
        "Size2/3 tori: compact +/-1 loops have norm-squared12, dark vertex sums but visible leg contrasts; actual unsigned unlike-pair replays checked, including a three-tick localized wave."
    )
    print(
        "Geometry, clock, pairing, common scale, signed/deviation readout and preparation remain supplied. No gauge quotient, physical speed, emergent spacetime or QM is derived."
    )


if __name__ == "__main__":
    main()
