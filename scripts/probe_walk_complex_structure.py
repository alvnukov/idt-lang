"""A local isotropic cone does not supply a continuous complex scalar globally.

FROZEN INPUT. The six-tick word (14,21,0) and four raw real deviations of
probe_periodic_collision_metric.py, with G/R convention inherited from
probe_routed_diamond_cones.py. No six-mode lift, fitted parameters, or new
physical readout is used. The Fourier variables here are the three RELATIVE
leg phases kappa. Cartesian derivatives use the supplied tetrahedral rows.

EXACT WALL. At Gamma, F(0)=I. Write F(te_x)=I+i*t*Hx+O(t^2). Direct expansion
of EVERY Laurent coefficient gives
 Hx = [[-1,1,1,1],[1,-1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]].
Its kernel is exactly the real line (1,1,0,0): a complementary 3x3 minor is
-4. Suppose J(k) is continuous at Gamma, J(k)^2=-I, commutes with F(k), and
J(-k)=conj(J(k)) so that it acts on the original real-space field. Then J(0)
is real. Dividing [J(te_x),F(te_x)]=0 by i*t and taking the limit gives
[J(0),Hx]=0. No differentiability of J is needed, since F(0) is scalar.
Thus J(0) preserves a one-dimensional real line, where squaring to -1 is
impossible. In fact the common commutant of all three Gamma tangents is
only the scalars. The exact common commutant of ALL Laurent coefficient
matrices is also only the scalars (an on-site symmetry calculation).

This excludes EVERY continuous translation-invariant real-space complex
structure commuting with this full walk, including every finite-range or
absolutely summable convolution kernel. It does not require J to be
orthogonal. An arbitrary finite-volume discrete momentum set has no Gamma
derivative requirement; this is not a claim about every finite-size encoding.

DO NOT CONFUSE CENTRALIZERS. The full momentum-dependent Laurent-polynomial
centralizer is not just scalars: it contains F(k), its powers, and scalar
translation polynomials. We compute the constant internal/on-site commutant,
not that entire polynomial module. The continuity argument excludes a
polynomial J^2=-I without pretending other commuting polynomials are absent.

LOCAL HIT. At the real corner Q=(1,-1,1,1), F(Q)^2=-I and the checked first
order Gram is 4I. J_Q=F(Q) is a real orthogonal complex structure at that
point, but fails to commute with the full walk. A genuine k-dependent local
choice exists on a spectral patch avoiding eigenvalues +/-1: put
 A=F-F^*, J=A*(-A^2)^(-1/2), with the positive inverse square root.
It commutes with F, squares to -I, and respects reality. At Q it equals F(Q).
For max_j|delta kappa_j|<=1/8, telescoping the three pairs gives
 ||F(k)-F(Q)||<=6/8=3/4<sqrt(2), the distance from +/-i to +/-1.
This proves a nonempty separated patch, not an exact finite-range operation
or a global spectral split. Extending it continuously through Gamma is blocked.

NONLOCAL ESCAPE WITHOUT DOUBLING. On the infinite-lattice real l2 space,
J(k)=i*sign(sin(kappa_1))*I is a bounded measurable multiplier, defined almost
everywhere. It commutes with every F, respects reality, and squares to -I.
Its discontinuities forbid a continuous, finite-range, or absolutely summable
kernel. Measure-zero hyperplanes are immaterial on l2 but include Gamma;
this is not a complex structure on a retained isolated uniform mode. Thus
the result is a LOCALITY/CONTINUITY wall, not an abstract real-Hilbert-space
no-go. The arbitrary Fourier-half-space choice is additional structure.

DOUBLED ESCAPE. Two real copies diag(F,F) have the on-site complex structure
[[0,-I],[I,0]]. This is an explicit extra copy, not already present evidence.
Conversely, conjugate Floquet phases/momenta in a real field are linked by
reality and do not by themselves prove two independent mirror particles.
Complex envelopes on the local separated patch are consistent with the wall.
No complex quantum-state postulate, Born law, particle statistics, or physical
species is derived by these exact algebraic controls and elementary arguments.
"""

from __future__ import annotations

import json
import sys
from collections.abc import Iterable
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import probe_balanced_phase_composition as b
from scripts import probe_periodic_collision_metric as source
from scripts import probe_routed_diamond_cones as r

Exponent = tuple[int, int, int]
Polynomial = dict[Exponent, b.Matrix]
ORIGIN = (0, 0, 0)
LEGS = (ORIGIN, (1, 0, 0), (0, 1, 0), (0, 0, 1))
ZERO = b.scale(0, r.I4)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def shift(a: Exponent, c: Exponent) -> Exponent:
    return a[0] + c[0], a[1] + c[1], a[2] + c[2]


def clean(p: Polynomial) -> Polynomial:
    return {e: a for e, a in p.items() if a != ZERO}


def compose(p: Polynomial, q: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for e, a in p.items():
        for f, c in q.items():
            exponent = shift(e, f)
            out[exponent] = b.add(out.get(exponent, ZERO), b.multiply(a, c))
    return clean(out)


def pair_polynomial(index: int) -> Polynomial:
    rotations = r.rotations()
    a, c = divmod(index, 6)
    ca, cb = b.multiply(r.G, rotations[a]), b.multiply(r.G, rotations[c])
    out: Polynomial = {}
    for i, j in product(range(4), repeat=2):
        leg = LEGS[j]
        exponent = shift(LEGS[i], (-leg[0], -leg[1], -leg[2]))
        term = b.matrix(
            tuple(
                tuple(cb[i][j] * ca[j][col] if row == i else 0 for col in range(4))
                for row in range(4)
            )
        )
        out[exponent] = b.add(out.get(exponent, ZERO), term)
    return clean(out)


def word_polynomial() -> Polynomial:
    out = {ORIGIN: r.I4}
    for index in source.WORD:
        out = compose(pair_polynomial(index), out)
    return out


def evaluate_signs(p: Polynomial, signs: tuple[int, int, int]) -> b.Matrix:
    need(all(x in (-1, 1) for x in signs), "real Fourier corner")
    out = ZERO
    for e, a in p.items():
        factor = prod(
            -1 if sign == -1 and power % 2 else 1
            for sign, power in zip(signs, e, strict=True)
        )
        out = b.add(out, b.scale(factor, a))
    return out


def tangent(p: Polynomial, direction: Exponent) -> b.Matrix:
    out = ZERO
    for e, a in p.items():
        weight = sum(x * y for x, y in zip(e, direction, strict=True))
        out = b.add(out, b.scale(weight, a))
    return out


def commutator(a: b.Matrix, c: b.Matrix) -> b.Matrix:
    return r.sub(b.multiply(a, c), b.multiply(c, a))


def nullspace(rows: Iterable[tuple[F, ...]], width: int) -> tuple[tuple[F, ...], ...]:
    """Incremental rational RREF; the unknown width is fixed at sixteen."""
    pivots: dict[int, list[F]] = {}
    for original in rows:
        need(len(original) == width, "linear constraint width")
        row = list(original)
        for column in sorted(pivots):
            if row[column]:
                factor = row[column]
                row = [x - factor * y for x, y in zip(row, pivots[column], strict=True)]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is None:
            continue
        factor = row[pivot]
        row = [x / factor for x in row]
        for column, other in pivots.items():
            factor = other[pivot]
            pivots[column] = [x - factor * y for x, y in zip(other, row, strict=True)]
        pivots[pivot] = row
    result = []
    for free in range(width):
        if free not in pivots:
            vector = [F(int(i == free)) for i in range(width)]
            for pivot, row in pivots.items():
                vector[pivot] = -row[free]
            result.append(tuple(vector))
    return tuple(result)


def commutant(matrices: Iterable[b.Matrix]) -> tuple[b.Matrix, ...]:
    def constraints() -> Iterable[tuple[F, ...]]:
        for a in matrices:
            for i, j in product(range(4), repeat=2):
                yield tuple(
                    int(i == row) * a[col][j] - a[i][row] * int(col == j)
                    for row, col in product(range(4), repeat=2)
                )

    return tuple(
        tuple(v[4 * i : 4 * i + 4] for i in range(4))
        for v in nullspace(constraints(), 16)
    )


def polynomial_controls(p: Polynomial) -> tuple[b.Matrix, ...]:
    need(source.WORD == (14, 21, 0), "source word changed")
    need(len(p) == 147, "full Laurent support changed")
    need(evaluate_signs(p, (1, 1, 1)) == r.I4, "Gamma return")
    for signs in product((1, -1), repeat=3):
        expected = r.I4
        generators = source.generators((1, *signs))
        for index in source.WORD:
            expected = b.multiply(generators[index][0], expected)
        need(
            evaluate_signs(p, (signs[0], signs[1], signs[2])) == expected,
            "all real corners independently matched",
        )
    directions = tuple(
        (
            int(r.TETRA[1][axis] - r.TETRA[0][axis]),
            int(r.TETRA[2][axis] - r.TETRA[0][axis]),
            int(r.TETRA[3][axis] - r.TETRA[0][axis]),
        )
        for axis in range(3)
    )
    hs = tuple(tangent(p, direction) for direction in directions)
    # Independent product-rule construction from the frozen root implementation.
    expected_h: tuple[b.Matrix, ...] = (ZERO,) * 3
    generators = source.generators((1, 1, 1, 1))
    for index in source.WORD:
        gate, delta = generators[index]
        expected_h = tuple(
            b.add(x, r.conjugate(gate, y))
            for x, y in zip(delta, expected_h, strict=True)
        )
    need(hs == expected_h, "full-coefficient and product-rule tangents")
    need(all(h == b.transpose(h) for h in hs), "Hermitian Gamma generators")
    need(commutant(hs) == (r.I4,), "Gamma joint commutant is scalars")
    need(
        commutant(p.values()) == (r.I4,),
        "all Laurent coefficients have scalar common commutant",
    )
    return hs


def gamma_obstruction(hs: tuple[b.Matrix, ...]) -> dict[str, object]:
    hx = b.matrix(((-1, 1, 1, 1), (1, -1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1)))
    need(hs[0] == hx, "explicit x tangent")
    kernel = b.matrix(((1,), (1,), (0,), (0,)))
    need(b.multiply(hx, kernel) == b.scale(0, kernel), "real kernel line")
    selected = (0, 2, 3)
    minor = b.matrix(tuple(tuple(hx[i][j] for j in selected) for i in selected))
    need(b.determinant(minor) == -4, "rank exactly three")
    need(len(commutant((ZERO,))) == 16, "unconstrained commutant control")
    single = commutant((hx,))
    need(len(single) == 4, "single-tangent commutant control")
    need(all(commutator(x, hx) == ZERO for x in single), "nullspace reconstruction")
    # A commuting real J restricts to scalar c on this line, so J^2=-I
    # requires c^2=-1 over R. This is an elementary general implication,
    # not a finite search over candidate J matrices.
    return {
        "Hx": [[int(x) for x in row] for row in hx],
        "kernel_generator": [1, 1, 0, 0],
        "rank_certificate_minor": "-4",
        "joint_tangent_commutant_dimension": 1,
        "wall": "no continuous reality-compatible commuting J with J^2=-I",
    }


def local_controls(p: Polynomial, hs: tuple[b.Matrix, ...]) -> dict[str, object]:
    need(source.REPS[1] == (1, -1, 1, 1), "source corner changed")
    corner = evaluate_signs(p, (-1, 1, 1))
    need(b.multiply(corner, corner) == b.scale(-1, r.I4), "corner complex structure")
    need(
        b.transpose(corner) == b.scale(-1, corner), "orthogonal skew complex structure"
    )
    need(
        source.exact_word(source.REPS[1], source.WORD)
        == (F(0), b.scale(4, b.identity(3))),
        "frozen isotropic Gram",
    )
    need(commutator(corner, hs[0]) != ZERO, "corner J is not a global constant scalar")
    need(
        any(commutator(corner, a) != ZERO for a in p.values()),
        "full coefficient noncommutation",
    )
    delta = F(1, 8)
    bound = 2 * len(source.WORD) * delta
    need(bound == F(3, 4) and bound**2 < 2, "spectral patch avoids +/-1")
    # At Q, A=F-F*=2F and -A^2=4I, so the positive-root formula is F.
    a = r.sub(corner, b.transpose(corner))
    need(b.scale(-1, b.multiply(a, a)) == b.scale(4, r.I4), "flattening at corner")
    need(b.scale(F(1, 2), a) == corner, "local flattening normalization")
    return {
        "Q_leg_signs": [1, -1, 1, 1],
        "local_Gram": "4 I3",
        "relative_phase_patch_radius": str(delta),
        "operator_norm_difference_bound": str(bound),
        "corner_constant_J_fails_globally": True,
        "local_J": "(F-F*)[-(F-F*)^2]^(-1/2), on the separated patch",
    }


def doubled(a: b.Matrix) -> b.Matrix:
    return b.matrix(
        tuple(
            tuple(a[i % 4][j % 4] if i // 4 == j // 4 else 0 for j in range(8))
            for i in range(8)
        )
    )


def escape_controls(p: Polynomial) -> dict[str, object]:
    j = b.matrix(
        tuple(
            tuple(
                (-1 if i < 4 else 1) * int(i % 4 == col % 4)
                if i // 4 != col // 4
                else 0
                for col in range(8)
            )
            for i in range(8)
        )
    )
    need(
        b.multiply(j, j) == b.scale(-1, b.identity(8)),
        "two-copy on-site complex scalar",
    )
    need(b.transpose(j) == b.scale(-1, j), "two-copy orthogonality")
    for a in p.values():
        need(
            commutator(j, doubled(a)) == b.scale(0, j),
            "two-copy coefficient commutation",
        )

    def half_space(turns: F) -> int:
        value = turns % 1
        if value in (0, F(1, 2)):
            raise ValueError("discontinuous Fourier hyperplane")
        return 1 if value < F(1, 2) else -1

    checked = 0
    for denominator in (3, 5, 8, 12):
        for numerator in range(1, denominator):
            value = F(numerator, denominator)
            if value == F(1, 2):
                continue
            sign = half_space(value)
            need(
                sign * sign == 1 and half_space(-value) == -sign,
                "measurable i*sign reality and square",
            )
            checked += 1
    for value in (F(0), F(1, 2), F(1)):
        try:
            half_space(value)
        except ValueError:
            pass
        else:
            raise ArithmeticError(
                "discontinuity was silently assigned a continuous value"
            )
    return {
        "doubled_real_components": 8,
        "doubled_on_site_J": "[[0,-I4],[I4,0]]",
        "nonlocal_same_carrier": "i sign(sin kappa1) I4 almost everywhere on infinite-lattice l2",
        "exact_half_space_checks": checked,
        "boundary": "measurable nonlocal escape is not a continuous/local scalar",
    }


def main() -> None:
    p = word_polynomial()
    hs = polynomial_controls(p)
    result = {
        "status": "exact finite controls plus stated continuity argument; not a physical complex-state derivation",
        "word": list(source.WORD),
        "nonzero_Laurent_coefficients": len(p),
        "onsite_commutant_dimension": 1,
        "Gamma_obstruction": gamma_obstruction(hs),
        "local_patch": local_controls(p, hs),
        "escapes": escape_controls(p),
        "scope": "full polynomial centralizer not classified; no finite-range commuting complex structure by Gamma wall",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
