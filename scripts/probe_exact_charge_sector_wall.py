"""Exact conservation versus conservation in the limit of native paired-rail words.

Gaussian-dyadic entries are closed under any finite word. For coordinate
charge blocks, exact no-leakage makes each block unitary, so each determinant
is a Gaussian-dyadic scalar of norm one. These are just the four axis units:
if a^2+b^2=4^k and k>0 then a,b are both even (reduce modulo four).

This does not restrict determinants of nonunitary subblocks with small
leakage. We construct exact dyadic unitaries approaching a specific 3+2
relative phase, then actually synthesize them with T and i. We do not infer a
charge superselection rule, visibility across charges, gauge fields, or a fit.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    eye,
    g,
    run,
    synthesize,
    unitary,
)

Z = g(F(3, 5), F(4, 5))
AXES = (ONE, I, g(-1), g(0, -1))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def unit_power(z: Gaussian, n: int) -> Gaussian:
    if n < 0:
        return unit_power(z.star(), -n)
    answer = ONE
    for _ in range(n):
        answer = answer * z
    return answer


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def circle_units(denom: int) -> set[Gaussian]:
    if denom < 1:
        raise ValueError("positive denominator required")
    points: set[Gaussian] = set()
    for a in range(-denom, denom + 1):
        b2 = denom**2 - a**2
        b = isqrt(b2)
        if b * b == b2:
            points.update((g(F(a, denom), F(b, denom)), g(F(a, denom), F(-b, denom))))
    return points


@cache
def four_squares(n: int) -> tuple[int, int, int, int]:
    """Finite certificate finder; Lagrange's theorem explains general existence."""
    if n < 0:
        raise ValueError("negative remainder")
    pairs: dict[int, tuple[int, int]] = {}
    for x in range(isqrt(n // 2) + 1):
        for y in range(x, isqrt(n - x * x) + 1):
            s = x * x + y * y
            pairs.setdefault(s, (x, y))
            if n - s in pairs:
                return x, y, *pairs[n - s]
    raise ArithmeticError("missing four-square witness")


def paired_rotation(j: int, k: int, level: int) -> Matrix:
    """R(v) R((e_j+e_k)/sqrt(2)) approaches diag(conj(z),z) at j,k.

    v truncates the three real components of (e_j+z e_k)/sqrt(2)
    downwards; a four-square certificate fills the missing norm on two
    spectator slots. Truncation error is <2^-level per real component,
    and added squared norm tends to zero. No irrational gate is supplied.
    """
    if not (0 <= j < k < 5 and level >= 1):
        raise ValueError("ordered slots in five-slot carrier; positive level")
    d = 2**level
    a, b, c = isqrt(d * d // 2), isqrt(9 * d * d // 50), isqrt(16 * d * d // 50)
    l, m, n, p = four_squares(d * d - a * a - b * b - c * c)
    rest = [t for t in range(5) if t not in (j, k)]
    v = [ZERO] * 5
    v[j], v[k] = g(F(a, d)), g(F(b, d), F(c, d))
    v[rest[0]], v[rest[1]] = g(F(l, d), F(m, d)), g(F(n, d), F(p, d))
    need(sum(x.norm2() for x in v) == 1, "reflection normal is not unit")
    # Multiplication on the right by the exact balanced reference reflection
    # just exchanges and negates columns j and k.
    h = tuple(
        tuple(g(int(r == s)) - g(2) * v[r] * v[s].star() for s in range(5))
        for r in range(5)
    )
    return tuple(
        tuple(
            ZERO - row[k] if s == j else ZERO - row[j] if s == k else row[s]
            for s in range(5)
        )
        for row in h
    )


def five_slot_target() -> Matrix:
    phases = (unit_power(Z, -2),) * 3 + (unit_power(Z, 3),) * 2
    return tuple(
        tuple(phases[r] if r == s else ZERO for s in range(5)) for r in range(5)
    )


def approximant(level: int) -> Matrix:
    u = eye(5)
    for j, k in product(range(3), range(3, 5)):
        u = mm(paired_rotation(j, k, level), u)
    return u


def distance2(a: Matrix, b: Matrix) -> F:
    return sum(
        (
            (x - y).norm2()
            for ra, rb in zip(a, b, strict=True)
            for x, y in zip(ra, rb, strict=True)
        ),
        F(0),
    )


def leakage2(a: Matrix) -> F:
    """Sum over input axes of leaked weight, not a probability for one input."""
    return sum(
        (
            x.norm2()
            for r, row in enumerate(a)
            for s, x in enumerate(row)
            if (r < 3) != (s < 3)
        ),
        F(0),
    )


def exact_projective_gap2() -> F:
    """Lower bound for squared operator distance even modulo a common phase.

    Compare (det A)^2 conjugate(det B)^3; it is immune to one common phase.
    Each determinant changes by at most its block size times operator
    distance (telescope unit columns); powers have Lipschitz factors 2,3.
    Thus every exact block-preserving word is separated from this target by
    at least dist(z^-30, fourth roots)/12, independent of word length.
    """
    invariant = unit_power(Z, -30)
    return min((invariant - u).norm2() for u in AXES) / 144


def main() -> None:
    for d in (1, 2, 4, 8, 16, 32, 64, 128, 3, 7, 9, 21):
        need(circle_units(d) == set(AXES), "axis-unit denominator controls")
    for d in (5, 10, 13, 15, 17, 25):
        need(len(circle_units(d)) > 4, "split-prime enlargement control")
    need(Z in circle_units(5) and Z.norm2() == 1, "rational phase comparator")
    target, gap = five_slot_target(), exact_projective_gap2()
    need(unitary(target) and gap > 0, "target or projective gap")
    errors = []
    for level in (3, 8, 13, 18):
        approx = approximant(level)
        word = synthesize(approx)
        need(run(eye(5), word) == approx, "exact native reconstruction")
        err, leak = distance2(approx, target), leakage2(approx)
        mixers = sum(tag == "T" for tag, _, _ in word)
        need(0 < leak <= err and leak >= F(1, 2**mixers), "depth/leakage control")
        errors.append(err)
        print(
            f"level {level}: {len(word)} logical instructions ({mixers} mixers), "
            f"squared Frobenius distance {float(err):.6g}, total off-block weight {float(leak):.6g}"
        )
    need(
        errors[-1] < gap < errors[0],
        "native approximant crosses exact projective exclusion",
    )
    print(
        f"Exact block conservation, even modulo common phase: squared operator-distance "
        f"lower bound {float(gap):.6g}. Comparisons used rational arithmetic."
    )
    print(
        "Supplied: paired code, addressed logical control, norm and rational coordinate charges. "
        "Approximate conservation is not exact conservation; no gauge or observability conclusion."
    )


if __name__ == "__main__":
    main()
