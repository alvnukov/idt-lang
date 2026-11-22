"""A finite five-readout relation, without fitting a density matrix.

Use complete normalized port records, common effective rows having common
probabilities, and the power-of-two row attenuation furnished by coherent
duplication. The separate duplication probe specifies operational premises
sufficient for those comparisons. No Born probabilities are used to derive
the balance between the two complete tests below. Quantum weights are used
only as an independent comparator. A failure can implicate those premises,
not every theory that happens to use signed integers.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
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
    isometry,
    run,
    synthesize_isometry,
)

Row = tuple[Gaussian, ...]
Interval = tuple[F, F]
Z0, Z1 = (ONE, ZERO), (ZERO, ONE)
B = g(F(1, 2), -F(1, 2))
XPLUS = (B, B)
YPLUS = (B, g(0, -1) * B)
TARGET = (g(F(3, 4), -F(2, 4)), g(F(1, 4), -F(1, 4)))
COEFF = (F(1), -F(7, 16), F(1, 4), -F(5, 8), -F(1, 8))  # r, Z0, Z1, X+, Y+


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def scale(t: Gaussian, row: Row) -> Row:
    return tuple(t * z for z in row)


def tests() -> tuple[Matrix, Matrix]:
    half, quarter, pi4 = g(F(1, 2)), g(F(1, 4)), g(F(1, 4), F(1, 4))
    # Identical remaining rows on both sides: their Gram equals
    # [[3, -5+i],[-5-i,10]]/16. Both outcomes are retained.
    slack = (scale(pi4, (ONE, g(-2))), scale(quarter, (ONE, g(-1, 1))))
    left = (TARGET, scale(half, Z1), *slack)
    right = (
        scale(half, Z0),
        scale(pi4, Z0),
        scale(quarter, Z0),
        scale(B, XPLUS),
        scale(pi4, XPLUS),
        scale(pi4, YPLUS),
        *slack,
    )
    return left, right


def mass(row: Row, psi: Row) -> F:
    return sum((r * x for r, x in zip(row, psi, strict=True)), ZERO).norm2()


def contrast(values: tuple[F, ...]) -> F:
    return sum((a * b for a, b in zip(values, COEFF, strict=True)), F(0))


def residual_range(intervals: tuple[Interval, ...]) -> Interval:
    if len(intervals) != len(COEFF) or any(not 0 <= a <= b <= 1 for a, b in intervals):
        raise ValueError("five simultaneous probability intervals in [0,1] required")
    terms = [
        (c * a, c * b) if c >= 0 else (c * b, c * a)
        for c, (a, b) in zip(COEFF, intervals, strict=True)
    ]
    return sum((x for x, _ in terms), F(0)), sum((y for _, y in terms), F(0))


def diagnostic(
    intervals: tuple[Interval, ...],
    row_errors: tuple[F, ...],
    shared_slack_errors: tuple[F, ...],
) -> str:
    """Bounds in probability units: 2 left + 6 right rows; 2 matched slack differences.

    These are externally certified bounds, not inferred from the five rates.
    A null route remains when calibration is missing; this API rejects a
    missing budget instead of silently substituting an exact measurement.
    """
    if (
        len(row_errors) != 8
        or len(shared_slack_errors) != 2
        or any(e < 0 or e > 1 for e in row_errors + shared_slack_errors)
    ):
        raise ValueError("eight row and two slack error bounds in [0,1] required")
    lo, hi = residual_range(intervals)
    budget = sum(row_errors + shared_slack_errors)
    return (
        "excluded_under_supplied_bounds"
        if lo > budget or hi < -budget
        else "inconclusive"
    )


def main() -> None:
    left, right = tests()
    for side in (left, right):
        need(isometry(side), "incomplete comparison")
        moves = synthesize_isometry(side)
        need(
            run(tuple(row[:2] for row in eye(len(side))), moves) == side,
            "failed exact circuit",
        )
    need(left[-2:] == right[-2:], "unmatched detector remainders")
    # Both normalized probabilities sums equal 1. Matching the last two
    # rows gives p(r)+p(Z1)/4=(7p(Z0)+10p(X+)+2p(Y+))/16. The coefficients
    # are only sums of binary splitter factors, not |z|^2 stipulated for
    # arbitrary complex scalars. This is a single finite data constraint.
    expected = (F(13, 16), F(1, 8), F(25, 32), F(17, 32))
    for bra, target_mass in zip((Z0, Z1, XPLUS, YPLUS), expected, strict=True):
        psi = tuple(w.star() for w in bra)
        p = tuple(mass(r, psi) for r in (TARGET, Z0, Z1, XPLUS, YPLUS))
        need(p[0] == target_mass and contrast(p) == 0, "independent Born comparator")
        need(
            sum(mass(r, psi) for r in left) == sum(mass(r, psi) for r in right) == 1,
            "incomplete retained mass",
        )
    squares = [mass(r, Z0) ** 2 for r in left]
    nonlinear = (squares[0] / sum(squares), F(1), F(0), F(1, 2), F(1, 2))
    need(contrast(nonlinear) == F(221, 1392), "normalized quartic control")
    points = tuple((v, v) for v in nonlinear)
    need(
        diagnostic(points, (F(0),) * 8, (F(0),) * 2) == "excluded_under_supplied_bounds"
        and diagnostic(points, (F(1, 50),) * 8, (F(0),) * 2) == "inconclusive",
        "calibration uncertainty must not force exclusion",
    )
    print(
        "Two complete native tests (4 and 8 rows) with shared remainder: "
        "16 p(r) = 7 p(Z0) - 4 p(Z1) + 10 p(X+) + 2 p(Y+)."
    )
    print(
        f"For four calibrated ideal preparations p(r)={expected}. Normalized fourth-power "
        "control on Z0 has excess 221/1392; with large enough calibration error it is not excluded."
    )
    print(
        "No physical calibration data, no Born input in the normalization identity, "
        "no claim about how an individual click is selected."
    )


if __name__ == "__main__":
    main()
