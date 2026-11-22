"""When can unobserved RAW ports evade the aligned three-family modulus wall?

Absolute (not survivor-normalized) amplitudes, ordinary lossless complex
port kinematics and the fixed common raw frame are supplied. With one spare
port the bound is uniform over word length and includes nonzero leakage.
With two spares, arbitrary target unitaries are possible only IN CLOSURE,
modulo row and column phases. Neither statement predicts any CKM element.
The companion note includes the dimension and determinant argument.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    Matrix,
    apply,
    eye,
    g,
    unitary,
)
from scripts.probe_ckm_raw_family_wall import (
    CYCLES,
    PDG,
    cycle_gaps,
    determinant,
    total_offdiagonal,
)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def target_gap() -> F:
    center = tuple(tuple(e.central for e in row) for row in PDG)
    gap = max(cycle_gaps(center)) / 3
    require((total_offdiagonal(center) + 6 * gap) ** 2 < 2, "determinant not locked")
    return gap


def minimum_one_spare_leakage(modulus_error: F, certified_distance: F) -> F:
    """Necessary SUM over the three prepared inputs into the one spare.

    Supply a justified distance of the target from the locked three-port
    class, not an uncertainty inferred from the candidate. Equality does
    not exclude the candidate; neither a converse nor a confidence bound.
    """
    if not 0 <= modulus_error <= 1 or not 0 <= certified_distance <= 1:
        raise ValueError("absolute modulus error and distance must be in [0,1]")
    return max(F(0), certified_distance - modulus_error) ** 2 / 3


Box = tuple[tuple[tuple[F, F], ...], ...]


@dataclass(frozen=True)
class BoxCheck:
    status: str
    leakage_upper: F
    cyclic_leakage_lower: F
    triangle_excess_lower: F


def one_spare_box(box: Box) -> BoxCheck:
    """Sufficient disjointness test, no fit: limits are ABSOLUTE moduli.

    Do not use conditional-on-survival frequencies or globally fitted bounds
    as independent constraints on an experimental fourth generation.
    Absence of this separating witness is always inconclusive.
    """
    if len(box) != 3 or any(len(r) != 3 for r in box):
        raise ValueError("three aligned data inputs and three outputs required")
    if any(not 0 <= lo <= hi <= 1 for r in box for lo, hi in r):
        raise ValueError("unordered interval or modulus outside [0,1]")
    norms = tuple(tuple(lo**2 for lo, _ in r) for r in box)
    upper = 3 - sum((sum(r, F(0)) for r in norms), F(0))
    if any(sum(r) > 1 for r in (*norms, *zip(*norms, strict=True))):
        return BoxCheck("incompatible_with_a_unitary_subblock", upper, F(0), F(0))
    v = max(
        F(0),
        *(
            box[i][j][0]
            - sum((box[k][l][1] for k, l in cycle if (k, l) != (i, j)), F(0))
            for cycle in CYCLES
            for i, j in cycle
        ),
    )
    s = sum((box[i][j][1] for i, j in product(range(3), repeat=2) if i != j), F(0))
    # Assume nuclear repair norm <v. The two matrix masks (cycle and
    # offdiagonal) cost at most 1 and 2 times that norm, respectively.
    # Then the repaired word is determinant-locked and still violates its
    # cycle. Thus v <= nuclear norm <= 8 sqrt(ell/3).
    lower = F(3, 64) * v**2 if (s + 2 * v) ** 2 < 2 else F(0)
    return BoxCheck(
        "excluded_one_raw_spare" if lower > upper else "inconclusive", upper, lower, v
    )


def isolated_pair(z: Gaussian) -> Matrix:
    require(z.norm2() == 1, "unit phase needed")
    a, b = g(F(1, 2)) * (ONE + z), g(F(1, 2)) * (ONE - z)
    return ((a, b), (b, a))


def two_spare_reference() -> Matrix:
    # An isolated moderately small mixing with absolutely no two other
    # family couplings. Non-dyadic rational point of the continuous group,
    # deliberately NOT claimed to be a finite raw word nor a CKM fit.
    z = g(F(15, 17), F(8, 17))
    data, spare = isolated_pair(z), isolated_pair(z.star())
    m = tuple(
        tuple(
            data[i][j]
            if i < 2 and j < 2
            else spare[i - 3][j - 3]
            if i >= 3 and j >= 3
            else g(int(i == j == 2))
            for j in range(5)
        )
        for i in range(5)
    )
    require(unitary(m) and all(sum(r, ZERO) == ONE for r in m), "uniform/metric")
    require(determinant(tuple(r[:3] for r in m[:3])) == z, "data phase")
    require(
        z * (spare[0][0] * spare[1][1] - spare[0][1] * spare[1][0]) == ONE,
        "total phase",
    )
    require(m[0][1].norm2() == F(1, 17) and m[1][2] == m[2][0] == ZERO, "isolated pair")
    require(not m[0][0].dyadic(), "not an exact raw word")
    return m


def one_spare_controls() -> int:
    edges = tuple(combinations(range(4), 2))
    layer = {eye(4)}
    seen: set[Matrix] = set()
    for depth in range(5):
        seen.update(layer)
        if depth != 4:
            layer = {apply(u, ("T", j, k)) for u in layer for j, k in edges}
    for u in seen:
        d = u[3][3]
        leak = sum((u[3][k].norm2() for k in range(3)), F(0))
        require(
            leak == 1 - d.norm2() == sum(u[k][3].norm2() for k in range(3)),
            "row/column leak",
        )
        require((ONE - d).norm2() <= 3 * leak, "reference phase bound")
        # q is the normalized component of e_4 orthogonal to the
        # four-port uniform direction. This is ||Uq-q||².
        rot2 = F(8, 3) * (1 - d.re)
        require(
            rot2 == F(4, 3) * (leak + (ONE - d).norm2()) <= F(16, 3) * leak, "rotation"
        )
        if not leak:
            data = tuple(r[:3] for r in u[:3])
            require(d == ONE and unitary(data), "exact return")
            require(all(sum(r, ZERO) == ONE for r in data), "exact uniform")
            require(
                determinant(data) in (ONE, g(-1), g(0, 1), g(0, -1)),
                "exact determinant",
            )
    return len(seen)


def main() -> None:
    gap = target_gap()
    ell = minimum_one_spare_leakage(F(0), gap)
    require(
        gap == F(45007, 750000) and F(1200, 1000000) < ell < F(1201, 1000000),
        "historical comparator",
    )
    require(minimum_one_spare_leakage(gap, gap) == 0, "loose magnitude bounds")
    box_check = one_spare_box(tuple(tuple((e.low, e.high) for e in r) for r in PDG))
    require(
        box_check.status == "excluded_one_raw_spare"
        and box_check.cyclic_leakage_lower == F(".001493342163")
        and box_check.leakage_upper == F(".001417497735"),
        "rank-two repair versus full box",
    )
    u5 = two_spare_reference()
    phases = (ONE, g(0, 1), g(F(3, 5), F(4, 5)))
    a = tuple(
        tuple(phases[i] * u5[i][j] * phases[(j + 1) % 3] for j in range(3))
        for i in range(3)
    )
    require(
        all(
            a[i][j].norm2() == u5[i][j].norm2() for i, j in product(range(3), repeat=2)
        ),
        "external phases",
    )
    print(
        f"One blank raw port: {one_spare_controls()} exact short-word controls. For the central PDG modulus target and zero additional error, total leakage must be at least {float(ell):.9f}."
    )
    print(
        f"Full quoted modulus rectangle: cyclic repair requires leakage >= {float(box_check.cyclic_leakage_lower):.12f}, but nine magnitudes permit <= {float(box_check.leakage_upper):.12f}. This is an incompatibility with a historical fitted target, not a significance test on independent measurements."
    )
    print(
        "Two blank raw ports: an explicit non-dyadic reference violates the triangle in closure. In closure two spare ports can hide an arbitrary sector determinant; arbitrary CKM equivalence classes can be approximated, not predicted."
    )
    print(
        "At exactly ZERO leakage a finite Gaussian-dyadic raw word still has a four-valued data determinant, for ANY number of spare ports. No measurement of hidden-sector leakage is supplied."
    )


if __name__ == "__main__":
    main()
