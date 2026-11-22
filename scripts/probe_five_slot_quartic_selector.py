"""Exact conditional selector on a supplied five-dimensional spectral space.

Analytic argument (not a Lean proof): on sum(x)=0, sum(x*x)=1, extrema of
sum(x**4) satisfy 4*x**3 - 2*lambda*x - mu = 0. The constraint gradients
are independent, so every extremum has at most three distinct real roots.
For two roots with multiplicities m, 5-m use values 5-m, -m up to scale.
For three distinct roots a,b,c their sum is zero. Multiplicities p,q,r
also give p*a+q*b+r*c=0, hence (a,b,c) is proportional to
(q-r,r-p,p-q). All six positive ordered compositions p+q+r=5 are below.
Compactness plus this complete critical-point list proves the extrema.

Consequently 7/30 <= tr(X^4)/tr(X^2)^2 <= 13/20 for a nonzero traceless
Hermitian 5-by-5 X, conditional on the supplied spectral representation.
The lower equality has a 3+2 spectrum; the upper equality has 4+1.

For V=-m2*tr(X^2)+lam*tr(X^2)^2+kappa*tr(X^4), define
beta=lam+kappa*(7/30 if kappa>=0 else 13/20). If beta<0, V is unbounded
below. If beta=0 it is unbounded for m2>0, has flat zero-energy rays for
m2=0, and has the unique zero minimum for m2<0. If beta>0, m2<=0 again
gives zero; m2>0 gives radius squared m2/(2*beta) and the sign-selected
shape. Kappa=0 leaves every shape degenerate. Cubic terms are NOT excluded
by tracelessness or conjugation invariance; an explicit tilt defeats 3+2.

Five slots, a real/Hermitian spectral carrier, tracelessness, the second
moment constraint and the objective are inputs. This does not derive
their IDT origin, fermions, particles, gauge redundancy or gauge dynamics.
No literature attribution or empirical fit is used by this probe.
"""

from __future__ import annotations

import argparse
import json
import unittest
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd


def require(condition: bool, message: object) -> None:
    """Keep executable gates active under python -O."""
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True, order=True)
class Spectrum:
    values: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.values) != 5 or sum(self.values) != 0 or not any(self.values):
            raise ValueError("expected five nonzero-in-total traceless values")

    @property
    def second(self) -> int:
        return sum(value**2 for value in self.values)

    @property
    def fourth_ratio(self) -> Fraction:
        return Fraction(sum(value**4 for value in self.values), self.second**2)

    @property
    def cubic_square(self) -> Fraction:
        """Square of tr(X^3) after normalizing tr(X^2)=1."""
        return Fraction(sum(value**3 for value in self.values) ** 2, self.second**3)

    @property
    def multiplicities(self) -> tuple[int, ...]:
        return tuple(sorted(Counter(self.values).values(), reverse=True))

    @property
    def centralizer_dimension(self) -> int:
        """Lie dimension inside a SUPPLIED SU(5), not a local gauge claim."""
        return sum(size**2 for size in self.multiplicities) - 1


def canonical(values: tuple[int, ...]) -> Spectrum:
    divisor = reduce(gcd, (abs(value) for value in values), 0)
    if divisor == 0:
        raise ValueError("zero has no unit-second-moment normalization")
    scaled = tuple(value // divisor for value in values)
    return Spectrum(max(tuple(sorted(scaled)), tuple(sorted(-x for x in scaled))))


def two_root_candidates() -> tuple[tuple[tuple[int, int], Spectrum], ...]:
    return tuple(
        ((m, 5 - m), canonical((5 - m,) * m + (-m,) * (5 - m))) for m in range(1, 5)
    )


def three_root_candidates() -> tuple[tuple[tuple[int, int, int], Spectrum], ...]:
    rows: list[tuple[tuple[int, int, int], Spectrum]] = []
    for p in range(1, 4):
        for q in range(1, 5 - p):
            r = 5 - p - q
            a, b, c = q - r, r - p, p - q
            require(r > 0 and len({a, b, c}) == 3, (p, q, r))
            require(a + b + c == p * a + q * b + r * c == 0, "root constraints")
            # Every root obeys the same depressed cubic, without approximation.
            for root in (a, b, c):
                require(
                    root**3 + (a * b + a * c + b * c) * root - a * b * c == 0,
                    "common critical polynomial",
                )
            rows.append(((p, q, r), canonical((a,) * p + (b,) * q + (c,) * r)))
    return tuple(rows)


def critical_spectra() -> tuple[Spectrum, ...]:
    return tuple(
        sorted({row[1] for row in two_root_candidates() + three_root_candidates()})
    )


def quartic_shape(kappa: Fraction) -> str:
    if kappa > 0:
        return "3+2"
    if kappa < 0:
        return "4+1"
    return "entire traceless unit sphere"


def radial_coefficient(lam: Fraction, kappa: Fraction) -> Fraction:
    endpoint = Fraction(7, 30) if kappa >= 0 else Fraction(13, 20)
    return lam + kappa * endpoint


def radial_regime(m2: Fraction, lam: Fraction, kappa: Fraction) -> str:
    beta = radial_coefficient(lam, kappa)
    if beta < 0 or (beta == 0 and m2 > 0):
        return "unbounded below"
    if beta == 0 and m2 == 0:
        return "flat zero-energy rays"
    if m2 <= 0:
        return "unique zero minimum"
    return "nonzero minimum: " + quartic_shape(kappa)


def cubic_tilt_control() -> dict[str, str]:
    """At fixed second moment, tr(X^4)+tr(X^3) defeats both 3+2 signs.

    Favorable 3+2 has energy 7/30-1/sqrt(30)>1/30.
    Favorable 4+1 has energy 13/20-3/sqrt(20)<-1/60.
    The exact rational comparisons below prove a gap greater than 1/20.
    This is a counterexample, not a complete minimization of the tilted model.
    """
    balanced = canonical((-2, -2, -2, 3, 3))
    unbalanced = canonical((-1, -1, -1, -1, 4))
    require(balanced.cubic_square == Fraction(1, 30), "3+2 cubic")
    require(unbalanced.cubic_square == Fraction(9, 20), "4+1 cubic")
    require(balanced.cubic_square < Fraction(1, 5) ** 2, "upper square-root bound")
    require(unbalanced.cubic_square > Fraction(2, 3) ** 2, "lower square-root bound")
    balanced_lower = balanced.fourth_ratio - Fraction(1, 5)
    unbalanced_upper = unbalanced.fourth_ratio - Fraction(2, 3)
    require(balanced_lower - unbalanced_upper == Fraction(1, 20), "strict tilt gap")
    return {
        "3+2_energy_strictly_above": str(balanced_lower),
        "4+1_energy_strictly_below": str(unbalanced_upper),
        "gap_strictly_above": "1/20",
    }


def cut_maximizers(n: int) -> tuple[int, ...]:
    """Number of cross-color edges on a supplied complete two-color graph."""
    if n < 1:
        raise ValueError("positive slot count required")
    scores = tuple(k * (n - k) for k in range(n + 1))
    return tuple(k for k, score in enumerate(scores) if score == max(scores))


def audit() -> dict[str, object]:
    two, three = two_root_candidates(), three_root_candidates()
    require(len(two) == 4 and len(three) == 6, "complete ordered multiplicities")
    spectra = critical_spectra()
    expected = {
        canonical((-2, -2, -2, 3, 3)): Fraction(7, 30),
        canonical((-1, -1, 0, 1, 1)): Fraction(1, 4),
        canonical((-1, 0, 0, 0, 1)): Fraction(1, 2),
        canonical((-1, -1, -1, -1, 4)): Fraction(13, 20),
    }
    require({s: s.fourth_ratio for s in spectra} == expected, "critical spectra")
    require(min(expected.values()) == Fraction(7, 30), "quartic minimum")
    require(max(expected.values()) == Fraction(13, 20), "quartic maximum")
    require(quartic_shape(Fraction(1)) == "3+2", "positive quartic")
    require(quartic_shape(Fraction(-1)) == "4+1", "reversed quartic")
    require(
        quartic_shape(Fraction(0)) == "entire traceless unit sphere", "flat quartic"
    )
    for n in range(1, 32):
        require(
            cut_maximizers(n) == tuple(sorted({n // 2, (n + 1) // 2})), "balanced cut"
        )
        for k in range(n + 1):
            require(4 * k * (n - k) == n * n - (n - 2 * k) ** 2, "cut identity")
    require(cut_maximizers(5) == (2, 3), "five-slot cut")
    rows = [
        {
            "values_up_to_scale_and_sign": list(s.values),
            "multiplicities": list(s.multiplicities),
            "fourth_over_second_squared": str(s.fourth_ratio),
            "supplied_su5_centralizer_dimension": s.centralizer_dimension,
        }
        for s in sorted(spectra, key=lambda s: s.fourth_ratio)
    ]
    return {
        "ok": True,
        "two_root_ordered_cases": len(two),
        "three_root_ordered_cases": len(three),
        "critical_spectra": rows,
        "positive_quartic": quartic_shape(Fraction(1)),
        "negative_quartic": quartic_shape(Fraction(-1)),
        "zero_quartic": quartic_shape(Fraction(0)),
        "cubic_tilt_control": cubic_tilt_control(),
        "two_color_complete_graph_cut": list(cut_maximizers(5)),
        "boundary": "conditional exact finite audit; analytic completeness argument in docstring; no Lean proof; no derivation of five slots, spectral carrier, objective, or gauging",
    }


class SelectorTests(unittest.TestCase):
    def test_complete_critical_multiplicities(self) -> None:
        self.assertEqual(len(two_root_candidates()), 4)
        self.assertEqual(len(three_root_candidates()), 6)
        self.assertEqual(len(critical_spectra()), 4)
        self.assertTrue(audit()["ok"])

    def test_scale_sign_and_invalid_spectra(self) -> None:
        self.assertEqual(canonical((-4, -4, -4, 6, 6)), canonical((2, 2, 2, -3, -3)))
        for values in ((0, 0, 0, 0, 0), (1, 1, 1, 1, 1), (1, -1)):
            with self.assertRaises(ValueError):
                canonical(values)

    def test_competing_shapes_and_global_centralizers(self) -> None:
        balanced = canonical((-2, -2, -2, 3, 3))
        two_two_zero = canonical((-1, -1, 0, 1, 1))
        unbalanced = canonical((-1, -1, -1, -1, 4))
        self.assertLess(balanced.fourth_ratio, two_two_zero.fourth_ratio)
        self.assertLess(two_two_zero.fourth_ratio, unbalanced.fourth_ratio)
        self.assertEqual(
            tuple(
                s.centralizer_dimension for s in (balanced, unbalanced, two_two_zero)
            ),
            (12, 16, 8),
        )

    def test_full_radial_parameter_regimes(self) -> None:
        f = Fraction
        self.assertEqual(radial_regime(f(1), f(0), f(1)), "nonzero minimum: 3+2")
        self.assertEqual(radial_regime(f(1), f(1), f(-1)), "nonzero minimum: 4+1")
        self.assertEqual(
            radial_regime(f(1), f(1), f(0)),
            "nonzero minimum: entire traceless unit sphere",
        )
        self.assertEqual(radial_regime(f(1), f(-7, 30), f(1)), "unbounded below")
        self.assertEqual(radial_regime(f(0), f(-7, 30), f(1)), "flat zero-energy rays")
        self.assertEqual(radial_regime(f(-1), f(-7, 30), f(1)), "unique zero minimum")
        self.assertEqual(radial_regime(f(-1), f(-1), f(1)), "unbounded below")
        self.assertEqual(radial_regime(f(0), f(1), f(-1)), "unique zero minimum")

    def test_cubic_countercontrol(self) -> None:
        self.assertEqual(cubic_tilt_control()["gap_strictly_above"], "1/20")

    def test_cut_requires_two_colors_and_repulsion(self) -> None:
        self.assertEqual(cut_maximizers(5), (2, 3))
        scores = [k * (5 - k) for k in range(6)]
        self.assertEqual(
            [k for k, score in enumerate(scores) if score == min(scores)], [0, 5]
        )
        self.assertEqual(
            [k for k in range(1, 5) if scores[k] == min(scores[1:5])], [1, 4]
        )
        # A third supplied color permits 2+2+1 and eight cross-color edges,
        # versus six with two colors. The two-color premise is not selected.
        self.assertEqual((25 - (2**2 + 2**2 + 1**2)) // 2, 8)
        self.assertEqual(max(scores), 6)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="print the exact audit packet"
    )
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print("PASS: all 4 two-root and 6 three-root ordered critical cases checked.")
        print(
            "Fixed second moment: 3+2 = 7/30 < 2+2+0 = 1/4 < 1+1+3zero = 1/2 < 4+1 = 13/20."
        )
        print(
            "Positive quartic selects 3+2; negative selects 4+1; zero leaves every shape."
        )
        print(
            "Cubic tilt tr(X^4)+tr(X^3): a 4+1 spectrum beats both 3+2 signs by > 1/20."
        )
        print(
            "Two-color complete-graph repulsion selects 3+2, conditional on two colors and five slots."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
