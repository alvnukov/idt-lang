"""Constructive finite row-rule bridge, conditional on fine-row noncontextuality.

ANALYTICAL CLAIM (not a Lean proof). Fix finite input dimension d and
D=Z[i,1/2]=Z[i,1/(1+i)]. Tests are ALL finite rectangular D-isometries.
For one fixed preparation, a specific row r has one real value f(r), independent
of its completed test and output position. On every test its values are
nonnegative and sum to one. f is required only on rows occurring in tests.
No continuity, probability homogeneity, pure-state calibration, or prior Born
rule is assumed. Availability of every such compiled test and the row-level
operational identification are substantial premises, not compiler outputs.

1. Appending a zero row gives f(0)=0. Replacing r by two identical r/pi,
   pi=1+i, preserves the Gram matrix, so normalization gives f(r)=2f(r/pi).
   The replacement is itself a native isometry; f(r) is bounded by one only
   for admitted rows, not arbitrary unscaled vectors. Repeating the split
   handles every denominator exponent, including odd k with its phase.
2. For any finite D-row list R, attenuate every row by pi^(-k). For large k,
   H=I-2^(-k)R*R satisfies H_ii > sum_{j!=i}(|Re H_ij|+|Im H_ij|).
   This componentwise l1 dominance, stronger than ordinary complex-modulus
   dominance, permits a finite exact Gram decomposition using coordinate,
   e_i +/- e_j, and e_i +/- i e_j rows. Each nonnegative dyadic coefficient
   is a sum of four dyadic squares: make its denominator an even power of
   two and apply the integer four-square theorem to its numerator.
3. Equal-Gram lists R,S have the SAME remainder H and padding C. Comparing
   the two completed tests cancels sum f(C). Thus 2^k sum f(pi^(-k)R) depends
   only on R*R, not list or sufficiently large k. Independence of k follows
   from the identical-row split, not a supplied homogeneity axiom.
4. Concatenation gives an additive functional on the native Gram cone.
   The cone is half-closed by splitting and spans every Hermitian D-matrix:
   for sufficiently large integer M, both MI+X and MI have constructive Gram
   decompositions. The Grothendieck difference functional is well-defined
   because A-B=A'-B' implies A+B'=A'+B. It is Z[1/2]-linear.
5. Values on the finite Hermitian coordinate basis specify one complex
   Hermitian matrix rho by real parameters, with F(X)=tr(rho X). This formula
   supplies a continuous quadratic polynomial; no continuity of f was used.
   Nonnegativity on all native rank-one rows, after admissible attenuation,
   and density of D^d imply rho>=0. The identity test gives tr(rho)=1.
   Hence f(r)=r rho r* on every admitted native row. Continuity only extends
   the derived formula mathematically; application to nonnative physical tests
   needs its own approximation bridge. rho=|psi><psi| needs a preparation or
   calibration premise; this argument reconstructs some density matrix.

NON-DUPLICATION. DyadicEffectDomainActualization supplies a complex effect
domain, calibration and closure/additivity for EVERY admissible cross-context
sum. Here constructive common padding transfers additivity from normalized
finite native frames, but fine-row noncontextuality remains supplied.
GeneratedEventConeControl shows why an insufficient generated cone cannot be
silently replaced by the full positive order. Here the native Gram cone spans
the Hermitian dyadic module and its vector directions are dense; arbitrary
positive-semidefinite boundary matrices need not have an exact native factor.

OPERATIONAL WALL. The columns ((1+6i),3,3,3)/8 and ((1+6i),5,1,1)/8 are
native unit columns with the identical first row. Their unread coordinate
ideals are 3D and D. Any invertible dyadic unread-output matrix preserves the
coordinate ideal, even after adding zero outputs. Blank-input rotations fixing
the active input do not change the active column, so do not remove this
obstruction either. This blocks a direct unread-rest orbit proof, not every
possible derivation from additional operational axioms.

The nonlinear normalized-square control satisfies per-test normalization but
violates fine-row noncontextuality (and generally unread-basis invariance).
The uniform-per-port control respects unread-basis changes at fixed output
count but fails zero-output stabilization. Neither is advertised as a model
satisfying all stronger premises. No probability origin or QM status upgrade.
"""

from __future__ import annotations

import argparse
import json
import sys
import unittest
from collections.abc import Callable, Sequence
from fractions import Fraction as F
from functools import cache
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    eye,
    g,
    isometry,
    run,
    synthesize_isometry,
)

Row = tuple[Gaussian, ...]
PI_INV = g(F(1, 2), F(-1, 2))
RowLaw = Callable[[Row], F]


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def attenuator(k: int) -> Gaussian:
    if k < 0:
        raise ValueError("nonnegative exponent required")
    value = ONE
    for _ in range(k):
        value = value * PI_INV
    return value


def scaled(rows: Matrix, value: Gaussian) -> Matrix:
    return tuple(tuple(value * x for x in row) for row in rows)


def gram(rows: Matrix, width: int) -> Matrix:
    if width < 1 or any(len(row) != width for row in rows):
        raise ValueError("positive common row width required")
    return tuple(
        tuple(sum((row[i].star() * row[j] for row in rows), ZERO) for j in range(width))
        for i in range(width)
    )


def hermitian(a: Matrix) -> bool:
    return (
        bool(a)
        and all(len(row) == len(a) for row in a)
        and all(a[i][j] == a[j][i].star() for i in range(len(a)) for j in range(len(a)))
    )


def dominance_margin(a: Matrix, i: int) -> F:
    return a[i][i].re - sum(
        (abs(a[i][j].re) + abs(a[i][j].im) for j in range(len(a)) if i != j), F(0)
    )


@cache
def four_squares(n: int) -> tuple[int, int, int, int]:
    """Finite exact search; existence uses Lagrange's integer four-square theorem.

    Time/storage can grow with n; this is a constructive finite benchmark,
    not a polynomial-resource claim for arbitrarily encoded coefficients.
    """
    if n < 0:
        raise ValueError("nonnegative integer required")
    pairs: dict[int, tuple[int, int]] = {}
    for a in range(isqrt(n) + 1):
        for b in range(a, isqrt(n - a * a) + 1):
            pairs.setdefault(a * a + b * b, (a, b))
    for subtotal, left in pairs.items():
        if n - subtotal in pairs:
            result = (*left, *pairs[n - subtotal])
            require(sum(x * x for x in result) == n, "four-square identity")
            return result
    raise ArithmeticError("integer four-square search failed")


def dyadic_squares(value: F) -> tuple[F, ...]:
    denominator = value.denominator
    if value < 0 or denominator & (denominator - 1):
        raise ValueError("nonnegative dyadic coefficient required")
    power = denominator.bit_length() - 1
    numerator = value.numerator
    if power % 2:
        numerator *= 2
        power += 1
    terms = tuple(F(x, 1 << (power // 2)) for x in four_squares(numerator) if x)
    require(sum((x * x for x in terms), F(0)) == value, "dyadic four-square identity")
    return terms


def dominant_gram(a: Matrix) -> Matrix:
    """Exact componentwise-diagonally-dominant Hermitian Gram decomposition."""
    if not hermitian(a) or not all(x.dyadic() for row in a for x in row):
        raise ValueError("Hermitian Gaussian-dyadic matrix required")
    if any(dominance_margin(a, i) < 0 for i in range(len(a))):
        raise ValueError("componentwise l1 diagonal dominance required")
    width = len(a)
    rows: list[Row] = []
    for i in range(width):
        for j in range(i + 1, width):
            for coefficient, phase in ((a[i][j].re, ONE), (a[i][j].im, I)):
                sign = 1 if coefficient >= 0 else -1
                for amplitude in dyadic_squares(abs(coefficient)):
                    row = [ZERO] * width
                    row[i], row[j] = g(amplitude), g(sign * amplitude) * phase
                    rows.append(tuple(row))
        for amplitude in dyadic_squares(dominance_margin(a, i)):
            rows.append(tuple(g(amplitude) if j == i else ZERO for j in range(width)))
    result = tuple(rows)
    require(gram(result, width) == a, "constructive remainder Gram identity")
    return result


def common_padding(
    lists: Sequence[Matrix], width: int
) -> tuple[int, Matrix, tuple[Matrix, ...]]:
    """Attenuate arbitrary finite equal-Gram native lists, then use one remainder."""
    if not lists or any(not x.dyadic() for rows in lists for row in rows for x in row):
        raise ValueError("nonempty family of Gaussian-dyadic row lists required")
    total = gram(lists[0], width)
    if any(gram(rows, width) != total for rows in lists):
        raise ValueError("lists must have the same Gram matrix")
    k = 0
    while True:
        factor = g(F(1, 1 << k))
        remainder = tuple(
            tuple(
                (ONE if i == j else ZERO) - factor * total[i][j] for j in range(width)
            )
            for i in range(width)
        )
        if all(dominance_margin(remainder, i) > 0 for i in range(width)):
            break
        k += 1
    padding = dominant_gram(remainder)
    attenuated = tuple(scaled(rows, attenuator(k)) for rows in lists)
    require(
        all(isometry(rows + padding) for rows in attenuated),
        "all common-padding tests are isometries",
    )
    return k, padding, attenuated


def hermitian_difference(a: Matrix) -> tuple[Matrix, Matrix]:
    """Construct X=A* A-B* B for every finite Hermitian Gaussian-dyadic X."""
    if not hermitian(a) or not all(x.dyadic() for row in a for x in row):
        raise ValueError("Hermitian Gaussian-dyadic matrix required")
    bound = max(
        abs(a[i][i].re)
        + sum(
            (abs(a[i][j].re) + abs(a[i][j].im) for j in range(len(a)) if i != j), F(0)
        )
        for i in range(len(a))
    )
    shift = bound.numerator // bound.denominator + 1
    base = tuple(
        tuple(g(shift) if i == j else ZERO for j in range(len(a)))
        for i in range(len(a))
    )
    raised = tuple(
        tuple(base[i][j] + a[i][j] for j in range(len(a))) for i in range(len(a))
    )
    positive, negative = dominant_gram(raised), dominant_gram(base)
    gp, gn = gram(positive, len(a)), gram(negative, len(a))
    require(
        tuple(tuple(gp[i][j] - gn[i][j] for j in range(len(a))) for i in range(len(a)))
        == a,
        "Hermitian group-completion witness",
    )
    return positive, negative


def compiled(target: Matrix) -> int:
    moves = synthesize_isometry(target)
    initial = tuple(row[: len(target[0])] for row in eye(len(target)))
    require(run(initial, moves) == target, "exact native compiler replay")
    return len(moves)


def density_from_gram(rows: Matrix, width: int) -> Matrix:
    a = gram(rows, width)
    trace = sum((a[i][i].re for i in range(width)), F(0))
    if trace <= 0:
        raise ValueError("nonzero positive Gram required")
    return scaled(a, g(1 / trace))


def density_weight(row: Row, rho: Matrix) -> F:
    value = sum(
        (
            row[i] * rho[i][j] * row[j].star()
            for i in range(len(row))
            for j in range(len(row))
        ),
        ZERO,
    )
    require(value.im == 0, "real density weight")
    return value.re


def extended_weight(row: Row, law: RowLaw) -> F:
    """Query law only on an explicitly completed row, never an unbounded row."""
    k, _, attenuated = common_padding(((row,),), len(row))
    return (1 << k) * law(attenuated[0][0])


def tomography(width: int, law: RowLaw) -> Matrix:
    axes = tuple(
        tuple(ONE if i == j else ZERO for j in range(width)) for i in range(width)
    )
    diagonal = tuple(extended_weight(row, law) for row in axes)
    result = [
        [g(diagonal[i]) if i == j else ZERO for j in range(width)] for i in range(width)
    ]
    for i in range(width):
        for j in range(i + 1, width):
            real_row = tuple(axes[i][k] + axes[j][k] for k in range(width))
            imag_row = tuple(axes[i][k] + I * axes[j][k] for k in range(width))
            re = (extended_weight(real_row, law) - diagonal[i] - diagonal[j]) / 2
            im = (extended_weight(imag_row, law) - diagonal[i] - diagonal[j]) / 2
            result[i][j], result[j][i] = g(re, im), g(re, -im)
    return tuple(tuple(row) for row in result)


def bridge_controls() -> list[dict[str, object]]:
    examples: tuple[Matrix, ...] = (
        ((ONE, g(F(1, 2), F(1, 2))), (g(0, F(1, 2)), g(-1))),
        ((ONE, g(F(1, 2)), ZERO), (ZERO, I, g(F(1, 2))), (g(0, F(1, 2)), ZERO, ONE)),
    )
    output: list[dict[str, object]] = []
    for rows in examples:
        width = len(rows[0])
        left = tuple(PI_INV * (a + b) for a, b in zip(rows[0], rows[1], strict=True))
        right = tuple(PI_INV * (a - b) for a, b in zip(rows[0], rows[1], strict=True))
        other = (left, right, *rows[2:])
        k, padding, attenuated = common_padding((rows, other), width)
        move_counts = [compiled(part + padding) for part in attenuated]
        state_rows = tuple(
            tuple(ONE if i == j else ZERO for j in range(width))
            for i in range(width - 1)
        )
        state_rows += (tuple(I if j == 1 else ONE for j in range(width)),)
        rho = density_from_gram(state_rows, width)

        def law(row: Row, state: Matrix = rho) -> F:
            return density_weight(row, state)

        require(tomography(width, law) == rho, "exact Hermitian density tomography")
        totals = []
        for part in attenuated:
            values = tuple(law(row) for row in part + padding)
            require(
                min(values) >= 0 and sum(values) == 1,
                "supplied density control normalized",
            )
            totals.append(sum((law(row) for row in part), F(0)))
        require(totals[0] == totals[1], "same-Gram sum control")
        output.append(
            {
                "input_dimension": width,
                "attenuation_exponent": k,
                "padding_rows": len(padding),
                "compiler_moves": move_counts,
                "same_Gram_probability_sum": str(totals[0]),
                "density_trace": str(sum((rho[i][i].re for i in range(width)), F(0))),
            }
        )
    return output


def ideal_and_context_controls() -> dict[str, object]:
    first = g(F(1, 8), F(6, 8))
    left = ((first,), (g(F(3, 8)),), (g(F(3, 8)),), (g(F(3, 8)),))
    right = ((first,), (g(F(5, 8)),), (g(F(1, 8)),), (g(F(1, 8)),))
    require(
        isometry(left) and isometry(right) and left[0] == right[0],
        "same effective row completions",
    )
    counts = (compiled(left), compiled(right))

    def residue(value: Gaussian) -> tuple[int, int]:
        if not value.dyadic():
            raise ValueError("native Gaussian-dyadic entry required")
        residues = tuple(
            x.numerator * pow(x.denominator, -1, 3) % 3 for x in (value.re, value.im)
        )
        return residues[0], residues[1]

    require(
        all(residue(row[0]) == (0, 0) for row in left[1:]),
        "unread ideal contained in 3D",
    )
    require(
        left[1][0] == g(F(3, 8)) and right[2][0] == g(F(1, 8)),
        "unread ideals exactly 3D and D",
    )
    require(
        residue(right[2][0]) != (0, 0), "odd ideal remains proper after inverting two"
    )

    def nonlinear_first(test: Matrix) -> F:
        weights = tuple(row[0].norm2() ** 2 for row in test)
        return weights[0] / sum(weights)

    p_left, p_right = nonlinear_first(left), nonlinear_first(right)
    require(
        p_left == F(1369, 1612) and p_right == F(1369, 1996),
        "nonlinear normalization-only counter",
    )
    stabilized = left + ((ZERO,),)
    require(isometry(stabilized), "zero-output stabilization is native")
    uniform_before, uniform_after = F(1, len(left)), F(1, len(stabilized))
    require(
        len(left) * uniform_before == len(stabilized) * uniform_after == 1
        and uniform_before != uniform_after,
        "uniform ports normalize but violate zero-output stability",
    )
    # Same-Gram scalar rows can differ by a phase not in D, yet acquire common
    # native padding. This is not assumed native scalar-phase transitivity.
    phase_rows = (((g(F(3, 8), F(4, 8)),),), ((g(F(5, 8)),),))
    _, padding, small = common_padding(phase_rows, 1)
    phase_moves = [compiled(rows + padding) for rows in small]
    odd_phase = g(F(3, 5), F(4, 5))
    require(
        odd_phase.norm2() == 1
        and not odd_phase.dyadic()
        and odd_phase * g(F(5, 8)) == g(F(3, 8), F(4, 8)),
        "equal-Gram scalar phase lies outside the native ring",
    )
    return {
        "observed_row": "(1+6i)/8",
        "unread_coordinate_ideals": ["3D", "D"],
        "compiled_move_counts": list(counts),
        "stable_obstruction": "zero-output padding and blank-input rotations fixing active input preserve the unread ideal",
        "scope": "obstruction to a direct unread-rest orbit proof, not an overall independence theorem",
        "normalization_only_polynomial_first_probabilities": [
            str(p_left),
            str(p_right),
        ],
        "uniform_port_zero_padding_control": [str(uniform_before), str(uniform_after)],
        "odd_denominator_phase_common_padding_moves": phase_moves,
    }


def audit() -> dict[str, object]:
    for numerator in range(33):
        for denominator_power in range(6):
            value = F(numerator, 1 << denominator_power)
            require(
                sum((term * term for term in dyadic_squares(value)), F(0)) == value,
                "all parity coefficient controls",
            )
    exponents = []
    for row in ((ONE,), (g(2),), (g(4),)):
        k, padding, lists = common_padding(
            ((row,), (tuple(PI_INV * x for x in row),) * 2), 1
        )
        require(gram(lists[0] + padding, 1) == eye(1), "split common completion")
        exponents.append(k)
    require(exponents == [1, 3, 5], "odd attenuation exponents are retained")
    indefinite = (
        (g(F(1, 2)), g(F(1, 4), F(1, 8))),
        (g(F(1, 4), F(-1, 8)), g(F(-3, 4))),
    )
    positive, negative = hermitian_difference(indefinite)
    bad_density = ((ONE, ONE), (ONE, ZERO))
    vector = (ONE, g(-2))
    _, _, admissible = common_padding(((vector,),), 2)
    require(
        density_weight(admissible[0][0], bad_density) < 0,
        "native positivity excludes an indefinite trace-one matrix",
    )
    return {
        "ok": True,
        "compiled_common_padding": bridge_controls(),
        "odd_attenuation_exponents": exponents,
        "Hermitian_difference_Gram_rows": [len(positive), len(negative)],
        "ideal_and_context_controls": ideal_and_context_controls(),
        "boundary": "conditional finite-frame density-rule bridge; fine-row noncontextuality and test availability supplied; no Lean proof or physical actualization derived",
    }


class RowProbabilityTests(unittest.TestCase):
    def test_full_exact_audit(self) -> None:
        self.assertTrue(audit()["ok"])

    def test_zero_and_coefficient_denominator_parity(self) -> None:
        self.assertEqual(dyadic_squares(F(0)), ())
        self.assertEqual(sum(x * x for x in dyadic_squares(F(7, 8))), F(7, 8))
        with self.assertRaises(ValueError):
            dyadic_squares(F(1, 3))

    def test_dominance_must_use_real_plus_imaginary(self) -> None:
        a = ((ONE, g(F(3, 4), F(1, 2))), (g(F(3, 4), F(-1, 2)), ONE))
        self.assertLess(a[0][1].norm2(), 1)
        self.assertLess(dominance_margin(a, 0), 0)
        with self.assertRaises(ValueError):
            dominant_gram(a)

    def test_bad_equal_gram_request(self) -> None:
        with self.assertRaises(ValueError):
            common_padding((((ONE,),), ((g(2),),)), 1)

    def test_empty_lists_and_zero_outputs(self) -> None:
        k, padding, lists = common_padding(((), ((ZERO, ZERO),)), 2)
        self.assertEqual(k, 0)
        self.assertTrue(all(isometry(rows + padding) for rows in lists))
        for rows in lists:
            compiled(rows + padding)

    def test_tomography_uses_only_admissible_rows(self) -> None:
        rho = ((g(F(2, 3)), g(0, F(1, 3))), (g(0, F(-1, 3)), g(F(1, 3))))

        def law(row: Row) -> F:
            self.assertLessEqual(sum(x.norm2() for x in row), 1)
            return density_weight(row, rho)

        self.assertEqual(tomography(2, law), rho)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: constructive common native padding, d=2,3 exact compiler replay, and density tomography."
        )
        print(
            "PASS: dyadic coefficient parity, Hermitian difference span, and native positivity control."
        )
        print(
            "PASS: same-row completions with stable unread ideals 3D versus D, and contextual controls."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
