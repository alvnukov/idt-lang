"""Reference-sensitive controls for the SUPPLIED coherent six-packet lift.

The unsigned packet counts have NOT become amplitudes by themselves. Supply
complex amplitudes on six addressed species, the raw T stock, complement C,
and the fixed uniform reference. On the centered five-dimensional space the
minus/plus dimensions are 3+2. Write their scalar phases as (a,b).

EXACT WORD WALL. Every exactly C-preserving Gaussian-dyadic unitary has
Gaussian-dyadic unitary blocks, hence each block determinant lies in mu4.
This holds even if intermediate gates leak between sectors. A Gaussian-dyadic
scalar of modulus one is in mu4: after clearing a power-of-two denominator,
x^2+y^2=4^k forces x,y even until k=0. If the centered plus plane is scalar
b and its uniform axis fixed, its offdiagonal entry is (1-b)/3. Of the four
units only b=1 makes that entry dyadic. Consequently the pure traceless
circle (a,b)=(z^-2,z^3) has only z=1 as an exact six-species raw word.
Projectively on the centered five modes, four relative phases remain.
The wall concerns lossless fixed-carrier words, not heralded rational
instruments or tensor-program protocols with their own retained failure,
reset and normalization contracts.

FINITE SEPARATION, not merely a Lie-group quotient argument. Let D_i be a
within-pair T, acting as (phase_i, I), and M_ij be matched parallel T,
acting as (T_ij,T_ij). Then D_i M_ij D_i M_ij^-1 D_i^-1=(T_ij,I), because
D_i T_ij e_i is proportional to e_j-e_i. This is a 13-raw-T word. Cancel
it from M_ij to isolate (I,T_ij). Both finite sector groups therefore factor
directly. No independent phase gate on raw packet species is introduced.

CLOSURE COUNTS, CONDITIONAL on the marginal connected closures SU(3) and
SU(2): exact factorization gives the product closure with 16 independent
mu4 determinant cosets. Central scalars obey a in mu12 and b in mu8. Their
96 pairs give 24 relative phases. The pure weight circle meets this closure
at z in mu24. Projective z representatives lie in mu120 but still describe
only 24 relative phases (the weight circle's projective kernel is mu5).
Exact projective representatives similarly give mu20/ mu5, or four points.

RELAXING EXACT RETURN IS A DIFFERENT CONTRACT. If the full six-port raw
group's centered closure is SU(5), taking its closure BEFORE intersecting
the complement centralizer admits the continuous traceless circle. Closure
of exactly sector-returning words does not. Approximating those targets then
allows nonzero endpoint leakage; no robust fixed-leakage bound or synthesis
rate is asserted here. A limiting matrix is not an exact returning word.

ONE EXTRA PAIR. In the corresponding eight-species product closure SU(4)
x SU(3), one hidden minus and one hidden centered-plus direction compensate
arbitrary visible U(3) and U(2) determinants independently. This permits
U(3)xU(2), not a selected hypercharge U(1). Rational unitary target matrices
below are closure targets, not claimed finite words. An actual raw finite
word also gives a new exact control: the three perfect-matchings on four
plus coordinates yield reflection about their uniform vector. It phases
both the visible plus plane and its hidden companion by -1. The visible
z=-1 weight point is therefore possible with the extra pair, unlike at six.

ONE IMPORTED GATE. A phase z=(3+4i)/5 on one minus direction, compensated
by z^-1 on one centered-plus direction, preserves complement, uniform and
total determinant. It is NOT Gaussian-dyadic and NOT a native word. If this
fixed gate is added, its infinite-order powers and the supplied semisimple
closures generate the traceless central Lie direction: block averaging has
weights (1/3,-1/2)=(-1/6)*(-2,3). This conditional route imports a balanced
phase primitive; it does not derive one. An unbalanced phase would select a
different reference-sensitive charge embedding, although projectively it
can describe the same relative circle on the five fundamental modes.

MATTER/INTEGER CAUTIONS. Scalar sector endomorphisms preserve the fixed-total
integer lattice iff the two integer scalars have the same parity. The
primitive traceless weights (-2,3) fail this; their smallest integral-lattice
multiple is (-4,6). This does not obstruct complexification or the canonical
exterior functor, which requires no chosen basis. It DOES prevent treating
the integral lattice as an already split set of five independent counters.
Exterior occupation, even parity, statistics, Weyl matter and gauging remain
additional interpretations. A common phase on five fundamental modes is
not common on Lambda^0+Lambda^2+Lambda^4: its factors are 1,eta^2,eta^4.
Whether cross-grade phases can be observed needs its own reference and
preparation contract. No physical charge or probability law is derived.
Exterior powers are canonical once chosen, but symmetric powers are another
choice on exactly the same five-dimensional carrier. Uncolored permutations
alone act by real matrices and do not turn that choice into chiral matter.

This file checks finite exact controls, not the cited closure hypotheses or
an experimental claim. Run: python3 -B -O -m scripts.probe_packet_hypercharge_reference
"""

from __future__ import annotations

import sys
import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    apply,
    eye,
    g,
    run,
    unitary,
)

Word = tuple[Move, ...]
UNITS = (ONE, I, g(-1), g(0, -1))


def require(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def power(z: Gaussian, exponent: int) -> Gaussian:
    if exponent < 0:
        require(z.norm2() == 1, "negative powers here require a unit phase")
        return power(z.star(), -exponent)
    answer = ONE
    for _ in range(exponent):
        answer = answer * z
    return answer


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
              for col in zip(*b, strict=True))
        for row in a
    )


def determinant(a: Matrix) -> Gaussian:
    n = len(a)
    require(n > 0 and all(len(row) == n for row in a), "square matrix required")
    rows = [list(row) for row in a]
    answer = ONE
    for j in range(n):
        pivot = next((k for k in range(j, n) if rows[k][j] != ZERO), None)
        if pivot is None:
            return ZERO
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            answer = g(-1) * answer
        value = rows[j][j]
        answer = answer * value
        inverse = g(1 / value.norm2()) * value.star()
        for k in range(j + 1, n):
            coefficient = rows[k][j] * inverse
            rows[k] = [x - coefficient * y for x, y in zip(rows[k], rows[j], strict=True)]
    return answer


def diagonal(values: tuple[Gaussian, ...]) -> Matrix:
    return tuple(tuple(value if i == j else ZERO for j in range(len(values)))
                 for i, value in enumerate(values))


def centered_phase(n: int, phase: Gaussian) -> Matrix:
    require(n > 0 and phase.norm2() == 1, "unit centered phase required")
    return tuple(tuple((phase if i == j else ZERO) + g(F(1, n)) * (ONE - phase)
                       for j in range(n)) for i in range(n))


def lift(minus: Matrix, plus: Matrix) -> Matrix:
    n = len(minus)
    require(n > 0 and len(plus) == n and all(len(row) == n for row in minus + plus),
            "equal square blocks required")
    return tuple(
        tuple(g(F(1, 2)) * (plus[i // 2][j // 2]
              + g(1 if i % 2 == j % 2 else -1) * minus[i // 2][j // 2])
              for j in range(2 * n)) for i in range(2 * n)
    )


def blocks(u: Matrix) -> tuple[Matrix, Matrix]:
    n = len(u) // 2
    require(n > 0 and len(u) == 2 * n and all(len(row) == 2 * n for row in u),
            "even square carrier required")
    result = []
    for sign in (-1, 1):
        block = tuple(tuple(u[2 * i][2 * j] + g(sign) * u[2 * i][2 * j + 1]
                            for j in range(n)) for i in range(n))
        require(all(u[2 * i + 1][2 * j] + g(sign) * u[2 * i + 1][2 * j + 1]
                    == g(sign) * block[i][j] for i, j in product(range(n), repeat=2)),
                "endpoint mixes complement eigenspaces")
        result.append(block)
    return result[0], result[1]


def inverse_word(word: Word) -> Word:
    return tuple(move for move in reversed(word) for _ in range(3))


def matched(i: int, j: int) -> Word:
    return (("T", 2 * i, 2 * j), ("T", 2 * i + 1, 2 * j + 1))


def minus_only(i: int, j: int) -> Word:
    d: Word = (("T", 2 * i, 2 * i + 1),)
    m = matched(i, j)
    # Execution order is right-to-left in D M D M^-1 D^-1.
    return inverse_word(d) + inverse_word(m) + d + m + d


def plus_only(i: int, j: int) -> Word:
    return inverse_word(minus_only(i, j)) + matched(i, j)


def closure_phase_sets() -> tuple[set[F], set[F], set[F]]:
    """Exact rational turns, not floating approximations to roots of unity."""
    central_pairs = {(F(i, 12), F(j, 8)) for i, j in product(range(12), range(8))}
    relative = {(a - b) % 1 for a, b in central_pairs}
    pure = {F(k, 24) for k in range(24)}
    projective_representatives = {F(k, 120) for k in range(120)}
    require({(-5 * t) % 1 for t in pure} == relative, "pure circle misses relative class")
    require({(-5 * t) % 1 for t in projective_representatives} == relative,
            "projective kernel mismatch")
    return pure, relative, projective_representatives


def eight_species_reference(a: Gaussian, b: Gaussian) -> Matrix:
    """Visible scalar phases plus determinant-compensating hidden directions.

    This is a rational closure target, NOT an exact native-word constructor.
    Visible plus W is the first-three-coordinate centered plane; its hidden
    centered companion is (1,1,1,-3). The four-coordinate uniform axis is fixed.
    """
    require(a.norm2() == b.norm2() == 1, "unit visible phases required")
    minus = diagonal((a, a, a, power(a, -3)))
    h = (1, 1, 1, -3)
    plus = tuple(tuple(
        g(F(1, 4))
        + b * g(F(int(i == j)) - F(1, 3) if i < 3 and j < 3 else F(0))
        + power(b, -2) * g(F(h[i] * h[j], 12))
        for j in range(4)) for i in range(4))
    return lift(minus, plus)


def imported_balanced_phase(z: Gaussian) -> Matrix:
    require(z.norm2() == 1, "unit phase required")
    minus = diagonal((z, ONE, ONE))
    v = (1, -1, 0)
    plus = tuple(tuple((ONE if i == j else ZERO)
                       + (z.star() - ONE) * g(F(v[i] * v[j], 2))
                       for j in range(3)) for i in range(3))
    return lift(minus, plus)


class PacketHyperchargeReferenceControls(unittest.TestCase):
    def test_constructive_finite_sector_separation(self) -> None:
        for n in (3, 4):
            for i, j in combinations(range(n), 2):
                target = apply(eye(n), ("T", i, j))
                minus = run(eye(2 * n), minus_only(i, j))
                self.assertEqual(len(minus_only(i, j)), 13)
                self.assertEqual(blocks(minus), (target, eye(n)))
                plus = run(eye(2 * n), plus_only(i, j))
                self.assertEqual(blocks(plus), (eye(n), target))
                self.assertTrue(unitary(minus) and unitary(plus))

    def test_exact_pure_and_projective_counts(self) -> None:
        self.assertEqual({z for z in UNITS if (g(F(1, 3)) * (ONE - z)).dyadic()}, {ONE})
        pure, relative, representatives = closure_phase_sets()
        self.assertEqual((len(pure), len(relative), len(representatives)), (24, 24, 120))
        self.assertEqual({t for t in pure if (3 * t) % 1 == 0 and (8 * t).denominator == 1}, {F(0)})
        self.assertEqual(len({(-5 * F(k, 20)) % 1 for k in range(20)}), 4)
        for mu in UNITS:
            raw = lift(diagonal((mu,) * 3), eye(3))
            self.assertTrue(unitary(raw) and all(x.dyadic() for row in raw for x in row))
            count = UNITS.index(mu)
            word: Word = tuple(("T", 2 * i, 2 * i + 1) for i in range(3) for _ in range(count))
            self.assertEqual(run(eye(6), word), raw)

    def test_dyadic_unit_scalar_descent_small_exact_controls(self) -> None:
        for k in range(5):
            denominator = 2 ** k
            values = {
                g(F(x, denominator), F(y, denominator))
                for x, y in product(range(-denominator, denominator + 1), repeat=2)
                if x * x + y * y == denominator * denominator
            }
            self.assertEqual(values, set(UNITS))

    def test_integer_gluing_and_minimal_traceless_multiple(self) -> None:
        basis = [tuple(int(i == j) - int(i == 5) for i in range(6)) for j in range(5)]
        for a, b in product(range(-6, 7), repeat=2):
            images = [tuple(F(a + b, 2) * v[i] + F(b - a, 2) * v[i ^ 1]
                            for i in range(6)) for v in basis]
            self.assertEqual(all(x.denominator == 1 for row in images for x in row), (a - b) % 2 == 0)
        self.assertNotEqual((-2 - 3) % 2, 0)
        self.assertEqual(3 * (-4) + 2 * 6, 0)

    def test_uniform_reference_and_exterior_grade_control(self) -> None:
        exact_five = (g(0, -1),) * 3 + (ONE,) * 2
        pure_five = (g(-1),) * 3 + (g(0, -1),) * 2  # z=i in (-2,3)
        self.assertEqual(exact_five, tuple(I * x for x in pure_five))
        # Vacuum fixes any common exterior phase to one; degree two disagrees.
        self.assertEqual(power(I, 0), ONE)
        self.assertNotEqual(exact_five[0] * exact_five[1], pure_five[0] * pure_five[1])
        self.assertEqual(power(I, 4), ONE)
        exact_raw = lift(diagonal(exact_five[:3]), eye(3))
        pure_raw = lift(diagonal(pure_five[:3]), centered_phase(3, pure_five[3]))
        self.assertTrue(unitary(exact_raw) and unitary(pure_raw))
        self.assertTrue(all(sum(row, ZERO) == ONE for row in exact_raw + pure_raw))
        self.assertEqual(exact_raw[0][0].norm2(), F(1, 2))
        self.assertEqual(pure_raw[0][0].norm2(), F(2, 9))
        self.assertFalse(all(x.dyadic() for row in pure_raw for x in row))

    def test_single_particle_split_does_not_select_exterior_statistics(self) -> None:
        weights = (-2, -2, -2, 3, 3)
        exterior = Counter(weights[i] + weights[j] for i, j in combinations(range(5), 2))
        symmetric = Counter(weights[i] + weights[j] for i, j in combinations_with_replacement(range(5), 2))
        self.assertEqual(exterior, {-4: 3, 1: 6, 6: 1})
        self.assertEqual(symmetric, {-4: 6, 1: 6, 6: 3})
        self.assertEqual((sum(exterior.values()), sum(symmetric.values())), (10, 15))

    def test_extra_pair_closure_targets_are_not_claimed_exact_words(self) -> None:
        z = g(F(3, 5), F(4, 5))
        for a, b in ((power(z, -2), power(z, 3)), (z, ONE), (ONE, z)):
            u = eight_species_reference(a, b)
            minus, plus = blocks(u)
            self.assertTrue(unitary(u))
            self.assertEqual((determinant(minus), determinant(plus)), (ONE, ONE))
            self.assertTrue(all(sum(row, ZERO) == ONE for row in u))
            self.assertFalse(all(x.dyadic() for row in u for x in row))
            for v in ((1, -1, 0, 0), (0, 1, -1, 0)):
                image = tuple(sum((x * g(y) for x, y in zip(row, v, strict=True)), ZERO) for row in plus)
                self.assertEqual(image, tuple(b * g(x) for x in v))

    def test_extra_pair_has_a_new_exact_visible_weight_point(self) -> None:
        matchings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
        word = tuple(move for matching in matchings for i, j in matching for move in plus_only(i, j))
        u = run(eye(8), word)
        self.assertEqual(blocks(u), (eye(4), centered_phase(4, g(-1))))
        self.assertEqual(len(word), 246)
        self.assertTrue(all(sum(row, ZERO) == ONE for row in u))
        self.assertEqual(determinant(u), g(-1))

    def test_imported_balanced_gate_is_non_native_but_traceless(self) -> None:
        z = g(F(3, 5), F(4, 5))
        u = imported_balanced_phase(z)
        a, b = blocks(u)
        self.assertTrue(unitary(u))
        self.assertEqual((determinant(a), determinant(b), determinant(u)), (z, z.star(), ONE))
        self.assertNotIn(z, UNITS)
        self.assertFalse(all(x.dyadic() for row in u for x in row))
        self.assertTrue(all(sum(row, ZERO) == ONE for row in u))
        self.assertEqual((F(1, 3), F(-1, 2)), (F(-1, 6) * -2, F(-1, 6) * 3))

    def test_ambient_closure_target_is_not_an_exact_returning_word(self) -> None:
        z = g(F(3, 5), F(4, 5))
        u = lift(diagonal((power(z, -2),) * 3), centered_phase(3, power(z, 3)))
        a, b = blocks(u)
        self.assertTrue(unitary(u))
        self.assertEqual(determinant(u), ONE)
        self.assertNotIn(determinant(a), UNITS)
        self.assertNotIn(determinant(b), UNITS)
        self.assertFalse(all(x.dyadic() for row in u for x in row))


def main() -> None:
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(PacketHyperchargeReferenceControls)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)
    print("Finite native separation: isolated minus T in 13 raw gates; isolated plus T in 41.")
    print("Six-species lossless raw words: one exact pure weight point, four exact relative phases; conditional closure gives 24, not a continuous U(1).")
    print("Eight species: an exact z=-1 visible weight control with hidden plus phase; closure permits independent visible U(3)xU(2), not a selected hypercharge.")
    print("Projective fundamental phases do not automatically lift across exterior grades. The direct balanced (3+4i)/5 gate is not a lossless raw word; heralded instruments are a separate contract.")
    print("All interpretation, marginal closure, approximation, exterior/statistics and gauging bridges remain conditional; no physical status upgrade.")


if __name__ == "__main__":
    main()
