"""An exact finite eigenphase catalyst with an explicit preparation wall.

Supply the coherent six-packet data carrier, tensor addresses and native
Gaussian-dyadic unitary instructions. Let V=T01 T12 on THREE neutral clock
addresses. It fixes the uniform vector and has centered eigenvalues
lambda_+/-=(+/-sqrt(7)+3i)/4. Its reduction modulo 3 has order 6, so m=2
is the least positive value with V^(3m)=I modulo 3. Equivalently the
four-gate clock W=V^2 has order 3 modulo 3 and uses m=1. Its nontrivial
eigenvalues z_+/-=(-1+/-3i sqrt(7))/8 have infinite order: z+z^-1=-1/4
is rational but not an algebraic integer.

The joint endpoint
 U=P0 tensor I + Pminus tensor W^-2 + Pplus-centered tensor W^3
is unitary and Gaussian-dyadic: write it using (I+/-C)/2 and the residual
P0 tensor (I-W^3); W^3=I modulo 3 cancels P0's odd denominator. This
18-by-18 matrix has denominator at most 128. The standard exact compiler
currently gives 1380 logical instructions (941 T, 439 i), all replayed
exactly. The fixed input and output-size guards prevent an unbounded search.
This is a logical T/i compiler, not an 18-raw-T-only claim: paired physical
rails are needed for its local phase instructions. No readout is used.

On an initialized nontrivial clock eigenmode, the endpoint is EXACTLY
P0+z^-2 Pminus+z^3 Pplus on arbitrary data, with the clock returned and
uncorrelated, including with an external reference. Repetition supplies
the discrete phases z^n; their density is a mathematical closure, not exact
access to every real angle. The opposite eigenmode supplies z^-1 instead.
There is no continuously adjustable numerical gate parameter. There IS an
additional non-dyadic pure eigenreference, whose orientation is not selected
by the rational endpoint law. An eigenmode is stationary as a ray, not an
independently observable ticking clock.

PREPARATION WALL. No nonzero Q(i) vector is a nontrivial eigenvector of V
or W: a nonzero component would express the irrational eigenvalue as a
quotient of Gaussian-rational components. Thus finite native preparation
from a basis state cannot initialize this reference exactly, even up to
global normalization. A finite rational postselected branch would not fix
that projective-direction obstruction either; no such branch is used here.
This does not exclude an externally supplied, autonomously selected, or
approximately prepared eigenmode, each with its own physical bridge.

A quantitative bound separates exactness from arbitrarily good preparation.
If normalized psi has Gaussian-dyadic coordinates with denominators dividing
2^L, each component of (W-z)psi is (A+B sqrt(7))/2^(L+3), A,B Gaussian
integers. Choose a component of psi that is nonzero, so B is nonzero.
A^2-7B^2 is a nonzero Gaussian integer. The conjugate residual (W-z^-1)psi
has component magnitude <=2, giving ||(W-z)psi||>=2^(-2L-7). Since
W=W^3 W^-2, the uniform joint reuse error is >=2^(-2L-8). A preparation
using t native T instructions has L<=t; this bound is intentionally loose.
Conversely a normalized reference within delta of the correct eigenvector
gives joint implementation error <=2 delta. Repeated uses can accumulate
error; approximate preparation is not an exact indefinitely reusable clock.

MIXED/REAL CONTROLS. A stationary mixed clock can retain its marginal while
correlating with data and averaging opposite phases. Exact phase action with
uncorrelated reusable output requires support on one joint eigenspace of
W^-2 and W^3; their coprime exponents recover W, whose spectrum is simple.
For I/3, the three cross-sector coherence factors are -5/16, 37/64 and
-59/1024, not unit phases. A diagonal stationary density is necessarily I/3.
A real stationary density has equal weights on the two opposite clock
orientations, since their projectors have opposite nonzero imaginary parts.
It cannot supply the selected nontrivial phase. These density controls use
the supplied tensor/state formalism, not a derived readout law.

SUBSTEPS / MINIMALITY. The compiled endpoint commutes with all data sector
projectors, but a checked individual compiler instruction does not. No
strict substep-conservation claim is made. A two-state native T/i clock
cannot replace V: that group has only 96 matrices. A rational two-state
rotation with denominator 5 is an infinite-order control only after changing
the native stock. Three is minimal here for an infinite-order native word,
not a universal lower bound on physical clocks or hidden reference resources.

Finite exact controls plus analytical arguments only; no physical neutral
clock origin, preparation mechanism, Born rule, gauging or status upgrade.
Run: python3 -B -O -m scripts.probe_packet_eigenclock
"""

from __future__ import annotations

import sys
import unittest
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    Matrix,
    Move,
    apply,
    eye,
    g,
    run,
    synthesize,
    unitary,
)
from scripts.probe_neutral_phase_controller import adjoint, qubit_group
from scripts.probe_packet_hypercharge_reference import determinant, mm

Word = tuple[Move, ...]
V_WORD: Word = (("T", 1, 2), ("T", 0, 1))
V = run(eye(3), V_WORD)
W = mm(V, V)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def matrix_power(a: Matrix, exponent: int) -> Matrix:
    if exponent < 0:
        return matrix_power(adjoint(a), -exponent)
    result = eye(len(a))
    for _ in range(exponent):
        result = mm(a, result)
    return result


def residue(z: Gaussian) -> tuple[int, int]:
    parts = [int(x.numerator * pow(x.denominator, -1, 3)) % 3 for x in (z.re, z.im)]
    return parts[0], parts[1]


def identity_mod_three(a: Matrix) -> bool:
    return all(residue(value) == (int(i == j), 0) for i, row in enumerate(a) for j, value in enumerate(row))


def data_projectors() -> tuple[Matrix, Matrix, Matrix]:
    p0 = tuple(tuple(g(F(1, 6)) for _ in range(6)) for _ in range(6))
    minus = tuple(tuple(g(F(int(i == j) - int((i ^ 1) == j), 2)) for j in range(6)) for i in range(6))
    plus = tuple(tuple(eye(6)[i][j] - p0[i][j] - minus[i][j] for j in range(6)) for i in range(6))
    return p0, minus, plus


def tensor(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x * y for x in row_a for y in row_b) for row_a in a for row_b in b)


@cache
def endpoint(m: int = 2) -> Matrix:
    if type(m) is not int or not 1 <= m <= 2:
        raise ValueError("this bounded probe permits m=1 or m=2 only")
    p0, minus, plus = data_projectors()
    left, right = matrix_power(V, -2 * m), matrix_power(V, 3 * m)
    return tuple(tuple(
        p0[a][b] * eye(3)[i][j] + minus[a][b] * left[i][j] + plus[a][b] * right[i][j]
        for b in range(6) for j in range(3)) for a in range(6) for i in range(3))


def denominator_exponent(a: Matrix) -> int:
    if not all(value.dyadic() for row in a for value in row):
        raise ValueError("not a Gaussian-dyadic matrix")
    return max(part.denominator.bit_length() - 1 for row in a for value in row for part in (value.re, value.im))


@cache
def compiled_word() -> Word:
    target = endpoint()
    require(len(target) == 18 and denominator_exponent(target) <= 7, "fixed synthesis input guard")
    word = synthesize(target)
    require(len(word) <= 2000, "fixed synthesis output guard")
    require(run(eye(18), word) == target, "compiler replay differs from endpoint")
    return word


def first_sector_violation() -> tuple[int, Move, str]:
    projectors = tuple(tensor(p, eye(3)) for p in data_projectors())
    for index, move in enumerate(compiled_word()):
        operation = apply(eye(18), move)
        for name, projector in zip(("uniform", "minus", "centered_plus"), projectors, strict=True):
            if mm(operation, projector) != mm(projector, operation):
                return index, move, name
    raise ArithmeticError("expected an explicit non-preserving compiler substep")


@dataclass(frozen=True)
class Q7:
    """a+b*sqrt(7), with a,b exact Gaussian rationals."""

    a: Gaussian = ZERO
    b: Gaussian = ZERO

    def __add__(self, other: Q7) -> Q7:
        return Q7(self.a + other.a, self.b + other.b)

    def __sub__(self, other: Q7) -> Q7:
        return Q7(self.a - other.a, self.b - other.b)

    def __mul__(self, other: Q7) -> Q7:
        return Q7(self.a * other.a + g(7) * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    def star(self) -> Q7:
        return Q7(self.a.star(), self.b.star())

    def orientation(self) -> Q7:
        return Q7(self.a, g(-1) * self.b)


QMat = tuple[tuple[Q7, ...], ...]
QZERO, QONE = Q7(), Q7(ONE)
LAMBDA = Q7(g(0, F(3, 4)), g(F(1, 4)))
PHASE = Q7(g(F(-1, 8)), g(0, F(3, 8)))


def qpower(z: Q7, exponent: int) -> Q7:
    if exponent < 0:
        require(z * z.star() == QONE, "negative powers need a unit phase")
        return qpower(z.star(), -exponent)
    result = QONE
    for _ in range(exponent):
        result = result * z
    return result


def embed(a: Matrix) -> QMat:
    return tuple(tuple(Q7(x) for x in row) for row in a)


def qmm(a: QMat, b: QMat) -> QMat:
    return tuple(tuple(sum((x * y for x, y in zip(row, col, strict=True)), QZERO)
                       for col in zip(*b, strict=True)) for row in a)


def qscale(a: QMat, z: Q7) -> QMat:
    return tuple(tuple(z * x for x in row) for row in a)


def real_sign(z: Q7) -> int:
    require(z.a.im == z.b.im == 0, "real algebraic value required")
    a, b = z.a.re, z.b.re
    if not b:
        return (a > 0) - (a < 0)
    if not a or (a > 0) == (b > 0):
        return (b > 0) - (b < 0)
    difference = a * a - 7 * b * b
    return ((difference > 0) - (difference < 0)) * (1 if a > 0 else -1)


@cache
def eigenprojector() -> QMat:
    wstar = adjoint(W)
    return tuple(tuple(
        Q7(g(F(1, 2)) * (eye(3)[i][j] - g(F(1, 3))))
        + Q7(ZERO, g(0, F(-2, 21))) * Q7(W[i][j] - wstar[i][j])
        for j in range(3)) for i in range(3))


def reuse_error_squared(column: Matrix, exponent: int) -> Q7:
    image = qmm(embed(matrix_power(W, exponent)), embed(column))
    target = qscale(embed(column), qpower(PHASE, exponent))
    return sum(((row[0] - other[0]).star() * (row[0] - other[0])
                for row, other in zip(image, target, strict=True)), QZERO)


class PacketEigenclockControls(unittest.TestCase):
    def test_small_native_clock_and_minimal_congruence(self) -> None:
        self.assertTrue(unitary(V))
        self.assertEqual(determinant(V), g(-1))
        self.assertEqual(sum((V[i][i] for i in range(3)), ZERO), g(1, F(3, 2)))
        self.assertEqual(denominator_exponent(W), 2)
        self.assertEqual([k for k in range(1, 7) if identity_mod_three(matrix_power(V, k))], [6])
        self.assertEqual([k for k in range(1, 4) if identity_mod_three(matrix_power(W, k))], [3])
        self.assertEqual(qpower(LAMBDA, 2), PHASE)
        self.assertEqual(PHASE + PHASE.star(), Q7(g(F(-1, 4))))
        self.assertEqual(PHASE * PHASE.star(), QONE)
        self.assertNotEqual(F(-1, 4).denominator, 1)

    def test_odd_denominator_cancellation_and_compiler_guard(self) -> None:
        self.assertTrue(unitary(endpoint(1)))
        self.assertFalse(all(z.dyadic() for row in endpoint(1) for z in row))
        self.assertTrue(unitary(endpoint()))
        self.assertEqual(denominator_exponent(endpoint()), 7)
        self.assertEqual(determinant(endpoint()), ONE)
        word = compiled_word()
        self.assertEqual((len(word), sum(op[0] == "T" for op in word), sum(op[0] == "i" for op in word)), (1380, 941, 439))
        with self.assertRaises(ValueError):
            endpoint(3)

    def test_endpoint_conservation_is_not_substep_conservation(self) -> None:
        for projector in data_projectors():
            p = tensor(projector, eye(3))
            self.assertEqual(mm(endpoint(), p), mm(p, endpoint()))
        index, move, sector = first_sector_violation()
        self.assertGreaterEqual(index, 0)
        self.assertIn(move[0], ("T", "i"))
        self.assertIn(sector, ("uniform", "minus", "centered_plus"))

    def test_exact_pure_reference_and_opposite_orientation(self) -> None:
        p = eigenprojector()
        self.assertEqual(qmm(p, p), p)
        self.assertEqual(tuple(tuple(x.star() for x in row) for row in zip(*p, strict=True)), p)
        self.assertEqual(sum((p[i][i] for i in range(3)), QZERO), QONE)
        self.assertEqual(qmm(embed(V), p), qscale(p, LAMBDA))
        opposite = tuple(tuple(x.orientation() for x in row) for row in p)
        self.assertEqual(qmm(embed(W), opposite), qscale(opposite, PHASE.star()))
        self.assertEqual(qmm(p, opposite), tuple((QZERO,) * 3 for _ in range(3)))
        for exponent in (-2, 3):
            self.assertEqual(qmm(embed(matrix_power(W, exponent)), p), qscale(p, qpower(PHASE, exponent)))
        self.assertTrue(any(x.b != ZERO for row in p for x in row))
        self.assertTrue(any(x.a.im or x.b.im for row in p for x in row))

    def test_preparation_direction_and_finite_denominator_lower_bound(self) -> None:
        words: tuple[Word, ...] = ((), (("T", 0, 1),), V_WORD, V_WORD * 2, V_WORD * 3,
                                  (("i", 0, 0),) + V_WORD)
        for word in words:
            column = tuple((row[0],) for row in run(eye(3), word))
            level = denominator_exponent(column)
            self.assertLessEqual(level, sum(op[0] == "T" for op in word))
            residual = reuse_error_squared(column, 1)
            self.assertGreater(real_sign(residual), 0)
            self.assertGreaterEqual(real_sign(residual - Q7(g(F(1, 2 ** (4 * level + 14))))), 0)
            errors = [reuse_error_squared(column, exponent) for exponent in (-2, 3)]
            maximum = errors[0] if real_sign(errors[0] - errors[1]) >= 0 else errors[1]
            self.assertGreaterEqual(real_sign(maximum - Q7(g(F(1, 2 ** (4 * level + 16))))), 0)

    def test_stationary_mixed_reference_is_not_a_pure_phase_gate(self) -> None:
        expected = {-2: F(-5, 16), 3: F(37, 64), 5: F(-59, 1024)}
        for exponent, coherence in expected.items():
            powered = matrix_power(W, exponent)
            self.assertEqual(g(F(1, 3)) * sum((powered[i][i] for i in range(3)), ZERO), g(coherence))
            self.assertLess(abs(coherence), 1)
        p = eigenprojector()
        other = tuple(tuple(x.orientation() for x in row) for row in p)
        average = tuple(tuple(Q7(g(F(1, 2))) * (x + y) for x, y in zip(a, b, strict=True))
                        for a, b in zip(p, other, strict=True))
        self.assertTrue(all(x.a.im == x.b.im == 0 for row in average for x in row))
        # A commuting diagonal has equal weights along these connected edges.
        self.assertTrue(all(V[i][j] != ZERO for i, j in ((0, 1), (1, 2))))

    def test_two_state_parent_requires_a_changed_gate_stock(self) -> None:
        self.assertEqual(len(qubit_group()), 96)
        alternative = ((g(F(3, 5)), g(F(-4, 5))), (g(F(4, 5)), g(F(3, 5))))
        self.assertTrue(unitary(alternative))
        self.assertFalse(all(x.dyadic() for row in alternative for x in row))
        with self.assertRaises(ValueError):
            synthesize(alternative)


def main() -> None:
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(PacketEigenclockControls)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)
    word = compiled_word()
    print("Native three-state clock: V has mod-3 order 6; m=2. W=V^2 has mod-3 order 3 and phase (-1+3i*sqrt(7))/8 of infinite order.")
    print(f"Exact joint endpoint: 18 coordinates, denominator <=128, {len(word)} logical gates; first non-preserving compiler substep {first_sector_violation()}.")
    print("Exact uncorrelated reuse requires the supplied non-dyadic pure eigenreference. Finite dyadic basis preparation cannot make it exactly.")
    print("At preparation denominator 2^L, uniform reuse error >=2^(-2L-8). Stationary I/3 instead yields coherence factors -5/16, 37/64, -59/1024.")
    print("No herald/readout is used by the gate; physical clock origin, reference preparation, strict substep conservation and charge interpretation remain unestablished.")


if __name__ == "__main__":
    main()
