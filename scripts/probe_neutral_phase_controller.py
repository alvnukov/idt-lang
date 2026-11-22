"""One two-state neutral controller: a tight reference-sensitive phase wall.

SUPPLIED HARDWARE. Data are complex amplitudes on six packet species, with
commuting permutations C (three opposite-pair flips) and A (a cyclic shift
of the three pairs). A two-state ancilla starts in |0>. Allowed operations
are ancilla-only native T and i, SELECT-C=diag(I,C), and SELECT-A=diag(I,A).
They commute with the full DATA Pminus, Pplus-centered and P0 projectors.
This statement holds for the factor-level operations, not automatically
for a sequential decomposition into individual raw gates on 12 addresses.
Matched/synchronized hardware or the controlled-permutation primitive is
an explicit import. No measurement, Born rule, herald or data loss is used.

ZERO-CHARACTER WALL. In the joint character fibers (c,w^k), c=+/-1,
k=0,1,2, the controls become qubit T,i, diag(1,c), diag(1,w^k).
At k=0 the last control is identity. Native qubit T,i generate 96 exact
matrices, 24 projectively, NOT a dense qubit group. The two k=0 fibers
together generate 1536 matrices; their relative factor is Pauli. Exact
return phases are all 16 pairs in mu4 x mu4. Leakage squared in either
fiber is only 0, 1/2 or 1. Thus leakage norm <1/sqrt(2) already forces
exact return there. No longer word can approximate a new return phase.

For the full referenced target U_z=P0+z^-2 Pminus+z^3 Pplus-centered,
arbitrarily accurate uniform joint return requires z^-2 in mu4, or z^8=1.
Allowing a loose overall phase does NOT enlarge this set: the uniform and
minus k=0 characters must still have a fourth-root relative phase. For
z=(3+4i)/5, a=z^-2=(-7-24i)/25. The fixed-phase joint-isometry error is
at least sqrt(2/25). After optimizing an arbitrary overall phase it is
still at least sqrt(2-7*sqrt(2)/5), about 0.14178. These are operator-norm
lower bounds, also applicable with an untouched external reference. A
plain data address alone witnesses squared fixed-phase error >=1/75,
without needing an exactly prepared character eigenvector.

TIGHT CLOSURE CLASSIFICATION (analytical, not a Lean proof). Each k=1,2
fiber has dense projective SU(2). For V=T diag(1,w), tr(V)^2/det(V)=1/2;
the eigenvalue ratio has sum with its inverse -3/2 and so cannot be a root
of unity (a rational algebraic integer must be an integer). Clifford
conjugation supplies nonparallel axes for the resulting connected circle.
The four nontrivial fibers have independent connected closure SU(2)^4.
Indeed a subdirect Lie algebra could couple two simple factors only by an
automorphism. Common Clifford conjugation forces that automorphism to be
identity: its SO(3) commutant is scalar. Opposite c fibers are then separated
by SELECT-C; k=1 versus k=2 is separated by SELECT-A. This proves absence
of diagonal factor identifications, not a numerical controllability guess.

Consequently the central returning data phases, after fixing P0, are
(a,b) in mu4 x U(1): an arbitrary PLUS-plane phase is approximable while
minus is fixed to a fourth root. The eight z^8=1 pure-weight targets are
therefore also sufficient in closure. Arbitrary relative phases on the
centered five modes are possible only if the distinct uniform-reference
action is ignored; that is NOT the same referenced traceless Y circle.
The controls overgenerate four independent nontrivial character responses,
not a selected central phase law. No circuit length/error rate follows
merely from this closure argument.

EXACT RETURN IS SMALLER. A finite circuit returning the ancilla exactly
has a Gaussian-dyadic unitary data block. Its uniform scalar is in mu4.
After removing that scalar, a pure centered-plus scalar b requires the
dyadic entry (1-b)/3, forcing b=1; scalar a is also in mu4. Thus exact
pure-weight return still permits only z=1, even up to an overall phase.
An explicit 29-factor-gate parity-phase circuit returns exactly with
(a,b)=(-i,1); it attains the discrete optimum on the two blind fibers,
but its full U_(3+4i)/5 error is much larger. It is NOT presented as an
approximation to the forbidden full target. No approximate full-target
finite circuit is fabricated from the closure result.

DETERMINANTS AND SYMMETRIES. With m ancilla gates, n SELECT-C and l
SELECT-A gates, the six fiber determinants are i^m*c^n*w^(k*l), and the
full 12-dimensional determinant is (-1)^(m+n). A returned phase can be
compensated on unused ancilla |1>; determinant alone is not the obstruction.
Finite k=1,2 matrices are related by the field automorphism w<->w^2 fixing
i. That automorphism is not a continuous coupling of their dense closures.
All numerical decimals below summarize exact expressions, not observations.
No physical neutral-ancilla origin, tensor structure, statistics, charge,
gauge redundancy or quantum-theory derivation is established.
"""

from __future__ import annotations

import math
import sys
import unittest
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import ONE, ZERO, Gaussian, I, Matrix, apply, eye, g
from scripts.probe_packet_hypercharge_reference import determinant, mm

T = apply(eye(2), ("T", 0, 1))
S = apply(eye(2), ("i", 1, 1))
X = ((ZERO, ONE), (ONE, ZERO))
Y = ((ZERO, g(0, -1)), (I, ZERO))
Z = ((ONE, ZERO), (ZERO, g(-1)))
UNITS = (ONE, I, g(-1), g(0, -1))
Word = tuple[str, ...]


def require(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(x.star() for x in row) for row in zip(*a, strict=True))


@cache
def qubit_group() -> frozenset[Matrix]:
    seen = {eye(2)}
    pending = [eye(2)]
    while pending:
        current = pending.pop()
        for generator in (T, S):
            image = mm(generator, current)
            if image not in seen:
                seen.add(image)
                pending.append(image)
        require(len(seen) <= 96, "native qubit group exceeded claimed finite order")
    return frozenset(seen)


@cache
def zero_character_group() -> frozenset[tuple[Matrix, Matrix]]:
    seen = {(eye(2), eye(2))}
    pending = list(seen)
    while pending:
        left, right = pending.pop()
        for a, b in ((T, T), (S, S), (eye(2), Z)):
            image = (mm(a, left), mm(b, right))
            if image not in seen:
                seen.add(image)
                pending.append(image)
        require(len(seen) <= 1536, "blind-character group exceeded claimed order")
    return frozenset(seen)


def native_inverse(word: Word) -> Word:
    orders = {"T": 4, "S": 4, "C": 2, "A": 3}
    if any(gate not in orders for gate in word):
        raise ValueError("unknown factor-level gate")
    return tuple(gate for gate in reversed(word) for _ in range(orders[gate] - 1))


def parity_phase_word(exponent: int) -> Word:
    if type(exponent) is not int or not 0 <= exponent < 4:
        raise ValueError("fourth-root exponent required")
    h = ("S", "T", "S")  # e^(i*pi/4) H; no independent Hadamard imported.
    parity = h + ("C",) + native_inverse(h)
    return parity + ("S",) * exponent + parity


def permutation(mapping: tuple[int, ...]) -> Matrix:
    require(sorted(mapping) == list(range(len(mapping))), "permutation required")
    return tuple(tuple(g(int(i == mapping[j])) for j in range(len(mapping)))
                 for i in range(len(mapping)))


def tensor(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x * y for x in row_a for y in row_b) for row_a in a for row_b in b)


C = permutation(tuple(i ^ 1 for i in range(6)))
A = permutation(tuple((i + 2) % 6 for i in range(6)))


def controlled(data: Matrix) -> Matrix:
    n = len(data)
    return tuple(tuple(
        g(int(i == j)) if i < n and j < n
        else data[i - n][j - n] if i >= n and j >= n else ZERO
        for j in range(2 * n)) for i in range(2 * n))


def full_gate(name: str) -> Matrix:
    if name == "T":
        return tensor(T, eye(6))
    if name == "S":
        return tensor(S, eye(6))
    if name == "C":
        return controlled(C)
    if name == "A":
        return controlled(A)
    raise ValueError("unknown factor-level gate")


def run_word(word: Word) -> Matrix:
    current = eye(12)
    for name in word:
        current = mm(full_gate(name), current)
    return current


@dataclass(frozen=True)
class Cyclotomic:
    """a+b*w, w^2+w+1=0, over Gaussian rationals; no floating comparisons."""

    a: Gaussian = ZERO
    b: Gaussian = ZERO

    def __add__(self, other: Cyclotomic) -> Cyclotomic:
        return Cyclotomic(self.a + other.a, self.b + other.b)

    def __sub__(self, other: Cyclotomic) -> Cyclotomic:
        return Cyclotomic(self.a - other.a, self.b - other.b)

    def __mul__(self, other: Cyclotomic) -> Cyclotomic:
        repeated = self.b * other.b
        return Cyclotomic(self.a * other.a - repeated,
                          self.a * other.b + self.b * other.a - repeated)

    def star(self) -> Cyclotomic:
        return Cyclotomic(self.a.star() - self.b.star(), g(-1) * self.b.star())

    def galois(self) -> Cyclotomic:
        return Cyclotomic(self.a - self.b, g(-1) * self.b)


CMat = tuple[tuple[Cyclotomic, ...], ...]
CZ, CO, CW = Cyclotomic(), Cyclotomic(ONE), Cyclotomic(ZERO, ONE)


def cmm(a: CMat, b: CMat) -> CMat:
    return tuple(tuple(sum((x * y for x, y in zip(row, col, strict=True)), CZ)
                       for col in zip(*b, strict=True)) for row in a)


def cpower(z: Cyclotomic, exponent: int) -> Cyclotomic:
    answer = CO
    for _ in range(exponent):
        answer = answer * z
    return answer


def cdet(a: CMat) -> Cyclotomic:
    require(len(a) == 2 and all(len(row) == 2 for row in a), "two dimensions required")
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def fiber_gate(name: str, sign: int, character: int) -> CMat:
    require(sign in (-1, 1) and character in (0, 1, 2), "character required")
    if name in ("T", "S"):
        return tuple(tuple(Cyclotomic(x) for x in row) for row in (T if name == "T" else S))
    if name == "C":
        return ((CO, CZ), (CZ, Cyclotomic(g(sign))))
    if name == "A":
        return ((CO, CZ), (CZ, cpower(CW, character)))
    raise ValueError("unknown factor-level gate")


def fiber_word(word: Word, sign: int, character: int) -> CMat:
    current: CMat = ((CO, CZ), (CZ, CO))
    for name in word:
        current = cmm(fiber_gate(name, sign, character), current)
    return current


def rank(rows: list[list[F]]) -> int:
    rows = [row[:] for row in rows]
    pivot_row = 0
    for j in range(len(rows[0])):
        k = next((i for i in range(pivot_row, len(rows)) if rows[i][j]), None)
        if k is None:
            continue
        rows[pivot_row], rows[k] = rows[k], rows[pivot_row]
        coefficient = rows[pivot_row][j]
        rows[pivot_row] = [x / coefficient for x in rows[pivot_row]]
        for i in range(len(rows)):
            if i != pivot_row:
                coefficient = rows[i][j]
                rows[i] = [x - coefficient * y for x, y in zip(rows[i], rows[pivot_row], strict=True)]
        pivot_row += 1
        if pivot_row == len(rows):
            break
    return pivot_row


def pauli_rotation(u: Matrix) -> tuple[tuple[int, ...], ...]:
    images = [mm(mm(u, p), adjoint(u)) for p in (X, Y, Z)]
    return tuple(tuple(
        1 if image == p else -1 if image == tuple(tuple(g(-1) * x for x in row) for row in p) else 0
        for image in images) for p in (X, Y, Z))


class NeutralPhaseControllerControls(unittest.TestCase):
    def test_native_qubit_is_finite_even_with_its_global_phases(self) -> None:
        group = qubit_group()
        self.assertEqual(len(group), 96)
        scalar = {u[0][0] for u in group if u[0][1] == u[1][0] == ZERO and u[0][0] == u[1][1]}
        self.assertEqual(scalar, set(UNITS))
        self.assertEqual(len(group) // len(scalar), 24)
        self.assertEqual({u[1][0].norm2() for u in group}, {F(0), F(1, 2), F(1)})
        # Every first entry lies in the convex hull of the four unit phases;
        # leakage cannot improve overlap with any desired unit return phase.
        expected = {ZERO, *UNITS} | {g(F(a, 2), F(b, 2)) for a, b in product((-1, 1), repeat=2)}
        self.assertEqual({u[0][0] for u in group}, expected)

    def test_two_blind_characters_have_only_fourth_root_relative_phases(self) -> None:
        group = zero_character_group()
        self.assertEqual(len(group), 1536)
        returning = {(a[0][0], b[0][0]) for a, b in group if a[1][0] == b[1][0] == ZERO}
        self.assertEqual(returning, set(product(UNITS, repeat=2)))
        relative = {mm(b, adjoint(a)) for a, b in group}
        pauli = {tuple(tuple(mu * x for x in row) for row in p)
                 for mu, p in product(UNITS, (eye(2), X, Y, Z))}
        self.assertEqual(relative, pauli)
        overlaps = {sum((a[i][0].star() * b[i][0] for i in range(2)), ZERO) for a, b in group}
        self.assertEqual(overlaps, {ZERO, *UNITS})

    def test_fixed_phase_obstruction_is_exact_and_leakage_does_not_help(self) -> None:
        a = g(F(-7, 25), F(-24, 25))
        errors = {(u[0][0] - a).norm2() + u[1][0].norm2() for u in qubit_group()}
        self.assertEqual(min(errors), F(2, 25))
        self.assertEqual(F(2, 25) / 6, F(1, 75))
        best_relative_cosine = max((a.star() * mu).re for mu in UNITS)
        self.assertEqual(best_relative_cosine, F(24, 25))
        self.assertEqual((1 + best_relative_cosine) / 2, F(49, 50))
        # The projective optimum squared is 2-7*sqrt(2)/5, strictly >1/64.
        self.assertGreater((F(2) - F(1, 64)) ** 2, F(98, 25))
        blind = tuple((g((-1) ** i),) for i in range(6))
        self.assertEqual(mm(A, blind), blind)
        self.assertEqual(mm(C, blind), tuple((g(-1) * row[0],) for row in blind))
        self.assertEqual(sum(row[0].norm2() for row in blind), 6)

    def test_factor_level_substeps_preserve_all_data_projectors(self) -> None:
        p0 = tuple(tuple(g(F(1, 6)) for _ in range(6)) for _ in range(6))
        minus = tuple(tuple(g(F(1, 2)) * (eye(6)[i][j] - C[i][j]) for j in range(6)) for i in range(6))
        plus = tuple(tuple(eye(6)[i][j] - minus[i][j] - p0[i][j] for j in range(6)) for i in range(6))
        for name, projector in product(("T", "S", "C", "A"), (minus, plus, p0)):
            q = tensor(eye(2), projector)
            self.assertEqual(mm(full_gate(name), q), mm(q, full_gate(name)))
        # One raw address mixer is not a valid replacement for a synchronized layer.
        single = apply(eye(12), ("T", 0, 2))
        q = tensor(eye(2), minus)
        self.assertNotEqual(mm(single, q), mm(q, single))

    def test_explicit_exact_return_circuit_is_not_a_full_forbidden_approximation(self) -> None:
        word = parity_phase_word(3)
        self.assertEqual(len(word), 29)
        u = run_word(word)
        minus_phase = g(0, -1)
        expected = tuple(tuple(
            g(F(1, 2)) * ((ONE + minus_phase) * eye(6)[i][j] + (ONE - minus_phase) * C[i][j])
            for j in range(6)) for i in range(6))
        self.assertEqual(tuple(row[:6] for row in u[:6]), expected)
        self.assertTrue(all(x == ZERO for row in u[6:] for x in row[:6]))
        self.assertEqual(determinant(u), g(-1))
        a, b = g(F(-7, 25), F(-24, 25)), g(F(-117, 125), F(44, 125))
        self.assertEqual((minus_phase - a).norm2(), F(2, 25))
        self.assertEqual((ONE - b).norm2(), F(484, 125))

    def test_character_determinants_galois_symmetry_and_full_determinant(self) -> None:
        word = ("T", "A", "S", "C", "A", "T", "C", "S", "A")
        m, n, ell = sum(x in ("T", "S") for x in word), word.count("C"), word.count("A")
        for sign, k in product((-1, 1), range(3)):
            value = fiber_word(word, sign, k)
            target = cpower(Cyclotomic(I), m) * Cyclotomic(g(sign ** n)) * cpower(CW, k * ell)
            self.assertEqual(cdet(value), target)
        for sign in (-1, 1):
            first = fiber_word(word, sign, 1)
            self.assertEqual(tuple(tuple(x.galois() for x in row) for row in first), fiber_word(word, sign, 2))
        self.assertEqual(determinant(run_word(word)), g((-1) ** (m + n)))

    def test_nontrivial_character_infinite_order_certificate(self) -> None:
        v = fiber_word(("A", "T"), 1, 1)
        trace = v[0][0] + v[1][1]
        self.assertEqual(trace * trace, Cyclotomic(g(F(1, 2))) * cdet(v))
        self.assertEqual(F(1, 2) - 2, F(-3, 2))
        self.assertNotEqual(F(-3, 2).denominator, 1)

    def test_graph_couplings_are_excluded_by_common_control_symmetries(self) -> None:
        equations: list[list[F]] = []
        for rotation in (pauli_rotation(T), pauli_rotation(S)):
            for i, j in product(range(3), repeat=2):
                equation = [F(0)] * 9
                for k in range(3):
                    equation[3 * k + j] += rotation[i][k]
                    equation[3 * i + k] -= rotation[k][j]
                equations.append(equation)
        self.assertEqual(rank(equations), 8)  # Only scalar 3x3 intertwiners.
        self.assertNotEqual(mm(mm(Z, X), Z), X)
        cx = tuple(tuple(Cyclotomic(x) for x in row) for row in X)
        images = []
        for k in (1, 2):
            d = fiber_gate("A", 1, k)
            ds = tuple(tuple(x.star() for x in row) for row in zip(*d, strict=True))
            images.append(cmm(cmm(d, cx), ds))
        self.assertNotEqual(images[0], images[1])

    def test_eight_closure_targets_but_only_one_exact_pure_target(self) -> None:
        turns = {F(k, 8) for k in range(8)}
        self.assertTrue(all((8 * t).denominator == 1 for t in turns))
        exact = {
            t for t in turns
            if (4 * 3 * t).denominator == 1 and (3 * t) % 1 == 0
        }
        self.assertEqual(exact, {F(0)})
        self.assertEqual({z for z in UNITS if (g(F(1, 3)) * (ONE - z)).dyadic()}, {ONE})


def main() -> None:
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(NeutralPhaseControllerControls)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)
    print("One qubit: 96 native matrices, 24 projectively; A=1 character pair has 1536 matrices and 16 exact return-phase pairs.")
    print("Referenced pure-weight closure: z^8=1 only; exact return: z=1 only. An arbitrary plus-plane phase is a different, analytically controllable closure target.")
    print(f"At z=(3+4i)/5, joint-isometry error >=sqrt(2/25)={math.sqrt(2/25):.9f}; up to global phase >=sqrt(2-7sqrt(2)/5)={math.sqrt(2-7*math.sqrt(2)/5):.9f}.")
    print("A 29-factor-gate exact parity-phase circuit saturates the blind-fiber bound, not the full target bound; its full squared error is 484/125.")
    print("Connected SU(2)^4 classification is analytical; no finite approximation rate, physical controller, readout, Born or gauge claim is supplied.")


if __name__ == "__main__":
    main()
