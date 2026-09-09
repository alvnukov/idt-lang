"""Differential, metamorphic and evidence-mutation checks for exact positivity."""

from __future__ import annotations

import copy
import itertools
import unittest
from fractions import Fraction as F
from unittest.mock import patch

from theory_experiments.primitive_screen import (
    Matrix,
    PairKernel,
    Vector,
    reference_trials,
)
from theory_experiments.quadratic_certificate import SCHEMA, certify, verify_certificate


def principal_minors_nonnegative(matrix: Matrix) -> bool:
    # Independent criterion for n<=3. No Schur decomposition or certificate code.
    n = len(matrix)
    if any(matrix[i][i] < 0 for i in range(n)):
        return False
    if any(matrix[i][i]*matrix[j][j] - matrix[i][j]**2 < 0
           for i in range(n) for j in range(i+1, n)):
        return False
    if n == 3:
        a, b, c = matrix[0]
        _, d, e = matrix[1]
        _, _, f = matrix[2]
        return a*d*f + 2*b*c*e - a*e*e - d*c*c - f*b*b >= 0
    return True


def congruence(matrix: Matrix, transform: Matrix) -> Matrix:
    n = len(matrix)
    return tuple(tuple(sum((transform[k][i]*matrix[k][l]*transform[l][j]
                            for k in range(n) for l in range(n)), F())
                       for j in range(n)) for i in range(n))


class QuadraticCertificateTests(unittest.TestCase):
    def check_matrix(self, matrix: Matrix) -> dict[str, object]:
        certificate = certify(matrix)
        self.assertTrue(verify_certificate(matrix, certificate))
        expected = "weighted_squares" if principal_minors_nonnegative(matrix) else "negative_direction"
        self.assertEqual(certificate["kind"], expected)
        return certificate

    def test_all_729_symmetric_ternary_three_by_three_matrices(self) -> None:
        for values in itertools.product((-1, 0, 1), repeat=6):
            a, b, c, d, e, f = map(F, values)
            with self.subTest(values=values):
                self.check_matrix(((a, b, c), (b, d, e), (c, e, f)))

    def test_all_169_previous_search_kernels(self) -> None:
        positive = negative = 0
        for i in range(13):
            for j in range(13):
                a, c = F(i, 12), F(j, 12)
                b = (1-a-c)/2
                result = self.check_matrix(((a, b), (b, c)))
                positive += result["kind"] == "weighted_squares"
                negative += result["kind"] == "negative_direction"
        self.assertEqual((positive, negative), (130, 39))

    def test_nonleading_minor_and_zero_diagonal_traps(self) -> None:
        examples: tuple[Matrix, ...] = (
            ((F(0), F(0), F(0)), (F(0), F(1), F(2)), (F(0), F(2), F(1))),
            ((F(0), F(1)), (F(1), F(0))),
            ((F(0), F(0)), (F(0), F(3))),
            ((F(0),),), ((F(-1),),), ((F(3),),),
        )
        for matrix in examples:
            with self.subTest(matrix=matrix):
                self.check_matrix(matrix)

    def test_singular_gram_and_exact_near_singular_directions(self) -> None:
        for epsilon in (F(), F(1, 10**11), F(-1, 10**11)):
            self.check_matrix(((F(1), F(1)), (F(1), F(1)+epsilon)))
        v = (F(1, 17), F(-3, 19), F(4, 23))
        self.check_matrix(tuple(tuple(x*y for y in v) for x in v))

    def test_large_input_fractions_keep_exact_certificates(self) -> None:
        # Near-unit entries with distinct 12-digit numerators/denominators stress
        # Schur arithmetic growth without a floating-point eigenvalue tolerance.
        for index in range(64):
            a, b, c, d, e, f = (F(999999999989-2*index-k, 999999999937-6*index-k)
                                for k in range(6))
            self.check_matrix(((a, b, c), (b, d, e), (c, e, f)))

    def test_permutation_scaling_and_invertible_congruence(self) -> None:
        transform = ((F(1), F(2), F(-1)), (F(0), F(1), F(3)), (F(0), F(0), F(1)))
        for diagonal in ((1, 2, 3), (1, 0, 2), (1, -2, 3), (0, 0, 0)):
            matrix = tuple(tuple(F(diagonal[i] if i == j else 0) for j in range(3)) for i in range(3))
            expected = self.check_matrix(matrix)["kind"]
            changed = congruence(matrix, transform)
            self.assertEqual(self.check_matrix(changed)["kind"], expected)
            for permutation in itertools.permutations(range(3)):
                permuted = tuple(tuple(changed[i][j]*F(1, 1234567)
                                       for j in permutation) for i in permutation)
                self.assertEqual(self.check_matrix(permuted)["kind"], expected)

    def test_negative_certificate_replays_actual_composition_with_nonzero_sum(self) -> None:
        matrices: tuple[Matrix, ...] = (
            ((F(1), F(1)), (F(1), F(0))),  # Schur lift has zero sum before perturbation.
            ((F(0), F(1, 24)), (F(1, 24), F(11, 12))),
        )
        for matrix in matrices:
            certificate = self.check_matrix(matrix)
            raw = certificate["vector"]
            assert isinstance(raw, list)
            vector: Vector = tuple(F(str(x)) for x in raw)
            self.assertNotEqual(sum(vector, F()), 0)
            trial = next(iter(reference_trials(PairKernel("replay", matrix), (vector,))))
            self.assertLess(trial.actual, 0)
            self.assertEqual(str(trial.actual), certificate["normalized_reference_weight"])

    def test_verifier_does_not_call_generator(self) -> None:
        matrix = ((F(1), F(0)), (F(0), F(2)))
        certificate = certify(matrix)
        with patch("theory_experiments.quadratic_certificate._decompose", side_effect=AssertionError("search called")):
            self.assertTrue(verify_certificate(matrix, certificate))

    def test_positive_evidence_mutants_fail(self) -> None:
        matrix = ((F(1), F(0)), (F(0), F(2)))
        mutants: tuple[object, ...] = (
            {"schema": SCHEMA, "kind": "weighted_squares", "terms": []},
            {"schema": SCHEMA, "kind": "weighted_squares", "terms": [{"weight": "-1", "vector": ["1", "0"]}]},
            {"schema": SCHEMA, "kind": "weighted_squares", "terms": [{"weight": "1", "vector": ["1", "0"]}]},
            {"schema": SCHEMA, "kind": "weighted_squares", "terms": [{"weight": "1", "vector": ["1"]}]},
            {"schema": SCHEMA, "kind": "weighted_squares", "terms": [{"weight": "1", "vector": ["1", "0"]}]*4},
        )
        for mutant in mutants:
            self.assertFalse(verify_certificate(matrix, mutant))
        self.assertFalse(verify_certificate(((F(1), F(1)), (F(1), F(2))), certify(matrix)))

    def test_negative_evidence_mutants_fail(self) -> None:
        matrix = ((F(1), F(2)), (F(2), F(1)))
        valid = certify(matrix)
        for key, value in (("vector", ["0", "0"]), ("vector", ["1", "-1"]),
                           ("quadratic", "0"), ("normalized_reference_weight", "0"),
                           ("vector", ["NaN", "1"]), ("vector", ["9"*513, "1"]),
                           ("vector", [1.0, "1"]), ("schema", "other"), ("extra", True)):
            mutant = copy.deepcopy(valid)
            mutant[key] = value
            with self.subTest(key=key, value=str(value)[:30]):
                self.assertFalse(verify_certificate(matrix, mutant))
        self.assertFalse(verify_certificate(matrix, None))

    def test_invalid_input_is_not_positive_evidence(self) -> None:
        invalid: tuple[Matrix, ...] = ((), ((F(1), F(0)),), ((F(1), F(2)), (F(0), F(1))))
        for matrix in invalid:
            with self.assertRaises(ValueError):
                certify(matrix)
            self.assertFalse(verify_certificate(matrix, {"schema": SCHEMA, "kind": "weighted_squares", "terms": []}))


if __name__ == "__main__":
    unittest.main()
