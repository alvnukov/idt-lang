"""Exact, small regression oracles for the operational sector-word fixtures."""

import unittest
from contextlib import redirect_stdout
from fractions import Fraction as F
from io import StringIO
from math import prod

from scripts import probe_echo_gauge_normal_form as echo
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
    synthesize_isometry,
    unitary,
)
from scripts.probe_exact_charge_sector_wall import (
    AXES,
    Z,
    approximant,
    distance2,
    exact_projective_gap2,
    five_slot_target,
    leakage2,
    unit_power,
)
from scripts.probe_heralded_sector_phase import physical_word, simple_heralded_control
from scripts.probe_projective_repeat_classification import diag, instrument, primitive


def scale(scalar: Gaussian, matrix: Matrix) -> Matrix:
    return tuple(tuple(scalar * entry for entry in row) for row in matrix)


def paired(matrix: Matrix) -> Matrix:
    return tuple(rail for row in matrix for rail in (row, tuple(ZERO - x for x in row)))


class OperationalSectorWordsTest(unittest.TestCase):
    def test_scalar_shutter_gram_equality_does_not_identify_fourth_power(self) -> None:
        ref, rotated, _ = echo.models()
        s = echo.add(echo.P0, echo.scale(F(1, 3), echo.P1))
        t = echo.add(echo.scale(F(2, 5), echo.P0), echo.P1)
        reference_word = echo.mul(echo.mul(t, ref), echo.mul(s, ref))
        rotated_word = echo.mul(echo.mul(t, rotated), echo.mul(s, rotated))
        for port in (echo.P0, echo.P1):
            self.assertEqual(
                echo.port_gram(reference_word, port), echo.port_gram(rotated_word, port)
            )
        self.assertEqual(echo.power(ref, 4), echo.scale(F(10000), echo.eye(4)))
        self.assertNotEqual(echo.power(rotated, 4), echo.power(ref, 4))

    def test_primitive_gaussian_rescaling_leaves_norm_and_ray(self) -> None:
        source = diag((g(2, 1), g(2, -1)))
        scaled = scale(g(F(-7, 13), F(4, 15)), source)
        base, m = primitive(source)
        resized, resized_m = primitive(scaled)
        self.assertEqual((m, resized_m), (5, 5))
        self.assertIn(resized, tuple(scale(u, base) for u in AXES))

    def test_dyadic_nonunitary_is_rejected(self) -> None:
        # Unit norm for both columns is insufficient: the columns coincide.
        target = ((ONE, ONE), (ZERO, ZERO))
        with self.assertRaisesRegex(ValueError, "orthonormal"):
            synthesize(target)
        with self.assertRaisesRegex(ValueError, "projectively unitary"):
            primitive(target)

    def test_unitary_nondyadic_is_rejected(self) -> None:
        target = diag((Z, ONE))
        self.assertTrue(unitary(target))
        with self.assertRaisesRegex(ValueError, "Gaussian-dyadic"):
            synthesize(target)

    def test_exact_three_slot_rectangular_paired_native_replay(self) -> None:
        half = g(F(1, 2))
        h = g(F(1, 2), F(1, 2))
        target = ((half, h), (half, ZERO - h), (h, ZERO))
        seed = tuple(row[:2] for row in eye(3))
        word = synthesize_isometry(target)
        self.assertEqual(run(seed, word), target)
        physical = physical_word(word)
        self.assertTrue(physical)
        self.assertTrue(all(tag == "T" for tag, _, _ in physical))
        self.assertEqual(run(paired(seed), physical), paired(target))
        completion = run(eye(3), word)
        self.assertTrue(unitary(completion))
        self.assertEqual(tuple(row[:2] for row in completion), target)

    def test_five_slot_invariant_is_unchanged_by_common_sign_or_phase(self) -> None:
        def invariant(matrix: Matrix) -> Gaussian:
            d = tuple(row[j] for j, row in enumerate(matrix))
            a, b = prod(d[:3], start=ONE), prod(d[3:], start=ONE)
            return a * a * b.star() * b.star() * b.star()

        target = five_slot_target()
        self.assertEqual(prod((row[j] for j, row in enumerate(target)), start=ONE), ONE)
        expected = unit_power(Z, -30)
        self.assertEqual(invariant(target), expected)
        self.assertNotIn(expected, AXES)
        for phase in (g(-1), I, Z):
            self.assertEqual(invariant(scale(phase, target)), expected)
        self.assertEqual(
            exact_projective_gap2(), min((expected - u).norm2() for u in AXES) / 144
        )
        self.assertGreater(exact_projective_gap2(), 0)

    def test_costlier_replay_crosses_exact_gap_only_with_leakage(self) -> None:
        target = five_slot_target()
        coarse, fine = approximant(3), approximant(18)
        coarse_word, fine_word = synthesize(coarse), synthesize(fine)
        self.assertGreater(len(fine_word), len(coarse_word))
        self.assertTrue(unitary(fine))
        self.assertEqual(run(eye(5), fine_word), fine)
        distance = distance2(fine, target)
        leak = leakage2(fine)
        mixers = sum(tag == "T" for tag, _, _ in fine_word)
        self.assertLess(distance, exact_projective_gap2())
        self.assertLess(exact_projective_gap2(), distance2(coarse, target))
        self.assertGreaterEqual(leak, F(1, 2**mixers))
        self.assertLessEqual(leak, distance)
        self.assertLess(leak, leakage2(coarse))
        self.assertEqual(leakage2(target), 0)

    def test_complete_one_herald_table_can_record_the_input(self) -> None:
        with redirect_stdout(StringIO()):
            operators = simple_heralded_control()
        effects = tuple((a.norm2(), b.norm2()) for a, b in operators)
        self.assertEqual(
            tuple(sum(column) for column in zip(*effects, strict=True)), (1, 1)
        )
        self.assertEqual(effects[0], (F(25, 64), F(25, 64)))
        self.assertEqual(effects[4], (F(1, 64), F(9, 64)))

    def test_grouped_retry_has_harmless_failures_but_resolved_success_dephases(
        self,
    ) -> None:
        blocks, probs, m = instrument(diag((Z, ONE)))
        success, *failures = (blocks[j : j + 2] for j in range(0, len(blocks), 2))
        a, b = success[0][0], success[1][1]
        self.assertEqual((m, probs[0]), (5, F(5, 8)))
        self.assertEqual((a, a.norm2(), b.norm2()), (Z * b, probs[0], probs[0]))
        self.assertEqual(sum(probs), 1)
        self.assertEqual(sum(probs[1:]), F(3, 8))
        for block, p in zip(failures, probs[1:], strict=True):
            c = block[0][0]
            self.assertEqual(block, diag((c, c)))
            self.assertEqual(c.norm2(), p)
        input_coherence = g(F(1, 2))
        grouped = a * b.star() * input_coherence
        resolved = sum(
            (x * y.star() * input_coherence for x, y in ((a, ZERO), (ZERO, b))), ZERO
        )
        self.assertEqual(grouped, g(F(5, 16)) * Z)
        self.assertEqual(resolved, ZERO)
