import unittest
from fractions import Fraction as F
from itertools import combinations

from scripts import probe_phase_gradient_tomography as p


class PhaseGradientTomographyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c, cls.t = p.native_fixture()

    def test_aliased_laws_separate_at_gradient(self):
        self.assertEqual(p.table(self.c, p.TWO), self.t)
        self.assertEqual(p.table(self.c, p.FOUR), self.t)
        gradient = p.table(self.c, p.TWO, p.GRADIENT)
        self.assertEqual(gradient[2][3], F(2, 5))
        self.assertEqual(gradient[2][3] - self.t[2][3], F(8, 45))
        self.assertEqual(p.table(self.c, p.FOUR, p.GRADIENT), self.t)
        gamma = p.correlations(p.TWO)
        self.assertEqual(
            {pair for pair in p.PAIRS if gamma[pair] != p.ZERO}, {(0, 1), (2, 3)}
        )
        self.assertEqual(gamma[0, 1], p.I.scale(-1))
        self.assertEqual(gamma[2, 3], p.I.scale(-1))

    def test_all_column_subsets_and_nonflat_complex_correlations(self):
        law = (
            (F(1, 3), (p.ONE, p.I, p.W, p.I * p.W)),
            (F(2, 3), (p.W, p.ONE, p.I, p.W * p.W)),
        )
        gamma = p.correlations(law)
        base = p.table(self.c, law)
        tilted = p.table(self.c, law, p.GRADIENT)
        for n, size in enumerate((0, 3, 5, 6, 6)):
            for inputs in combinations(p.PORTS, n):
                got = p.recover(base, tilted, p.GRADIENT, inputs)
                self.assertEqual(len(got), size)
                self.assertEqual(got, {k: gamma[k] for k in got})
                self.assertEqual(set(got), {k for k in p.PAIRS if set(inputs) - set(k)})

    def test_rank_three_witness_for_every_pair(self):
        for a, b in p.PAIRS:
            law = p.three_contexts(a, b)
            self.assertEqual(tuple(prob for prob, _ in law), (F(1, 3),) * 3)
            self.assertEqual(p.table(self.c, law), self.t)
            gradient = p.table(self.c, law, p.GRADIENT)
            gamma = p.correlations(law)
            self.assertEqual(gamma[a, b], p.I.scale(-1))
            self.assertTrue(all(gamma[q] == p.ZERO for q in p.PAIRS if q != (a, b)))
            for i in p.PORTS:
                self.assertEqual(
                    [r[i] for r in gradient] == [r[i] for r in self.t], i in (a, b)
                )

    def test_alias_program_and_repeated_observations(self):
        with self.assertRaisesRegex(ValueError, "nonidentifying"):
            p.recover(self.t, self.t, p.BASELINE, p.PORTS)
        aliased = (p.ONE, p.I, p.ONE, p.I)
        with self.assertRaisesRegex(ValueError, "nonidentifying"):
            p.recover(self.t, self.t, aliased, (1,))
        bad = [list(row) for row in self.t]
        bad[2][3] += F(1, 9)
        with self.assertRaisesRegex(ValueError, "disagree"):
            p.recover(self.t, bad, p.GRADIENT, (2, 3))

    def test_program_sign_is_supplied_not_measured(self):
        reverse = tuple(z.conj() for z in p.GRADIENT)
        conjugate_law = tuple((q, tuple(z.conj() for z in row)) for q, row in p.TWO)
        observations = p.table(self.c, p.TWO, p.GRADIENT)
        self.assertEqual(observations, p.table(self.c, conjugate_law, reverse))
        self.assertNotEqual(p.correlations(p.TWO), p.correlations(conjugate_law))
        self.assertEqual(
            p.recover(self.t, observations, reverse, p.PORTS),
            p.correlations(conjugate_law),
        )

    def test_integer_weight_remains_exact(self):
        law = ((1, (p.ONE, p.I, p.W, p.ONE)),)
        self.assertEqual(p.table(self.c, law)[1][3], F(4, 45))

    def test_rank_three_vertices_are_unit_cube_roots(self):
        self.assertEqual(p.OMEGA * p.OMEGA * p.OMEGA, p.ONE)
        self.assertEqual(p.ONE + p.OMEGA + p.OMEGA * p.OMEGA, p.ZERO)

    def test_report_distinguishes_two_shot_assumption(self):
        report = p.report()
        self.assertEqual(
            report["two_shot"]["conditional_hit_probabilities"], ["0", "4/9"]
        )
        self.assertEqual(report["two_shot"]["shared"], "8/81")
        self.assertEqual(report["two_shot"]["iid"], "4/81")
        self.assertEqual(report["gradient"]["sines"], ["4/5", "24/25", "44/125"])
