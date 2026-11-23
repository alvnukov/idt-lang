"""Exact tests for a supplied coherent comparator on a frozen raw readout."""

import unittest
from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_fixed_phase_four_port as probe
from scripts import probe_raw_bond_junction_rates as raw


class FixedPhaseFourPort(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.probe = probe
        cls.native = raw.report()

    def test_observed_target_and_joint_are_checked_before_comparison(self):
        p, t = self.probe.native_tables(self.native)
        self.assertEqual(p[1], (F(1, 3), F(0), F(1, 3), F(1, 3)))
        self.assertEqual(t[1], (F(2, 9), F(1, 3), F(2, 9), F(2, 9)))
        cases = [("isolated", 0, "mass"), ("literal", 1, "joint")]
        for section, index, field in cases:
            rows = [dict(r) for r in self.native[section]]
            idx = [
                i for i, r in enumerate(rows) if r["law"] == "free" and r["offset"] == 6
            ][index]
            rows[idx][field] = (
                {"jam": "1"} if field == "joint" else ["0"] * 4 + ["1", "0"]
            )
            with self.assertRaises(ValueError):
                self.probe.native_tables(dict(self.native, **{section: rows}))

    def test_one_column_already_fails_under_any_fixed_rewiring(self):
        _, t = self.probe.native_tables(self.native)
        for perm in permutations(range(4)):
            # Reorder outputs relative to inputs; the native T is permutation invariant.
            obs = tuple(tuple(row[i] for i in perm) for row in t)
            dets = self.probe.inspect_table(obs)["one_input_gram_determinants"]
            self.assertEqual(
                dets, tuple(F(1) if perm[i] == i else F(3, 4) for i in range(4))
            )
        audit = self.probe.inspect_table(t)
        self.assertEqual(audit["gram_rank"], 4)
        self.assertEqual(audit["gram_determinant"], 1)
        self.assertFalse(audit["fixed_phase_possible"])

    def test_static_controls_and_exact_two_contexts(self):
        u = ((1, 0), (0, 1), (-1, 0), (0, -1))
        _, t = self.probe.native_tables(self.native)
        identity = tuple(tuple(F(i == j) for j in range(4)) for i in range(4))
        self.assertEqual(self.probe.phase_table([u[0]] * 4), identity)
        for phases in product(u, repeat=3):
            table = self.probe.phase_table((u[0], *phases))
            self.assertTrue(self.probe.inspect_table(table)["fixed_phase_possible"])
        a = self.probe.phase_table((u[0], u[1], u[0], u[1]))
        b = self.probe.phase_table((u[0], u[1], u[2], u[3]))
        self.assertNotEqual(a, b)
        self.assertEqual(
            tuple(tuple((x + y) / 2 for x, y in zip(xr, yr)) for xr, yr in zip(a, b)), t
        )
        rational = ((F(3, 5), F(4, 5)), u[3], u[2], u[0])
        self.assertTrue(
            self.probe.inspect_table(self.probe.phase_table(rational))[
                "fixed_phase_possible"
            ]
        )

    def test_inverse_detects_wrong_diagonal_asymmetry_and_non_psd(self):
        table = [list(row) for row in self.probe.phase_table([(1, 0)] * 4)]
        table[0][0] = F(1, 2)
        self.assertFalse(self.probe.inspect_table(table)["diagonal_consistent"])
        table[0][1] = F(1, 3)
        self.assertFalse(self.probe.inspect_table(table)["symmetric"])
        # All reconstructed offdiagonal scalar products -1: determinant/rank
        # checks alone must not call this a Gram of unit vectors.
        m = tuple(
            tuple(F(0) if i == j else F(4, 9) for j in range(4)) for i in range(4)
        )
        self.assertFalse(self.probe.inspect_table(m)["gram_psd"])
        with self.assertRaises(ValueError):
            self.probe.phase_table([(2, 0)] * 4)

    def test_independently_phased_stages_reduce_to_one_internal_diagonal(self):
        p = self.probe
        axes = ((1, 0), (0, 1), (F(3, 5), F(4, 5)), (F(-5, 13), F(12, 13)))
        c = p.C
        a = tuple(
            tuple(p.cmul(axes[i], axes[(j + 2) % 4], (c[i][j], 0)) for j in range(4))
            for i in range(4)
        )
        b = tuple(
            tuple(
                p.cmul(axes[(i + 1) % 4], axes[(j + 3) % 4], (c[i][j], 0))
                for j in range(4)
            )
            for i in range(4)
        )
        self.assertEqual(
            p.dephase_stage(a), tuple(tuple((v, 0) for v in row) for row in c)
        )
        self.assertEqual(p.dephase_stage(b), p.dephase_stage(a))
        prod = p.stage_product_table(a, b)
        self.assertEqual(
            prod,
            p.phase_table(
                tuple(p.cmul(axes[(j + 2) % 4], axes[(j + 1) % 4]) for j in range(4))
            ),
        )

    def test_exact_full_table_extremizer(self):
        result = self.probe.report(self.native)
        self.assertEqual(result["sharp_aligned_full_table_error"], "(1+sqrt(5))/18")
        witness = result["full_optimum_witness"]
        self.assertEqual(witness["phase_multiples_of_pi_over_5"], (0, 1, 3, 4))
        self.assertEqual(
            witness["twice_pair_cosines"],
            ((0, 1), (1, -1), (0, -1), (-1, 1), (1, -1), (0, 1)),
        )
        self.assertEqual(
            witness["twice_triangle_cosine_sums"], ((0, 1), (1, -1), (1, -1), (0, 1))
        )
        self.assertEqual(result["minimum_exact_frozen_phase_contexts"], 2)
