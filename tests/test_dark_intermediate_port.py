"""Frozen predictions (source rows, detector columns A/B/C, denominator eight)."""

from dataclasses import replace
from fractions import Fraction as F
from itertools import product
import unittest

from scripts import probe_dark_intermediate_port as p


CUT = ((6, 0, 2), (0, 6, 2), (2, 2, 4))
OFF = ((8, 0, 0), (0, 8, 0), (0, 0, 8))
PLATE_A = ((4, 2, 2), (2, 4, 2), (2, 2, 4))
PLATE_BC = ((4, 0, 4), (0, 4, 4), (4, 4, 0))
CYCLE = ((0, 4, 4), (4, 0, 4), (4, 4, 0))
COHERENT = ((1, 4, 3), (4, 1, 3), (3, 3, 2))


class DarkIntermediatePortTests(unittest.TestCase):
    def test_raw_census_and_independent_cycle_controls(self):
        report = p.verify()
        self.assertEqual(report["middle_over_8"], CUT)
        self.assertEqual(report["exit_over_8"],
                         dict(off=OFF, A=PLATE_A, B=PLATE_BC, C=PLATE_BC, cycle=CYCLE))
        self.assertEqual(report["cycle_comparator_over_8"],
                         dict(fixed_permutation=CYCLE, fixed_coherent=COHERENT))
        self.assertEqual(report["B_launch"]["A_exit"], {"q": "0", "r": "0", "s": "1/4"})
        self.assertEqual(report["B_launch"]["non_B_exit"], {"q": "0", "r": "0", "s": "1/2"})

    def test_report_separates_hypothetical_error_budgets_from_census(self):
        report = p.verify()
        self.assertEqual(report.get("hypothetical_simultaneous_bounds"),
                         {"q_upper": "1/64", "r_upper": "1/64", "s_lower": "1/4",
                          "allowed_s_upper": "9/64", "excluded_under_scope": True})

    def test_same_stock_and_no_cut_reread_or_full_arm_reroute(self):
        for source, stock in product(range(3), product((1, 2), repeat=3)):
            baseline = p.history(source, stock, "off")
            for setting in ("off", "A", "B", "C", "cycle"):
                initial, middle, after, final = p.history(source, stock, setting)
                self.assertEqual((initial, middle), baseline[:2])
                self.assertEqual(baseline[-1], initial)
                data, shades = middle[0::4], middle[1::4]
                wanted = list(middle)
                if setting == "cycle":
                    wanted[0::4] = (data[2], data[0], data[1])
                elif setting != "off":
                    port = "ABC".index(setting)
                    wanted[4*port + 1] = 3-shades[port]
                self.assertEqual(after, tuple(wanted))
                for state in (initial, middle, after, final):
                    self.assertEqual((len(state), state.count(3), state[2::4], state[3::4]),
                                     (12, 1, (0, 0, 0), (1, 1, 1)))

    def test_strict_stable_certificate_and_scalar_phase_sharpness(self):
        scope = p.Scope(True, True, True, True, True)
        def verdict(q, r, s, model="supported_unitary"):
            return p.interval_verdict({"q": q, "r": r, "s": s}, scope, model)["excluded"]
        q = r = (0, F(1, 64))
        self.assertFalse(verdict(q, r, (F(9, 64), 1)))  # equality not excluded
        self.assertTrue(verdict(q, r, (F(1, 4), 1)))
        self.assertFalse(verdict((0, F(1, 4)), (0, 0), (F(4, 5), 1)))
        self.assertTrue(verdict((0, F(1, 4)), (0, 0), (F(4, 5), 1), "scalar_pi"))
        self.assertFalse(verdict((0, F(1, 4)), (0, 0), (F(3, 4), 1), "scalar_pi"))
        self.assertFalse(verdict((0, F(3, 4)), (0, 0), (1, 1), "scalar_pi"))
        self.assertFalse(verdict((F(3, 4), 1), (0, 0), (F(4, 5), 1), "scalar_pi"))
        high = {"q": (F(3, 4), 1), "r": (0, 0), "s": (F(4, 5), 1)}
        self.assertTrue(p.interval_verdict(high, scope, "scalar_pi",
                                          q_lower_certified=True)["excluded"])
        self.assertFalse(p.interval_verdict(high, scope, "scalar_pi",
                                           q_lower_certified=1)["excluded"])

    def test_invalid_or_unidentified_scope_never_excludes(self):
        scope = p.Scope(True, True, True, True, True)
        box = {"q": (0, 0), "r": (0, 0), "s": (F(1, 4), 1)}
        self.assertTrue(p.interval_verdict(box, scope)["excluded"])
        for field in vars(scope):
            for flag in (False, None, 1):
                self.assertFalse(p.interval_verdict(box, replace(scope, **{field: flag}))["excluded"])
        for bad in (None, {}, dict(box, q=(0, False)), dict(box, q=(0, 0.0)),
                    dict(box, s=(2, 1)), dict(box, r=(0,)), dict(box, s=(F(1, 2), 0))):
            self.assertFalse(p.interval_verdict(bad, scope)["excluded"])
        self.assertFalse(p.interval_verdict(box, scope, "stock_switch")["excluded"])
