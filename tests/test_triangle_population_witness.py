"""Synthetic counts only: no stored physical measurements or candidate upgrade."""

import json
import unittest
from fractions import Fraction as F
from math import comb

from scripts import check_triangle_population_witness as w


def fixture(minus=(8064,4096,4096), n=8192):
    return {"schema": w.SCHEMA, "contract": dict.fromkeys(w.CONTRACT, True),
            "programs": {name: {"issued": n, "plus": n-k, "minus": k}
                         for name,k in zip(w.PROGRAMS, minus, strict=True)}}


class TrianglePopulationWitnessTests(unittest.TestCase):
    def test_exact_tails_against_direct_small_binomials(self):
        for p in (1-w.CORNER[0], w.CORNER[1]):
            for n in range(1,9):
                for k in range(n+1):
                    exact = sum(comb(n,i)*p**i*(1-p)**(n-i) for i in range(k+1))
                    self.assertEqual(w.lower_tail(n,k,p), exact)

    def test_fixed_witness_and_upward_rounded_tail(self):
        self.assertEqual(sum(c*x for c,x in zip((-30,8,48), w.CORNER)), F(-3,16))
        report = w.check(fixture())
        self.assertEqual((report["decision"], report["p_upper_millionths"]),
                         ("reject_fixed_null", 2416))
        self.assertEqual(report["empirical_verdict"], "not_assessed")
        for counts in ((4096,4096,4096), (8064,8192,4096), (8064,4096,8192)):
            self.assertEqual(w.check(fixture(counts))["decision"], "not_rejected")

    def test_drift_cluster_and_loss_do_not_issue_verdict(self):
        # Isotropic source gives every true marginal 1/2. A single fair block
        # bit in row 1 selects this many ones (positions randomly permuted).
        # All individual trial marginals are fair but rejection occurs on
        # half the blocks. The other two rows always have exactly half ones.
        ns = (8064,128)
        self.assertEqual(sum(ns), 8192)
        self.assertEqual([w.check(fixture((k,4096,4096)))["decision"] for k in ns],
                         ["reject_fixed_null", "not_rejected"])
        # Drift: mix median and edge at normalized weights 1:63 only for
        # row 1 to realize 63/64; isotropic preparations give rows 2,3 half.
        for key in ("common_preparation", "independent_units_within_program"):
            f = fixture()
            f["contract"][key] = False
            r = w.check(f)
            self.assertEqual((r["decision"], r["unmet_declarations"]), ("contract_not_met", [key]))
            self.assertNotIn("p_upper_millionths", r)
        f = fixture()
        f["programs"]["swap01"]["plus"] -= 1
        self.assertEqual((w.check(f)["decision"], w.check(f)["missing_outcomes"]),
                         ("contract_not_met", 1))

    def test_invalid_input(self):
        for bad in (False, -1, 9000, 12.5, "20"):
            f = fixture()
            f["programs"]["swap01"]["minus"] = bad
            with self.assertRaises(ValueError):
                w.check(f)
        f = fixture()
        del f["programs"]["swap01"]
        with self.assertRaises(ValueError):
            w.check(f)
        with self.assertRaises(ValueError):
            json.loads('{"schema":1,"schema":2}', object_pairs_hook=w.unique)
