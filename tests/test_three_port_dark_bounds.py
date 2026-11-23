from dataclasses import replace
from fractions import Fraction as F
from itertools import product
import unittest

from scripts import probe_three_port_dark_bounds as p


SCOPE = p.Scope(orthogonal_inputs=True, single_mode_per_port=True, complete_three_ports=True,
                all_launches_accounted=True, same_device_and_settings=True)
PLAN = p.CountPlan(F(1, 5), F(1, 100), F(1, 20), 512, 512,
                   preregistered=True, iid_within_each_row=True)
ROWS = ((384, 0, 128), (0, 384, 128))


def box(ac=F(1, 4), bc=F(1, 4), ab=0, ba=0):
    return {"AC": (ac, 1), "BC": (bc, 1), "AB": (0, ab), "BA": (0, ba)}


class ThreePortDarkBoundsTests(unittest.TestCase):
    def test_exact_and_near_threshold(self):
        for z, excluded in [(0, True), (F(2144, 100000), True),
                            (F(2145, 100000), False), (F(1, 2), False)]:
            self.assertEqual(p.interval_verdict(box(ab=z, ba=z), SCOPE)["excluded"], excluded)

    def test_asymmetric_darks_and_brights(self):
        self.assertTrue(p.interval_verdict(box(F(1, 4), F(1, 3), 0, F(1, 10)), SCOPE)["excluded"])
        self.assertFalse(p.interval_verdict(box(F(1, 4), F(1, 4), 0, F(1, 12)), SCOPE)["excluded"])
        self.assertTrue(p.interval_verdict(box(F(1, 2), F(2, 3), 1, 1), SCOPE)["excluded"])

    def test_sharp_rational_reflection_and_four_entry_removals(self):
        rows = ((F(2, 3), F(-1, 3), F(2, 3)), (F(-1, 3), F(2, 3), F(2, 3)),
                (F(2, 3), F(2, 3), F(-1, 3)))
        for i, j in product(range(3), repeat=2):
            self.assertEqual(sum(a * b for a, b in zip(rows[i], rows[j])), int(i == j))
        self.assertFalse(p.interval_verdict(box(F(4, 9), F(4, 9), F(1, 9), F(1, 9)), SCOPE)["excluded"])
        for key in box():
            controls = box()
            controls[key] = (0, 1)
            self.assertFalse(p.interval_verdict(controls, SCOPE)["excluded"])
            a, b = p.removal_witnesses()[key]
            self.assertEqual(sum(a), 1)
            self.assertEqual(sum(b), 1)
            cells = dict(AC=a[2], BC=b[2], AB=a[1], BA=b[0])
            # These witnesses attain the other ORIGINAL three values exactly.
            self.assertNotEqual(cells.pop(key), box()[key][0])
            self.assertEqual(cells, {k: v[0] for k, v in box().items() if k != key})
            positive = [v * w for v, w in zip(a, b) if v*w]
            self.assertTrue(not positive or len(positive) == 2 and positive[0] == positive[1])

    def test_invalid_missing_censored_or_unresolved_are_inconclusive(self):
        for field in SCOPE.__dataclass_fields__:
            for flag in (False, None, 1):
                with self.subTest(field=field, flag=flag):
                    self.assertFalse(p.interval_verdict(box(), replace(SCOPE, **{field:flag}))["excluded"])
        for problem in (None, {}, dict(box(), AC=(1, 0)), dict(box(), BC=(-1, 1)),
                        dict(box(), AB=(None, 0)), dict(box(), AB=(0, float("nan"))),
                        dict(box(), AB=(1, 1)), dict(box(), BA=(False, 0))):
            self.assertFalse(p.interval_verdict(problem, SCOPE)["excluded"])

    def test_binomial_strict_threshold_fixed_counts_and_controls(self):
        large = p.count_verdict(ROWS, SCOPE, PLAN)
        self.assertTrue(large["excluded"])
        self.assertTrue(all(F(0) < x <= PLAN.alpha / 4 for x in large["tails"].values()))
        self.assertEqual(large["tails"]["AB"], (1 - PLAN.z) ** 512)
        small = p.count_verdict(((6, 0, 2), (0, 6, 2)), SCOPE, replace(PLAN, n_a=8, n_b=8))
        self.assertFalse(small["excluded"])
        self.assertFalse(p.count_verdict(ROWS, SCOPE, replace(PLAN, z=0))["excluded"])
        for attr in ("preregistered", "iid_within_each_row"):
            self.assertFalse(p.count_verdict(ROWS, SCOPE, replace(PLAN, **{attr:False}))["excluded"])
        self.assertFalse(p.count_verdict(ROWS, replace(SCOPE, all_launches_accounted=False), PLAN)["excluded"])
        for values in (None, ((383, 0, 128), ROWS[1]), ((386, -2, 128), ROWS[1]),
                       ((384, False, 128), ROWS[1]), ((384, 128), ROWS[1])):
            self.assertFalse(p.count_verdict(values, SCOPE, PLAN)["excluded"])
        for attr, value in (("alpha", 1), ("c", None), ("z", F(1, 2)), ("n_a", True)):
            self.assertFalse(p.count_verdict(ROWS, SCOPE, replace(PLAN, **{attr:value}))["excluded"])

    def test_shared_physical_shades_fixed_dephased_and_independently_refreshed(self):
        echo = p.echo_controls()
        self.assertEqual(echo["raw_launches_restored"], 24)
        self.assertEqual(echo["one_over_8"], ((6, 0, 2), (0, 6, 2), (2, 2, 4)))
        self.assertEqual(echo["shared_over_8"], ((8, 0, 0), (0, 8, 0), (0, 0, 8)))
        self.assertEqual(echo["fresh_over_64"], ((40, 4, 20), (4, 40, 20), (20, 20, 24)))
        self.assertEqual(echo["fixed_dephased_over_8"], echo["one_over_8"])
        self.assertEqual(echo["fixed_permutation_over_8"], echo["shared_over_8"])
        self.assertEqual(echo["fixed_coherent_over_8"], echo["shared_over_8"])

    def test_report_connects_interval_to_raw_census_separately_from_synthetic_counts(self):
        report = p.verify()
        self.assertTrue(report["literal_interval"]["excluded"])
        self.assertTrue(report["hypothetical_fixed_count_example"]["excluded_under_stated_scope"])


if __name__ == "__main__":
    unittest.main()
