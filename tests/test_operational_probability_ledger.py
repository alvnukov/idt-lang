"""Standalone feasibility, exact certificates and negative controls on small event ledgers."""

import copy
import hashlib
import unittest
from dataclasses import replace
from fractions import Fraction
from itertools import product
from pathlib import Path
from unittest.mock import patch

from theory_experiments import operational_probability_ledger as op
from theory_experiments.primitive_screen import Limits

PASS = "no_counterexample_within_bounds"


def ledger(settings, bounds=(), links=(), basis="all_attempts"):
    return {"id": "test", "family": "operational_probability_ledger", "basis": basis,
            "settings": [{"id": s, "outcomes": list(o)} for s, o in settings],
            "bounds": [{"event": {"setting": s, "outcomes": list(o)}, "lower": str(lo), "upper": str(hi)}
                       for s, o, lo, hi in bounds],
            "links": [{"left": {"setting": s, "outcomes": list(o)}, "right": {"setting": t, "outcomes": list(p)},
                       "tolerance": str(eps)} for s, o, t, p, eps in links]}


def six(eps, basis="all_attempts"):
    # In each separate setting the complementary outcome is certain; exclude
    # its other outcome there. Transfer those five near-zeros to distinct full
    # row outputs, with the sixth also dark. Exact minimum tolerance = 1/5.
    names = tuple("abcde")
    return ledger([("full", (*names, "dark")), *((s, ("certain", "other")) for s in names)],
                  [("full", ("dark",), 0, 0), *((s, ("certain",), 1, 1) for s in names)],
                  [(s, ("other",), "full", (s,), eps) for s in names], basis)


def evaluate(raw, budget=1000, **opts):
    c = op.parse_operational_probability_ledger(raw)
    (ck,), d = op.evaluate_operational_probability_ledger(c, Limits(max_cases=budget), **opts)
    return c, ck, d


class OperationalProbabilityTests(unittest.TestCase):
    def test_six_outcome_contradiction_and_sharp_rational_boundary(self):
        for eps, verdict in (("0", "counterexample"), ("199999999999/999999999999", "counterexample"),
                             ("1/5", PASS), ("200000000000/999999999999", PASS), ("1", PASS)):
            c, check, details = evaluate(six(eps))
            self.assertEqual(check.status, verdict)
            cert = details["checked_certificate"]
            self.assertTrue(op.verify_ledger_certificate(c, cert))
            self.assertEqual(check.checked, 1)
            self.assertEqual((details["proof_status"], details["empirical_status"], details["scientific_status"]),
                             ("not_attempted", "not_tested", "unassessed"))
            if verdict == "counterexample":
                self.assertLess(Fraction(check.witness["actual"]), 0)
                self.assertEqual(cert["kind"], "farkas")
            elif eps == "1/5":
                vector = iter(map(Fraction, cert["values"]))
                table = {(s, o): next(vector) for s, names in c.settings for o in names}
                self.assertEqual([table["full", s] for s in "abcde"], [Fraction(1, 5)]*5)
                self.assertEqual(table["full", "dark"], 0)
        # Complementary formulation: five disjoint targets with lower transfers
        # each >=1/5 fit only at or below that common floor.
        for floor, verdict in (("1/5", PASS), ("201/1000", "counterexample")):
            raw = ledger([("full", "abcdef")], [("full", (s,), floor, 1) for s in "abcde"])
            self.assertEqual(evaluate(raw)[1].status, verdict)
        # Five independently certain local outcomes; NO bound on the sixth
        # outcome in the target. The transfer error (not floor) threshold is 4/5.
        for tol, verdict in (("0", "counterexample"), ("799999999999/999999999999", "counterexample"),
                             ("4/5", PASS), ("1", PASS)):
            raw = ledger([("full", "abcdef"), *((s, "xy") for s in "abcde")],
                         [(s, "x", 1, 1) for s in "abcde"],
                         [(s, "x", "full", s, tol) for s in "abcde"])
            c, check, details = evaluate(raw)
            self.assertEqual(check.status, verdict)
            self.assertTrue(op.verify_ledger_certificate(c, details["checked_certificate"]))

    def test_missing_transfer_and_separately_postselected_escape(self):
        raw = six(0, "separately_postselected")
        c, ck, d = evaluate(raw)
        self.assertEqual((ck.status, ck.checked, ck.witness, d["checked_certificate"]), ("unsupported", 0, None, None))
        self.assertFalse(op.verify_ledger_certificate(c, {"kind": "primal", "values": ["0"]*16}))
        raw["links"] = []
        self.assertEqual(evaluate(raw)[1].status, PASS)
        raw["basis"] = "all_attempts"
        self.assertEqual(evaluate(raw)[1].status, PASS)

    def test_ordinary_qubit_rows_and_sum_of_different_events(self):
        # |0> measured in Z or X; declarations are compatible only, not a
        # reconstruction of a state or of incompatible measurements.
        c, ck, d = evaluate(ledger([("z", "ab"), ("x", "pm")],
                                   [("z", "a", 1, 1), ("x", "p", "1/2", "1/2")]))
        self.assertEqual(ck.status, PASS)
        self.assertTrue(op.verify_ledger_certificate(c, d["checked_certificate"]))
        for expected, verdict in (("3/5", PASS), ("4/5", "counterexample")):
            raw = ledger([("left", "abc"), ("right", "de")],
                         [("left", "a", "1/5", "1/5"), ("left", "b", "2/5", "2/5"),
                          ("right", "e", expected, expected)], [("left", "ab", "right", "e", 0)])
            self.assertEqual(evaluate(raw)[1].status, verdict)
        # Same-row overlapping events: shared variables cancel exactly.
        raw = ledger([("s", "abc")], [("s", "b", "1/2", "1/2"), ("s", "c", 0, 0)],
                     [("s", "ab", "s", "ac", "1/3")], basis="separately_postselected")
        self.assertEqual(evaluate(raw)[1].status, "counterexample")

    def test_primal_and_dual_witnesses_refuse_tampering(self):
        for eps, key in (("1/5", "values"), ("0", "weights")):
            c, _, d = evaluate(six(eps))
            cert = d["checked_certificate"]
            for invalid in ({}, {**cert, "more": True}, {**cert, key: cert[key][:-1]},
                            {**cert, key: ["0"]*len(cert[key])}):
                self.assertFalse(op.verify_ledger_certificate(c, invalid))
            for invalid in (True, 0, "1/0", "-1", "00", "2/2", str(2**256), "1"*1000):
                tampered = copy.deepcopy(cert)
                tampered[key][0] = invalid
                self.assertFalse(op.verify_ledger_certificate(c, tampered))
        raw = ledger([("s", "ab")])
        with patch.object(op, "verify_ledger_certificate", return_value=False), self.assertRaises(ArithmeticError):
            evaluate(raw)

    def test_budget_caps_and_deadline_return_no_unchecked_certificate(self):
        raw = six(0)
        _, ck, d = evaluate(raw)
        exact = d["completed_pivots"]
        self.assertGreater(exact, 1)
        for budget in (1, exact-1, exact):
            _, result, details = evaluate(raw, budget)
            self.assertEqual(details["completed_pivots"], budget)
            self.assertEqual(result.status, ck.status if budget == exact else "inconclusive")
            if budget < exact:
                self.assertEqual((result.checked, result.witness, details["checked_certificate"]), (0, None, None))
        for budget_name, cap in (("MAX_UPDATES", 1), ("MAX_BITS", 1)):
            with patch.object(op, budget_name, cap):
                _, short, info = evaluate(six("1/5"))
                self.assertEqual((short.status, short.witness, info["checked_certificate"]), ("inconclusive", None, None))
        for calls in ([3], [0, 0, 3]):
            with patch.object(op, "monotonic", side_effect=calls):
                _, short, info = evaluate(raw, deadline=3)
                self.assertEqual((short.status, short.witness, info["stop_reason"]), ("inconclusive", None, "deadline"))
        for invalid in (True, float("nan"), float("inf")):
            with self.assertRaises(ValueError):
                evaluate(raw, deadline=invalid)

    def test_two_binary_rows_against_independent_small_grid_oracle(self):
        # Rows parametrized by p=P(s.a), q=P(t.a). Bounds and two links give
        # axes and diagonals, quarter-integral RHS. Every polygon vertex lies
        # on the 1/8 grid (absolute determinant of any two normals <=2).
        for lo, hi, eps, eta in product(range(0, 5, 2), range(0, 5, 2), range(3), range(3)):
            raw = ledger([("s", "ab"), ("t", "ab")],
                         [("s", "a", Fraction(lo, 4), 1), ("t", "a", 0, Fraction(hi, 4))],
                         [("s", "a", "t", "a", Fraction(eps, 4)), ("s", "a", "t", "b", Fraction(eta, 4))])
            feasible = any(p >= 2*lo and q <= 2*hi and abs(p-q) <= 2*eps and abs(p+q-8) <= 2*eta
                           for p, q in product(range(9), repeat=2))
            c, ck, d = evaluate(raw)
            self.assertEqual(ck.status, PASS if feasible else "counterexample")
            self.assertTrue(op.verify_ledger_certificate(c, d["checked_certificate"]))

    def test_strict_schema_canonicalization_and_ownership(self):
        raw = six("2/10")
        c = op.parse_operational_probability_ledger(raw)
        normal = c.specification()
        self.assertEqual(op.parse_operational_probability_ledger(normal), c)
        self.assertTrue(all(r["tolerance"] == "1/5" for r in normal["links"]))
        self.assertEqual(op.LOADED_SOURCE_SHA256, hashlib.sha256(Path(op.__file__).read_bytes()).hexdigest())
        for link in raw["links"]:
            link["left"], link["right"] = link["right"], link["left"]
        for setting in raw["settings"]:
            setting["outcomes"].reverse()
        raw["settings"].reverse()
        self.assertEqual(op.parse_operational_probability_ledger(raw), c)
        raw["settings"].clear()
        self.assertEqual(c.specification(), normal)
        for key, invalid in (("settings", []), ("settings", normal["settings"]*3),
                             ("links", normal["links"]*20), ("basis", True),
                             ("extra", "predicted"), ("bounds", [normal["bounds"][0]]*2)):
            with self.assertRaises(ValueError):
                op.parse_operational_probability_ledger({**normal, key: invalid})
        for lower, upper in ((True, "1"), ("2", "2"), ("-1", "1"), ("1/0", "1"), ("1", "0"),
                             ("0.5", "1"), ("1/1000000000000", "1")):
            with self.assertRaises(ValueError):
                op.parse_operational_probability_ledger(ledger([("s", "ab")], [("s", "a", lower, upper)]))
        for setting, event in (("missing", "a"), ("s", ""), ("s", "aa"), ("s", "z")):
            with self.assertRaises(ValueError):
                op.parse_operational_probability_ledger(ledger([("s", "ab")], [(setting, event, 0, 1)]))
        with self.assertRaises(ValueError):
            replace(c, settings=tuple(reversed(c.settings)))
        with self.assertRaises(TypeError):
            op.evaluate_operational_probability_ledger(c, object())

    def test_maximum_dimension_and_shared_coarse_rows(self):
        settings = [(f"s{i}", "abcd") for i in range(16)]
        bounds = [(s, o, "1/4", "1/4") for s, names in settings for o in names]
        links = [(s, left, settings[(i+1) % 16][0], right, 0) for i, (s, _) in enumerate(settings)
                 for left, right in (("ab", "bc"), ("cd", "ad"))]
        c, check, d = evaluate(ledger(settings, bounds, links))
        self.assertEqual((check.status, d["variables"], d["inequalities"]), (PASS, 64, 224))
        self.assertEqual(set(d["checked_certificate"]["values"]), {"1/4"})
        self.assertTrue(op.verify_ledger_certificate(c, d["checked_certificate"]))
        links.append(("s0", "a", "s1", "a", 0))
        with self.assertRaises(ValueError):
            op.parse_operational_probability_ledger(ledger(settings, bounds, links))


if __name__ == "__main__":
    unittest.main()
