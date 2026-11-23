"""Exact signed-refinement reference, modular aliasing and unobservable stationary stocks."""

import copy
import hashlib
import json
import unittest
from dataclasses import replace
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from unittest.mock import patch

from scripts.probe_mobile_refinement_field import enc, ideal, read, signed_star
from theory_experiments import ternary_network_nulls as net
from theory_experiments.primitive_screen import Limits

PASS = "no_counterexample_within_bounds"
H, G = (0, 1, 2), (1, 2, 3)


def raw(rule, seed, word, reads, p=None):
    return {"id": "network", "family": "ternary_network_nulls", "rule": rule, "modulus": p, "initial": list(seed),
            "contacts": [list(h) for h in word],
            "readouts": [{"after": k, "port": j, "dark": dark} for k, j, dark in reads]}


def evaluate(spec, budget=64, **opts):
    cand = net.parse_ternary_network_nulls(spec)
    (ck,), d = net.evaluate_ternary_network_nulls(cand, Limits(max_cases=budget), **opts)
    return ck, d


def oracle(initial, word, rule, p=None):
    """Fraction reflection and explicit elementary signed reservoir deposits."""
    x = list(map(Fraction, initial))
    reservoir = {}
    history = []
    for h in word:
        if rule in ("mobile_depth", "residue_field"):
            x = ideal(x, h)
        elif rule == "stationary_bucket":
            support = frozenset(h)
            units = int(2*sum(x[j] for j in h))
            stock, q = reservoir.get(support, 0), 0
            for _ in range(abs(units)):
                stock += 1 if units > 0 else -1
                if stock == 3:
                    q += 1
                    stock = 0
                elif stock < 0:
                    q -= 1
                    stock = 2
            reservoir[support] = stock
            for i in h:
                x[i] = q-x[i]
        # Every rational denominator here is a power of three and invertible
        # in the admitted field, so modulo-p zero is a numerator-only test.
        history.append([u.numerator % p == 0 if p is not None else u == 0 for u in x])
    return history


class TernaryNetworkNullTests(unittest.TestCase):
    def test_exhaustive_four_command_words_against_independent_null_oracles(self):
        for seed in ((0, 0, 0, 0), (0, 0, 1, 0), (2, -1, 0, -2), (-32, 0, 32, 1)):
            for word in product((H, G), repeat=4):
                for rule, p in (("mobile_depth", None), ("stationary_bucket", None), ("idle_wire", None),
                                ("residue_field", 2), ("residue_field", 5), ("residue_field", 997)):
                    flags = oracle(seed, word, rule, p)
                    reads = [(k, i, dark) for k, row in enumerate(flags, 1) for i, dark in enumerate(row)]
                    ck, d = evaluate(raw(rule, seed, word, reversed(reads), p))
                    self.assertEqual((ck.status, ck.checked, d["contacts_consumed"]), (PASS, 16, 4))
                    self.assertTrue(all(type(r["predicted_dark"]) is bool for r in d["comparisons"]))
                    self.assertEqual((d["proof_status"], d["empirical_status"], d["scientific_status"]),
                                     ("not_attempted", "not_tested", "unassessed"))

    def test_mobile_values_match_nested_signed_marks_and_fractions_through_depth_64(self):
        seed = (1, 0, 0, 0)
        num, depths = list(seed), [0]*4
        signed = enc(seed)
        rational = list(map(Fraction, seed))
        for h in (H, G)*32:
            net._mobile(num, depths, h)
            rational = ideal(rational, h)
            signed = signed_star(signed, h)
            self.assertEqual([Fraction(n, 3**k) for n, k in zip(num, depths, strict=True)], rational)
            self.assertEqual([read(row) for row in signed], rational)
            self.assertTrue(all(k == 0 or n % 3 for n, k in zip(num, depths, strict=True)))
        self.assertEqual(max(depths), 64)
        for h in (G, H)*32:
            net._mobile(num, depths, h)
        self.assertEqual((num, depths), (list(seed), [0]*4))

    def test_distinct_rules_can_agree_or_disagree_at_raw_single_ports(self):
        # After two overlapping commands port 2 is 5/9, hence dark in F5
        # but bright in the rational channel. The F5-dark flag is legitimate,
        # not a claim the underlying expression vanished over all fields.
        seed, word = (0, 0, 1, 0), (H, G)
        mobile, residue = (evaluate(raw(r, seed, word, [(2, 2, True)], p))[0] for r, p in
                           (("mobile_depth", None), ("residue_field", 5)))
        self.assertEqual((mobile.status, residue.status), ("counterexample", PASS))
        self.assertEqual(mobile.witness["inputs"]["predicted_dark"], False)
        # Even an untouched initial value can alias zero in Fp.
        for rule, p, verdict in (("mobile_depth", None, "counterexample"), ("residue_field", 5, PASS)):
            self.assertEqual(evaluate(raw(rule, (1, 0, 0, 5), (H,), [(1, 3, True)], p))[0].status, verdict)
        # A single dark read need not distinguish any candidates.
        for rule in net.RULES:
            ck, _ = evaluate(raw(rule, (1, 0, 0, 0), (H,), [(1, 3, True)], 7 if rule == "residue_field" else None))
            self.assertEqual(ck.status, PASS)

    def test_stationary_private_support_stock_excluded_from_detector(self):
        # Nonzero bucket remainder 2, but raw stationary port 1 is zero.
        for rule, verdict in (("stationary_bucket", PASS), ("mobile_depth", "counterexample")):
            self.assertEqual(evaluate(raw(rule, (1, 0, 0), (H,), [(1, 1, True)]))[0].status, verdict)
        # Negative quotient must floor, not truncate. At step 3, a single
        # global stock would falsely darken port 1; at step 4, a new stock
        # for the reordered/repeated G would falsely brighten that port.
        word = (H, G, H[::-1], G[::-1])
        ck, d = evaluate(raw("stationary_bucket", (0, 0, 0, -1), word, [(2, 1, False), (3, 1, False), (4, 1, True)]))
        self.assertEqual(ck.status, PASS)
        self.assertEqual(set(d["comparisons"][0]), {"after", "port", "predicted_dark", "submitted_dark"})

    def test_partial_budget_and_deadline_do_not_leak_unperformed_comparisons(self):
        spec = raw("idle_wire", (1, 0, 0, 0), (H, G, H), [(2, 0, True)])
        for budget, compared in ((1, 0), (2, 1)):
            ck, d = evaluate(spec, budget)
            self.assertEqual((ck.status, ck.checked, ck.planned, ck.witness, d["contacts_consumed"], d["stop_reason"]),
                             ("inconclusive", compared, 1, None, budget, "max_cases"))
        self.assertEqual(evaluate(spec, 3)[0].status, "counterexample")
        for n in range(4):
            with patch.object(net, "monotonic", side_effect=[0]*n+[2]):
                ck, d = evaluate(spec, deadline=2)
                self.assertEqual((ck.status, ck.witness, d["contacts_consumed"], d["stop_reason"]),
                                 ("inconclusive", None, n, "deadline"))
        for bad in (True, float("nan"), float("-inf")):
            with self.assertRaises(ValueError):
                evaluate(spec, deadline=bad)
        with self.assertRaises(ValueError):
            evaluate(spec, 0)

    def test_strict_schema_and_canonical_per_support_only_not_per_schedule(self):
        good = raw("residue_field", (0, 0, 1, 0), (H[::-1], G[::-1]), [(2, 2, True), (1, 0, False)], 5)
        c = net.parse_ternary_network_nulls(good)
        normal = c.specification()
        self.assertEqual(net.parse_ternary_network_nulls(normal), c)
        self.assertEqual((c.contacts, c.readouts), ((H, G), ((1, 0, False), (2, 2, True))))
        changed_order = copy.deepcopy(good)
        changed_order["contacts"].reverse()
        self.assertNotEqual(net.parse_ternary_network_nulls(changed_order), c)
        self.assertEqual(evaluate(good)[0].status, PASS)
        self.assertEqual(evaluate(changed_order)[0].status, "counterexample")
        good["contacts"][0].clear()
        self.assertEqual(c.specification(), normal)
        for key, v in (("initial", [True, 0, 0, 0]), ("initial", [0, 0, 33]), ("initial", [0, 0]),
                       ("initial", [0]*9), ("contacts", []), ("contacts", normal["contacts"]*49),
                       ("contacts", [[0, 1, 1]]), ("contacts", [[0, 2, 4]]), ("contacts", [[0, 1, True]]),
                       ("contacts", [[0, 1]]), ("readouts", []), ("readouts", normal["readouts"]*2),
                       ("readouts", normal["readouts"]*33), ("visible_gain", 1), ("family", False), ("rule", "other")):
            with self.subTest(key=key), self.assertRaises(ValueError):
                net.parse_ternary_network_nulls({**normal, key: v})
        for p in (True, None, -2, 1, 3, 4, 49, 341, 961, 1009, 7.0, "7"):
            with self.assertRaises(ValueError):
                net.parse_ternary_network_nulls({**normal, "modulus": p})
        for rule in set(net.RULES)-{"residue_field"}:
            with self.assertRaises(ValueError):
                net.parse_ternary_network_nulls({**normal, "rule": rule})
        for k, val in (("after", 0), ("after", True), ("after", 3), ("port", -1), ("port", False),
                       ("dark", 0), ("dark", None), ("dark", "false"), ("stock", 2)):
            bad = copy.deepcopy(normal)
            bad["readouts"][0][k] = val
            with self.assertRaises(ValueError):
                net.parse_ternary_network_nulls(bad)
        with self.assertRaises(ValueError):
            replace(c, contacts=(H[::-1],))
        with self.assertRaises(TypeError):
            net.evaluate_ternary_network_nulls(c, {})
        self.assertEqual(net.LOADED_SOURCE_SHA256, hashlib.sha256(Path(net.__file__).read_bytes()).hexdigest())

    def test_maximum_network_and_receipt_remain_bounded(self):
        combos = list(combinations(range(8), 3))
        word = (combos+combos)[:96]
        seed = (32, -32, 0, 1, 7, -19, 4, 0)
        for rule in net.RULES:
            p = 997 if rule == "residue_field" else None
            flags = oracle(seed, word, rule, p)
            spec = raw(rule, seed, word, [(k+1, k % 8, flags[k][k % 8]) for k in range(32, 96)], p)
            ck, d = evaluate(spec, 96)
            self.assertEqual((ck.status, ck.checked, ck.planned, d["contacts_consumed"]), (PASS, 64, 64, 96))
            self.assertLess(len(json.dumps([spec, ck.specification(), d])), 32*1024)
            with self.assertRaises(ValueError):
                net.parse_ternary_network_nulls({**spec, "contacts": [*spec["contacts"], list(H)]})
            with self.assertRaises(ValueError):
                net.parse_ternary_network_nulls({**spec, "readouts": [*spec["readouts"], {"after": 1, "port": 0, "dark": False}]})


if __name__ == "__main__":
    unittest.main()
