"""Raw triangle-law controls, independent replay and interpolation checks."""

import ast
import hashlib
import unittest
from dataclasses import replace
from fractions import Fraction
from itertools import product
from pathlib import Path

from theory_experiments import triangle_stock as adapter
from theory_experiments.primitive_screen import Limits


Q = [[1, 0, 0], [0, 1, 0], [1, 1, 0]]
ONE = [[0, 0, 1]]


def spec(m=1, forms=None, overrides=None, gains=("4", "4", "4")):
    return {"id": "submitted", "family": "triangle_stock", "modulus": m,
            "default_forms": Q if forms is None else forms,
            "overrides": [] if overrides is None else overrides, "gains": list(gains)}


def override(a, b, forms):
    return {"residue": [a, b], "forms": forms}


def evaluate(raw, budget=1000):
    (check,), scope = adapter.evaluate_triangle_stock(
        adapter.parse_triangle_stock(raw), Limits(max_cases=budget))
    return check, scope


def stock(raw, v):
    a, b, c = v
    assert a + b + c == 0
    residue = [a % raw["modulus"], b % raw["modulus"]]
    forms = next((r["forms"] for r in raw["overrides"] if r["residue"] == residue),
                 raw["default_forms"])
    return sum((kx*a + ky*b + offset)**2 for kx, ky, offset in forms)


def branches(v, k):
    a, b, c = v
    w = ((a, c, b), (c, b, a), (b, a, c))[k]
    return [[p+q for p, q in zip(v, w)], [p-q for p, q in zip(v, w)]]


def residual(raw, k, v):
    pos, neg = branches(v, k)
    return stock(raw, pos) + stock(raw, neg) - Fraction(raw["gains"][k])*stock(raw, v)


class TriangleStockAdapterTests(unittest.TestCase):
    def assert_replay(self, raw, check):
        self.assertEqual(check.status, "counterexample")
        w = check.witness["inputs"]
        v, k = w["input"], w["fixed_port"]
        self.assertEqual(v[:2], [r+raw["modulus"]*i for r, i in
                                  zip(w["input_residue"], w["stencil_offset"])])
        p, n = branches(v, k)
        self.assertEqual([w["plus_output"], w["minus_output"]], [p, n])
        self.assertEqual([w["input_stock"], w["plus_stock"], w["minus_stock"]],
                         [stock(raw, u) for u in (v, p, n)])
        self.assertEqual(Fraction(w["claimed_gain"]), Fraction(raw["gains"][k]))
        value = residual(raw, k, v)
        self.assertNotEqual(value, 0)
        self.assertEqual(str(value), check.witness["actual"])

    def test_quadratic_all_moduli_and_exact_budget_boundary(self):
        for m in range(1, 8):
            raw = spec(m=m)
            n = 18*m*m
            check, scope = evaluate(raw, n)
            self.assertEqual((check.status, check.checked, check.planned),
                             ("no_counterexample_within_bounds", n, n))
            self.assertTrue(scope["identity_certified_on_submitted_integer_domain"])
            self.assertEqual(scope["rejection_scope"], "only_submitted_quasipolynomial_and_gain_law")
            self.assertEqual((scope["proof_status"], scope["empirical_status"]),
                             ("not_attempted", "not_tested"))
            self.assertEqual([r["positive_unit_stock"] for r in scope["edge_stock"]], [2]*3)
            self.assertEqual([r["negative_unit_stock"] for r in scope["median_stock"]], [6]*3)
            short, info = evaluate(raw, n-1)
            self.assertEqual((short.status, short.checked, short.planned), ("inconclusive", n-1, n))
            self.assertEqual(info["stop_reason"], "max_cases")
            self.assertFalse(info["identity_certified_on_submitted_integer_domain"])

    def test_dark_mod_three_passes_no_required_median_or_scale(self):
        raw = spec(3, [], [override(a, b, [[0, 0, 5]]) for a, b in product(range(3), repeat=2)
                           if a != b], gains=("1",)*3)
        check, scope = evaluate(raw)
        self.assertEqual((check.status, check.checked), ("no_counterexample_within_bounds", 162))
        self.assertTrue(all(r["identically_dark_on_integer_ray"] for r in scope["median_stock"]))
        self.assertEqual([r["negative_unit_stock"] for r in scope["edge_stock"]], [25]*3)
        self.assertTrue(scope["identity_certified_on_submitted_integer_domain"])

    def test_failed_mixtures_anisotropy_and_per_setting_gain_claims_replay(self):
        mixture = [override(a, b, Q + ONE) for a, b in product(range(3), repeat=2) if a != b]
        for raw in (spec(3, Q, mixture, ("1",)*3), spec(3, Q, mixture),
                    spec(3, Q, mixture, ("1", "4", "4")), spec(forms=[[1, 0, 0]]),
                    spec(gains=("4", "4", "5/3"))):
            check, scope = evaluate(raw)
            self.assert_replay(raw, check)
            self.assertFalse(scope["identity_certified_on_submitted_integer_domain"])
            self.assertEqual(scope["stop_reason"], "first_counterexample")
            if check.checked > 1:
                truncated, _ = evaluate(raw, check.checked-1)
                self.assertEqual(truncated.status, "inconclusive")
            self.assertEqual(evaluate(raw, check.checked)[0], check)

    def test_hidden_seven_sublattice_is_invisible_in_small_window(self):
        raw = spec(7, Q, [override(0, 0, [[2*x, 2*y, 2*c] for x, y, c in Q])])
        for a, b in product(range(-1, 2), repeat=2):
            self.assertTrue(all(residual(raw, k, (a, b, -a-b)) == 0 for k in range(3)))
        check, _ = evaluate(raw)
        self.assertGreater(check.checked, 18)
        self.assert_replay(raw, check)
        self.assertEqual(evaluate(raw, 18)[0].status, "inconclusive")

    def test_late_lit_ray_is_not_classified_by_the_unit_reads(self):
        # All unit medians and edges are dark; on 7L, a^2 lights some of them.
        raw = spec(7, [], [override(0, 0, [[1, 0, 0]])])
        _, scope = evaluate(raw)
        for row in scope["median_stock"]:
            self.assertEqual([row["positive_unit_stock"], row["negative_unit_stock"],
                              row["first_positive_lit_scale"]], [0, 0, 7])
        self.assertTrue(scope["edge_stock"][0]["identically_dark_on_integer_ray"])

    def test_domain_exclusions_are_not_counterexamples(self):
        for raw, reason in ((spec(forms=ONE, gains=("2",)*3), "nonzero_origin"),
                            (spec(forms=[]), "zero_stock"),
                            (spec(1, Q, [override(0, 0, [])]), "zero_stock")):
            check, scope = evaluate(raw)
            self.assertEqual((check.status, check.checked, check.planned, check.witness),
                             ("unsupported", 0, 0, None))
            self.assertEqual(scope["stop_reason"], "unsupported_"+reason)
            self.assertFalse(scope["identity_certified_on_submitted_integer_domain"])

    def test_malformed_data_and_direct_dataclass_guards(self):
        invalid = [None, True, {**spec(), "labels_are_symmetric": True}]
        for key in spec():
            invalid.append({k: v for k, v in spec().items() if k != key})
        for key, choices in {
            "id": ["UPPER"], "family": ["other"], "modulus": [True, 0, 8, "3", 2.0],
            "default_forms": [None, (Q,), [[]], [[1]*4], ONE*6, [[True, 0, 1]], [[0, 65, 0]]],
            "gains": [["1"]*2, ["1", 1, "1"], [True]*3, ["0"]*3, ["-1/2"]*3, ["1.5"]*3,
                      ["1/0"]*3, ["1/1000000000000"]*3],
            "overrides": [True, [override(2, 0, [])], [override(-1, 0, [])],
                          [override(0, False, [])], [override(0, 0, [])]*2,
                          [{"residue": [1], "forms": []}], [{"residue": [1, 1], "forms": 1}],
                          [{"residue": [1, 1], "forms": [], "extra": 0}]],
        }.items():
            invalid.extend({**spec(m=2), key: v} for v in choices)
        for raw in invalid:
            with self.subTest(raw=raw), self.assertRaises((ValueError, TypeError)):
                adapter.parse_triangle_stock(raw)
        parsed = adapter.parse_triangle_stock(spec())
        for bad in ({"gains": (1, 1, 1)}, {"default_forms": ([1, 0, 0],)},
                    {"overrides": (((True, 0), ()),)}, {"modulus": False}):
            with self.assertRaises(ValueError):
                replace(parsed, **bad)

    def test_canonical_roundtrip_residue_order_square_sign_and_multiplicity(self):
        raw = spec(3, [[-1, 0, 0], [1, 0, 0], [0, 0, 0]],
                   [override(2, 0, []), override(1, 0, ONE), override(0, 2, [[1, 0, 0]]*2)],
                   ("2/2", "6/2", "9/3"))
        canon = adapter.parse_triangle_stock(raw).specification()
        self.assertEqual(canon, spec(3, [[1, 0, 0]]*2,
                                     [override(1, 0, ONE), override(2, 0, [])], ("1", "3", "3")))
        self.assertEqual(adapter.parse_triangle_stock(canon).specification(), canon)

    def test_stencil_reconstructs_residual_at_negative_distant_coordinates(self):
        raw = spec(3, [[1,-2,3]], [override(0,0,Q), override(0,2,ONE), override(1,2,[])],
                   ("2/3","1","4"))
        for a, b, k in product(range(3), repeat=3):
            def val(i, j):
                x, y = a + 3*i, b + 3*j
                return residual(raw, k, (x,y,-x-y))
            c, d, e, f, g, h = (val(i,j) for i,j in adapter._STENCIL)
            for i, j in ((-434,157), (999,0), (0,-1), (91,285)):
                self.assertEqual(val(i,j), c+i*(d-c)+j*(e-c)+i*(i-1)//2*(f-2*d+c)
                                 +i*j*(g-d-e+c)+j*(j-1)//2*(h-2*e+c))

    def test_loaded_source_pin_and_no_frozen_probe_import(self):
        source = Path(adapter.__file__).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), adapter.LOADED_SOURCE_SHA256)
        for node in ast.walk(ast.parse(source)):
            names = ([node.module or ""] if isinstance(node, ast.ImportFrom)
                     else [n.name for n in node.names] if isinstance(node, ast.Import) else [])
            self.assertFalse(any(s.startswith("scripts") for s in names))


if __name__ == "__main__":
    unittest.main()
