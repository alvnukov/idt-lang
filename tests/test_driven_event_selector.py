"""Independent cycle enumeration, evidence replay and parser/resource controls."""

import copy
import hashlib
import unittest
from dataclasses import replace
from fractions import Fraction
from itertools import product
from pathlib import Path
from unittest.mock import patch

from theory_experiments import driven_event_selector as adapter
from theory_experiments.primitive_screen import Limits


def ctx(v=(1, 0, -1), i=0):
    return {"current": list(v), "fixed": i}


def spec(contexts, table, initial=0):
    return {"id": "selector", "family": "driven_event_selector",
            "contexts": contexts, "initial": initial, "transitions": table}


def evaluate(raw, budget=5000, **kwargs):
    (check,), details = adapter.evaluate_driven_event_selector(
        adapter.parse_driven_event_selector(raw), Limits(max_cases=budget), **kwargs)
    return check, details


def reference(raw):
    # Independent derivation as a fraction of the two raw branch stocks.
    v, i = raw["current"], raw["fixed"]
    j, k = [s for s in range(3) if s != i]
    w = v[:]
    w[j], w[k] = v[k], v[j]
    minus = sum((a-b)**2 for a, b in zip(v, w))
    plus = sum((a+b)**2 for a, b in zip(v, w))
    return Fraction(minus, plus+minus)


def reachable_states(raw):
    seen = {raw["initial"]}
    for _ in raw["transitions"]:
        seen |= {t for s in seen for t, _ in raw["transitions"][s]}
    return seen


def replay(raw, start, word):
    counts, minus = [[0]*len(raw["contexts"]) for _ in range(2)]
    s = start
    for c in word:
        s, y = raw["transitions"][s][c]
        counts[c] += 1
        minus[c] += y
    return s, counts, minus


def brute(raw):
    # A nonzero closed walk contains a nonzero simple cycle, length <= n.
    table, settings = raw["transitions"], range(len(raw["contexts"]))
    rates = list(map(reference, raw["contexts"]))
    for start in reachable_states(raw):
        for n in range(1, len(table)+1):
            for word in product(settings, repeat=n):
                end, counts, minus = replay(raw, start, word)
                if end == start and any(y != p*m for p, y, m in zip(rates, minus, counts)):
                    return False
    return True


class DrivenSelectorTests(unittest.TestCase):
    def witness(self, raw, check):
        self.assertEqual(check.status, "counterexample")
        w = check.witness["inputs"]
        self.assertEqual(w["initial_state"], raw["initial"])
        s = replay(raw, raw["initial"], w["prefix"])[0]
        self.assertTrue(w["loop"])
        end, counts, minus = replay(raw, s, w["loop"])
        self.assertEqual((s, end), (w["loop_state"], w["final_state"]))
        self.assertEqual(s, end)
        self.assertEqual((counts, minus), (w["context_counts"], w["minus_counts"]))
        j = w["context_index"]
        p = reference(raw["contexts"][j])
        d = p.denominator*minus[j] - p.numerator*counts[j]
        self.assertNotEqual(d, 0)
        self.assertEqual((w["target_minus_rate"], w["actual_minus_rate"], w["integer_residual"]),
                         (str(p), str(Fraction(minus[j], counts[j])), d))
        self.assertEqual(check.witness["actual"], str(d))

    def certificate(self, raw, info):
        self.assertTrue(info["all_eventually_periodic_context_rates_certified"])
        reached = reachable_states(raw)
        accounted = set()
        rates = list(map(reference, raw["contexts"]))
        for component in info["potential_certificate"]:
            values = dict(component["state_potentials"])
            self.assertEqual(values[component["base"]], [0]*len(rates))
            self.assertFalse(accounted.intersection(values))
            accounted.update(values)
            for s, vector in values.items():
                for c, (t, bit) in enumerate(raw["transitions"][s]):
                    if t in values:
                        delta = [0]*len(rates)
                        delta[c] = rates[c].denominator*bit - rates[c].numerator
                        self.assertEqual([a-b for a, b in zip(values[t], vector)], delta)
        self.assertEqual(accounted, reached)

    def test_exhaustive_small_labelled_machines_against_independent_oracle(self):
        integer = [ctx((0, 1, -1)), ctx((2, -1, -1))]
        fractional = [ctx(), ctx((0, 1, -1))]
        for n in (1, 2):
            for dest in product(range(n), repeat=2*n):
                for bits in product(range(2), repeat=2*n):
                    table = [[[dest[2*s+c], bits[2*s+c]] for c in (0, 1)] for s in range(n)]
                    for contexts in (integer, fractional):
                        raw = spec(contexts, table)
                        check, info = evaluate(raw)
                        if brute(raw):
                            self.assertEqual(check.status, "no_counterexample_within_bounds")
                            self.certificate(raw, info)
                        else:
                            self.witness(raw, check)

    def test_nonbottom_trap_reachable_after_prefix_and_unreachable_defect(self):
        contexts = [ctx((0, 1, -1)), ctx((0, 1, -1))]
        # 0->1; repeating A stays at bad non-bottom 1; B escapes to good 2.
        raw = spec(contexts, [[[1, 0], [1, 0]], [[1, 0], [2, 1]], [[2, 1], [2, 1]]])
        check, info = evaluate(raw)
        self.witness(raw, check)
        self.assertTrue(check.witness["inputs"]["prefix"])
        self.assertEqual(check.witness["inputs"]["loop_state"], 1)
        self.assertFalse(info["all_eventually_periodic_context_rates_certified"])
        raw["initial"] = 2
        check, info = evaluate(raw)
        self.assertEqual((check.planned, check.checked), (2, 2))
        self.certificate(raw, info)
        self.assertEqual(info["reachable_states"], 1)

    def test_disagreeing_paths_first_closure_harmless_second_is_witness(self):
        raw = spec([ctx((0, 1, -1)), ctx((2, -1, -1))],
                   [[[1, 0], [1, 0]], [[0, 1], [0, 0]]])
        check, _ = evaluate(raw)
        self.witness(raw, check)
        self.assertEqual(check.witness["inputs"]["loop"], [0, 0])
        self.assertEqual(evaluate(raw, check.checked)[0], check)
        short, info = evaluate(raw, check.checked-1)
        self.assertEqual((short.status, short.witness, info["stop_reason"]),
                         ("inconclusive", None, "max_cases"))

    def test_large_success_exact_budget_and_certified_scc_vectors(self):
        contexts = [ctx(), ctx()] + [ctx((0, 1, -1)), ctx((2, -1, -1))]*3
        table = []
        for s in range(128):
            a, b = s % 4, s//4 % 4
            table.append([[s-a+(a+1) % 4, int(a == 1)],
                          [s-4*b+4*((b+1) % 4), int(b == 2)]] +
                         [[(s+16) % 128, int(c % 2 == 0)] for c in range(2, 8)])
        raw = spec(contexts, table, 127)
        check, info = evaluate(raw, 1024)
        self.assertEqual((check.status, check.checked, check.planned),
                         ("no_counterexample_within_bounds", 1024, 1024))
        self.assertEqual(info["reachable_states"], 128)
        self.assertEqual(info["reference_minus_rates"], ["1/4", "1/4"] + ["1", "0"]*3)
        self.assertEqual(info["rejection_scope"], "only_submitted_finite_transducer_and_calibrated_reference")
        self.assertEqual((info["empirical_status"], info["proof_status"]), ("not_tested", "not_attempted"))
        self.certificate(raw, info)
        early, short = evaluate(raw, 1023)
        self.assertEqual((early.status, early.checked, early.planned), ("inconclusive", 1023, 1024))
        self.assertIsNone(short["potential_certificate"])

    def test_harmless_transient_and_reduced_reference_denominators(self):
        # 25/28, scaled and sign reversed: high absolute coordinates but
        # exactly the same reduced target, no rounding or phase averaging.
        for v in ((1, 2, -3), (-300000, -600000, 900000)):
            raw = spec([ctx(v)], [[[1, 1]]] +
                       [[[(s % 28)+1, int(s <= 25)]] for s in range(1, 29)])
            check, info = evaluate(raw, 28)
            self.assertEqual((check.checked, check.planned), (28, 28))
            self.assertEqual(info["reference_minus_rates"], ["25/28"])
            self.certificate(raw, info)
            raw["transitions"][27][0][1] = 1
            check, info = evaluate(raw)
            self.witness(raw, check)
            self.assertEqual(check.witness["inputs"]["integer_residual"], 28)

    def test_zero_reference_and_deadlines_cannot_pass(self):
        raw = spec([ctx((0, 0, 0)), ctx()], [[[0, 1], [0, 1]]])
        check, info = evaluate(raw)
        self.assertEqual((check.status, check.checked, check.planned), ("unsupported", 0, 0))
        self.assertIsNone(check.witness)
        self.assertEqual(info["reference_minus_rates"], [None, "1/4"])
        for deadline in (float("nan"), float("inf"), True, "soon"):
            with self.assertRaises(ValueError):
                evaluate(raw, deadline=deadline)
        raw = spec([ctx((0, 1, -1))], [[[0, 1]]])
        for calls in (0, 5):
            with patch.object(adapter, "monotonic", side_effect=[0]*calls + [20]*50):
                check, info = evaluate(raw, deadline=10)
            self.assertEqual((check.status, info["stop_reason"]), ("inconclusive", "deadline"))
            self.assertIsNone(info["potential_certificate"])
        with patch.object(adapter, "monotonic", return_value=0):
            self.certificate(raw, evaluate(raw, deadline=10)[1])

    def test_strict_immutable_schema_and_hash(self):
        genuine = spec([ctx()], [[[0, 1]]])
        candidate = adapter.parse_driven_event_selector(genuine)
        self.assertEqual(candidate.specification(), genuine)
        genuine["transitions"][0][0][1] = 0
        self.assertEqual(candidate.specification()["transitions"][0][0][1], 1)
        for field, value in (
            ("family", "other"), ("extra", 0), ("id", "BAD"), ("initial", True), ("initial", 1),
            ("contexts", []), ("contexts", [ctx()]*9), ("contexts", [ctx((2, 0, 0))]),
            ("contexts", [ctx((1000001, 0, -1000001))]), ("contexts", [ctx((True, 0, -1))]),
            ("contexts", [ctx(i=3)]), ("contexts", [ctx(i=False)]), ("contexts", [ctx() | {"extra": 1}]),
            ("contexts", [ctx((0, 0))]), ("contexts", [{"current": (0, 1, -1), "fixed": 0}]),
            ("transitions", []), ("transitions", [[[0, 0]]]*129), ("transitions", [[[0, 1], [0, 1]]]),
            ("transitions", [[[0, True]]]), ("transitions", [[[-1, 0]]]), ("transitions", [[[1, 1]]]),
            ("transitions", [[[0, -1]]]), ("transitions", [[[0, 0.0]]]), ("transitions", [[(0, 1)]]),
        ):
            with self.subTest(field=field, value=str(value)[:35]), self.assertRaises((ValueError, TypeError)):
                adapter.parse_driven_event_selector(copy.deepcopy(genuine) | {field: value})
        for key, value in (("contexts", [((1, 0, -1), 0)]), ("contexts", (([1, 0, -1], 0),)),
                           ("transitions", (((0, True),),)), ("transitions", (([0, 1],),))):
            with self.assertRaises((ValueError, TypeError)):
                replace(candidate, **{key: value})
        self.assertEqual(adapter.LOADED_SOURCE_SHA256, hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())


if __name__ == "__main__":
    unittest.main()
