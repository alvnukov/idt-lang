"""Raw signed counter predictions against independent cumulative counting formulae."""

import copy
import hashlib
import json
import unittest
from dataclasses import replace
from itertools import permutations, product
from pathlib import Path
from unittest.mock import patch

from theory_experiments import signed_contact_stream as stream
from theory_experiments.primitive_screen import Limits

PASS = "no_counterexample_within_bounds"


def raw(rule, d, phase, arrivals, reads):
    return {"id": "contact", "family": "signed_contact_stream", "ports": d, "rule": rule, "initial_phase": phase,
            "inputs": [{"port": i, "sign": s} for i, s in arrivals],
            "readouts": [{"after": k, "scope": kind, "counts": list(v)} for k, kind, v in reads]}


def evaluate(spec, budget=64, **opts):
    candidate = stream.parse_signed_contact_stream(spec)
    (ck,), d = stream.evaluate_signed_contact_stream(candidate, Limits(max_cases=budget), **opts)
    return ck, d


def cumulative(rule, d, r, arrivals):
    # Independent formula: signed visit counts to each congruence class
    # on the unwrapped path from r to r+2S. Negative S traverses it backwards.
    signed = [sum(s for i, s in arrivals if i == j) for j in range(d)]
    if rule == "idle_wire":
        return signed
    stop = r + 2*sum(signed)
    if rule == "anonymous_bucket":
        broadcast = (stop - (stop % d)) // d
        return [broadcast - x for x in signed]
    visits = [((stop+d-1-j)//d) - ((r+d-1-j)//d) for j in range(d)]
    return [v-x for v, x in zip(visits, signed, strict=True)]


class SignedContactTests(unittest.TestCase):
    def test_all_phases_and_ports_both_signs_against_independent_prefix_and_inverse(self):
        for d in range(2, 9):
            for rule in stream.RULES:
                for r in range(1 if rule == "idle_wire" else d):
                    for i, sign in product(range(d), (-1, 1)):
                        delta = cumulative(rule, d, r, [(i, sign)])
                        after, actual = stream._step(rule, d, r, i, sign)
                        self.assertEqual(actual, delta)
                        back, returned = stream._step(rule, d, after, i, -sign)
                        self.assertEqual((back, returned), (r, [-v for v in delta]))
                    # Mostly negative prefix, then a long run across multiple
                    # wraps, alternating signs, and repeated input ports.
                    ins = [((k*k+3*k) % d, -1 if k < 9 or (k > 19 and k % 2) else 1) for k in range(30)]
                    reads = []
                    previous = [0]*d
                    for k in range(1, len(ins)+1):
                        cur = cumulative(rule, d, r, ins[:k])
                        reads.extend(((k, "step", [v-w for v, w in zip(cur, previous, strict=True)]),
                                      (k, "prefix", cur)))
                        previous = cur
                    ck, details = evaluate(raw(rule, d, r, ins, reversed(reads)))
                    self.assertEqual((ck.status, ck.checked, ck.planned, details["inputs_consumed"]), (PASS, 60, 60, 30))
                    expected_phase = None if rule == "idle_wire" else (r+2*sum(s for _, s in ins)) % d
                    self.assertEqual(details["model_phase_after_consumed_inputs"], expected_phase)

    def test_closed_cycle_masks_different_arrival_outputs_and_rewinding_is_essential(self):
        ins = [(0, 1), (0, 1)]
        closed = [(2, "prefix", [-1, 1, 1, 1])]
        for rule in stream.RULES:
            ck, _ = evaluate(raw(rule, 4, 0, ins, closed))
            self.assertEqual(ck.status, "counterexample" if rule == "idle_wire" else PASS)
        observed = [(1, "step", [0, 1, 0, 0]), *closed]
        for rule in stream.RULES:
            ck, details = evaluate(raw(rule, 4, 0, ins, observed))
            self.assertEqual(ck.status, PASS if rule == "ordered_pair_rotor" else "counterexample")
            if ck.witness:
                w = ck.witness["inputs"]
                self.assertEqual(int(ck.witness["actual"]), w["predicted_count"]-w["submitted_count"])
            self.assertEqual((details["proof_status"], details["empirical_status"], details["scientific_status"]),
                             ("not_attempted", "not_tested", "unassessed"))
        # Phase zero: negative rotor command withdraws from ports 2,3
        # before returning one unit to port 0. A forward-first reader fails.
        rewind = [(1, "step", [1, 0, -1, -1]), (2, "prefix", [0]*4)]
        self.assertEqual(evaluate(raw("ordered_pair_rotor", 4, 0, [(0, -1), (0, 1)], rewind))[0].status, PASS)

    def test_bucket_full_renaming_rotor_has_only_a_supplied_cycle(self):
        d, phase = 5, 3
        before = [(0, 1), (4, -1), (3, 1)]
        for perm in permutations(range(d)):
            changed = [(perm[i], sign) for i, sign in before]
            expected = cumulative("anonymous_bucket", d, phase, before)
            renamed = [expected[perm.index(j)] for j in range(d)]
            self.assertEqual(evaluate(raw("anonymous_bucket", d, phase, changed, [(3, "prefix", renamed)]))[0].status, PASS)
        for offset in range(d):
            perm = [(j+offset) % d for j in range(d)]
            changed = [(perm[i], sign) for i, sign in before]
            expected = cumulative("ordered_pair_rotor", d, phase, before)
            renamed = [expected[perm.index(j)] for j in range(d)]
            self.assertEqual(evaluate(raw("ordered_pair_rotor", d, perm[phase], changed, [(3, "prefix", renamed)]))[0].status, PASS)
        # Fix the initial pointer, swap names 1 and 3: changes the cycle.
        check, _ = evaluate(raw("ordered_pair_rotor", 4, 0, [(0, 1)], [(1, "step", [0, 0, 0, 1])]))
        self.assertEqual(check.status, "counterexample")

    def test_degenerate_two_ports_and_inconsistent_but_well_formed_observations(self):
        ins = [(0, -1), (0, -1), (1, 1)]
        reads = [(1, "step", [0, -1]), (3, "prefix", [1, -2])]
        for rule in stream.RULES[:2]:
            for phase in (0, 1):
                self.assertEqual(evaluate(raw(rule, 2, phase, ins, reads))[0].status, PASS)
        for rule in stream.RULES:
            # Same counters at k=1 cannot be 1M in step and zero in prefix.
            spec = raw(rule, 2, 0, ins, [(1, "step", [10**6, -10**6]), (1, "prefix", [0, 0])])
            ck, d = evaluate(spec)
            self.assertEqual((ck.status, ck.checked, d["inputs_consumed"]), ("counterexample", 2, 3))

    def test_budget_and_deadline_do_not_promote_partial_disagreements(self):
        spec = raw("idle_wire", 2, 0, [(0, 1), (1, -1), (0, 1)], [(2, "prefix", [0, 0])])
        for budget, compared in ((1, 0), (2, 1)):
            ck, d = evaluate(spec, budget)
            self.assertEqual((ck.status, ck.checked, ck.planned, ck.witness, d["inputs_consumed"], d["stop_reason"]),
                             ("inconclusive", compared, 1, None, budget, "max_cases"))
        self.assertEqual(evaluate(spec, 3)[0].status, "counterexample")
        with self.assertRaises(ValueError):
            evaluate(spec, 0)
        for consumed in range(4):
            with patch.object(stream, "monotonic", side_effect=[0]*consumed+[2]):
                ck, d = evaluate(spec, deadline=2)
                self.assertEqual((ck.status, ck.witness, d["inputs_consumed"], d["stop_reason"]),
                                 ("inconclusive", None, consumed, "deadline"))
        for bad in (True, float("nan"), float("-inf")):
            with self.assertRaises(ValueError):
                evaluate(spec, deadline=bad)

    def test_canonicalization_bounds_and_small_receipt(self):
        spec = raw("idle_wire", 2, 0, [(0, 1), (1, -1)], [(2, "prefix", [1, -1]), (1, "step", [1, 0])])
        c = stream.parse_signed_contact_stream(spec)
        canonical = c.specification()
        spec["readouts"][0]["counts"].clear()
        spec["inputs"].reverse()
        self.assertEqual(c.specification(), canonical)
        self.assertEqual(stream.parse_signed_contact_stream(canonical), c)
        self.assertEqual(stream.LOADED_SOURCE_SHA256, hashlib.sha256(Path(stream.__file__).read_bytes()).hexdigest())
        for key, val in (("ports", True), ("ports", 9), ("initial_phase", 1), ("initial_phase", False),
                         ("rule", "fitted"), ("inputs", []), ("inputs", canonical["inputs"]*33),
                         ("inputs", [{"port": 0, "sign": True}]), ("inputs", [{"port": 0, "sign": 0}]),
                         ("inputs", [{"port": 2, "sign": 1}]), ("readouts", []),
                         ("readouts", canonical["readouts"]*2), ("readouts", canonical["readouts"]*33)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                stream.parse_signed_contact_stream({**canonical, key: val})
        for key, val in (("after", 0), ("after", 3), ("scope", "phase"), ("counts", [False, 1]),
                         ("counts", [1, 2, 3]), ("counts", [1000001, 0]), ("extra", 1)):
            raw_bad = copy.deepcopy(canonical)
            raw_bad["readouts"][0][key] = val
            with self.assertRaises(ValueError):
                stream.parse_signed_contact_stream(raw_bad)
        with self.assertRaises(ValueError):
            replace(c, readouts=tuple(reversed(c.readouts)))
        with self.assertRaises(TypeError):
            stream.evaluate_signed_contact_stream(c, {})
        ins = [(i % 8, 1) for i in range(64)]
        largest = raw("anonymous_bucket", 8, 0, ins, [(i+1, "prefix", [10**6]*8) for i in range(64)])
        ck, d = evaluate(largest)
        self.assertLess(len(json.dumps([largest, ck.specification(), d])), 64*1024)


if __name__ == "__main__":
    unittest.main()
