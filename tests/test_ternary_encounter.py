"""Independent occupancy and complete finite truth-table controls for the one-command adapter."""

import hashlib
import json
import unittest
from dataclasses import replace
from itertools import combinations, combinations_with_replacement
from pathlib import Path
from unittest.mock import patch

from theory_experiments import ternary_encounter as adapter
from theory_experiments.primitive_screen import Limits

PASS = "no_counterexample_within_bounds"
RECORDS = tuple(x for x in range(32) if x.bit_count() % 2 == 0)


def sample(packets, vertex, count):
    return {"packets": list(packets), "vertex": vertex, "count": count}


def raw(rule="relative", *rows, marked=(3, 4)):
    return {"id": "encounter", "family": "ternary_encounter", "marked_ports": list(marked),
            "rule": rule, "observations": list(rows)}


def run(spec, budget=64, **kwargs):
    candidate = adapter.parse_ternary_encounter(spec)
    (check,), details = adapter.evaluate_ternary_encounter(candidate, Limits(max_cases=budget), **kwargs)
    return check, details


def oracle_rules(marked):
    """Construct legal pairs by listing forward transitions, not by classifying an input."""
    anchored, relative = {}, {}
    for small in marked:
        for large in set(range(5)) - set(marked):
            def toggle(record, ports):
                occupied = {i for i in range(5) if record & (1 << i)}
                return sum(2**i for i in occupied.symmetric_difference(ports))
            for base in RECORDS:
                odd_one = toggle(base, {small, large})
                src = tuple(sorted((base, base, odd_one)))
                dst = tuple(sorted(toggle(x, set(range(5)) - {large}) for x in src))
                relative[src] = dst
                if base == 0:
                    anchored[src], anchored[dst] = dst, src
    return anchored, relative


class TernaryEncounterTests(unittest.TestCase):
    def test_all_ten_marks_all_816_preparations_against_independent_truth_tables(self):
        for marked in combinations(range(5), 2):
            mask = sum(1 << j for j in marked)
            anchored, relative = oracle_rules(marked)
            self.assertEqual((len(anchored), len(relative)), (12, 96))
            self.assertLessEqual(anchored.items(), relative.items())
            for rule, table in (("anchored", anchored), ("relative", relative), ("idle", {})):
                checked = 0
                for packets in combinations_with_replacement(RECORDS, 3):
                    after = adapter._step(packets, mask, rule)
                    self.assertEqual(after, table.get(packets, packets))
                    self.assertEqual(adapter._step(after, mask, rule), packets)
                    checked += 1
                self.assertEqual(checked, 816)

    def test_fixed_tag_counts_separate_rules_and_detect_idle(self):
        # Blank, common forward, common reverse, off-anchor, off-anchor reverse.
        controls = (sample((0, 0, 0), 0, 3), sample((0, 0, 9), 30, 2),
                    sample((23, 30, 30), 0, 2), sample((3, 3, 10), 29, 2),
                    sample((20, 29, 29), 3, 2))
        cases = (("relative", PASS, 4), ("anchored", "counterexample", 2),
                 ("idle", "counterexample", 0))
        for rule, status, triggers in cases:
            ck, d = run(raw(rule, *controls))
            self.assertEqual((ck.status, ck.checked, ck.planned), (status, 5, 5))
            self.assertEqual(d["distinct_triggering_preparations"], triggers)
            self.assertEqual((d["scientific_status"], d["proof_status"], d["empirical_status"]),
                             ("unassessed", "not_attempted", "not_tested"))
            if ck.witness is not None:
                w = ck.witness
                self.assertEqual(int(w["actual"]), w["inputs"]["predicted_count"] - w["inputs"]["submitted_count"])
                self.assertNotEqual(int(w["actual"]), 0)
        # Same off-anchor input, independently demanded no arrival: opposite verdicts.
        no_arrival = sample((3, 3, 10), 29, 0)
        self.assertEqual([run(raw(r, no_arrival))[0].status for r in adapter.RULES],
                         [PASS, "counterexample", PASS])
        # A dark, irrelevant tag alone cannot distinguish idle from a real change.
        for rule in adapter.RULES:
            ck, d = run(raw(rule, sample((0, 0, 9), 3, 0)))
            self.assertEqual(ck.status, PASS)
            self.assertEqual(d["rejection_scope"], adapter.SCOPE)
        for zero in ((0, 0, 0), (0, 0, 3), (0, 0, 24), (0, 3, 9)):
            for rule in adapter.RULES:
                ck, d = run(raw(rule, sample(zero, 0, zero.count(0))))
                self.assertEqual((ck.status, d["distinct_triggering_preparations"]), (PASS, 0))

    def test_one_command_per_unique_preparation_not_per_tag(self):
        spec = raw("anchored", sample((9, 0, 0), 23, 1), sample((0, 9, 0), 30, 2),
                   sample((0, 0, 9), 0, 0))
        with patch.object(adapter, "_step", wraps=adapter._step) as step:
            ck, d = run(spec)
        self.assertEqual((ck.status, ck.checked, ck.planned), (PASS, 3, 3))
        self.assertEqual((step.call_count, d["distinct_preparations_evaluated"],
                          d["distinct_triggering_preparations"]), (1, 1, 1))
        self.assertEqual([x["vertex"] for x in d["comparisons"]], [0, 23, 30])

    def test_strict_canonical_normalization_and_immutable_candidate(self):
        spec = raw("relative", sample((9, 0, 0), 30, 2), sample((0, 0, 0), 0, 3), marked=(4, 3))
        c = adapter.parse_ternary_encounter(spec)
        spec["observations"][0]["packets"][0] = 1
        spec["marked_ports"].clear()
        canonical = raw("relative", sample((0, 0, 0), 0, 3), sample((0, 0, 9), 30, 2))
        self.assertEqual(c.specification(), canonical)
        self.assertEqual(adapter.parse_ternary_encounter(canonical), c)
        for change in ({"marked_ports": (4, 3)}, {"rule": "other"}, {"observations": tuple(reversed(c.observations))},
                       {"observations": (((9, 0, 0), 0, 0),)}, {"observations": (((0, 0, 0), True, 3),)}):
            with self.assertRaises(ValueError):
                replace(c, **change)
        self.assertEqual(adapter.LOADED_SOURCE_SHA256, hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())

    def test_reject_invalid_or_impossible_demands_but_allow_valid_all_rules_mismatch(self):
        ok = raw("relative", sample((0, 0, 9), 30, 2))
        for key, invalid in (("id", "not valid"), ("family", False), ("rule", "lookup"),
                             ("marked_ports", [3, 3]), ("marked_ports", [True, 3]),
                             ("marked_ports", [2, 3, 4]), ("observations", []),
                             ("observations", [sample((0, 0), 0, 0)]),
                             ("observations", [sample((0, 0, 1), 0, 2)]),
                             ("observations", [sample((0, 0, False), 0, 2)]),
                             ("observations", [sample((0, 0, 0), 31, 0)]),
                             ("observations", [sample((0, 0, 0), 0, True)]),
                             ("observations", [sample((0, 0, 0), 0, 4)]),
                             ("observations", [sample((0, 0, 0), 0, 3)] * 65),
                             ("observations", [sample((9, 0, 0), 0, 2), sample((0, 0, 9), 0, 1)]),
                             ("observations", [sample((0, 0, 0), 0, 2), sample((0, 0, 0), 3, 2)]),
                             ("observations", [sample((0, 0, 9), v, 0) for v in RECORDS]),
                             ("observations", [{**ok["observations"][0], "fired": True}])):
            with self.subTest(key=key, invalid=invalid), self.assertRaises(ValueError):
                adapter.parse_ternary_encounter({**ok, key: invalid})
        with self.assertRaises(ValueError):
            adapter.parse_ternary_encounter({**ok, "charge": 0})
        for rule in adapter.RULES:
            self.assertEqual(run(raw(rule, sample((0, 0, 0), 9, 2)))[0].status, "counterexample")

    def test_bounded_run_never_overcharges_or_promotes_partial_result(self):
        inputs = raw("idle", sample((0, 0, 9), 23, 1), sample((0, 0, 9), 30, 2))
        ck, d = run(inputs, 1)
        self.assertEqual((ck.status, ck.checked, ck.planned, ck.witness), ("inconclusive", 1, 2, None))
        self.assertEqual(d["stop_reason"], "max_cases")
        self.assertEqual(run(inputs, 2)[0].status, "counterexample")
        with self.assertRaises(ValueError):
            run(inputs, 0)
        for sequence, checked in (([2], 0), ([0, 2], 1), ([0, 0, 2], 2)):
            with patch.object(adapter, "monotonic", side_effect=sequence):
                ck, d = run(inputs, deadline=2)
            self.assertEqual((ck.status, ck.checked, ck.witness, d["stop_reason"]),
                             ("inconclusive", checked, None, "deadline"))
        for bad in (True, float("nan"), float("inf")):
            with self.assertRaises(ValueError):
                run(inputs, deadline=bad)
        for objects in ((inputs, Limits()), (adapter.parse_ternary_encounter(inputs), {})):
            with self.assertRaises(TypeError):
                adapter.evaluate_ternary_encounter(*objects)

    def test_complete_tag_readout_and_maximum_body_size(self):
        triples = ((0, 0, 9), (23, 30, 30), (3, 3, 10), (20, 29, 29))
        afters = (triples[1], triples[0], triples[3], triples[2])
        rows = [sample(p, v, q.count(v)) for p, q in zip(triples, afters) for v in RECORDS]
        spec = raw("relative", *rows)
        ck, d = run(spec)
        self.assertEqual((ck.status, ck.checked, ck.planned), (PASS, 64, 64))
        self.assertEqual(d["distinct_triggering_preparations"], 4)
        self.assertLess(len(json.dumps([spec, ck.specification(), d])), 32 * 1024)


if __name__ == "__main__":
    unittest.main()
