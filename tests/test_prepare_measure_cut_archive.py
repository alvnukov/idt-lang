"""Keep original finite-cut claims, including refusals and non-rejections."""

import unittest
from fractions import Fraction as F
from itertools import product

from scripts.probe_streaming_observer_cut import response_matrix
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "4be3ac74eec3452246c2e3f188fd47dfb776e48c1cfcd0cfe007085b5c648efc"
BUDGET = Limits(max_cases=2)
COUNTER, UNKNOWN, SKIP = "counterexample", "inconclusive", "unsupported"
EXPECTED = [
    (COUNTER, COUNTER), (UNKNOWN, UNKNOWN), (SKIP, SKIP), (UNKNOWN, UNKNOWN),
    (SKIP, COUNTER), (SKIP, UNKNOWN), (COUNTER, UNKNOWN), (COUNTER, UNKNOWN),
    (UNKNOWN, UNKNOWN),
]


def points(spec):
    out = []
    for row in spec["intervals"]:
        if any(lo != hi for lo, hi in row):
            raise ValueError("not a point table")
        out.append([F(lo) for lo, _ in row])
    return out


class PrepareMeasureCutArchiveTests(unittest.TestCase):
    def test_inputs_are_the_claimed_events_not_only_named_controls(self):
        specs = load_json(pipeline.ROOT / "data/prepare_measure_cut_controls.json")
        for i in (0, 1, 2):
            self.assertEqual(points(specs[i]), response_matrix(3, 1))
        self.assertEqual(points(specs[4]), response_matrix(5, 2))
        conditional, joint = points(specs[2]), points(specs[3])
        for i, j in product(range(3), repeat=2):
            other = F(4*(i-j)**2, 25*(1+4*i*i))
            self.assertEqual(joint[i][j], F(1, 25*(1+4*i*i)))
            self.assertLessEqual(joint[i][j]+other, 1)
            self.assertEqual(conditional[i][j], joint[i][j]/(joint[i][j]+other))
        # Sender transmits seed[i]; receiver compares to seed[j]. The seed
        # is input independent but is accessible on both sides of the cut.
        seeds = list(product((0, 1), repeat=5))
        equality = [[F(sum(z[i] == z[j] for z in seeds), len(seeds))
                     for j in range(5)] for i in range(5)]
        self.assertEqual(points(specs[5]), equality)
        self.assertEqual(points(specs[6]), equality)
        self.assertNotEqual(specs[5]["memory"], specs[6]["memory"])
        for row in specs[8]["intervals"]:
            for lo, hi in row:
                self.assertLessEqual(F(lo), F(1, 2))
                self.assertLessEqual(F(1, 2), F(hi))

    def test_same_history_never_turns_nonrejection_into_confirmation(self):
        specs = load_json(pipeline.ROOT / "data/prepare_measure_cut_controls.json")
        request = {"schema": SCHEMA, "candidates": specs, "limits": BUDGET.specification()}
        self.assertEqual(pipeline.digest(request), PIN)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions", PIN), request)
        original = archive.baseline(PIN)["reports"]
        fresh = [i.report for i in pipeline.run_batch(specs, BUDGET, fresh=True)]
        self.assertEqual(list(map(semantic_report, original)), list(map(semantic_report, fresh)))
        self.assertEqual([tuple(c["status"] for c in r["checks"]) for r in fresh], EXPECTED)
        for r in (*original, *fresh):
            self.assertIn(r["status"], (COUNTER, UNKNOWN, SKIP))
            self.assertEqual((r["empirical_status"], r["proof_status"]), ("not_tested", "not_attempted"))
            self.assertTrue(r["scope"]["necessary_conditions_only"])
            self.assertEqual(r["scope"]["cut_sufficiency_status"], "declared_model_premise_not_verified")
