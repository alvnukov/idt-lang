"""Competing output predictions stay separate from a real observational record."""

import unittest

from scripts.compile_ternary_encounter_hypotheses import controls
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "b6d87a49bbf68ee0a48cff1955c92fb11f33c58371e05522f978932be89b5293"
LIMITS = Limits(max_cases=12)


class TernaryEncounterArchiveTests(unittest.TestCase):
    def test_compiled_inputs_and_immutable_competing_predictions(self):
        specs = load_json(pipeline.ROOT / "data/ternary_encounter_controls.json")
        self.assertEqual(specs, controls())
        request = {"schema": SCHEMA, "limits": LIMITS.specification(), "candidates": specs}
        self.assertEqual(pipeline.digest(request), PIN)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions", PIN), request)
        old = archive.baseline(PIN)["reports"]
        now = [r.report for r in pipeline.run_batch(specs, LIMITS, fresh=True)]
        self.assertEqual(list(map(semantic_report, old)), list(map(semantic_report, now)))
        ok, bad = "no_counterexample_within_bounds", "counterexample"
        self.assertEqual([r["status"] for r in now], [ok, ok, bad, ok, bad, bad, ok, ok, ok, bad])
        self.assertEqual([r["scope"]["distinct_triggering_preparations"] for r in now],
                         [2, 2, 0, 2, 3, 2, 3, 0, 3, 0])
        for r in [*old, *now]:
            self.assertEqual((r["empirical_status"], r["proof_status"]), ("not_tested", "not_attempted"))

    def test_same_questions_not_rule_shaped_targets(self):
        q = controls()
        for a, b in ((0, 1), (0, 2), (3, 4), (5, 6)):
            self.assertEqual(q[a]["observations"], q[b]["observations"])
            self.assertNotEqual(q[a]["rule"], q[b]["rule"])
        self.assertIn({"packets": [17, 24, 24], "vertex": 24, "count": 2}, q[3]["observations"])
        self.assertIn({"packets": [17, 24, 24], "vertex": 6, "count": 2}, q[5]["observations"])
