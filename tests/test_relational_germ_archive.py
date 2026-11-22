"""Freeze predictions, different failed contracts, and undefined apparatus separately."""

import unittest

from scripts.compile_relational_germ_hypothesis import controls
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "53f1986595707ca3f8e9fc9b5e84d34e0918a4b7a8f7d255cc3b8fc4059c1c91"
BUDGET = Limits(max_cases=2048)


class RelationalGermArchiveTests(unittest.TestCase):
    def test_compiled_control_bundle_and_immutable_observation(self):
        specs = load_json(pipeline.ROOT / "data/relational_germ_observer_controls.json")
        self.assertEqual(specs, controls())
        request = {"schema": SCHEMA, "limits": BUDGET.specification(), "candidates": specs}
        self.assertEqual(pipeline.digest(request), PIN)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions", PIN), request)
        old = archive.baseline(PIN)["reports"]
        now = [r.report for r in pipeline.run_batch(specs, BUDGET, fresh=True)]
        self.assertEqual(list(map(semantic_report, old)), list(map(semantic_report, now)))
        ok, bad, skip = "no_counterexample_within_bounds", "counterexample", "unsupported"
        self.assertEqual([r["status"] for r in now], [ok, bad, bad, ok, ok, skip, skip, ok])
        self.assertEqual([r["scope"]["product_states_fully_expanded"] for r in now],
                         [80, 80, 160, 80, 160, 0, 0, 192])
        self.assertEqual(now[1]["scope"]["stop_reason"], "submitted_tally_interval_mismatch")
        self.assertEqual(now[2]["scope"]["stop_reason"], "two_paths_to_different_endpoint_bits")
        self.assertEqual(now[7]["scope"]["multiple_germs_at_vertex_in_completed_closures"], 96)
        for r in (*old, *now):
            self.assertEqual((r["empirical_status"], r["proof_status"]), ("not_tested", "not_attempted"))
            self.assertTrue(r["scope"]["finite_submitted_contract_only"])

    def test_no_reference_comes_from_executing_the_candidate(self):
        # Compare against literal values per named vertex, rather than
        # regenerating expectations from the observer implementation.
        r = {x["vertex"]: x["lower"] for x in controls()[0]["references"]}
        self.assertEqual((r[0], r[1], r[2], r[3]), (0, -3, -3, 6))
        self.assertCountEqual(r.values(), [0, 6, -3, -3, 2, 2, 2, -4, -4, -4, 1, 1, 1, 1, 1, 1])
