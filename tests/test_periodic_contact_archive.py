"""Published explicit local-observer devices must replay without promoting their source."""

import unittest

from scripts.compile_petal_clock_hypothesis import controls
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "c40bda27657a94ee82eec4b6550830d97865b46616dc61e1087c387524c19f2e"
BUDGET = Limits(max_cases=64)


class PeriodicContactArchiveTests(unittest.TestCase):
    def test_pinned_device_tables_and_first_observation_replay(self):
        specs = load_json(pipeline.ROOT / "data/periodic_contact_controls.json")
        self.assertEqual(specs,controls())
        request = {"schema":SCHEMA,"candidates":specs,"limits":BUDGET.specification()}
        self.assertEqual(pipeline.digest(request),PIN)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions",PIN),request)
        original = archive.baseline(PIN)["reports"]
        fresh = [r.report for r in pipeline.run_batch(specs,BUDGET,fresh=True)]
        self.assertEqual(list(map(semantic_report,original)),list(map(semantic_report,fresh)))
        self.assertEqual([r["status"] for r in fresh],
                         ["no_counterexample_within_bounds","counterexample","counterexample","unsupported"])
        self.assertEqual([r["scope"]["clock_period"] for r in fresh],[42,40,10,4])
        self.assertEqual(fresh[0]["scope"]["observed_phase_rail_counts"]["matching_rail_counts"],
                         [2,8,2,8])
        for i in (1,2):
            w = fresh[i]["checks"][0]["witness"]["inputs"]
            self.assertNotEqual(w["integer_residual"],0)
            self.assertEqual(w["relative_phase_offset"],0)
        for r in (*original,*fresh):
            self.assertEqual((r["empirical_status"],r["proof_status"]),("not_tested","not_attempted"))
            self.assertEqual(r["rejection_scope"],"only_submitted_periodic_devices_and_calibrated_reference")
