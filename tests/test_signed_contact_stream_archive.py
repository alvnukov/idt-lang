"""Replay both sides of the local signed-counter discriminator and its nulls."""

import unittest

from scripts.compile_signed_contact_streams import controls
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "8ae844254577b44c6a783df14af2379482930f018ac5b1d219ad16bc8b640777"
LIMITS = Limits(max_cases=32)


class SignedContactStreamArchiveTests(unittest.TestCase):
    def test_preserved_equal_cycle_and_both_resolved_alternatives(self):
        rows = load_json(pipeline.ROOT / "data/signed_contact_stream_controls.json")
        self.assertEqual(rows, controls())
        request = {"schema": SCHEMA, "limits": LIMITS.specification(), "candidates": rows}
        self.assertEqual(pipeline.digest(request), PIN)
        history = History(DEFAULT_HISTORY)
        self.assertEqual(history.get("submissions", PIN), request)
        old = history.baseline(PIN)["reports"]
        new = [r.report for r in pipeline.run_batch(rows, LIMITS, fresh=True)]
        self.assertEqual(list(map(semantic_report, old)), list(map(semantic_report, new)))
        ok, bad = "no_counterexample_within_bounds", "counterexample"
        self.assertEqual([r["status"] for r in new],
                         [ok, ok, bad, ok, bad, bad, ok, ok, ok, bad, ok, ok, ok, bad])
        for record, report in zip(rows, new, strict=True):
            self.assertEqual((report["proof_status"], report["empirical_status"]), ("not_attempted", "not_tested"))
            self.assertEqual(report["scope"]["inputs_consumed"], len(record["inputs"]))
            self.assertEqual(report["scope"]["readouts_compared"], len(record["readouts"]))
        for i, j in ((0, 1), (3, 4), (5, 6), (8, 9), (11, 12)):
            for key in ("ports", "initial_phase", "inputs", "readouts"):
                self.assertEqual(rows[i][key], rows[j][key])
