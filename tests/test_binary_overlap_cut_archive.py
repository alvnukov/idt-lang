"""Original noisy finite-cut controls, including a shared qubit on the boundary."""

import unittest
from fractions import Fraction as F

from scripts.probe_robust_shared_cut_overlap import box_around
from scripts.probe_streaming_observer_cut import response_matrix
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "da218c8145081504b9357a58f953ec17a3e25f13129c21a491ee9c565065185a"
BUDGET = Limits(max_cases=64)


class BinaryOverlapCutArchiveTests(unittest.TestCase):
    def test_input_boxes_preserve_their_experimental_meaning(self):
        rows = load_json(pipeline.ROOT / "data/binary_overlap_cut_controls.json")
        raw = response_matrix(5, 3)
        shared = [[F(1) if i == j else F(3, 8) for j in range(5)] for i in range(5)]
        flip = [[F(1, 25)+F(23, 25)*p for p in row] for row in shared]
        bits = [[F((i >> j) & 1) for j in range(3)] for i in range(5)]
        examples = [(raw, F(1, 200)), (raw, F(39, 4000)), (raw, 1), (shared, 0),
                    (flip, F(1, 100)), (bits, F(1, 100)), (bits, F(1, 100)),
                    (raw, F(1, 200))]
        for row, (table, radius) in zip(rows, examples, strict=True):
            self.assertEqual([[tuple(map(F, p)) for p in x] for x in row["intervals"]],
                             box_around(table, F(radius)))
        self.assertEqual(rows[-1]["event_basis"], "accepted_only")
        self.assertTrue(all(row["memory"]["shared_classical_seed"] for row in rows))

    def test_immutable_original_and_fresh_results(self):
        rows = load_json(pipeline.ROOT / "data/binary_overlap_cut_controls.json")
        req = {"schema": SCHEMA, "candidates": rows, "limits": BUDGET.specification()}
        self.assertEqual(pipeline.digest(req), PIN)
        history = History(DEFAULT_HISTORY)
        self.assertEqual(history.get("submissions", PIN), req)
        original = history.baseline(PIN)["reports"]
        fresh = [r.report for r in pipeline.run_batch(rows, BUDGET, fresh=True)]
        self.assertEqual(list(map(semantic_report, original)), list(map(semantic_report, fresh)))
        bad, open_ = "counterexample", "inconclusive"
        self.assertEqual([r["status"] for r in fresh],
                         [bad, bad, open_, open_, open_, bad, open_, "unsupported"])
        for r in (*original, *fresh):
            self.assertEqual((r["empirical_status"], r["proof_status"]),
                             ("not_tested", "not_attempted"))
            self.assertTrue(r["scope"]["necessary_conditions_only"])
