"""Archive both signed-null alternatives, including surviving untrained primes."""

import unittest

from scripts.compile_ternary_network_nulls import PANEL, SMALL_PRIMES, controls
from scripts.probe_modular_contact_nulls import probe
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "dadf855c02ad189cbe556a6f04b5b56d5b013a7b775d647806a6a9ac12cd51cf"
LIMITS = Limits(max_cases=96)


class TernaryNetworkNullArchiveTests(unittest.TestCase):
    def test_unchanged_design_and_all_alternatives(self):
        rows = load_json(pipeline.ROOT / "data/ternary_network_null_controls.json")
        self.assertEqual(rows, controls())
        request = {"schema": SCHEMA, "limits": LIMITS.specification(), "candidates": rows}
        self.assertEqual(pipeline.digest(request), PIN)
        history = History(DEFAULT_HISTORY)
        self.assertEqual(history.get("submissions", PIN), request)
        old = history.baseline(PIN)["reports"]
        new = [r.report for r in pipeline.run_batch(rows, LIMITS, fresh=True)]
        self.assertEqual(list(map(semantic_report, old)), list(map(semantic_report, new)))
        ok, bad = "no_counterexample_within_bounds", "counterexample"
        self.assertEqual([r["status"] for r in new], [ok,bad,bad,ok,ok,bad,ok,bad,ok,ok,ok,ok,ok] +
                         [bad]*len(SMALL_PRIMES) + [ok,ok])
        direct = probe()
        self.assertEqual(direct["chosen_blocks"], PANEL)
        for row,report in zip(rows,new,strict=True):
            self.assertEqual((report["proof_status"],report["empirical_status"]),("not_attempted","not_tested"))
            self.assertEqual(report["scope"]["contacts_consumed"],len(row["contacts"]))
            self.assertEqual(report["scope"]["readouts_compared"],len(row["readouts"]))
            if row["id"].startswith("nine_reads_"):
                wanted = [p for k,p in direct["coverage_by_chosen_block"].items() if k in PANEL]
                dark = [row["modulus"] in primes for primes in wanted]
                self.assertEqual([r["predicted_dark"] for r in report["scope"]["comparisons"]],dark)
