"""Recompare actual canonical submissions, not just a saved pass/fail flag."""

import unittest

from scripts.compile_spectator_probability_ledgers import controls
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.operational_probability_ledger import (
    parse_operational_probability_ledger,
    verify_ledger_certificate,
)
from theory_experiments.primitive_screen import Limits, load_json

PIN = "306f3f33c0291838ecdba445a4f686b8906dc3f07cd6eded6f7fdf0cf47b8a88"
LIMITS = Limits(max_cases=256)


class OperationalProbabilityLedgerArchiveTests(unittest.TestCase):
    def test_original_contracts_primal_and_separating_certificates(self):
        rows = load_json(pipeline.ROOT / "data/operational_probability_ledger_controls.json")
        self.assertEqual(rows, controls())
        request = {"schema": SCHEMA, "limits": LIMITS.specification(), "candidates": rows}
        self.assertEqual(pipeline.digest(request), PIN)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions", PIN), request)
        old = archive.baseline(PIN)["reports"]
        new = [r.report for r in pipeline.run_batch(rows, LIMITS, fresh=True)]
        self.assertEqual(list(map(semantic_report, old)), list(map(semantic_report, new)))
        ok, bad, skip = "no_counterexample_within_bounds", "counterexample", "unsupported"
        self.assertEqual([r["status"] for r in new], [bad, ok, skip, ok, ok, bad, ok, bad, ok, ok])
        for raw,r in zip(rows,new,strict=True):
            cert = r["scope"]["checked_certificate"]
            self.assertEqual((r["proof_status"], r["empirical_status"]), ("not_attempted", "not_tested"))
            if r["status"] == skip:
                self.assertIsNone(cert)
            else:
                self.assertTrue(verify_ledger_certificate(parse_operational_probability_ledger(raw),cert))
                self.assertEqual(cert["kind"], "farkas" if r["status"]==bad else "primal")

    def test_five_mode_controls_share_every_circuit_link(self):
        *_, residue, born, relaxed = controls()
        self.assertEqual(residue["settings"], born["settings"])
        self.assertEqual(residue["links"], born["links"])
        self.assertNotEqual(residue["bounds"], born["bounds"])
        self.assertEqual(residue["bounds"], relaxed["bounds"])
        self.assertEqual(len(residue["links"])-len(relaxed["links"]),3)
