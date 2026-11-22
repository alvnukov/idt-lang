"""Pin original unsigned source proposals and model-scoped stock outcomes."""

import unittest

from scripts.archive_existing_primitives import inventory_specifications
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.candidate_pipeline import ROOT, digest
from theory_experiments.primitive_screen import Limits, load_json, object_fields


class TransferStockBaselines(unittest.TestCase):
    def test_original_source_proposals_are_unassessed(self):
        h = History(DEFAULT_HISTORY)
        for spec in inventory_specifications(
            ROOT / "data/primitive_transfer_stock_inventory.json"
        ):
            key = digest(
                dict(schema=SCHEMA, candidates=[spec], limits=Limits().specification())
            )
            rows = h.baseline(key)["reports"]
            self.assertIsInstance(rows, list)
            self.assertEqual(len(rows), 1)
            r = object_fields(rows[0])
            self.assertEqual(
                (r["status"], r["proof_status"], r["empirical_status"]),
                ("unsupported", "not_attempted", "not_tested"),
            )

    def test_dark_and_hidden_stock_controls(self):
        h = History(DEFAULT_HISTORY)
        specs = load_json(ROOT / "data/triangle_stock_controls.json")
        p = "no_counterexample_within_bounds"
        inc = "inconclusive"
        c = "counterexample"
        u = "unsupported"
        for n, key, sts, counts in (
            (
                18,
                "4d6e33ee3fb0b1b3263300daef06676a0fb28e07ff014384dd6e1c008bab52c1",
                (p, inc, c, inc, c, c, u, u),
                (18, 18, 2, 18, 14, 9, 0, 0),
            ),
            (
                882,
                "517938170c760bf10018ddaa6af01a2941fcf76de55c506a5f2749d965fea83a",
                (p, p, c, c, c, c, u, u),
                (18, 162, 2, 20, 14, 9, 0, 0),
            ),
        ):
            self.assertEqual(
                h.get("submissions", key),
                dict(
                    schema=SCHEMA,
                    candidates=specs,
                    limits=Limits(max_cases=n).specification(),
                ),
            )
            rows = h.baseline(key)["reports"]
            self.assertIsInstance(rows, list)
            for rr, st, checked in zip(rows, sts, counts, strict=True):
                r = object_fields(rr)
                self.assertEqual(
                    (r["status"], r["proof_status"], r["empirical_status"]),
                    (st, "not_attempted", "not_tested"),
                )
                self.assertEqual(r["checks"][0]["checked"], checked)
                self.assertEqual(
                    r["scope"]["identity_certified_on_submitted_integer_domain"],
                    st == p,
                )
