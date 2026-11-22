"""Pins cover unsupported source proposals AND precise bounded adapter outcomes."""

from pathlib import Path
import unittest

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.candidate_pipeline import digest
from theory_experiments.primitive_screen import Limits, load_json, object_fields


class ContactsScreenBaselines(unittest.TestCase):
    def test_source_proposals_are_preserved(self) -> None:
        h = History(DEFAULT_HISTORY)
        specs = inventory_specifications(
            ROOT / "data/primitive_contacts_comparators_inventory.json"
        )
        self.assertEqual(len(specs), 6)
        for spec in specs:
            request = dict(
                schema=SCHEMA, limits=Limits().specification(), candidates=[spec]
            )
            key = digest(request)
            self.assertEqual(h.get("submissions", key), request)
            rows = h.baseline(key)["reports"]
            if not isinstance(rows, list) or len(rows) != 1:
                self.fail("missing retained source")
            r = object_fields(rows[0])
            self.assertEqual(
                (r["status"], r["proof_status"], r["empirical_status"]),
                ("unsupported", "not_attempted", "not_tested"),
            )

    def test_original_pencil_domain_and_late_failure_both_survive_replay(self) -> None:
        h = History(DEFAULT_HISTORY)
        specs = load_json(Path(ROOT / "data/chiral_pencil_controls.json"))
        passed = "no_counterexample_within_bounds"
        for n, key, expected, counts in (
            (
                19,
                "4bd55930498d11899814eac79b4f5cf0b2e9e9f0780d917387e70f36fbb2fb52",
                (
                    "inconclusive",
                    "inconclusive",
                    "counterexample",
                    "inconclusive",
                    "unsupported",
                ),
                (19, 19, 1, 19, 0),
            ),
            (
                20,
                "cfd4fd3bc1f4056ecaae451d055398420de91f1ac98999a62db8762dd1df14a4",
                (passed, passed, "counterexample", "counterexample", "unsupported"),
                (20, 20, 1, 20, 0),
            ),
        ):
            self.assertEqual(
                h.get("submissions", key),
                dict(
                    schema=SCHEMA,
                    limits=Limits(max_cases=n).specification(),
                    candidates=specs,
                ),
            )
            rows = h.baseline(key)["reports"]
            if not isinstance(rows, list):
                self.fail("missing original weighted controls")
            for rr, status, checked in zip(rows, expected, counts, strict=True):
                r = object_fields(rr)
                self.assertEqual(
                    (r["status"], r["proof_status"], r["empirical_status"]),
                    (status, "not_attempted", "not_tested"),
                )
                checks = r["checks"]
                if not isinstance(checks, list) or len(checks) != 1:
                    self.fail("not the original bounded screen")
                c = object_fields(checks[0])
                self.assertEqual(
                    (c["id"], c["status"], c["checked"]),
                    ("chiral_pencil_rank10_holdout", status, checked),
                )
