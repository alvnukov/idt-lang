"""Historical raw relays survive independently of source-only candidate records."""

import unittest

from scripts.marked_relay_controls import control_specs
from theory_experiments.candidate_history import DEFAULT_HISTORY, History
from theory_experiments.primitive_screen import Limits, object_fields


class MarkedRelayBaselineTests(unittest.TestCase):
    def test_complete_and_resource_limited_observations_are_both_preserved(
        self,
    ) -> None:
        archive = History(DEFAULT_HISTORY)
        full = control_specs()
        limited = [
            spec
            for spec in full
            if object_fields(spec)["id"]
            in {"relay_64_through_six", "shuttle_105_all_origins"}
        ]
        for submission, budget, specs, status_counts in (
            (
                "ecd5b42bf5512ea30a0d8c722bbfe353d01dc2146dda6b534da9ae0649d7f2ad",
                5000,
                full,
                {"no_counterexample_within_bounds": 5, "counterexample": 4},
            ),
            (
                "66d2b893e882dab7fec387b055de84f231e770cbb3302a56f2a2e59d6065d69c",
                1455,
                limited,
                {"inconclusive": 2},
            ),
        ):
            with self.subTest(submission=submission):
                submitted = archive.get("submissions", submission)
                self.assertEqual(submitted["candidates"], specs)
                self.assertEqual(
                    submitted["limits"], Limits(max_cases=budget).specification()
                )
                reports = archive.baseline(submission)["reports"]
                if not isinstance(reports, list):
                    self.fail("baseline must contain a report per raw relay")
                self.assertEqual(len(reports), len(specs))
                counts: dict[str, int] = {}
                for row, spec in zip(reports, specs, strict=True):
                    report = object_fields(row)
                    status = report["status"]
                    if not isinstance(status, str):
                        self.fail("invalid status")
                    counts[status] = counts.get(status, 0) + 1
                    self.assertEqual(
                        object_fields(report["request"])["candidate"], spec
                    )
                    self.assertEqual(report["proof_status"], "not_attempted")
                    self.assertEqual(report["empirical_status"], "not_tested")
                self.assertEqual(counts, status_counts)
