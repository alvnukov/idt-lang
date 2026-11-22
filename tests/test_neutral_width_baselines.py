"""Historical controls are descriptions, including a four-unit conflicting value."""

import unittest

from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.candidate_pipeline import ROOT
from theory_experiments.primitive_screen import Limits, load_json, object_fields


class WidthBaselineTests(unittest.TestCase):
    def test_calibrations_degeneracies_and_missing_bridges_remain_in_history(
        self,
    ) -> None:
        history = History(DEFAULT_HISTORY)
        source = load_json(ROOT / "data/neutral_current_width_controls.json")
        for budget, key, values in (
            (
                16,
                "dc5be6b913d8f4454a14cd712e989aade542d7f808ba56602727dff6ec323bd7",
                ("3", "4", "3", "3", "1587/625", "3", None, None),
            ),
            (
                9,
                "aa99f198b5a631e1dca46373780a5acf6e370346a2e47df18e623e41172d0485",
                ("3", None, None, None, None, None, None, None),
            ),
        ):
            self.assertEqual(
                history.get("submissions", key),
                dict(
                    schema=SCHEMA,
                    candidates=source,
                    limits=Limits(max_cases=budget).specification(),
                ),
            )
            rows = history.baseline(key)["reports"]
            if not isinstance(rows, list):
                self.fail("missing original width reports")
            for i, (rr, v) in enumerate(zip(rows, values, strict=True)):
                r = object_fields(rr)
                self.assertEqual(r["evidence_kind"], "descriptive_completion_only")
                self.assertEqual(
                    (r["proof_status"], r["empirical_status"]),
                    ("not_attempted", "not_tested"),
                )
                status = (
                    "unsupported"
                    if i >= 6
                    else (
                        "inconclusive"
                        if v is None
                        else "no_counterexample_within_bounds"
                    )
                )
                self.assertEqual(r["status"], status)
                s = object_fields(r["scope"])
                self.assertEqual(s["candidate_verdict"], "not_assessed")
                self.assertEqual(
                    object_fields(s["prediction"]).get("effective_species"), v
                )
                self.assertEqual("comparison" in s, v is not None)
