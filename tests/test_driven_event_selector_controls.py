"""Retain one table-only batch, not an assessment of historical source candidates."""

import unittest
from fractions import Fraction

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    SCHEMA,
    History,
    semantic_report,
)
from theory_experiments.primitive_screen import Limits, load_json

FIXTURE = pipeline.ROOT / "data/driven_event_selector_controls.json"
PIN = "122e526ad0c3782868808d92e0f14f39cd46894b7dc0cd0214f0ed7117d3becd"
LIMITS = Limits(max_cases=32)
PASS, FAIL = "no_counterexample_within_bounds", "counterexample"
SCOPE = "only_submitted_finite_transducer_and_calibrated_reference"
EXPECTED = (
    ("driven_separate_quarter_phases", PASS, 32, 32),
    ("driven_shared_quarter_phase", FAIL, 2, 8),
    ("driven_unreachable_defect", PASS, 2, 2),
    ("driven_reachable_nonbottom_defect", FAIL, 1, 3),
    ("driven_zero_current", "unsupported", 0, 0),
)


def play(spec, state, word):
    counts = [0]*len(spec["contexts"])
    minus = counts.copy()
    for c in word:
        state, bit = spec["transitions"][state][c]
        counts[c] += 1
        minus[c] += bit
    return state, counts, minus


def raw_rate(context):
    # Swapping the two unfixed coordinates gives the two *raw* branches;
    # compute from their squared norms independently of any machine outputs.
    v = context["current"]
    j, k = [i for i in range(3) if i != context["fixed"]]
    swapped = v.copy()
    swapped[j], swapped[k] = v[k], v[j]
    plus = sum((a+b)**2 for a, b in zip(v, swapped))
    minus = sum((a-b)**2 for a, b in zip(v, swapped))
    return str(Fraction(minus, minus+plus)) if minus+plus else None


class DrivenSelectorControlTests(unittest.TestCase):
    def check_reports(self, specs, reports):
        for spec, report, (name, verdict, done, planned) in zip(specs, reports, EXPECTED, strict=True):
            with self.subTest(candidate=name):
                self.assertEqual(report["request"]["candidate"], spec)
                self.assertEqual((spec["family"], spec["id"]), ("driven_event_selector", name))
                self.assertEqual((report["status"], report["proof_status"], report["empirical_status"]),
                                 (verdict, "not_attempted", "not_tested"))
                self.assertEqual(report["rejection_scope"], SCOPE)
                scope = report["scope"]
                self.assertEqual(scope["scientific_status"], "unassessed")
                self.assertEqual(scope["reference_minus_rates"], list(map(raw_rate, spec["contexts"])))
                self.assertEqual(scope["all_eventually_periodic_context_rates_certified"], verdict == PASS)
                check, = report["checks"]
                self.assertEqual((check["id"], check["checked"], check["planned"]),
                                 ("driven_event_selector_context_rates", done, planned))
                if verdict == FAIL:
                    w = check["witness"]["inputs"]
                    start = play(spec, spec["initial"], w["prefix"])[0]
                    end, counts, minus = play(spec, start, w["loop"])
                    self.assertTrue(w["loop"])
                    self.assertEqual((start, end), (w["loop_state"], w["loop_state"]))
                    self.assertEqual((counts, minus), (w["context_counts"], w["minus_counts"]))
                    c = w["context_index"]
                    rate = Fraction(raw_rate(spec["contexts"][c]))
                    residual = rate.denominator*minus[c] - rate.numerator*counts[c]
                    self.assertNotEqual(residual, 0)
                    self.assertEqual(check["witness"]["actual"], str(residual))
                else:
                    self.assertIsNone(check["witness"])

    def test_live_raw_controls_and_submission_id(self):
        specs = load_json(FIXTURE)
        self.assertEqual(len({s["id"] for s in specs}), len(EXPECTED))
        self.assertEqual(pipeline.digest({"schema": SCHEMA, "candidates": specs,
                                          "limits": LIMITS.specification()}), PIN)
        self.check_reports(specs, [r.report for r in pipeline.run_batch(specs, LIMITS)])

    def test_closed_visits_pooled_impostor_and_nonbottom_trap(self):
        separate, shared, unreachable, trap, zero = load_json(FIXTURE)
        # Same two references, related by relabelling rails. Both mechanisms
        # have one minus in four under either fixed setting. Only the separate
        # clocks deliver the reference within each setting under the mixed drive.
        knobs = separate["contexts"]
        self.assertEqual(knobs, shared["contexts"])
        self.assertEqual(list(map(raw_rate, knobs)), ["1/4", "1/4"])
        self.assertEqual(knobs, [{"current": [1, 0, -1], "fixed": 0},
                                 {"current": [0, 1, -1], "fixed": 1}])
        for c in range(2):
            for spec in (separate, shared):
                self.assertEqual(play(spec, spec["initial"], [c]*4)[2][c], 1)
        mixed = [0, 0, 0, 1]*4
        self.assertEqual(play(separate, 0, mixed), (0, [12, 4], [3, 1]))
        self.assertEqual(play(shared, 0, mixed), (0, [12, 4], [0, 4]))
        self.assertEqual(len(separate["transitions"]), 4*4)
        self.assertEqual(len(shared["transitions"]), 4)
        # Same table; only the prescribed initial state changes reachability.
        self.assertEqual(unreachable["transitions"], trap["transitions"])
        self.assertEqual(unreachable["contexts"], trap["contexts"])
        self.assertEqual(list(map(raw_rate, trap["contexts"])), ["1", "0"])
        self.assertEqual(play(unreachable, unreachable["initial"], [0, 1]*8), (2, [8, 8], [8, 0]))
        start = play(trap, trap["initial"], [0])[0]
        self.assertEqual(play(trap, start, [0]), (start, [1, 0], [0, 0]))
        self.assertNotEqual(play(trap, start, [1])[0], start)
        self.assertEqual(list(map(raw_rate, zero["contexts"])), [None])

    def test_pinned_reports_and_fresh_semantic_replay(self):
        # Missing baselines must fail. This read-only test does not pin today's
        # result automatically or join a submitted table to an old source theory.
        specs = load_json(FIXTURE)
        archive = History(DEFAULT_HISTORY)
        self.assertEqual(archive.get("submissions", PIN),
                         {"schema": SCHEMA, "candidates": specs, "limits": LIMITS.specification()})
        stored = archive.baseline(PIN)["reports"]
        fresh = [r.report for r in pipeline.run_batch(specs, LIMITS, fresh=True)]
        self.check_reports(specs, stored)
        self.assertEqual(list(map(semantic_report, stored)), list(map(semantic_report, fresh)))


if __name__ == "__main__":
    unittest.main()
