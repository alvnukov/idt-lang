"""Local physical traversal controls and export to the finite observer schema."""

from __future__ import annotations

import io
import json
import unittest
from collections import Counter
from contextlib import redirect_stderr, redirect_stdout
from math import lcm
from unittest.mock import patch

from scripts import compile_petal_clock_hypothesis as exporter
from scripts.probe_internal_detector_clocks import active_trace, sample
from scripts.probe_matched_vernier_petals import extend_one_wire, local_joint
from scripts.probe_reversible_excitation_detector import Apparatus
from theory_experiments.periodic_contact_observer import (
    SCOPE,
    evaluate_periodic_contact_observer,
    parse_periodic_contact_observer,
)
from theory_experiments.primitive_screen import Limits, canonical_json

PACKET = (1, 2, -1, -2)
PASS = "no_counterexample_within_bounds"


def evaluate(spec, budget=64):
    (check,), scope = evaluate_periodic_contact_observer(
        parse_periodic_contact_observer(spec), Limits(max_cases=budget))
    return check, scope


def cli(*args):
    output, errors = io.StringIO(), io.StringIO()
    with redirect_stdout(output), redirect_stderr(errors):
        status = exporter.main(list(args))
    return status, output.getvalue(), errors.getvalue()


class PetalClockCompilerTests(unittest.TestCase):
    def test_controls_are_compact_explicit_and_differentiating(self):
        controls = exporter.controls()
        self.assertEqual(controls, exporter.controls())
        self.assertLess(len(canonical_json(controls).encode()), 128 * 1024)
        self.assertEqual([row["id"] for row in controls],
                         ["petal_clock_matched", "petal_clock_identical",
                          "petal_clock_ring_10", "petal_clock_trapped"])
        self.assertTrue(all(row["signal"] == controls[0]["signal"] for row in controls))
        expected = [
            (PASS, 42, 20, [2, 8, 2, 8]),
            ("counterexample", 40, 1, [1, 0, 0, 0]),
            ("counterexample", 10, 4, [1, 1, 1, 1]),
            ("unsupported", 4, 0, None),
        ]
        for row, (status, clock_period, triggers, counts) in zip(controls, expected, strict=True):
            with self.subTest(row_id=row["id"]):
                check, scope = evaluate(row)
                self.assertEqual(check.status, status)
                self.assertEqual(scope["signal_period"], 40)
                self.assertEqual(scope["clock_period"], clock_period)
                self.assertEqual(scope["trigger_count_per_joint_period"], triggers)
                self.assertEqual(scope["rejection_scope"], SCOPE)
                self.assertEqual(scope["proof_status"], "not_attempted")
                observation = scope["observed_phase_rail_counts"]
                if status == "counterexample":
                    self.assertEqual(observation["first_mismatch"]["rail_counts"], counts)
                else:
                    self.assertEqual(observation["matching_rail_counts"], counts)
        partial, scope = evaluate(controls[0], budget=1)
        self.assertEqual((partial.status, partial.checked, partial.planned), ("inconclusive", 1, 2))
        self.assertIsNone(partial.witness)
        self.assertFalse(scope["all_recurrent_phase_rail_rates_certified"])

    def test_two_directions_and_preparations_replay_local_hops(self):
        sizes = tuple(map(abs, PACKET))
        for home in (0, 1, 3):
            for direction in (-1, 1):
                with self.subTest(home=home, direction=direction):
                    with (patch.object(exporter, "advance", wraps=exporter.advance) as advance,
                          patch.object(exporter, "retreat", wraps=exporter.retreat) as retreat):
                        spec = exporter.compile_hypothesis(PACKET, first_rail=home, direction=direction)
                    signal_rows = spec["signal"]["transitions"]
                    self.assertEqual(advance.call_count, len(signal_rows))
                    self.assertEqual(retreat.call_count, len(signal_rows))
                    signal, reference = Apparatus(sizes), Apparatus(sizes)
                    extend_one_wire(reference, home)
                    held, _, _ = active_trace(signal, home, direction)
                    self.assertEqual(tuple(rail for _, rail in signal_rows), held)
                    marked = {reference.starts[home, d, 1] for d in (-1, 1)}
                    state = start = reference.launch(home, -direction, 0)
                    for successor, trigger in spec["clock"]["transitions"]:
                        self.assertIs(trigger, state[0] == 0 and state[1] in marked)
                        state = reference.step(state)
                        self.assertEqual(state == start, successor == 0)
                    self.assertEqual(state, start)
                    m, n = len(signal_rows), len(spec["clock"]["transitions"])
                    for phase in range(n):
                        found = local_joint(signal, reference, home, direction, -direction,
                                            home, phase, lcm(m, n))
                        self.assertEqual(found, Counter({0: 2, 1: 8, 2: 2, 3: 8}))

    def test_ring_alias_against_independent_step_by_step_reference(self):
        spec = exporter.compile_hypothesis(PACKET, clock="ring", period=10)
        trace, _, _ = active_trace(Apparatus((1, 2, 1, 2)), 0, 1)
        all_counts = set()
        for phase in range(10):
            got = sample(trace, 10, phase, direction=-1)
            all_counts.add(tuple(got[rail] for rail in range(4)))
        self.assertEqual(len(all_counts), 2)
        self.assertTrue(all(sum(vector) == 4 for vector in all_counts))
        self.assertEqual(spec["clock"]["transitions"],
                         [[(i+1) % 10, i == 0] for i in range(10)])
        check, scope = evaluate(spec)
        witness = check.witness["inputs"]
        self.assertIn(tuple(witness["observed_rail_counts"]), all_counts)
        self.assertEqual(scope["expected_rail_counts_per_joint_period"], ["2/5", "8/5", "2/5", "8/5"])

    def test_trapped_reference_is_an_actual_prepared_orbit_and_keeps_all_clock_bits(self):
        spec = exporter.compile_hypothesis(PACKET, clock="trapped")
        apparatus = Apparatus((1, 2, 1, 2))
        extend_one_wire(apparatus, 0)
        state = start = (0, apparatus.starts[0, -1, 0], apparatus.cellmask[1])
        for successor, trigger in spec["clock"]["transitions"]:
            self.assertIs(trigger, False)
            self.assertEqual(state[2], apparatus.cellmask[1])
            self.assertEqual(apparatus.arc[state[:2]], (0, 0))
            state = apparatus.step(state)
            self.assertEqual(state == start, successor == 0)
        self.assertEqual(state, start)
        check, scope = evaluate(spec)
        self.assertEqual((check.status, scope["stop_reason"]),
                         ("unsupported", "unsupported_silent_recurrent_clock"))
        self.assertIsNone(check.witness)

    def test_sign_reversal_and_shifted_rail_labels_preserve_scope_and_not_a_sign_law(self):
        base = exporter.compile_hypothesis(PACKET + (0,))
        flipped = exporter.compile_hypothesis(tuple(-x for x in PACKET) + (0,))
        shifted = exporter.compile_hypothesis((0,) + PACKET)
        self.assertEqual(base["clock"], flipped["clock"])
        self.assertEqual(base["signal"], flipped["signal"])
        self.assertEqual(base["clock"], shifted["clock"])
        self.assertEqual(shifted["signal"]["transitions"],
                         [[target, rail+1] for target, rail in base["signal"]["transitions"]])
        for spec, expected in ((base, [2, 8, 2, 8, 0]), (flipped, [2, 8, 2, 8, 0]),
                               (shifted, [0, 2, 8, 2, 8])):
            check, scope = evaluate(spec)
            self.assertEqual(check.status, PASS)
            self.assertEqual(scope["observed_phase_rail_counts"]["matching_rail_counts"], expected)

    def test_validation_happens_before_geometry_allocation(self):
        cases = [
            ((), {}), ((0, 0), {}), ((True, -1), {}), ((1, -2), {}), (("1", -1), {}),
            ((1000000, -1000000), {}), ((1, -1), {"clock": "other"}), (PACKET, {"direction": False}),
            (PACKET, {"max_device_states": True}), (PACKET, {"first_rail": 4}),
            ((1, -1, 0), {"first_rail": 2}), (PACKET, {"clock": "ring", "period": 9}),
            (PACKET, {"clock": "ring", "period": exporter.MAX_STATES + 1}),
            (PACKET, {"clock": "ring"}), (PACKET, {"period": 10}),
            ((1, -1), {"clock": "trapped"}), (PACKET, {"identifier": "unsafe label"}),
        ]
        with patch.object(exporter, "Apparatus", side_effect=AssertionError("premature allocation")):
            for current, kwargs in cases:
                with self.subTest(current=current, kwargs=kwargs), self.assertRaises(ValueError):
                    exporter.compile_hypothesis(current, **kwargs)

    def test_censored_or_nonreversible_traversal_is_not_an_emitted_candidate(self):
        for budget, device in ((39, "signal"), (40, "reference"), (41, "reference")):
            with self.assertRaisesRegex(exporter.OrbitBudgetExceeded, device):
                exporter.compile_hypothesis(PACKET, max_device_states=budget)
        full = exporter.compile_hypothesis(PACKET, max_device_states=42)
        self.assertEqual(evaluate(full)[0].status, PASS)
        with (patch.object(exporter, "retreat", return_value=((0, 999, 0), 0)),
              self.assertRaisesRegex(ValueError, "did not reverse")):
            exporter.compile_hypothesis(PACKET)
        with self.assertRaisesRegex(ValueError, "transient"):
            exporter._trace_device(0, lambda _: 1, lambda _: False, max_states=2, name="invalid test source")

    def test_cli_emission_summary_and_bounds_have_distinct_outcomes(self):
        args = ("--current", "1", "2", "-1", "-2")
        result, output, errors = cli(*args, "--emit")
        data = json.loads(output)
        self.assertEqual((result, errors, data), (0, "", exporter.controls()[:1]))
        self.assertEqual(output, canonical_json(data) + "\n")
        for extras, expected, status in (
            ((), 0, PASS), (("--clock", "identical"), 1, "counterexample"),
            (("--clock", "ring", "--period", "10"), 1, "counterexample"),
            (("--clock", "trapped"), 3, "unsupported"),
            (("--max-cases", "1"), 3, "inconclusive"),
        ):
            result, output, errors = cli(*args, *extras)
            self.assertEqual((result, errors), (expected, ""))
            self.assertEqual(json.loads(output)["check"]["status"], status)
        for params, message in (
            ((*args, "--max-device-states", "40", "--emit"), "did not close"),
            ((*args, "--max-cases", "1", "--emit"), "set it on the screen CLI"),
            (("--current", "40", "-40", "--emit"), "128 KiB"),
        ):
            result, output, errors = cli(*params)
            self.assertEqual((result, output), (2, ""))
            self.assertIn(message, errors)


if __name__ == "__main__":
    unittest.main()
