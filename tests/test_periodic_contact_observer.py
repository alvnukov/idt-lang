"""Independent finite-orbit oracle and exact arithmetic/resource controls."""

import copy
import hashlib
import json
import unittest
from dataclasses import replace
from fractions import Fraction
from itertools import product
from math import gcd, lcm
from pathlib import Path
from unittest.mock import patch

from theory_experiments import periodic_contact_observer as adapter
from theory_experiments.primitive_screen import Limits


def ring(outputs):
    return [[(i+1) % len(outputs), out] for i, out in enumerate(outputs)]


def spec(signal, clock, current=(1, 0, -1), *, s0=0, c0=0):
    return {
        "id": "contact", "family": "periodic_contact_observer", "current": list(current),
        "signal": {"initial": s0, "transitions": signal},
        "clock": {"initial": c0, "transitions": clock},
    }


def evaluate(raw, budget=5000, **kwargs):
    (check,), details = adapter.evaluate_periodic_contact_observer(
        adapter.parse_periodic_contact_observer(raw), Limits(max_cases=budget), **kwargs)
    return check, details


def oracle_cycle(device):
    # Deliberately simple small-device traversal, preserving the phase ordering.
    states, state = [], device["initial"]
    while state not in states:
        states.append(state)
        state = device["transitions"][state][0]
    i = states.index(state)
    return i, states[i:]


def oracle_replay(raw, s, c, steps):
    start = s, c
    counts = [0] * len(raw["current"])
    for _ in range(steps):
        s, out = raw["signal"]["transitions"][s]
        c, trigger = raw["clock"]["transitions"][c]
        if trigger:
            counts[out] += 1
    if (s, c) != start:
        raise ValueError("oracle replay was not a whole joint period")
    return counts


def oracle(raw):
    s_prefix, signal = oracle_cycle(raw["signal"])
    c_prefix, clock = oracle_cycle(raw["clock"])
    joint = lcm(len(signal), len(clock))
    counts = {(i, j): oracle_replay(raw, s, c, joint)
              for i, s in enumerate(signal) for j, c in enumerate(clock)}
    return (s_prefix, c_prefix), (signal, clock), joint, counts


class PeriodicContactObserverTests(unittest.TestCase):
    def recorded_rows(self, info):
        summary = info["observed_phase_rail_counts"]
        n, common = summary["matching_prefix_length"], summary["matching_rail_counts"]
        self.assertEqual(common is None, n == 0)
        rows = [common] * n
        mismatch = summary["first_mismatch"]
        if mismatch is not None:
            self.assertEqual(mismatch["relative_phase_offset"], n)
            rows.append(mismatch["rail_counts"])
        return rows

    def verify_against_oracle(self, raw, *, force_packed=False):
        prefixes, (signal, clock), joint, counts = oracle(raw)
        g = gcd(len(signal), len(clock))
        norm = sum(x**2 for x in raw["current"])
        triggers = sum(counts[0, 0])
        expected = [Fraction(triggers * a**2, norm) for a in raw["current"]] if norm else None
        with patch.object(adapter, "_PACKED_WORK_THRESHOLD",
                          0 if force_packed else adapter._PACKED_WORK_THRESHOLD):
            check, info = evaluate(raw)
        self.assertEqual(
            (info["signal_transient_length"], info["clock_transient_length"]), prefixes)
        self.assertEqual(
            (info["signal_period"], info["clock_period"]), (len(signal), len(clock)))
        self.assertEqual(info["joint_period_steps"], joint)
        self.assertEqual(info["relative_phase_classes"], g)
        self.assertEqual(info["trigger_count_per_joint_period"], triggers)
        self.assertEqual(info["trigger_count_per_clock_cycle"], triggers * len(clock) // joint)
        self.assertEqual(
            (info["signal_recurrent_entry_state"], info["clock_recurrent_entry_state"]),
            (signal[0], clock[0]))
        self.assertTrue(info["planned_is_exact"])
        if norm == 0 or triggers == 0:
            self.assertEqual((check.status, check.checked, check.planned), ("unsupported", 0, 0))
            self.assertEqual(info["stop_reason"],
                             "unsupported_zero_current" if not norm else
                             "unsupported_silent_recurrent_clock")
            self.assertFalse(info["all_recurrent_phase_rail_rates_certified"])
            self.assertIsNone(check.witness)
            self.assertIsNone(info["expected_rail_counts_per_joint_period"])
            self.assertEqual(self.recorded_rows(info), [])
            return

        self.assertEqual(check.planned, g)
        self.assertEqual(info["expected_rail_counts_per_joint_period"], list(map(str, expected)))
        # Enumerate ALL phase pairs independently rather than assuming they
        # are equivalent under a shift or are adequately represented by (0,d).
        oracle_pass = all(row == expected for row in counts.values())
        self.assertEqual(info["all_recurrent_phase_rail_rates_certified"], oracle_pass)
        self.assertEqual(self.recorded_rows(info), [counts[0, d] for d in range(check.checked)])
        if oracle_pass:
            self.assertEqual((check.status, check.checked), ("no_counterexample_within_bounds", g))
            self.assertIsNone(check.witness)
            return

        self.assertEqual(check.status, "counterexample")
        witness = check.witness["inputs"]
        d = witness["relative_phase_offset"]
        self.assertEqual(check.checked, d+1)
        self.assertEqual((witness["signal_phase"], witness["clock_phase"]), (0, d))
        self.assertEqual((witness["signal_state"], witness["clock_state"]), (signal[0], clock[d]))
        row = counts[0, d]
        self.assertEqual(witness["observed_rail_counts"], row)
        self.assertEqual(witness["expected_rail_counts"], list(map(str, expected)))
        self.assertEqual(witness["trigger_count"], sum(row))
        rail = witness["mismatched_rail"]
        residual = norm * (row[rail] - expected[rail])
        self.assertNotEqual(residual, 0)
        self.assertEqual(witness["integer_residual"], residual)
        self.assertEqual(check.witness["actual"], str(residual))

    def test_exhaustive_small_independent_devices_against_full_lcm_oracle(self):
        signal_tables, clock_tables = [], []
        for n in (1, 2):
            signal_tables.extend((start, [list(row) for row in rows])
                                 for rows in product(product(range(n), range(3)), repeat=n)
                                 for start in range(n))
            clock_tables.extend((start, [list(row) for row in rows])
                                for rows in product(product(range(n), (False, True)), repeat=n)
                                for start in range(n))
        for (s0, signal), (c0, clock) in product(signal_tables, clock_tables):
            self.verify_against_oracle(spec(signal, clock, s0=s0, c0=c0))

    def test_noncontiguous_equal_totals_can_alias(self):
        alternating = ring([0, 2] * 4)
        mixed_clock = ring([i in (0, 1, 4, 5) for i in range(8)])
        aliased_clock = ring([i in (0, 2, 4, 6) for i in range(8)])
        mixed, alias = spec(alternating, mixed_clock), spec(alternating, aliased_clock)
        for raw in (mixed, alias):
            self.verify_against_oracle(raw)
            self.verify_against_oracle(raw, force_packed=True)
        check_good, good = evaluate(mixed)
        check_bad, bad = evaluate(alias)
        self.assertEqual((check_good.status, check_bad.status),
                         ("no_counterexample_within_bounds", "counterexample"))
        self.assertEqual([good["trigger_count_per_clock_cycle"], bad["trigger_count_per_clock_cycle"]],
                         [4, 4])
        self.assertEqual(self.recorded_rows(good), [[2, 0, 2]] * 8)
        self.assertEqual(self.recorded_rows(bad), [[4, 0, 0]])
        # If independently chosen phases were averaged, this alias would disappear.
        _, _, _, counts = oracle(alias)
        self.assertEqual([sum(counts[0, d][r] for d in range(8)) for r in range(3)], [16, 0, 16])

    def test_first_offset_pass_does_not_mask_later_failure_or_budget(self):
        raw = spec(ring([0, 0, 2, 2]), ring([True, False, False, True]))
        self.verify_against_oracle(raw)
        check, partial = evaluate(raw, 1)
        self.assertEqual((check.status, check.checked, check.planned, partial["stop_reason"]),
                         ("inconclusive", 1, 4, "max_cases"))
        self.assertFalse(partial["all_recurrent_phase_rail_rates_certified"])
        self.assertEqual(self.recorded_rows(partial), [[1, 0, 1]])
        check, result = evaluate(raw, 2)
        self.assertEqual((check.status, check.checked), ("counterexample", 2))
        self.assertEqual(check.witness["inputs"]["relative_phase_offset"], 1)
        self.assertEqual(self.recorded_rows(result), [[1, 0, 1], [0, 0, 2]])

    def test_transients_and_unreachable_defects_are_not_recurrent_contacts(self):
        signal = [[3, 0], [0, 1], [2, 1], [0, 2]]
        clock = [[2, True], [0, False], [0, True], [3, False], [2, True]]
        raw = spec(signal, clock, s0=1, c0=4)
        self.verify_against_oracle(raw)
        check, result = evaluate(raw)
        self.assertEqual(check.status, "no_counterexample_within_bounds")
        self.assertEqual([result["signal_recurrent_entry_state"], result["clock_recurrent_entry_state"]],
                         [0, 2])
        self.assertEqual(self.recorded_rows(result), [[1, 0, 1]] * 2)
        raw["signal"]["initial"] = 2  # change only the declared start
        self.verify_against_oracle(raw)
        self.assertEqual(evaluate(raw)[0].status, "counterexample")

    def test_recurrently_silent_and_zero_current_are_undefined(self):
        silent = spec([[0, 0]], [[1, True], [1, False]])
        dark_current = spec([[0, 0]], [[0, True]], (0, 0, 0))
        for raw in (silent, dark_current):
            self.verify_against_oracle(raw)
        self.assertEqual(evaluate(silent)[1]["clock_transient_length"], 1)
        self.assertIsNone(evaluate(dark_current)[1]["reference_rail_shares"])

    def test_reference_exact_large_integer_currents_and_rails_are_labelled(self):
        # Squared shares are 1/14, 4/14, 9/14, not the raw signed currents.
        for current in ((1, 2, -3), (-300000, -600000, 900000)):
            good = spec(ring([0] + [1]*4 + [2]*9), [[0, True]], current)
            self.verify_against_oracle(good)
            check, info = evaluate(good)
            self.assertEqual(check.status, "no_counterexample_within_bounds")
            self.assertEqual(info["reference_rail_shares"], ["1/14", "2/7", "9/14"])
            self.assertEqual(info["rejection_scope"], adapter.SCOPE)
            self.assertEqual((info["empirical_status"], info["proof_status"]),
                             ("not_tested", "not_attempted"))
            bad = spec(ring([0]*4 + [1] + [2]*9), [[0, True]], current)
            self.verify_against_oracle(bad)
            self.assertEqual(evaluate(bad)[0].status, "counterexample")

    def test_coprime_large_joint_orbit_needs_no_lcm_trace(self):
        raw = spec(ring([0, 1] * 8000), ring([True]*8192 + [False]*8191), (1, -1))
        check, info = evaluate(raw, 1)
        self.assertEqual((check.status, check.checked, check.planned),
                         ("no_counterexample_within_bounds", 1, 1))
        self.assertEqual(info["joint_period_steps"], 16000 * 16383)
        self.assertEqual(info["trigger_count_per_joint_period"], 16000 * 8192)
        self.assertEqual(self.recorded_rows(info), [[8000 * 8192] * 2])
        self.assertEqual(info["count_method"], "sparse_exact_circular")

    def test_large_gcd_packed_correlation_respects_max_cases(self):
        raw = spec(ring([0, 2] * 2048), ring([True, True, False, False] * 2048))
        check, info = evaluate(raw, 4096)
        self.assertEqual((check.status, check.checked, check.planned),
                         ("no_counterexample_within_bounds", 4096, 4096))
        self.assertEqual(info["count_method"], "packed_exact_circular")
        self.assertEqual(info["trigger_count_per_joint_period"], 4096)
        self.assertEqual(self.recorded_rows(info), [[2048, 0, 2048]] * 4096)
        check, info = evaluate(raw, 4095)
        self.assertEqual((check.status, check.checked, check.planned), ("inconclusive", 4095, 4096))
        self.assertFalse(info["all_recurrent_phase_rail_rates_certified"])
        self.assertEqual(self.recorded_rows(info), [[2048, 0, 2048]] * 4095)
        self.assertEqual(info["count_method"], "packed_exact_circular")

    def test_maximum_device_and_rail_sizes_have_constant_size_observation_summary(self):
        n = adapter.MAX_STATES
        raw = spec(ring(list(range(8)) * (n//8)), ring([True]*(n//2) + [False]*(n//2)),
                   (1, -1)*4)
        check, info = evaluate(raw, 5000)
        self.assertEqual((check.status, check.checked, check.planned), ("inconclusive", 5000, n))
        self.assertEqual(info["count_method"], "packed_exact_circular")
        self.assertFalse(info["all_recurrent_phase_rail_rates_certified"])
        observation = info["observed_phase_rail_counts"]
        self.assertEqual(observation, {"matching_prefix_length": 5000,
                                       "matching_rail_counts": [n//16]*8,
                                       "first_mismatch": None})
        self.assertLess(len(json.dumps(observation)), 256)
        payload = {"candidate": raw, "check": check.specification(), "details": info}
        self.assertLess(len(json.dumps(payload, separators=(",", ":"))), 512 * 1024)

    def test_packed_carry_bound_and_circular_indexing(self):
        clock = [0, 901, 1001, 0, 13, 509, 3]
        signal = [[109, 1, 523, 616, 17, 10, 313], [1, 0, 0, 2, 5, 0, 0], [0]*7]
        expected = [[sum(a * clock[(i + d) % len(clock)] for i, a in enumerate(row))
                     for row in signal] for d in range(len(clock))]
        self.assertEqual(list(adapter._packed_rows(signal, clock, len(clock), lambda: None)), expected)

    def test_deadline_never_certifies_an_incomplete_scan(self):
        raw = spec(ring([0, 2, 0, 2]), ring([True] * 4))
        for permitted in (0, 5, 17, 25, 41):
            for threshold in (0, 65536):
                with (patch.object(adapter, "_PACKED_WORK_THRESHOLD", threshold),
                      patch.object(adapter, "monotonic", side_effect=[0]*permitted + [20]*100)):
                    check, info = evaluate(raw, deadline=10)
                    self.assertEqual((check.status, info["stop_reason"]), ("inconclusive", "deadline"))
                    self.assertFalse(info["all_recurrent_phase_rail_rates_certified"])
                    observed = self.recorded_rows(info)
                    self.assertEqual(observed, [[2, 0, 2]] * check.checked)
                    self.assertIsNone(info["observed_phase_rail_counts"]["first_mismatch"])
                    self.assertIsNone(check.witness)
        for deadline in (float("nan"), float("inf"), True, "soon"):
            with self.assertRaises(ValueError):
                evaluate(raw, deadline=deadline)

    def test_strict_schema_round_trip_and_source_hash(self):
        raw = spec([[0, 0]], [[0, True]], (1, -1))
        candidate = adapter.parse_periodic_contact_observer(raw)
        self.assertEqual(candidate.specification(), raw)
        self.assertEqual(adapter.LOADED_SOURCE_SHA256,
                         hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())

        def reject(path, value):
            invalid = copy.deepcopy(raw)
            parent = invalid
            for item in path[:-1]:
                parent = parent[item]
            parent[path[-1]] = value
            with self.subTest(path=path, bad=str(value)[:40]), self.assertRaises((TypeError, ValueError)):
                adapter.parse_periodic_contact_observer(invalid)

        for path, bad_values in (
            (("id",), [True, "not a label"]),
            (("family",), ["alien", 1, True]),
            (("current",), [[True, -1], [1.0, -1], [1000001, -1000001], [], [0]*9,
                            [1, -2], (1, -1), ["1", "-1"]]),
            (("signal",), [None, [], {"initial": 0, "transitions": [[0, 0]], "extra": 0}]),
            (("clock",), [None, [], {"initial": 0}]),
            (("signal", "initial"), [False, -1, 1, 0.0]),
            (("clock", "initial"), [False, -1, 1, 0.0]),
            (("signal", "transitions"), [[], ((0, 0),), [[0, 0]] * (adapter.MAX_STATES + 1)]),
            (("clock", "transitions"), [[], [[0, True]] * (adapter.MAX_STATES + 1)]),
            (("signal", "transitions", 0), [(0, 0), [0], [0, 0, 0]]),
            (("clock", "transitions", 0), [(0, False), [0, False, 0]]),
            (("signal", "transitions", 0, 0), [False, -1, 1, 0.0]),
            (("clock", "transitions", 0, 0), [False, -1, 1, 0.0]),
            (("signal", "transitions", 0, 1), [False, -1, 2, 0.0, None]),
            (("clock", "transitions", 0, 1), [1, 0, 1.0, "true", None]),
        ):
            for value in bad_values:
                reject(path, value)
        for kwargs in ({"signal_transitions": ([0, 0],)}, {"clock_transitions": ((0, 1),)},
                       {"signal_transitions": ((0, False),)}, {"current": [1, -1]}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                replace(candidate, **kwargs)
        raw["signal"]["transitions"][0][1] = 1
        self.assertEqual(candidate.specification()["signal"]["transitions"], [[0, 0]])


if __name__ == "__main__":
    unittest.main()
