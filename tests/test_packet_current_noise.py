"""Exact finite-window and same-marginal controls for the packet count probe."""

import importlib
import importlib.util
import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import product

from scripts import probe_colorless_pair_additivity as pair


_SEEDS = ((1, 1), (1, 2), (2, 1), (2, 2))
_COUNTS = (1, 2, 1, 1)
_PROCESSES = ("iid", "frozen", "cycle")


def _histories(process, length):
    if process == "iid":
        return product(range(4), repeat=length)
    if process == "frozen":
        return ((i,) * length for i in range(4))
    return (tuple((phase + t) % 4 for t in range(length)) for phase in range(4))


def _moments(values):
    values = tuple(values)
    mean = F(sum(values), len(values))
    return mean, F(sum(x * x for x in values), len(values)) - mean * mean


class PacketCurrentNoiseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_packet_current_noise"
        cls.p = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.p, "packet current noise control is missing")

    def test_seed_labelled_outputs_from_original_pair(self):
        rows = self.p.seed_outcomes()
        self.assertEqual(tuple(row.seed for row in rows), _SEEDS)
        self.assertEqual(tuple(row.output for row in rows), (
            (3, 1, 0, 3, 2, 0), (3, 3, 0, 1, 1, 0),
            (1, 3, 0, 3, 2, 0), (1, 3, 0, 1, 3, 0),
        ))
        self.assertEqual(frozenset(row.output for row in rows), pair.read_suffix(pair.EARLY_WORD)[2])
        self.assertEqual(tuple(row.left_count for row in rows), _COUNTS)
        self.assertTrue(all(row.left_count + row.right_count == 2 for row in rows))
        self.assertTrue(all(min(row.left_count, row.right_count) >= 0 for row in rows))
        self.assertEqual(self.p.moments(_COUNTS), (F(5, 4), F(3, 16)))

    def test_aligned_marginals_include_entire_raw_output_not_just_counts(self):
        rows = self.p.seed_outcomes()
        expected = Counter({row.output: F(1, 4) for row in rows})
        self.assertEqual(self.p.PROCESSES, _PROCESSES)
        for process in _PROCESSES:
            # Sample different launch times in an independently enumerated stationary ensemble.
            histories = tuple(_histories(process, 5))
            for t in range(5):
                hist = Counter(rows[seq[t]].output for seq in histories)
                self.assertEqual({s: F(n, len(histories)) for s, n in hist.items()}, expected)
                joint = Counter((seq[0], seq[t]) for seq in histories)
                pairs = self.p.seed_pairs(process, t, len(rows))
                self.assertEqual({q: F(n, len(pairs)) for q, n in Counter(pairs).items()},
                                 {q: F(n, len(histories)) for q, n in joint.items()})

    def test_window_variance_laws_and_direct_count_enumeration(self):
        for m in range(1, 21):
            r = m % 4
            expected = (F(3 * m, 16), F(3 * m * m, 16), F(r * (4 - r), 16))
            for process, want in zip(_PROCESSES, expected, strict=True):
                with self.subTest(process=process, m=m):
                    self.assertEqual(self.p.window_variance(_COUNTS, process, m), want)
                    if process != "iid" or m <= 7:
                        direct = _moments(sum(_COUNTS[i] for i in seq)
                                          for seq in _histories(process, m))
                        self.assertEqual(direct, (F(5 * m, 4), want))

    def test_lag_covariance_and_finite_window_structure_factor(self):
        for lag in range(13):
            expected = (F(3, 16) if lag == 0 else 0, F(3, 16),
                        F(3, 16) if lag % 4 == 0 else F(-1, 16))
            self.assertEqual(tuple(self.p.lag_covariance(_COUNTS, k, lag) for k in _PROCESSES),
                             expected)

        # Independent squared-transform moments of finite paths. Center by the ensemble mean.
        for process in _PROCESSES:
            for m in range(1, 7):
                paths = tuple(_histories(process, m))
                for k in range(4):
                    square = 0
                    for seq in paths:
                        bins = [0] * 4
                        for t, i in enumerate(seq):
                            bins[t * k % 4] += 4 * _COUNTS[i] - 5
                        square += (bins[0] - bins[2]) ** 2 + (bins[1] - bins[3]) ** 2
                    expected = F(square, 16 * m * len(paths))
                    actual = self.p.window_structure_factor(_COUNTS, process, m, k)
                    self.assertEqual(actual, expected, (process, m, k))
                    self.assertGreaterEqual(actual, 0)
                    if k == 0:
                        self.assertEqual(actual * m, self.p.window_variance(_COUNTS, process, m))

    def test_splitter_independent_port_and_saturated_binary_controls(self):
        self.assertEqual(tuple(row.left_count for row in self.p.seed_outcomes(splitter_only=True)),
                         (1, 1, 1, 1))
        self.assertEqual(self.p.moments(self.p.independent_balanced_counts()), (F(1), F(1, 2)))
        counts = tuple(row.left_click for row in self.p.seed_outcomes())
        self.assertEqual(counts, (1, 1, 1, 1))
        self.assertEqual(self.p.moments(counts), (F(1), F(0)))
        for process, m in product(_PROCESSES, range(1, 9)):
            self.assertEqual(self.p.window_variance(counts, process, m), 0)

    def test_invalid_time_parameters_fail_explicitly(self):
        for args in ((_COUNTS, "iid", 0, 0), (_COUNTS, "iid", 2, -1),
                     (_COUNTS, "unknown", 2, 0)):
            with self.assertRaises(ValueError):
                self.p.window_structure_factor(*args)
        with self.assertRaises(ValueError):
            self.p.lag_covariance(_COUNTS, "iid", -1)

    def test_report_limits_the_bridge(self):
        report = self.p.report()
        for s in ("5/4", "3/16", "1/2", "same full", "stationary", "saturated",
                  "fixed time base", "number-to-current", "thermal", "background", "loss",
                  "between-realization", "not a prediction or rejection"):
            self.assertIn(s, report)


if __name__ == "__main__":
    unittest.main()
