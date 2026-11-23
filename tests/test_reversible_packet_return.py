"""Finite raw-kernel, readout-boundary, and offline spectrum contracts."""

import hashlib
import unittest
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
from tempfile import TemporaryDirectory

from scripts import probe_reversible_packet_return as probe


@cache
def report():
    return probe.packet_report()


class ReversiblePacketReturnTest(unittest.TestCase):
    def test_distinct_clocks_on_the_same_raw_orbit(self):
        summary = report()
        self.assertEqual(summary["raw_states"], 20)
        self.assertEqual(summary["offered_centers"], 16)
        self.assertEqual(summary["raw_labeled_directed_events"], 48)
        for name, expected, weights in (
            ("all_centers", ["1", "43/64", "15887/32768", "3142049/8388608"], 20),
            ("enabled_centers", ["1", "1/2", "1/3", "1/4"], 48),
        ):
            row = summary["kernels"][name]
            self.assertEqual(row["root_even_returns"][:4], expected)
            self.assertEqual(row["stationary_weight_sum"], weights)
            self.assertEqual(row["detailed_balance_pairs_checked"], 400)
            self.assertEqual(row["raw_point_events"], 20)
            self.assertEqual(row["vertex_unions"], 255)
            self.assertEqual(row["distinct_events_checked"], 268)
            self.assertGreaterEqual(row["max_k"], 12)
            self.assertEqual(
                row["difference_tests_per_event"],
                (row["max_k"] + 1) * (row["max_k"] + 2) // 2,
            )

    def test_controls_change_the_hypothesis_not_the_raw_rule(self):
        cases = report()["controls"]
        self.assertTrue(cases["ordered_offers"]["pair_map_bijective"])
        self.assertFalse(cases["ordered_offers"]["return_edge_from_root_image"])
        self.assertEqual(cases["ordered_offers"]["even_returns"], ["1", "0", "0", "1"])
        coarse = cases["coarse_detector"]
        self.assertEqual(len(coarse["accepted_vertex_labels"]), 5)
        self.assertEqual(coarse["point_prepared"], ["1", "1/2", "1/2", "19/36", "5/9"])
        self.assertEqual(
            coarse["stationary_conditioned"], ["1", "7/10", "2/3", "13/20", "173/270"]
        )
        self.assertEqual(cases["clock_mixture"]["mean_times"], ["1", "2", "3"])
        self.assertEqual(
            cases["clock_mixture"]["mean_readouts"], ["3/4", "5/8", "193/256"]
        )

    def test_higher_differences_and_nonreversibility_are_rejected(self):
        # Decreasing but not convex.
        with self.assertRaisesRegex(ArithmeticError, "difference"):
            probe.check_differences([4, 3, 1])
        with self.assertRaisesRegex(ArithmeticError, "detailed balance"):
            probe.verify_balance(({1: 1}, {2: 1}, {0: 1}), (1, 1, 1), 1)


def mock_table():
    # Headerless synthetic layout, not a redistributed experiment file.
    return "".join(
        f"{(95 + 10 * i) // 100}.{(95 + 10 * i) % 100:02} 20 10.5 999 0.1 0.2 0.3 0.4 0.5\n"
        for i in range(76)
    ).encode("ascii")


class SpectrumTest(unittest.TestCase):
    def test_decimal_background_sum_and_window_edges(self):
        rows = probe.parse_spectrum(mock_table())
        windows = probe.summarize_windows(rows)
        for window, bins in zip(windows, (6, 5, 5), strict=True):
            self.assertEqual(window["bins"], bins)
            self.assertEqual(window["observed"], 20 * bins)
            self.assertEqual(Q(window["reactor_no_oscillation"]), Q(21 * bins, 2))
            self.assertEqual(Q(window["modeled_nonreactor"]), Q(3 * bins, 2))
            self.assertEqual(Q(window["ratio"]), Q(37, 21))
            self.assertAlmostEqual(
                window["counting_only_sigma"], (20 * bins) ** 0.5 / (10.5 * bins)
            )

    def test_parser_rejects_shape_grid_and_noninteger_counts(self):
        raw = mock_table()
        with self.assertRaises(ValueError):
            probe.parse_spectrum(raw.split(b"\n", 1)[1])
        for old, new in ((b"0.95", b"1.05"), (b" 20 ", b" 0.5 "), (b" 999 ", b" ")):
            with self.assertRaises(ValueError):
                probe.parse_spectrum(raw.replace(old, new, 1))

    def test_default_is_source_only_and_unpinned_bytes_cannot_replay(self):
        default = probe.spectrum_report(None)
        self.assertFalse(default["replayed"])
        self.assertIn("not replayed", default["status"])
        self.assertEqual(
            [x["observed"] for x in default["descriptive_windows"]], [227, 205, 270]
        )
        with TemporaryDirectory() as dirname:
            path = Path(dirname) / "synthetic.dat"
            path.write_bytes(mock_table())
            with self.assertRaisesRegex(ValueError, "size"):
                probe.spectrum_report(path)
            path.write_bytes(b"x" * 5776)
            self.assertNotEqual(
                hashlib.sha256(path.read_bytes()).hexdigest(), probe.SPECTRUM_SHA256
            )
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                probe.spectrum_report(path)


if __name__ == "__main__":
    unittest.main()
