"""Independent whole-link controls for cyclic binary-star scattering."""

import unittest
from itertools import product

from scripts import probe_available_link_logic as base
from scripts import probe_binary_star_contrast as star


class BinaryStarContrastTest(unittest.TestCase):
    def test_offers_replay_on_the_actual_incidence_graph(self):
        d, n = 3, 3
        edges = tuple(
            (0 if j == 0 else 1 + i * n + j - 1, 1 + i * n + j)
            for i in range(d)
            for j in range(n)
        )
        generators = base.offer_tables(edges)
        order = (2, 0, 1)
        even = [i * n + j for i in order for j in range(0, n, 2)]
        odd = [i * n + j for i in order for j in range(1, n, 2)]
        for raw in range(1 << (d * n)):

            def unpack(bits):
                return tuple(bits >> (i * n) & 7 for i in range(d))

            mid = base.replay(raw, even, generators)
            end = base.replay(mid, odd, generators)
            self.assertEqual(
                star.sweep(unpack(raw), n, order), (unpack(mid), unpack(end))
            )

    def test_all_short_raw_states_keep_endpoint_current(self):
        for n in (3, 4):
            row = star.raw_balance(3, n)
            self.assertEqual(row["states"], 2 ** (3 * n))
            self.assertGreater(row["states_with_remote_flux"], 0)
        self.assertEqual(star.charge(0b110), -1)
        self.assertEqual(star.charge(0b11), 1)

    def test_both_arrival_and_departure_whole_states(self):
        expected3 = (
            (0, 0, 0),
            (1, 3, 3),
            (0, 1, 3),
            (1, 1, 3),
            (0, 0, 1),
            (1, 3, 1),
            (0, 1, 1),
            (1, 1, 1),
        )
        expected10 = (
            (0, 0, 0),
            (0, 3 << 14, 3 << 14),
            (3 << 12, 0, 3 << 14),
            (0, 0, 3 << 14),
            (3 << 12, 3 << 12, 0),
            (3 << 10, 3 << 10 | 3 << 14, 3 << 12),
            (3 << 12, 0, 0),
            (3 << 10, 3 << 10, 3 << 12),
        )
        for mask in range(8):
            prep = tuple((5,) if mask >> i & 1 else () for i in range(3))
            r = star.scatter(prep, 40, 10, ((0, 1, 2),))
            self.assertEqual(r["states"][3], expected3[mask])
            self.assertEqual(r["states"][10], expected10[mask])
            self.assertEqual(r["sum"], (r["bursts"],) * 3)

    def test_clock_control_and_unclean_cut_do_not_disappear(self):
        prep = ((5,), (), ())
        r = star.scatter(prep, 40, 10, ((0, 1, 2), (2, 1, 0)))
        self.assertEqual(r["sum"], (2, 1, 1))
        self.assertEqual(r["states"][-1], (3 << 12, 3 << 14, 3 << 14))
        with self.assertRaisesRegex(ValueError, "clean"):
            star.scatter(prep, 40, 3, ((0, 1, 2),))
        with self.assertRaisesRegex(ValueError, "endpoint"):
            star.scatter(prep, 12, 10, ((0, 1, 2),))
        for dirty in (1, 3 << 5, 15 << 4, (3 << 4) | (1 << 12)):
            with self.assertRaises(ValueError):
                star.outgoing(dirty)

    def test_complete_and_truncated_bursts(self):
        for stream, expected in [((1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0), 2), ((), 0)]:
            self.assertEqual(star.complete_bursts(stream, 3), expected)
        for stream in ((1,), (1, 1, 1, 1), (1, 1, 1, 0, 1, 1, 1)):
            with self.assertRaises(ValueError):
                star.complete_bursts(stream, 3)

    def test_frozen_preparations_and_discriminating_controls(self):
        r = star.experiment()
        self.assertEqual(
            r["prepared_grid"]["cases"], len(list(product(range(5), repeat=3)))
        )
        self.assertEqual(set(r["held_out"]["degrees"]), {2, 3, 4, 5})
        self.assertEqual(r["masks"][5]["out"], (1, 2, 1))
        self.assertEqual(r["clock_control"]["sum"], (2, 1, 1))
        self.assertTrue(r["weight_control"]["only_nonnegative_solution_is_zero"])
        self.assertEqual(r["weight_control"]["signed_kernel_dimension"], 2)
        timing = r["timing_control"]
        self.assertEqual(timing["synchronous"]["in"], timing["delayed"]["in"])
        self.assertEqual(timing["synchronous"]["out"], (1, 2, 1))
        self.assertEqual(timing["delayed"]["out"], (0, 1, 0))
        self.assertEqual(
            r["prepared_grid"]["burst_histogram"], {0: 1, 1: 17, 2: 57, 3: 46, 4: 4}
        )


if __name__ == "__main__":
    unittest.main()
