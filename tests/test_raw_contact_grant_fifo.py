import unittest
from itertools import product

from scripts.probe_raw_contact_grant_fifo import (
    closed_inventory,
    echo_inventory,
    fifo_replay,
    open_inventory,
    tick,
    two_device_tick,
)


class RawContactGrantFifoTests(unittest.TestCase):
    def test_closed_prefix_support_and_grant_cycles(self) -> None:
        report = closed_inventory()
        self.assertEqual(report["states"], 64)
        self.assertEqual(
            report["legal_prefixes"], {"H": 24, "HG": 10, "HGH": 8, "HGHG": 8}
        )
        self.assertEqual(report["one_per_pair_states"], 8)
        self.assertEqual(len(report["grant_cycles"]), 2)
        self.assertEqual(
            {state for cycle in report["grant_cycles"] for state in cycle},
            {
                (a, b, 1 - b, d, 1 - a, 1 - d)
                for a in (0, 1)
                for b in (0, 1)
                for d in (0, 1)
            },
        )
        self.assertTrue(all(len(cycle) == 4 for cycle in report["grant_cycles"]))
        self.assertEqual(
            (report["H_shared_input"], report["G_shared_input"]), ((0, 1), (1, 0))
        )

    def test_open_fifo_partitions_all_previous_balanced_arrivals(self) -> None:
        for k, expected in (
            (1, (6, 2, 3, 1)),
            (2, (90, 6, 15, 69)),
            (3, (1860, 20, 93, 1747)),
        ):
            with self.subTest(k=k):
                report = open_inventory(k)
                self.assertEqual(
                    (
                        report["total"],
                        report["same_phase"],
                        report["opposite_phase"],
                        report["neither"],
                    ),
                    expected,
                )
                self.assertEqual(report["row_phase_checks"], 4 * k * expected[0])

    def test_wait_preserves_head_and_mirror(self) -> None:
        self.assertEqual(tick(None, 0), (None, 0))
        self.assertEqual(tick(None, 1), (None, 1))
        self.assertEqual(tick((0, 0, 0), 1), (None, 1))
        word = ((1, 0, 0), (0, 1, 1))
        self.assertEqual(fifo_replay(word, 1, waits=5), (2, 1))
        self.assertEqual(fifo_replay(word, 0, waits=5), (0, 0))
        for phase in (0, 1):
            self.assertEqual(
                fifo_replay(((0, 0, 0), (1, 1, 1)), phase, waits=5), (0, phase)
            )

    def test_two_device_tick_matches_independent_four_bit_mask_oracle(self) -> None:
        legal_masks = {0b0011, 0b0101, 0b0110, 0b1001, 0b1010, 0b1100}
        inactive_h = inactive_g = active_both = 0
        for a, b, c, h, g, s in product((0, 1), repeat=6):
            with self.subTest(drive=(a, b, c), h=h, g=g, s=s):
                h_input = (a << 3) | (b << 2) | (c << 1) | h
                expected: tuple[tuple[int, int, int] | None, int, int]
                if h_input not in legal_masks:
                    expected = None, h, g
                    inactive_h += 1
                else:
                    h_output = h_input ^ 0b1111
                    # Route just H's middle bits into G's first two slots.
                    g_input = ((h_output & 0b0110) << 1) | (s << 1) | g
                    if g_input not in legal_masks:
                        expected = None, h_output & 1, g
                        inactive_g += 1
                    else:
                        g_output = g_input ^ 0b1111
                        ordered = (
                            (g_output >> 3) & 1,
                            (g_output >> 2) & 1,
                            (g_output >> 1) & 1,
                        )
                        expected = ordered, h_output & 1, g_output & 1
                        active_both += 1
                self.assertEqual(two_device_tick((a, b, c), h, g, s), expected)
        self.assertEqual((inactive_h, inactive_g, active_both), (40, 14, 10))

    def test_reconnected_echo_is_rotated_input_not_a_new_readout(self) -> None:
        self.assertEqual(two_device_tick((1, 0, 1), 0, 1, 0), ((0, 1, 1), 1, 0))
        self.assertEqual(two_device_tick((1, 0, 1), 0, 0, 0), (None, 1, 0))
        self.assertEqual(echo_inventory(), 6)
