import unittest
from typing import ClassVar

from scripts.probe_pair_compiled_packet_instruments import Report, run_probe


class PairCompiledPacketInstrumentTests(unittest.TestCase):
    report: ClassVar[Report]

    @classmethod
    def setUpClass(cls) -> None:
        cls.report = run_probe()

    def test_octagon_uses_all_global_offers_and_raw_signed_contrasts(self) -> None:
        row = self.report.octagon
        self.assertEqual((row.addresses, row.rails, row.cells_per_color), (16, 32, 8))
        self.assertEqual((row.direct_sweeps, row.direct_offers), (48, 5_760))
        self.assertTrue(row.common_central_z)
        self.assertTrue(row.central_w)
        self.assertEqual(row.w_squared, row.z)
        self.assertEqual(len(row.signed_w_images), 8)
        for before, (middle, first_sign) in enumerate(row.signed_w_images):
            self.assertEqual(row.signed_w_images[middle], (before, -first_sign))

    def test_both_fixed_layouts_scan_every_cell_in_both_orders(self) -> None:
        self.assertEqual(set(self.report.modes), {"D", "H"})
        for mode, row in self.report.modes.items():
            with self.subTest(mode=mode):
                self.assertEqual((row.input_rails, row.class_rails, row.residue_rails), (32, 64, 8))
                self.assertEqual((row.cells, row.inputs, row.outputs), (256, 256, 256))
                self.assertEqual((row.unique_forward, row.unique_reverse), (256, 256))
                self.assertEqual(set(row.orders), {"supplied", "reversed"})
                for order in row.orders.values():
                    self.assertEqual(order.lifted_sweeps, 512)
                    self.assertEqual(order.lifted_cell_visits, 512 * 256)
                    self.assertEqual(order.lifted_offers, 512 * 3_840)
                    self.assertEqual(order.effective_cells, 512)
                    self.assertEqual(order.partial_visits, {1: 16_384, 3: 0})
                    self.assertEqual((order.direct_sweeps, order.direct_offers), (8, 30_720))

    def test_partial_encounters_clean_but_are_not_microscopically_idle(self) -> None:
        row = self.report.local
        self.assertEqual(row.parity_activity_by_occupancy, {0: 0, 1: 4, 2: 8, 3: 4, 4: 0})
        self.assertEqual(row.clean_patterns, 16)
        self.assertEqual(row.embedded_clean_patterns, 16)
        self.assertTrue(row.dirty_cross_bond_blocks_clean_lift)
        self.assertEqual(row.parity_all_equal_internal_offers, (0, 0))
        self.assertEqual(row.code7_same_word_all_equal_internal_offers, (15, 15))
        self.assertEqual(row.code7_same_word_all_equal_bonds, (55, 55))
        self.assertEqual(row.code7_clean_word_all_equal_internal_offers, (144, 144))
        self.assertEqual(row.code7_clean_word_all_equal_bonds, (0, 0))


if __name__ == "__main__":
    unittest.main()
