import unittest
from fractions import Fraction
from importlib.util import find_spec
from itertools import permutations, product


class BinaryPairSwitchWallTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(
            find_spec("scripts.probe_binary_pair_switch_wall"),
            "missing binary pair switch probe",
        )
        from scripts import probe_binary_pair_switch_wall as probe

        self.p = probe

    def test_all_oriented_and_symmetric_tables(self):
        gates, affine, symmetric = self.p.pair_tables()
        self.assertEqual(set(permutations(range(4))), gates)
        self.assertEqual(gates, affine)
        self.assertEqual(
            symmetric, {(0, 1, 2, 3), (0, 2, 1, 3), (3, 2, 1, 0), (3, 1, 2, 0)}
        )
        for g in symmetric:
            for x, y in product(range(4), repeat=2):
                self.assertEqual((x ^ y).bit_count(), (g[x] ^ g[y]).bit_count())

    def test_settings_order_and_port_conventions(self):
        rows = list(product(range(2), repeat=2))
        for source in range(2):
            for order in (rows, rows[::-1]):
                for s, c in order:
                    expected = tuple(int(s and i == source ^ c) for i in range(2))
                    self.assertEqual(self.p.ternary_flags(source, s, c), expected)
                    self.assertEqual(
                        self.p.oriented_flags(source, s, c), expected if s else (c, c)
                    )
                a = self.p.rate_certificate(order)
                self.assertEqual(a["mismatch_counts"], [1] * 4 + [3] * 4)
                self.assertEqual(a["sharp_errors"], [Fraction(1, 4)] * 4)
                self.assertEqual(a["offset_minimax"], Fraction(1, 2))

    def test_addressed_extension_all_raw_bits(self):
        for a, b, t in product(range(2), repeat=3):
            self.assertEqual(self.p.three_toggles(a, b, t), (a, b, t ^ (a & b), 0))
        report = self.p.verify()
        self.assertEqual(
            report["ternary_cost"],
            {
                "logical_contacts": 6,
                "native_contacts": 64,
                "sites": 11,
                "meter_ports": 2,
            },
        )


if __name__ == "__main__":
    unittest.main()
