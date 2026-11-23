import unittest
from itertools import product

from scripts import probe_binary_unanimous_triples as p


class BinaryUnanimousTriples(unittest.TestCase):
    def test_complete_role_free_tables(self):
        expected = {
            tuple(i ^ (7 if (extreme if i in (0, 7) else mixed) else 0) for i in range(8))
            for extreme, mixed in product(range(2), repeat=2)
        }
        self.assertEqual(set(p.equivariant_tables()), expected)
        self.assertEqual(tuple(p.offer(i, 7) for i in range(8)), (7, 1, 2, 3, 4, 5, 6, 0))

    def test_nine_rows_clean_bit_and_raw_transients(self):
        for x, y in product(range(3), repeat=2):
            start = 16 | x | y << 2
            out = {(1, 1): (2, 2), (2, 2): (1, 1), (0, 1): (1, 0), (1, 0): (0, 1)}.get((x,y), (x,y))
            walk = p.trace(start, p.CS)
            self.assertEqual(walk[-1], 16 | out[0] | out[1] << 2)
            self.assertTrue(all(s.bit_count() % 3 == start.bit_count() % 3 for s in walk))
            self.assertEqual(p.trace(walk[-1], p.CS[::-1]), walk[::-1])
            self.assertEqual(p.trace(start ^ 31, p.CS), tuple(s ^ 31 for s in walk))
        report = p.local_audit()
        self.assertGreater(report['transient_invalid_pair_rows'], 0)
        self.assertGreater(report['wrong_clean_bit_failures'], 0)
        self.assertEqual(report['min_offers_fixed_code_high_bit'], 6)
        self.assertEqual(report['no_helper_codes'], {'residue': 20, 'jammed': 4})

    def test_low_helper_is_viable_with_a_different_word(self):
        report = p.local_audit()
        self.assertEqual(report.get("min_offers_fixed_code_low_bit"), 9)
        for x, y in product("abT", repeat=2):
            u, v = p.cs.contact(x, y)
            start = p.CODE[x] | p.CODE[y] << 2
            self.assertEqual(p.trace(start, p.CS_LOW)[-1], p.CODE[u] | p.CODE[v] << 2)

    def test_fredkin_uses_a_restored_high_bit(self):
        for c, a, b in product(range(2), repeat=3):
            state = 8 | c | a << 1 | b << 2
            self.assertEqual(p.trace(state, p.FREDKIN)[-1],
                             (8 | c | b << 1 | a << 2) if c else state)

    def test_compiled_launches_and_independent_cuts(self):
        r = p.apparatus_audit()
        self.assertEqual((r['two_arm']['launches'], r['two_arm']['vacuum_controls']), (512, 1024))
        self.assertEqual(len(r['two_arm']['rows']), 32)
        for source, plates, opened, counts in r['two_arm']['rows']:
            dest = source ^ plates[0] ^ plates[1]
            self.assertEqual(counts, (16 * (dest == 0), 16 * (dest == 1), 0) if all(opened)
                             else ((4, 4, 8) if any(opened) else (0, 0, 16)))
        self.assertEqual((r['three_port']['launches'], r['three_port']['hub_checks']), (72, 192))
        self.assertEqual((r['two_arm']['bits'], r['three_port']['bits']), (51, 33))
        self.assertEqual(r['two_arm']['max_offers'], 1740)
        self.assertEqual(r['three_port']['max_offers'], 1062)
