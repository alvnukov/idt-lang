import unittest
from itertools import combinations, product
from scripts import probe_binary_unanimous_triples as unanimous
from scripts import probe_mixed_binary_triples as mixed


class MixedBinaryTriples(unittest.TestCase):
    def test_law_and_raw_vacuum(self):
        p = mixed
        table = tuple(p.offer(s, 7) for s in range(8))
        self.assertEqual(table, (0, 6, 5, 4, 3, 2, 1, 7))
        self.assertIn(table, unanimous.equivariant_tables())
        self.assertNotEqual(table[1].bit_count() % 3, 1)
        for width in (4, 5):
            for s in range(1 << width):
                for m in unanimous.masks(combinations(range(width), 3)):
                    t = p.offer(s, m)
                    self.assertEqual(p.offer(t, m), s)
                    self.assertEqual((t ^ s) & ~m, 0)
                    self.assertEqual(t ^ ((1 << width)-1), p.offer(s ^ ((1 << width)-1), m))

    def test_compilers_and_reversible_lower_bound(self):
        p = mixed
        for helper, word, minimum in ((None, p.CS4, 13), (1, p.CS5, 8), (0, p.CS5_LOW, 11)):
            self.assertEqual(len(word), minimum)
            for x, y in product(range(3), repeat=2):
                u, v = {(1,1):(2,2), (2,2):(1,1), (0,1):(1,0), (1,0):(0,1)}.get((x,y), (x,y))
                h = 16 if helper else 0
                state = x | y << 2 | h
                self.assertEqual(p.replay(state, word), u | v << 2 | h)
            audit = p.compiler_audit(helper, word)
            self.assertEqual(audit["lower_bound"], minimum)
            self.assertGreater(audit["transient_spare_rows"], 0)

    def test_unscheduled_unordered_distinct_endpoints(self):
        p = mixed
        for helper, count, all_reached, min_extras in ((None, 16, 1, 26),
                                                       (0, 1024, 598, 2), (1, 1024, 598, 4)):
            r = p.support_audit(helper)
            self.assertEqual(r["supports"], count)
            self.assertEqual(r["exact_supports"], 0)
            self.assertEqual(r["native_distinct_pairs"], 2)
            self.assertEqual(r["all_desired_reachable"], all_reached)
            self.assertEqual(r["minimum_extra_if_all_desired"], min_extras)
        # A nonuniform isolated site does not obstruct jamming of an offered monochrome triple.
        self.assertEqual(p.jammed_words(4, (7,)), {0, 7, 8, 15})
        self.assertEqual(p.jammed_words(4, (7, 14)), {0, 15})

    def test_transport_controls_and_ordinary_registers(self):
        r = mixed.apparatus_audit()
        self.assertEqual((r["two_arm_launches"], r["ordinary_source_controls"],
                          r["three_port_launches"]), (512, 1024, 72))
        self.assertEqual(r["two_arm_data_bits_including_stocks_and_registers"], 50)
        self.assertEqual(r["three_port_data_bits_including_stocks_and_registers"], 32)
        self.assertEqual(r["offers_per_vacancy"], 117)
        self.assertEqual(r["offers_per_protected_meter"], 65)
