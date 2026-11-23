"""Independent graph oracle and subfamily controls for the template census."""

from collections import Counter
from importlib.util import find_spec
from itertools import combinations
import unittest


class TemplateCensusTest(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(find_spec("scripts.probe_unclocked_template_census"),
                             "the executable native-template census is missing")
        from scripts import probe_unclocked_template_census as probe
        self.p = probe

    def test_all_uniform_two_bit_codebooks_reduce_or_fail_residue(self):
        p = self.p
        self.assertTrue(hasattr(p, "codebook_control"), "missing finite codebook normalization")
        rows = p.codebook_control()
        self.assertEqual(len(rows), 24)
        self.assertEqual(sum(row["status"] == "aa_bb_residue" for row in rows), 20)
        survivors = [r for r in rows if r["status"] == "equivalent"]
        self.assertEqual({tuple(r["code"]) for r in survivors},
                         {(0, 1, 2), (0, 2, 1), (3, 1, 2), (3, 2, 1)})
        for r in survivors:
            t, a, b = r["code"]
            v = [x ^ (3 if r["complement_all"] else 0) for x in (t, a, b)]
            if r["swap_data_wires"]:
                v = [((x & 1) << 1) | (x >> 1) for x in v]
            self.assertEqual(v, [0, 1, 2])

    def test_one_helper_full_and_joined(self):
        p = self.p
        for stock, hist in [(0, {8: 1}), (1, {8: 1, 46: 3})]:
            edges = tuple(combinations(range(5), 3))
            hits = p.local_fits(1, stock, edges)
            self.assertEqual(Counter(p.compare_path(1, stock, edges, m, 3)
                                     for m in hits), {(0, k): n for k, n in hist.items()})
            # Independent route: apply unanimous bit flips in a raw-graph BFS
            # rather than adding DSU links. Check negative cases as well.
            expected = [m for m in range(1024) if p.compare_path(1, stock, edges, m, 2) == (0, 0)]
            self.assertEqual(sorted(hits), expected)

    def test_balanced_two_helpers(self):
        p = self.p
        edges = tuple((i, j, k) for i, j in combinations(range(4), 2) for k in (4, 5))
        for stock, hist in [(0, {5: 4}), (1, {6: 4}), (2, {6: 4}), (3, {})]:
            hits = p.local_fits(2, stock, edges)
            self.assertEqual(Counter(p.compare_path(2, stock, edges, m, 3)
                                     for m in hits), {(0, k): n for k, n in hist.items()})
            for m in hits:
                pairs = p.clean_pairs(2, stock, edges, m, 3)
                self.assertTrue(all(a.count("T") == b.count("T") for a, b in pairs))

    def test_general_mask_counts_and_label_controls(self):
        p = self.p
        hits = [set(p.local_fits(2, s, p.TWO)) for s in range(4)]
        self.assertEqual([len(f) for f in hits], [232, 528, 528, 323])
        for s, row in enumerate(hits):
            for mask in row:
                t, n = p.swap_helpers(s, mask)
                self.assertIn(n, hits[t])
                self.assertEqual(p.swap_helpers(t, n), (s, mask))
        self.assertEqual(Counter(s for s, _ in p.minimal_templates()), {0: 68, 1: 54, 2: 54, 3: 46})
        # Cross-check a subcube obtained from the lex-first stock-zero minimum
        # plus unused incidences of all kinds. Both fits and misses required.
        s, m = p.minimal_templates()[0]
        ids = [j for j in range(20) if m >> j & 1]
        ids += [j for j in range(20) if j not in ids][:10-len(ids)]
        edges = tuple(p.TWO[j] for j in ids)
        local = set(p.local_fits(2, s, edges))
        self.assertTrue(0 < len(local) < (1 << len(ids)))
        for mask in range(1 << len(ids)):
            lifted = sum(1 << j for i, j in enumerate(ids) if mask >> i & 1)
            self.assertEqual(mask in local, lifted in hits[s])
            self.assertEqual(mask in local, p.compare_path(2, s, edges, mask, 2) == (0, 0))

    def test_minimal_heterogeneous_near_miss_and_symmetries(self):
        p = self.p
        x, y = (1, 12328), (1, 139552)
        for a in (x, p.swap_helpers(*x)):
            for b in (y, p.swap_helpers(*y)):
                actual = p.mixed_pairs((p.two_recipe(*a), p.two_recipe(*b)))
                self.assertEqual(actual - p.native_pairs(3), {("Tba", "abT")})
                self.assertFalse(p.native_pairs(3) - actual)

    def test_complete_mixed_census(self):
        p = self.p
        result = p.mixed_census()
        self.assertEqual((result["minimal_labeled"], result["minimal_representatives"],
                          result["representative_pairs"], result["labeled_pairs"]),
                         (222, 115, 13225, 49284))
        self.assertEqual(result["survivors"], [])
        self.assertEqual(result["labeled_extra_histogram"][1], 12)
        self.assertEqual(sum(result["labeled_extra_histogram"].values()), 49284)
        nearest = result["nearest_minimal_representatives"]
        self.assertEqual({(r["left"], r["right"]) for r in nearest}, {
            ((1, 12328), (1, 139552)), ((1, 12328), (3, 270880)), ((3, 270880), (1, 139552))})
        self.assertTrue(all(r["multiplicity"] == 4 and r["extra_pairs"] == [("Tba", "abT")]
                            for r in nearest))


if __name__ == "__main__":
    unittest.main()
