import unittest
from collections import Counter
from fractions import Fraction
from itertools import product

from scripts import probe_binary_unanimous_triples as clocked


def probe():
    from scripts import probe_unclocked_binary_compiler
    return probe_unclocked_binary_compiler


def extra(left, right):
    return tuple(sorted((left, right)))


EXTRAS = {extra("TTT", w) for w in ("aaa", "bba", "abb")} | {
    extra("bTT", "TTb"), *(extra(x, y) for x in ("baT", "bTa") for y in ("aTb", "Tab"))}


class UnclockedBinaryCompiler(unittest.TestCase):
    def setUp(self):
        from importlib.util import find_spec
        self.assertIsNotNone(find_spec("scripts.probe_unclocked_binary_compiler"),
                             "missing executable unclocked graph probe")

    def test_whole_local_raw_graph_and_clean_partition(self):
        p = probe()
        g = p.Gadget(2, ((0, 1),))
        self.assertEqual(g.masks, tuple(sorted(set(clocked.masks(clocked.CS)))))
        self.assertEqual(len(g.adj), 32)
        for s, row in enumerate(g.adj):
            self.assertEqual(set(row), {clocked.offer(s, m) for m in g.masks} - {s})
        self.assertEqual(set(g.partition()), {("aa", "bb"), ("Ta", "aT"), ("TT",),
                                             ("ab",), ("ba",), ("Tb",), ("bT",)})
        for s in ("aa", "Ta"):
            self.assertEqual(Counter(len(g.adj[t]) for t in g.component(s)), {1: 4, 4: 1})
        self.assertEqual([len(g.adj[t]) for t in g.component("TT")], [2] * 6)
        for s in ("ab", "ba", "Tb", "bT"):
            self.assertFalse(g.adj[g.code[s]])

    def test_uniform_random_changing_edge_cut_and_distinct_waits(self):
        g = probe().Gadget(2, ((0, 1),))
        for s, t in (("aa", "bb"), ("bb", "aa"), ("Ta", "aT"), ("aT", "Ta")):
            self.assertEqual(g.wait(s, set(g.code)), ({s: Fraction(1, 2), t: Fraction(1, 2)}, 4))
            self.assertEqual(g.wait(s, {t}), ({t: 1}, 8))
        self.assertEqual(g.wait("TT", set(g.code)), ({"TT": 1}, 6))
        self.assertIsNone(g.wait("ab", set(g.code)))

    def test_joined_components_and_orientation_controls(self):
        p = probe()
        for rev, shared in product(product((False, True), repeat=2), (False, True)):
            edges = tuple((k+1, k) if r else (k, k+1) for k, r in enumerate(rev))
            g = p.Gadget(3, edges, shared)
            c = p.compare(g)
            self.assertEqual((c["native_components"], c["raw_code_components"]), (15, 12))
            self.assertEqual(c["pair_count"], 351)
            self.assertEqual(c["losses"], [])
            self.assertEqual(set(c["extras"]), EXTRAS)
            self.assertTrue(all((x.bit_count() - y.bit_count()) % 3 == 0
                                for x, row in enumerate(g.adj) for y in row))

    def test_shortest_literal_paths_have_no_intermediate_global_cut(self):
        for shared, length in ((False, 5), (True, 3)):
            g = probe().Gadget(3, ((0, 1), (1, 2)), shared)
            for s, t in EXTRAS:
                self.assertIsNotNone(g.shortest(s, t, skip_cuts=True))
            path = g.shortest("TTT", "aaa", skip_cuts=True)
            self.assertEqual((path[0], path[-1]), (g.code["TTT"], g.code["aaa"]))
            self.assertEqual(len(path)-1, length)
            self.assertEqual(len(g.shortest("TTT", "aaa"))-1, length)
            self.assertTrue(all(s not in g.code.values() for s in path[1:-1]))
            for s, t in zip(path, path[1:]):
                self.assertIn(s ^ t, g.masks)
                self.assertEqual(clocked.offer(s, s ^ t), t)

    def test_waiting_is_layout_dependent_but_hits_are_literal(self):
        means = []
        for shared in (False, True):
            g = probe().Gadget(3, ((0, 1), (1, 2)), shared)
            for start in ("TTT", "TTb", "baT"):
                probs, mean = g.wait(start, set(g.code))
                hits = {w for w in g.code if w != start and g.shortest(start, w, skip_cuts=True)}
                self.assertEqual(set(probs), hits | {start})
                self.assertEqual(sum(probs.values()), 1)
                self.assertTrue(all(v > 0 for v in probs.values()))
                self.assertGreater(mean, 1)
                distinct, later = g.wait(start, set(g.code)-{start})
                self.assertEqual(distinct, {w: probs[w]/(1-probs[start]) for w in hits})
                self.assertEqual(later, mean/(1-probs[start]))
                if start == "TTT":
                    means.append(mean)
        self.assertNotEqual(*means)

    def test_disjoint_private_modules_compose(self):
        p = probe()
        g = p.Gadget(4, ((0, 1), (2, 3)))
        self.assertEqual(g.width, 10)
        row = p.compare(g)
        self.assertEqual((row["native_components"], row["raw_code_components"]), (49, 49))
        self.assertEqual((row["extras"], row["losses"]), ([], []))

    def test_holdouts_compare_the_full_relation_not_just_counts(self):
        r = probe().verify()
        for row in r["orientations"]:
            self.assertTrue(row["same_addresses_as_forward"])
        for row in r["forward_path_holdouts"]:
            n = row["sites"]
            self.assertTrue(row["same_clean_partition_as_private"])
            self.assertEqual(row["pair_count"], {4: 3240, 5: 29403}[n])
            self.assertEqual((row["native_components"], row["raw_code_components"],
                              row["losses"], row["extras"]),
                             {4: (31, 17, 0, 129), 5: (63, 24, 0, 1439)}[n])
            self.assertTrue(all((int(k[-1]) - int(k[0])) % 3 == 0
                                for k in row["extras_by_hole_counts"]))

    def test_exact_waits_and_target_law_are_distinct_observables(self):
        for shared, wait, target_time, cuts in ((False, 65, 86, ("209/251", "21/251")),
                                                (True, 17, 27, ("8/11", "3/22"))):
            g = probe().Gadget(3, ((0, 1), (1, 2)), shared)
            probs, _ = g.wait("TTT", g.code)
            self.assertEqual((probs["TTT"], probs["aaa"]), tuple(Fraction(x) for x in cuts))
            self.assertEqual(g.wait("TTT", set(g.code)-{"TTT"}),
                             ({"aaa": Fraction(1, 2), "abb": Fraction(1, 4),
                               "bba": Fraction(1, 4)}, wait))
            self.assertEqual(g.wait("TTT", {"aaa"}), ({"aaa": 1}, target_time))


if __name__ == "__main__":
    unittest.main()
