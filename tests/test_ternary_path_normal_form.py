import unittest
from itertools import product

from scripts import probe_ternary_path_normal_form as path
from scripts.probe_ternary_active_readout import contact


def replay(word, trace):
    state = list(word)
    for i in trace:
        if not 0 <= i < len(state) - 1:
            raise AssertionError(("not an open-path edge", i))
        old = tuple(state[i:i + 2])
        new = contact(*old)
        if new == old:
            raise AssertionError(("not a changing contact", old, i))
        state[i:i + 2] = new
    return "".join(state)


class TernaryPathNormalFormTests(unittest.TestCase):
    def test_reduction_replays_every_prefix_composition(self):
        for n in range(8):
            for word in map("".join, product("abT", repeat=n)):
                nf = path.normal_form(word)
                self.assertEqual(replay(word, path.reduction_trace(word)), nf.representative())
                self.assertTrue(all(pair not in nf.skeleton for pair in ("aa", "bb", "Ta")))
                self.assertEqual(len(word), len(nf.skeleton) + 2 * nf.pairs)

    def test_native_contacts_fix_exactly_the_named_partition(self):
        for n in range(10):
            row = path.census(n)
            self.assertTrue(row["partition_and_tag_ranges_match"])
            self.assertEqual(row["components"], 2 ** (n + 1) - 1)
            self.assertEqual(row["raw_states"], 3 ** n)
            self.assertEqual(row["bfs_edge_offers"], max(0, n - 1) * 3 ** n)
            self.assertEqual(row["classifier_symbol_reads"], n * 3 ** n)

    def test_fixed_sites_no_endpoint_or_transcription_quotient(self):
        self.assertTrue(path.reachable("baTa", "bTaa"))
        self.assertFalse(path.reachable("Tba", "abT"))  # native wrap edge ONLY
        self.assertFalse(path.reachable("aa", ""))
        self.assertFalse(path.reachable("Tb", "bT"))
        self.assertIsNone(path.witness("Tba", "abT"))
        self.assertEqual(replay("bbTaa", path.witness("bbTaa", "Taaaa")), "Taaaa")
        self.assertFalse(path.reachable("TaTbb", "baaTb"))
        with self.assertRaises(ValueError):
            path.normal_form("abX")

    def test_all_rank_intervals_not_just_tag_counts(self):
        self.assertEqual(path.tag_intervals("bbTaa"), ((0, 4),))
        self.assertEqual(path.tag_intervals("baTba"), ((1, 2),))
        self.assertEqual(path.tag_intervals("bTaTTbTTaa"), ((1, 4), (2, 5), (3, 6), (6, 8), (7, 9)))
        self.assertEqual(path.tag_intervals("abba"), ())

    def test_long_orders_with_both_long_factors_and_deep_stack(self):
        size = 100_000
        for word, skeleton, pairs in (
            ("T" * size + "a" * size, "T" * size, size // 2),
            ("ab" * size + "ba" * size, "", 2 * size),
            ("aTb" * size, "aTb" * size, 0),
        ):
            counts = {}
            nf = path.normal_form(word, counts)
            self.assertEqual((nf.skeleton, nf.pairs), (skeleton, pairs))
            self.assertEqual(counts["symbol_reads"], len(word))

    def test_fixed_projector_and_independent_cost_rows(self):
        row = path.caging_control()
        self.assertEqual([r["reachable_sites"] for r in row], [[0, 1, 2, 3, 4], [1, 2]])
        self.assertEqual([r["component_size"] for r in row], [22, 2])
        self.assertEqual(row[0]["counts_abT"], row[1]["counts_abT"])
        self.assertEqual(row[0]["staggered_b"], row[1]["staggered_b"])
        self.assertEqual(row[0]["initial_T_site"], row[1]["initial_T_site"])
        self.assertEqual([r["fixed_site_zero_accessible"] for r in row], [True, False])
        for r in path.query_workloads():
            self.assertEqual(r["bfs_result"], r["reachable"])
            self.assertEqual(r["classifier_symbol_reads"], 2 * r["length"])
            self.assertGreater(r["bfs_edge_offers"], r["classifier_symbol_reads"])

    def test_active_loop_and_hit_from_same_start_with_same_detector(self):
        control = path.schedule_control()
        self.assertEqual(replay(control["initial"], control["repeating_edges"]), control["initial"])
        self.assertEqual(control["loop_tag_sites"], [2, 2, 2])
        self.assertEqual(replay(control["initial"], control["hit_edges"])[0], "T")


if __name__ == "__main__":
    unittest.main()
