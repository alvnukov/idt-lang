import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

from scripts.probe_conserved_bond_gait import Move, Ports, cycle_square, link, offers
from scripts.probe_two_packet_matchings import isolated_table, readings


class MatchedSinglesBondCounts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from scripts import probe_matched_singles_bond_counts as probe
        cls.probe = probe
        cls.rows = probe.histories()

    def test_near_far_and_matching_strata(self):
        near, far = self.rows["near"], self.rows["far"]
        self.assertEqual([r["g_bin"] for r in near[:7]],
                         [2, 2, 1, F(2, 3), F(17, 18), F(1, 9), F(163, 324)])
        self.assertEqual([r["g_bin"] for r in far], [0] * 10 + [F(1, 1296)])
        self.assertEqual(near[2]["p_matching"], (0, F(1, 2), F(1, 2)))
        self.assertEqual(near[2]["p_adjacent_and_matching"], (0, 0, F(1, 2)))
        self.assertEqual(near[6]["p_adjacent_and_matching"], (F(1, 27), F(29, 324), F(1, 8)))
        self.assertEqual(far[6]["p_matching"], (F(1, 48), F(47, 48), 0))
        self.assertEqual(far[10]["p_adjacent_and_matching"], (F(1, 2592), 0, 0))
        for rows in self.rows.values():
            self.assertEqual(rows[0]["p_matching"], (0, 1, 0))
            for r in rows:
                self.assertEqual(sum(r["p_count"]), 1)
                self.assertEqual(r["mean_count"], F(1, 4))
                self.assertEqual(sum(r["p_matching"]), 1)
                self.assertEqual(sum(r["p_adjacent_and_matching"]), 16 * r["p_count"][2])

    def test_direct_labelled_rotated_raw_joint(self):
        # Evolve the lab-frame mixture: no orbit reduction or adjacency formula.
        n = 16
        ports = Ports.from_graph(cycle_square(n))
        table = isolated_table(ports)
        shorts = [link(i, (i + 1) % n) for i in range(n)]
        longs = [link(i, (i + 2) % n) for i in range(n)]
        for name, offset, tail in (("near", 1, 3), ("far", 8, 5)):
            dist = Counter()
            for i in range(n):
                s = frozenset((shorts[i], shorts[(i + offset) % n], longs[(i - 3) % n],
                               longs[(i + tail) % n]))
                dist[s] += F(1, n)
            for t in range(11):
                singles, joint, successors = Counter(), Counter(), Counter()
                for s, w in dist.items():
                    for edge in s:
                        singles[edge] += w
                    short = s & ports.short_links
                    k = len(readings(table, short, s - short))
                    count = len(s.intersection(shorts[:2]))
                    joint[count, k] += w
                    if t < 10:
                        raw = offers(ports, s)
                        if raw:
                            for event in raw:
                                successors[event.apply(s)] += w / len(raw)
                        else:
                            successors[s] += w
                self.assertEqual([singles[e] for e in shorts + longs], [F(1, 8)] * (2 * n))
                r = self.rows[name][t]
                self.assertEqual(r["p_count_and_matching"],
                                 tuple(tuple(joint[c, k] for k in range(3)) for c in range(3)))
                dist = successors

    def test_move_equivariance_on_reachable_states(self):
        n = 16
        ports = Ports.from_graph(cycle_square(n))

        def rotate(e):
            return frozenset((v + 1) % n for v in e)

        layer = set(self.probe.preparations().values())
        for _ in range(11):
            nxt = set()
            for s in layer:
                raw = offers(ports, s)
                self.assertEqual({Move((m.center + 1) % n, rotate(m.old), rotate(m.new))
                                  for m in raw}, offers(ports, frozenset(map(rotate, s))))
                nxt.update(m.apply(s) for m in raw)
                if not raw:
                    nxt.add(s)
            layer = nxt

    def test_jam_and_distinct_edge_reference(self):
        ports = Ports.from_graph(cycle_square(16))
        jam = frozenset((link(0, 1), link(1, 2), link(8, 10), link(9, 11)))
        self.assertFalse(offers(ports, jam))
        self.assertEqual(self.probe.advance(ports, {jam: F(1)}), {jam: F(1)})
        counts = [len({0, 1}.intersection(pair)) for pair in combinations(range(16), 2)]
        mean = F(sum(counts), len(counts))
        factorial = F(sum(c * (c - 1) for c in counts), len(counts))
        self.assertEqual(factorial / mean**2, F(4, 15))
        self.assertEqual(self.probe.references(), {
            "two_uniform_distinct_short_edges": F(4, 15),
            "two_iid_draws_with_replacement_counting_multiplicity": F(1, 2),
            "poisson_count_fluctuating_total": 1,
        })


if __name__ == "__main__":
    unittest.main()
