import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

from scripts.probe_conserved_bond_gait import Ports, cycle_square, link, offers


class HiddenPairCorrelations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from scripts import probe_hidden_pair_correlations as probe
        cls.probe = probe
        cls.report = probe.run()

    def test_all_lab_frame_inclusions_and_next_event(self):
        ports = Ports.from_graph(cycle_square(16))
        edges = list(ports.short_links) + list(ports.motifs)
        previous = None
        for name, long_starts in (("A", (1, 9)), ("B", (5, 13))):
            marginals = [Counter() for _ in range(4)]
            next_pairs, next_singles = Counter(), Counter()
            for a in range(16):
                for h in (1, -1):
                    def edge(i, d, a=a, h=h):
                        return link((a + h * i) % 16, (a + h * (i + d)) % 16)
                    state = {edge(0, 1), edge(4, 1), *(edge(i, 2) for i in long_starts)}
                    for k in range(1, 4):
                        marginals[k].update(map(frozenset, combinations(state, k)))
                    events = offers(ports, state)
                    self.assertEqual(len(events), 2)
                    for m in events:
                        target = m.apply(state)
                        next_singles.update(target)
                        next_pairs.update(map(frozenset, combinations(target, 2)))
            self.assertEqual(set(next_singles.values()), {8})
            self.assertEqual(set(next_singles), set(edges))
            self.assertEqual([marginals[1][frozenset([e])] for e in edges], [4] * 32)
            if previous is not None:
                for pair in combinations(edges, 2):
                    self.assertEqual(previous[2][frozenset(pair)], marginals[2][frozenset(pair)])
                self.assertEqual(sum(previous[3][frozenset(t)] != marginals[3][frozenset(t)]
                                     for t in combinations(edges, 3)), 128)
            previous = marginals
            jets = [F(next_pairs[frozenset((link(0, 1), link(i, i+1)))], 64) for i in (3, 5)]
            self.assertEqual(jets, [0, F(1, 32)] if name == "A" else [F(1, 32), 0])
            self.assertEqual(self.report["named"][name]["post_joint_s0_s3_s0_s5"], jets)

    def test_census(self):
        self.assertEqual(self.report["census"], {
            "raw_states": 14400, "orbits": 484, "pair_signatures": 480,
            "collision_matching_counts": {"0,0": 2, "0,1": 2},
            "largest_fiber": 2,
        })

    def test_single_offer_countercontrol(self):
        u, v = (self.report["named"][s] for s in ("U", "V"))
        for row in (u, v):
            self.assertEqual(row["matchings"], 0)
            self.assertEqual(row["offer_count"], 1)
        self.assertEqual(self.report["uv_initial_different_inclusion_slots"][:2], [0, 0])
        self.assertEqual(u["post_joint_s0_s3_s0_s5"], [0, F(1, 16)])
        self.assertEqual(v["post_joint_s0_s3_s0_s5"], [F(1, 16), 0])

    def test_complete_panel_by_direct_lab_frame_counts(self):
        # Independent full 496-slot fingerprint: count every labelled pair
        # across all 32 transforms, including repeated orbit members.
        edges = [link(i, (i+d) % 16) for d in (1, 2) for i in range(16)]
        ix = {e: i for i, e in enumerate(edges)}
        perms = [[ix[frozenset((a+h*v) % 16 for v in edge)] for edge in edges]
                 for a in range(16) for h in (1, -1)]
        remaining = {a+b for a in combinations(range(16), 2)
                     for b in combinations(range(16, 32), 2)}
        groups = {}
        while remaining:
            s = remaining.pop()
            copies = [tuple(sorted(p[i] for i in s)) for p in perms]
            remaining.difference_update(copies)
            counts = Counter(t for c in copies for t in combinations(c, 2))
            groups.setdefault(tuple(sorted(counts.items())), []).append(copies)
        self.assertEqual(Counter(map(len, groups.values())), {1: 476, 2: 4})
        ports = Ports.from_graph(cycle_square(16))
        differences = []
        for fiber in groups.values():
            if len(fiber) != 2:
                continue
            rates = []
            for copies in fiber:
                counts = Counter()
                for c in copies:
                    s = frozenset(edges[i] for i in c)
                    events = offers(ports, s)
                    targets = [m.apply(s) for m in events] or [s]
                    for t in targets:
                        for pair in combinations(sorted(ix[e] for e in t), 2):
                            counts[pair] += F(1, 32*len(targets))
                rates.append(counts)
            p, q = rates
            differences.append({t for t in p.keys() | q.keys() if p[t] != q[t]})
        self.assertTrue(all({(0, 3), (0, 18)} & d for d in differences))
        self.assertEqual(max(sum(t in d for d in differences) for t in combinations(range(32), 2)), 2)
        panel = self.report["followup_pair_panel"]
        self.assertEqual(panel["single_complete_panel_representatives"], [])
        self.assertEqual(panel["max_fibers_resolved_by_one"], 2)
        self.assertEqual(panel["example_complete_two_panel_if_needed"], [((0, 3), (0, 18))])

    def test_shared_input_exact_event_reachability(self):
        self.assertEqual(self.report["reachable_from_fixed_input"],
                         {"first_event": {"A": 18, "B": 20}, "members_at_20": {"A": 2, "B": 16}})

    def test_witness_and_support(self):
        r = self.report
        self.assertEqual(r["initial_different_inclusion_slots"], [0, 0, 128])
        self.assertEqual(r["initial_triple_s0_s4_l1"], {"A": F(1, 32), "B": 0})
        self.assertEqual([r["named"][n]["matchings"] for n in ("A", "B")], [0, 1])
        self.assertEqual([r["named"][n]["successor_short_separations"] for n in ("A", "B")],
                         [[4, 5], [3, 4]])
        self.assertEqual([r["named"][n]["post_g_s0_s3_s0_s5"] for n in ("A", "B")],
                         [[0, 2], [2, 0]])

    def test_idle_mixtures(self):
        r = self.report["idle_mixture_control"]
        self.assertEqual(r["support_sizes"], [64, 64])
        self.assertEqual(r["shared_states"], 0)
        self.assertEqual(r["states_with_any_legal_move"], 0)
        self.assertEqual(r["different_inclusion_slots"], [0, 0, 176])
        self.assertEqual(r["p_triple_s0_l3_l4"], [F(1, 64), 0])


if __name__ == "__main__":
    unittest.main()
