"""Raw four-bond states, not two labeled particles."""

import unittest
from itertools import combinations, product

from scripts.probe_conserved_bond_gait import Move, fixture, link, offers


class PacketMatchingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from scripts import probe_two_packet_matchings as probe

        cls.probe = probe
        cls.shell = probe.Shell(16)

    def test_complete_sector_and_combinatorial_oracle(self):
        for n, shell, counts, mismatches in (
            (11, self.probe.Shell(11), (1430, 1375, 220), (638, 0)),
            (16, self.shell, (10640, 3440, 320), (928, 0)),
        ):
            self.assertEqual(shell.counts, counts)
            self.assertEqual(shell.mismatches, mismatches)
            self.assertEqual(self.probe.matching_oracle(n), counts)

    def test_shortest_loss_replays_all_raw_edges(self):
        for i, h, distance in ((8, 1, 7), (8, -1, 6), (5, 1, 2)):
            state = fixture(16, 0, 1)[0] | fixture(16, i, h)[0]
            report = self.shell.preparation(i, h)
            witness = report["first_loss"]
            self.assertEqual(witness["distance"], distance)
            self.assertEqual(len(witness["steps"]), distance)
            for row in witness["steps"]:
                self.assertEqual(self.probe.state_record(state), row["before"])
                self.assertGreater(len(self.shell.matchings(state)), 0)
                move = Move(row["center"], link(*row["old"]), link(*row["new"]))
                self.assertIn(move, offers(self.shell.ports, state))
                state = move.apply(state)
                self.assertEqual(self.probe.state_record(state), row["after"])
            self.assertFalse(self.shell.matchings(state))
            self.assertEqual(len(state & self.shell.ports.short_links), 2)
            self.assertEqual(len(state), 4)

    def test_one_center_is_not_one_event(self):
        state = fixture(16, 0, 1)[0] | fixture(16, 1, 1)[1]
        moves = offers(self.shell.ports, state)
        self.assertEqual(len({m.center for m in moves}), 1)
        self.assertEqual(len({m.apply(state) for m in moves}), 2)
        self.assertEqual(len(self.shell.edges[self.shell.index[state]]), 2)

    def test_independent_relabeling(self):
        self.assertEqual(self.probe.Shell(11).check_relabeling(), 3025)

    def test_interval_count_with_and_without_wrapping(self):
        for n in range(7, 21):
            ports = self.probe.Ports.from_graph(self.probe.cycle_square(n))
            compatible = self.probe.isolated_table(ports)
            counts = [0, 0, 0]
            for (a, b), (c, d) in product(
                combinations(ports.short_links, 2), combinations(ports.motifs, 2)
            ):
                k = int((a, c) in compatible and (b, d) in compatible)
                k += int((a, d) in compatible and (b, c) in compatible)
                counts[k] += 1
            self.assertEqual(tuple(counts), self.probe.matching_oracle(n))
            if n >= 11:
                self.assertEqual(counts[1:], [n * (18 * n - 73), 20 * n])

    def test_global_classes_and_recovery(self):
        for shell, sizes, max_rank, idle in (
            (self.probe.Shell(11), [2915], 10, 110),
            (self.shell, [2944, 2944, 6512], 24, 2000),
        ):
            row = shell.census()
            self.assertEqual(row["max_active_k0_min_to_unique"], max_rank)
            self.assertEqual(row["isolated_jams"], idle)
            profile = row["whole_shell_sccs"]
            self.assertTrue(all(r["terminal"] for r in profile))
            self.assertEqual(
                sorted(sum(r["k012"]) for r in profile for _ in range(r["components"])
                       if sum(r["k012"]) > 1),
                sizes,
            )
            # Independent orientation check: forward and backward search from
            # a representative visit exactly its claimed component.
            for g in shell.scc[0]:
                if len(g) == 1:
                    self.assertFalse(shell.edges[g[0]] or shell.reverse[g[0]])
                    continue
                root = g[0]
                reverse_seen = {root}
                queue = [root]
                while queue:
                    for t in shell.reverse[queue.pop()]:
                        if t not in reverse_seen:
                            reverse_seen.add(t)
                            queue.append(t)
                self.assertEqual(set(g), reverse_seen)
                self.assertEqual(set(g), set(self.probe.bfs(shell.edges, root)[0]))

    def test_long_incidence_components_separate_active_classes(self):
        for n, shell, expected in (
            (11, self.probe.Shell(11), [((2,), 2915)]),
            (16, self.shell, [((0, 2), 2944), ((0, 2), 2944), ((1, 1), 6512)]),
        ):
            rows = shell.active_long_sectors()
            self.assertEqual(sorted((r["long_counts_unordered"], r["states"]) for r in rows),
                             expected, n)
        # n=7 has no k=0 configurations, so there is no maximum return rank.
        self.assertIsNone(self.probe.Shell(7).census()["max_active_k0_min_to_unique"])

    def test_may_return_but_not_on_every_word(self):
        for i, h, rank, count in ((8, 1, 9, 2), (8, -1, 2, 2), (5, 1, 4, 1)):
            result = self.shell.preparation(i, h)
            self.assertEqual(result["nearest_loss_states"], count)
            self.assertEqual(result["nearest_loss_with_infinite_k0_path"], count)
            self.assertEqual(result["nearest_loss_ranks"],
                             [{"to_pairable_unique_jam": (rank, rank, -1), "states": count}])
            returned = result["return_from_displayed_loss"]["unique"]
            self.assertEqual(returned["distance"], rank)
            state = frozenset(link(*e) for e in result["first_loss"]["steps"][-1]["after"])
            for row in returned["steps"]:
                self.assertFalse(self.shell.matchings(state))
                self.assertEqual(self.probe.state_record(state), row["before"])
                move = Move(row["center"], link(*row["old"]), link(*row["new"]))
                self.assertIn(move, offers(self.shell.ports, state))
                state = move.apply(state)
                self.assertEqual(self.probe.state_record(state), row["after"])
            self.assertEqual(len(self.shell.matchings(state)), 1)
            self.assertIsNone(result["return_from_displayed_loss"]["jam"])


if __name__ == "__main__":
    unittest.main()
