"""Independent coordinate oracle for a raw, address-free binary update."""

import importlib
import random
import unittest


def edge(a, b):
    return frozenset((a, b))


def compact(n, i, h):
    return frozenset((edge(i % n, (i + 2*h) % n), edge((i + 2*h) % n, (i + 3*h) % n)))


class BinaryShapeGaitTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(importlib.util.find_spec("scripts.probe_binary_shape_gait"),
                             "raw binary gait rule is not implemented")
        self.rule = importlib.import_module("scripts.probe_binary_shape_gait")

    def test_frozen_coordinate_oracle_for_both_headings_and_both_phases(self):
        for n in (7, 8, 9, 11, 18):
            graph = self.rule.cycle_square(n)
            seen = set()
            for h in (-1, 1):
                for i in range(n):
                    start = compact(n, i, h)
                    end = compact(n, i+h, h)
                    expanded = start | end
                    for state, center, kind, target in (
                        (start, (i+3*h) % n, "copy", expanded),
                        (expanded, (i+2*h) % n, "erase", end),
                    ):
                        self.assertNotIn(state, seen)
                        seen.add(state)
                        moves = self.rule.offers(graph, state)
                        self.assertEqual([(move.center, move.kind) for move in moves],
                                         [(center, kind)])
                        self.assertEqual(moves[0].links, state ^ target)
                        self.assertEqual(moves[0].apply(state), target)
            self.assertEqual(len(seen), 4*n)

    def test_no_order_or_numeric_structure_required_of_vertex_names(self):
        n = 11
        names = [object() for _ in range(n)]
        random.Random(1902).shuffle(names)
        native = self.rule.cycle_square(n)
        graph = {names[v]: frozenset(names[w] for w in native[v]) for v in reversed(native)}
        def rename(state):
            return frozenset(frozenset(names[v] for v in e) for e in state)
        for h in (-1, 1):
            state = rename(compact(n, 4, h))
            origin = state
            seen = set()
            while state not in seen:
                seen.add(state)
                moves = self.rule.offers(graph, state)
                self.assertEqual(len(moves), 1)
                state = moves[0].apply(state)
            self.assertEqual((state, len(seen)), (origin, 2*n))
            self.assertEqual({rename(compact(n, i, h)) for i in range(n)},
                             {s for s in seen if len(s) == 2})

    def test_off_sector_no_event_or_two_distinct_event_centers(self):
        graph = self.rule.cycle_square(16)
        self.assertEqual(len(self.rule.offers(graph, frozenset())), 0)
        state = compact(16, 0, 1) | compact(16, 8, 1)
        moves = self.rule.offers(graph, state)
        self.assertEqual({(m.kind, m.center) for m in moves}, {("copy", 3), ("copy", 11)})
        self.assertEqual(len({m.apply(state) for m in moves}), 2)

    def test_small_carriers_cannot_supply_the_two_link_types(self):
        for n, count in ((5, 3), (6, 2)):
            graph = self.rule.cycle_square(n)
            self.assertEqual({len(graph[v] & graph[w]) for v in graph for w in graph[v]}, {count})
            self.assertEqual(len(self.rule.offers(graph, compact(n, 0, 1))), 0)

    def test_report_counts_raw_periods_not_a_supplied_address_walk(self):
        result = self.rule.report()
        for row in result["clean_sectors"]:
            n = row["n"]
            self.assertEqual(row["distinct_states"], 4*n)
            self.assertEqual(row["cycle_lengths"], [2*n, 2*n])
            self.assertEqual(row["marked_link_counts"], [2, 4])
            self.assertTrue(row["all_relabelled_offers_agree"])
        self.assertEqual(result["off_sector"]["separated_seed_offers"], [3, 11])


if __name__ == "__main__":
    unittest.main()
