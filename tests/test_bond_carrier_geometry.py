"""Independent controls for reconstructing the line, not physical space."""

import importlib
import importlib.util
import unittest
from collections import Counter
from itertools import combinations, pairwise
from random import Random

from scripts.probe_binary_shape_gait import cycle_square, link
from scripts.probe_conserved_bond_gait import Move, Ports, offers


class BondGeometryTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(importlib.util.find_spec("scripts.probe_bond_carrier_geometry"),
                             "the carrier reconstruction is not implemented")
        self.g = importlib.import_module("scripts.probe_bond_carrier_geometry")

    def test_all_neighbor_graphs_against_path_permutations(self):
        from itertools import permutations

        possible = list(combinations(range(4), 2))
        expected = {frozenset(link(a, b) for a, b in pairwise(p))
                    for p in permutations(range(4))}
        actual = set()
        for mask in range(64):
            edges = frozenset(link(a, b) for i, (a, b) in enumerate(possible) if mask >> i & 1)
            star = {i: frozenset(v for v in range(4) if link(i, v) in edges) for i in range(4)}
            if self.g.is_port_link(star):
                actual.add(edges)
        self.assertEqual(len(expected), 12)
        self.assertEqual(actual, expected)

    def test_short_certificate_and_connected_scope(self):
        for n in (7, 8, 10, 31):
            self.assertEqual(self.g.recover_short_cycle(cycle_square(n)),
                             {link(i, (i+1) % n) for i in range(n)})
        first = cycle_square(7)
        second = {v+20: frozenset(w+20 for w in ns) for v, ns in first.items()}
        for graph in ({}, first | second):
            Ports.from_graph(graph)  # the old guard is local, unlike this certificate
            with self.assertRaises(ValueError):
                self.g.recover_short_cycle(graph)
        for n in (5, 6):
            with self.assertRaises(ValueError):
                self.g.recover_short_cycle(cycle_square(n))
        with self.assertRaises(ValueError):
            self.g.compile_lines({0: frozenset({1}), 1: frozenset()})
        with self.assertRaises(ValueError):
            self.g.compile_lines({0: frozenset({1}), 1: frozenset({0})})

    def test_single_line_agrees_with_every_original_two_bond_offer(self):
        graph = cycle_square(9)
        old = Ports.from_graph(graph)
        atlas = self.g.compile_lines(graph)
        for pair in combinations(old.short_links | old.motifs.keys(), 2):
            state = frozenset(pair)
            self.assertEqual(atlas.offers(state), offers(old, state))

    def test_product_line_recovery_against_coordinate_fibers(self):
        for ns in ((7,), (7, 8), (7, 7, 7)):
            graph = self.g.product_graph(ns)
            groups = {}
            for v in graph:
                for axis in range(len(ns)):
                    key = (axis, v[:axis] + v[axis+1:])
                    groups.setdefault(key, set()).add(v)
            atlas = self.g.compile_lines(graph)
            self.assertEqual({line.vertices for line in atlas.lines},
                             {frozenset(vs) for vs in groups.values()})
            if len(ns) > 1:
                with self.assertRaises(ValueError):
                    Ports.from_graph(graph)
            for v, ns_v in graph.items():
                self.assertEqual(self.g.local_groups(graph, v), frozenset(
                    frozenset(w for w in ns_v if w in vs) for vs in groups.values() if v in vs))

    def test_opaque_integer_relabeling_transports_lines_and_crossing_events(self):
        graph = self.g.product_graph((7, 8))
        labels = list(range(-353, -353+len(graph)))
        Random(421).shuffle(labels)
        rename = dict(zip(graph, labels))
        rg = {rename[v]: frozenset(rename[w] for w in graph[v]) for v in reversed(graph)}
        atlas = self.g.compile_lines(rg)
        src = [(0, 0), (6, 0), (4, 0), (0, 7), (0, 5)]
        o, a, b, c, d = (rename[v] for v in src)
        state = frozenset((link(b, a), link(a, o), link(d, c), link(c, o)))
        self.assertEqual(atlas.offers(state), {
            Move(o, link(a, o), link(o, rename[1, 0])),
            Move(o, link(c, o), link(o, rename[0, 1]))})
        self.assertEqual({line.short for line in atlas.lines},
                         {frozenset(frozenset(rename[v] for v in edge) for edge in line.short)
                          for line in self.g.compile_lines(graph).lines})

    def test_wedge_has_nonconstant_local_rank_and_an_articulation(self):
        graph = self.g.wedge_graph(7, 8)
        atlas = self.g.compile_lines(graph)
        self.assertEqual(sorted(len(line.vertices) for line in atlas.lines), [7, 8])
        shared = set.intersection(*(set(line.vertices) for line in atlas.lines))
        center, = shared
        self.assertEqual(Counter(len(self.g.local_groups(graph, v)) for v in graph), {1: 13, 2: 1})
        self.assertEqual(len(graph[center]), 8)
        left, right = (line.vertices - shared for line in atlas.lines)
        self.assertFalse(any(graph[v] & right for v in left))

    def test_finite_motion_and_joint_orbits(self):
        rows = self.g.report()["fixtures"]
        expected = {"product_7": ({7: 1}, 0), "product_7x8": ({7: 8, 8: 7}, 252),
                    "product_7x7x7": ({7: 147}, 441), "wedge_7_8": ({7: 1, 8: 1}, 252)}
        self.assertEqual({r["name"] for r in rows}, set(expected))
        for row in rows:
            line_lengths, joint = expected[row["name"]]
            self.assertEqual(row["line_length_histogram"], line_lengths)
            self.assertEqual(row["old_guard_accepts"], not joint)
            self.assertEqual(row["single_states"], 21)
            if joint:
                self.assertFalse(row["transverse_target_reached"])
                self.assertGreater(row["joint_same_center_states"], 0)
                self.assertEqual(row["joint_states"], joint)

    def test_free_alternatives_agree_on_ring_and_differ_on_same_wedge(self):
        graph = cycle_square(9)
        atlas = self.g.compile_lines(graph)
        free = self.g.FreeAlternatives(graph)
        for pair in combinations(atlas.lines[0].edges, 2):
            state = frozenset(pair)
            self.assertEqual(free.offers(state), atlas.offers(state))
        row = self.g.junction_control()
        self.assertEqual(row["offers_along_witness"], [3, 1, 3, 1, 1])
        self.assertEqual(row["reachable_outdegrees"], {0: 4, 1: 148, 3: 20})
        self.assertEqual(row["all_phase_a_orientations_positions"], [22, 26])
        self.assertFalse(row["same_line_reaches_other_ring"])
        self.assertEqual(row["offers_along_jam_witness"], [3, 1, 0])

    def test_small_regular_census(self):
        self.assertEqual(self.g.small_regular_census(), {
            5: {"labeled": 1, "accepted": 0}, 6: {"labeled": 15, "accepted": 0},
            7: {"labeled": 465, "accepted": 360}})

    def test_free_rule_is_equivariant_on_every_reachable_wedge_state(self):
        g = self.g
        graph = g.wedge_graph(11, 13)
        names = list(range(341, 341 + len(graph)))
        Random(289).shuffle(names)
        ren = dict(zip(graph, names))
        renamed = {ren[v]: frozenset(ren[w] for w in graph[v]) for v in reversed(graph)}
        free, rr = g.FreeAlternatives(graph), g.FreeAlternatives(renamed)

        def edge(e):
            return frozenset(ren[v] for v in e)

        seed = frozenset((link((0, 9), (0, 0)), link((0, 10), (0, 0))))
        states = g.orbit(free, seed)
        self.assertEqual(len(states), 172)
        for state in states:
            moves = free.offers(state)
            self.assertEqual(rr.offers(frozenset(map(edge, state))),
                             {Move(ren[m.center], edge(m.old), edge(m.new)) for m in moves})


if __name__ == "__main__":
    unittest.main()
