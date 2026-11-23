"""Independent coordinate witnesses for the incidence-only conserved-bond rule."""

import importlib
import unittest
from itertools import combinations
from math import gcd

from scripts.probe_binary_shape_gait import cycle_square, link


def phases(n, i, h):
    def bond(a, b):
        return link((i + h*a) % n, (i + h*b) % n)
    return (frozenset((bond(0, 2), bond(2, 3))),
            frozenset((bond(0, 2), bond(3, 4))),
            frozenset((bond(2, 4), bond(3, 4))))


class ConservedBondTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(importlib.util.find_spec("scripts.probe_conserved_bond_gait"),
                             "conserved raw rule is not implemented")
        self.rule = importlib.import_module("scripts.probe_conserved_bond_gait")

    def test_each_phase_and_each_heading_without_scheduled_centers(self):
        for n in (7, 8, 9, 12, 17):
            ports = self.rule.Ports.from_graph(cycle_square(n))
            actual = {}
            for h in (-1, 1):
                for i in range(n):
                    a, b, c = phases(n, i, h)
                    for src, offset, dst in ((a, 3, b), (b, 2, c), (c, 4, phases(n, i+2*h, h)[0])):
                        self.assertNotIn(src, actual)
                        move, = self.rule.offers(ports, src)
                        self.assertEqual((move.center, move.apply(src)), ((i+offset*h) % n, dst))
                        self.assertEqual(move.old in ports.short_links, move.new in ports.short_links)
                        actual[src] = dst
            self.assertEqual(len(actual), 6*n)
            self.assertEqual(set(actual), set(actual.values()))

    def test_complete_two_bond_shell_against_independent_sector_membership(self):
        for n in (7, 8, 11):
            graph = cycle_square(n)
            ports = self.rule.Ports.from_graph(graph)
            edges = {link(v, w) for v in graph for w in graph[v]}
            expected = {s for i in graph for h in (-1, 1) for s in phases(n, i, h)}
            for pair in combinations(edges, 2):
                state = frozenset(pair)
                self.assertEqual(len(self.rule.offers(ports, state)), int(state in expected))

    def test_arbitrary_opaque_relabeling_including_same_center_competition(self):
        n = 16
        names = [object() for _ in range(n)]
        graph = cycle_square(n)
        renamed = {names[v]: frozenset(names[w] for w in graph[v]) for v in reversed(graph)}
        ports = self.rule.Ports.from_graph(renamed)
        a, _, _ = phases(n, 0, 1)
        _, b, _ = phases(n, 1, 1)
        state = a | b
        def translate(edges):
            return frozenset(frozenset(names[v] for v in e) for e in edges)
        moves = self.rule.offers(ports, translate(state))
        expected = {(names[3], translate((old,)), translate((new,))) for old, new in
                    ((link(1, 3), link(3, 5)), (link(2, 3), link(3, 4)))}
        self.assertEqual({(m.center, frozenset((m.old,)), frozenset((m.new,))) for m in moves},
                         expected)
        self.assertEqual(len({m.apply(translate(state)) for m in moves}), 2)

    def test_close_but_vertex_disjoint_seeds_offer_a_cross_pair_event(self):
        n = 16
        ports = self.rule.Ports.from_graph(cycle_square(n))
        a = phases(n, 0, 1)[0]
        b = phases(n, 4, 1)[0]
        self.assertTrue(frozenset.union(*a).isdisjoint(frozenset.union(*b)))
        self.assertEqual({(m.center, m.old, m.new) for m in self.rule.offers(ports, a | b)},
                         {(3, link(2, 3), link(3, 4)), (7, link(6, 7), link(7, 8)),
                          (4, link(4, 6), link(2, 4))})

    def test_geometry_failure_and_finite_report(self):
        for n in (5, 6):
            with self.assertRaises(ValueError):
                self.rule.Ports.from_graph(cycle_square(n))
        result = self.rule.report()
        for row in result["clean_sectors"]:
            n = row["n"]
            self.assertEqual(row["active"], 6*n)
            self.assertEqual(row["cycle_lengths"], [3*n//gcd(n, 2)] * (2*gcd(n, 2)))
            self.assertEqual(row["idle"] + row["active"], n*(2*n-1))
        self.assertEqual(result["controls"]["separated"]["centers"], [3, 11])
        self.assertEqual(result["controls"]["all_destinations_occupied"],
                         {"marked_bonds": 32, "successors": 0})

    def test_every_c7_word_against_independent_mask_oracle(self):
        n = 7
        graph = cycle_square(n)
        ports = self.rule.Ports.from_graph(graph)
        edges = list({link(v, w) for v in graph for w in graph[v]})
        bits = {e: 1 << j for j, e in enumerate(edges)}
        motifs = []
        for h in (-1, 1):
            for i in graph:
                a, b, c = phases(n, i, h)
                for src, dst in ((a, b), (b, c), (c, phases(n, i+2*h, h)[0])):
                    old, = src - dst
                    new, = dst - src
                    center, = old & new
                    motifs.append((sum(bits[e] for e in src), bits[new], (center, old, new)))
        for word in range(1 << len(edges)):
            state = frozenset(e for e in edges if word & bits[e])
            actual = {(m.center, m.old, m.new) for m in self.rule.offers(ports, state)}
            expected = {event for required, blocked, event in motifs
                        if word & required == required and not word & blocked}
            self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
