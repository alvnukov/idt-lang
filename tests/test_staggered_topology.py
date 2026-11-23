import itertools
import unittest
from collections import deque

from scripts import probe_two_helper_staggered_search as original
from scripts import probe_staggered_topology as probe


class StaggeredTopologyTests(unittest.TestCase):
    def test_holdouts_are_all_labelled_choices_not_a_best_orientation(self):
        rows = list(probe.holdouts(8))
        for name, number, edges in (
            ("Y", 16, ((0, 1), (0, 2), (0, 3))),
            ("double_Y", 64, ((0, 1), (0, 2), (0, 3), (1, 4), (1, 5))),
        ):
            selected = [g for g in rows if g.name == name]
            self.assertEqual(len(selected), number)
            self.assertEqual({g.edges for g in selected}, {edges})
            self.assertEqual(
                {(g.books[0], g.mask) for g in selected},
                set(itertools.product("AB", range(1 << len(edges)))),
            )
        rings = [g for g in rows if g.name.startswith("ring")]
        self.assertEqual([len(g.books) for g in rings], [4, 6, 8])
        for g in rings:
            self.assertEqual(g.ports, g.edges)
            self.assertEqual(g.books, "AB" * (len(g.books) // 2))

    def test_literal_local_moves_match_the_frozen_masks_and_both_generators(self):
        for orientation in range(2):
            g = probe.Graph("edge", "AB", ((0, 1),), orientation)
            _, reference = original.SELECTED[orientation + 1]
            masks = [t for j, t in enumerate(original.TRIPLES) if reference >> j & 1]
            left, right = g.ports[0]
            slots = (2*left, 2*left+1, 2*right, 2*right+1, 4, 5)
            self.assertEqual(set(g.moves), {sum(1 << slots[k] for k in t) for t in masks})
            self.assertEqual(probe.compare(g)["missing_extra"], (0, 0))
            self.assertEqual(probe.spectator_check(g), 2)

    def test_open_controls_match_preexisting_whole_path(self):
        for n in range(2, 6):
            edges = tuple((i, i+1) for i in range(n-1))
            for phase in range(2):
                books = "".join("AB"[(i+phase)%2] for i in range(n))
                mask = sum((books[i] == "B") << i for i in range(n-1))
                result = probe.compare(probe.Graph("path", books, edges, mask))
                self.assertEqual(result["missing_extra"], (0, 0))
                self.assertEqual(result["raw_partition_sha256"], result["native_partition_sha256"])

    def test_ring4_against_independent_tuple_flip_and_logical_edge_search(self):
        g = next(probe.holdouts(4))
        words = list(map("".join, itertools.product("Tab", repeat=4)))
        code = {}
        for w in words:
            bits = []
            for i, c in enumerate(w):
                bits.extend({"a":(0,0), "T":(1,0), "b":(int(i % 2 == 1),1)}[c])
            code[w] = tuple(bits) + (0,0,0,0)
        supports = ((0,1,3),(1,2,3),(2,3,8),(2,8,9),(4,5,9),(4,8,9),
                    (4,5,7),(5,6,7),(6,7,10),(6,10,11),(0,1,11),(0,10,11))
        def flood(seed, neighbours):
            seen, queue = {seed}, deque([seed])
            while queue:
                for y in neighbours(queue.popleft()):
                    if y not in seen:
                        seen.add(y)
                        queue.append(y)
            return seen
        def raw_neighbours(s):
            for tri in supports:
                if len({s[k] for k in tri}) == 1:
                    yield tuple(1-v if i in tri else v for i,v in enumerate(s))
        def native_neighbours(w):
            for i in range(4):
                j = (i+1)%4
                for left, right in (("aa","bb"), ("bb","aa"), ("Ta","aT"), ("aT","Ta")):
                    if w[i]+w[j] == left:
                        v = list(w)
                        v[i], v[j] = right
                        yield "".join(v)
        actual, target = {}, {}
        for w in words:
            if w not in actual:
                group = flood(code[w], raw_neighbours)
                actual.update({v:w for v in words if code[v] in group})
            if w not in target:
                target.update({v:w for v in flood(w, native_neighbours)})
        row = probe.compare(g)
        self.assertEqual(row["missing_extra"], (0,21))
        self.assertEqual(row["native_pairs"], 212)
        self.assertEqual(row["raw_partition_sha256"], probe.partition_digest(words, actual))
        self.assertEqual(row["native_partition_sha256"], probe.partition_digest(words, target))
        states = row["shortest_extra"]["raw"]
        self.assertEqual(len(states)-1, 8)
        u,v = row["shortest_extra"]["words"]
        self.assertNotEqual(target[u], target[v])
        states = [tuple((s >> k) & 1 for k in range(12)) for s in states]
        self.assertEqual((states[0],states[-1]),(code[u],code[v]))
        self.assertTrue(all(b in raw_neighbours(a) for a,b in itertools.pairwise(states)))

    def test_every_monochrome_fork_witness_lifts_with_no_outside_support(self):
        self.assertEqual(set(probe.FORK_PATHS), set(itertools.product(("ABB","BAA"), (0,3))))
        for (b, m), route in probe.FORK_PATHS.items():
            g = probe.Graph("fork",b,((0,1),(0,2)),m)
            u,v = ("Tba","Tab") if not m else ("baT","bTa")
            self.assertEqual((route[0],route[-1]),(g.encode(u),g.encode(v)))
            for x,y in itertools.pairwise(route):
                self.assertIn(x^y,g.moves)
                self.assertIn(x & (x^y),(0,x^y))
            self.assertNotEqual(probe.native(3,g.edges)[1][u],probe.native(3,g.edges)[1][v])

    def test_holdout_regressions_include_both_branch_colors_and_all_y_masks(self):
        expected_y = {"ABBB": (39,15,15,6,15,6,6,6), "BAAA": (39,33,33,46,33,46,46,48)}
        for g in probe.holdouts(6):
            if g.name == "Y":
                self.assertEqual(probe.compare(g)["missing_extra"], (0,expected_y[g.books][g.mask]))
            elif g.name == "ring6":
                r = probe.compare(g)
                self.assertEqual((r["native_pairs"], r["missing_extra"]), (12728, (0,357)))
            elif g.name == "double_Y" and g.mask == 1:
                r = probe.compare(g)
                self.assertEqual((r["native_pairs"], r["missing_extra"]), (11521, (0,1540)))


if __name__ == "__main__":
    unittest.main()
