import unittest
from itertools import product

from scripts import probe_staggered_next_event as p
from scripts import probe_two_helper_staggered_search as frozen


class NextEvent(unittest.TestCase):
    def test_frozen_incidence_and_independent_literal_first_cuts(self):
        for n in (2, 3, 4):
            for phase in (0, 1):
                g = p.Path(n, phase)
                books, recipes = frozen.tile(*frozen.SELECTED, n, phase)
                self.assertEqual(set(g.moves), {m for e, (_, k) in enumerate(recipes)
                                                for m in frozen._local_moves(n, e, k)})
                self.assertEqual(set(g.clean), set(frozen.prior.codes(books)))
                for x, w in g.clean.items():
                    # Independent flat-frontier closure, with every clean node absorbing.
                    seen, frontier, ends = {x}, {x}, set()
                    while frontier:
                        reachable = {s ^ m for s in frontier for m in g.moves
                                     if s & m in (0, m)} - seen
                        ends.update(g.clean[s] for s in reachable if s in g.clean)
                        seen |= reachable
                        frontier = reachable - g.clean.keys()
                    self.assertEqual(set(g.first(x)), ends)
                    self.assertTrue(p.native_next(w) <= ends)

    def test_heldout_first_event_counts_and_shortest_literal_witness(self):
        for n, expected in ((2, (0, 0)), (3, (10, 16)), (4, (170, 194)), (5, (1580, 1616))):
            rows = [p.event_audit(n, phase) for phase in (0, 1)]
            self.assertEqual(tuple(r["extra_directed"] for r in rows), expected)
            self.assertFalse(any(r["missing_directed"] for r in rows))
        g = p.Path(3, 1)
        self.assertNotIn("aTa", p.native_next("Tbb"))
        route = g.first(g.encode("Tbb"))["aTa"]
        self.assertEqual(len(route), 4)
        self.assertFalse(any(s in g.clean for s in route[1:-1]))
        for s, t in zip(route, route[1:]):
            self.assertIn(t, g.neighbors(s))

    def test_middle_tag_is_not_a_passage_certificate(self):
        for n in (3, 4, 5):
            for phase, site in product(range(2), range(1, n - 1)):
                g = p.Path(n, phase)
                route = g.bypass(site)
                self.assertEqual((g.clean[route[0]], g.clean[route[-1]]),
                                 ("T" + "a" * (n-1), "a" * (n-1) + "T"))
                self.assertTrue(all((s >> (2*site)) & 3 != 1 for s in route))
                self.assertTrue(all(y in g.neighbors(x) for x,y in zip(route,route[1:])))

    def test_complete_local_histories_indistinguishable_even_at_equal_offer_times(self):
        for n in (3, 4, 7, 12):
            g = p.Path(n, 1)
            a, b, moves = p.source_twins(g)
            self.assertEqual(g.clean[a[0]], "aT" + "a"*(n-2))
            self.assertEqual(g.clean[b[0]], "a"*n)
            self.assertEqual(a[0], a[1])  # emission offer stutters only here
            self.assertNotEqual(b[0], b[1])
            self.assertEqual(len(moves), 1 + 2*(n-2))
            self.assertTrue(all(m in g.moves for m in moves))
            for trace in (a,b):
                self.assertEqual([p.offer(x,m) for x,m in zip(trace,moves)], trace[1:])
            diff = 3 << (2*n)
            self.assertTrue(all(x ^ y == diff for x,y in zip(a[1:],b[1:])))
            # Equality of entire exterior traces also covers deterministic memory of those traces.
            hidden = diff | (3 << 2)
            self.assertEqual([x & ~hidden for x in a], [x & ~hidden for x in b])
            self.assertNotEqual(a[-1] & diff,b[-1] & diff)
            self.assertEqual(g.clean[a[-1]], "a"*(n-1)+"T")
            self.assertNotIn(b[-1],g.clean)

    def test_invalid_barrier_or_wrong_emitter_phase(self):
        with self.assertRaises(ValueError):
            p.Path(3, 0).bypass(0)
        with self.assertRaises(ValueError):
            p.source_twins(p.Path(3, 0))
        with self.assertRaises(ValueError):
            p.Path(2, 2)
