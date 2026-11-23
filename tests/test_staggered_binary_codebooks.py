"""Controls for the site-dependent two-rail/one-helper unclocked E census."""

from importlib.util import find_spec
from itertools import combinations, product
import unittest


class StaggeredCensusTest(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(find_spec("scripts.probe_staggered_binary_codebooks"),
                             "site-dependent codebook probe is missing")
        from scripts import probe_staggered_binary_codebooks as p
        self.p = p

    def test_quotient_residue_and_colex_index(self):
        p = self.p
        self.assertEqual(len(p.BOOKS), 12)
        self.assertEqual((p.BOOKS[3], p.BOOKS[4]), ((1, 0, 2), (1, 0, 3)))
        self.assertEqual(p.TRIPLES, tuple(sorted(combinations(range(5), 3),
                                                key=lambda t: tuple(reversed(t)))))
        pairs = {(i, j) for i, j in product(range(12), repeat=2) if p.compatible(i, j)}
        self.assertEqual(len(pairs), 16)
        self.assertEqual(sum((i, j) in pairs and (j, k) in pairs
                             for i, j, k in product(range(12), repeat=3)), 28)

    def test_native_and_raw_independent_oracles(self):
        from scripts import probe_unclocked_template_census as reference
        p = self.p
        for n in (2, 3, 4, 5):
            groups = p.native_components(n)
            self.assertEqual({pair for g in groups for pair in combinations(sorted(g), 2)},
                             reference.native_pairs(n))
        uniform = p.BOOKS.index((0, 1, 2))
        for m, h in ((0, 0), (1023, 1), (73, 0), (651, 1)):
            expected = reference.clean_pairs(1, h, p.TRIPLES, m, 3)
            part = p.raw_components((uniform,)*3, ((m, h),)*2)
            self.assertEqual(expected, {pair for g in part for pair in combinations(sorted(g), 2)})

    def test_complete_training_census(self):
        p = self.p
        census = p.training()
        self.assertEqual(len(census['books_by_pair']), 16)
        self.assertEqual(census['compatible_book_triples'], 28)
        self.assertEqual(len(census['survivors']), 72)
        self.assertEqual({w for w, _, _ in census['survivors']}, {(3, 4, 3), (8, 7, 8)})
        for books, left, right in census['survivors']:
            self.assertEqual(p.compare(books, (left, right))[:2], (0, 0))

    def test_orientation_and_stocks_are_frozen_between_sizes(self):
        p = self.p
        left, right = (811, 1), (91, 0)
        self.assertEqual(p.tile((3, 4, 3), left, right, 5, 1),
                         ((4, 3, 4, 3, 4), (right, left, right, left)))
        self.assertEqual(p.tile((3, 4, 3), left, right, 4, 0),
                         ((3, 4, 3, 4), (left, right, left)))

    def test_frozen_holdouts_and_window_obstruction(self):
        p = self.p
        hits = p.training()['survivors']
        self.assertTrue(hasattr(p, 'window_obstruction'), 'window obstruction controls missing')
        obstruction = p.window_obstruction(hits)
        self.assertEqual(obstruction['overlapping_exact_book_windows'], [])
        self.assertEqual(len(obstruction['spectator_collapses_3_to_4']), 6)
        self.assertFalse(any(obstruction['spectator_collapses_3_to_4'].values()))
        self.assertGreater(obstruction['erasure_step_checks_2_to_5'], 0)
        self.assertEqual(obstruction['erasure_violations'], 0)
        # Positive overlap control: train on a fictitious reciprocal book window.
        augmented = (*hits, ((4, 3, 4), (0, 0), (0, 0)))
        self.assertEqual(len(p.window_obstruction(augmented)['overlapping_exact_book_windows']), 2)
        rows = p.heldouts(hits)
        self.assertEqual([r['exact'] for r in rows], [72, 0, 0, 0, 0, 0])
        self.assertEqual([min(h['extra'] for h in r['histogram']) for r in rows],
                         [0, 4, 38, 38, 634, 572])
        self.assertTrue(all(sum(h['count'] for h in r['histogram']) == 72 and
                            all(h['missing'] == 0 for h in r['histogram']) for r in rows))

    def test_site_dependent_local_masks_against_literal_raw_bfs(self):
        p = self.p
        local = p.training()['books_by_pair']
        for pair in ((3, 4), (4, 3), (5, 6)):
            expected = {(m, h) for m, h in product(range(1024), (0, 1))
                        if p.compare(pair, ((m, h),))[:2] == (0, 0)}
            self.assertEqual(set(local[pair]), expected)


if __name__ == '__main__':
    unittest.main()
