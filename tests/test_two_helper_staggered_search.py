import itertools
import os
import unittest
from collections import Counter

from scripts import probe_staggered_binary_codebooks as prior
from scripts import probe_two_helper_staggered_search as probe


class TwoHelperStaggeredTests(unittest.TestCase):
    @unittest.skipUnless(
        os.environ.get("IDT_FULL_STAGGERED") == "1", "opt-in full census"
    )
    def test_full_census_regression(self):
        totals = Counter()
        staged = [0, 0, 0]
        refs = fits = 0
        for books in probe.BOOK_PAIRS:
            if books[0] > books[1]:
                continue
            recipes, mirrored, _, _ = probe.search_family(books, False)
            self.assertEqual(mirrored, {(False, False): len(recipes)})
            recipes, mixed, _, hits = probe.search_family(books, True)
            refs += 1
            fits += len(recipes)
            totals.update(mixed)
            rows = probe.heldouts(books, hits)
            for i, row in enumerate(rows):
                staged[i] += row["both_exact_ordered"]
            if books == (3, 4):
                self.assertEqual(
                    probe.digest(recipes),
                    "fa82754137e7fa48f1351ea62bde94677b39f1f2cf46c6c86a3d2f8c1ecec0ee",
                )
                self.assertEqual(
                    probe.digest(hits),
                    "09a6fa3021958628e526707279f930dff68a896622d598643a2f2e33760937db",
                )
                self.assertEqual(
                    rows[-1]["both_survivor_sha256"],
                    "51729d4f641f24eb72ecbb9237a250b168064f48d684265bd10cfb940373e89a",
                )
        self.assertEqual((refs, fits), (9, 1204))
        self.assertEqual(
            totals,
            {
                (False, False): 201908,
                (False, True): 110,
                (True, False): 110,
                (True, True): 24,
            },
        )
        self.assertEqual(staged, [12, 12, 12])

    def test_minimal_masks_match_independent_one_helper_partitions(self):
        fits = prior.local_fits()
        books = (1, 8)
        for stock in (0, 1):
            literal = [
                sum(
                    1 << probe.TRIPLES.index(prior.TRIPLES[j])
                    for j in range(10)
                    if m >> j & 1
                )
                for m, s in fits[books]
                if s == stock
            ]
            expected = {
                m for m in literal if not any(q != m and q & m == q for q in literal)
            }
            allowed = tuple(i for i, tri in enumerate(probe.TRIPLES) if 5 not in tri)
            self.assertEqual(set(probe.minima(books, stock, allowed)), expected)

    def test_complete_relation_matches_previous_oriented_bfs(self):
        books = (3, 2, 3)
        for left, right in (
            ((379, 1), (661, 0)),
            ((57, 0), (940, 1)),
            ((1023, 1), (1023, 0)),
        ):

            def convert(recipe):
                m, s = recipe
                return s, sum(
                    1 << probe.TRIPLES.index(t)
                    for j, t in enumerate(prior.TRIPLES)
                    if m >> j & 1
                )

            measured = probe.compare(books, (convert(left), convert(right)))
            self.assertEqual(measured[:2], prior.compare(books, (left, right))[:2])

    def test_mirror_data_ports_preserves_stock_and_reverses_ternary_words(self):
        books = (1, 8)
        m = sum(1 << j for j in (1, 4, 6, 17))
        self.assertEqual(probe.mirror(probe.mirror(m)), m)
        self.assertEqual(
            probe.compare(books, ((1, m),))[:2],
            probe.compare(tuple(reversed(books)), ((1, probe.mirror(m)),))[:2],
        )

    def test_window_verdict_matches_full_bfs_on_minimal_and_superset_masks(self):
        books = (3, 4)
        a, b, *rest = probe.minimal_recipes(books)
        for x, y in ((a, b), (rest[-1], a), ((1, (1 << 20) - 1), a)):
            ba = y[0], probe.mirror(y[1])
            for phase in (0, 1):
                inputs = probe.tile(books, x, ba, 3, phase)
                missing, extra, _ = probe.compare(*inputs)
                self.assertEqual(missing, 0)
                self.assertEqual(probe.window_exact(*inputs), extra == 0)

    def test_selected_recipe_on_whole_paths_in_both_phases(self):
        counts = (2, 21, 155, 1037, 6660)
        for n, expected in enumerate(counts, 2):
            self.assertEqual(
                sum(prior.pairs_in(len(g)) for g in prior.native_components(n)),
                expected,
            )
            for phase in (0, 1):
                self.assertEqual(
                    probe.compare(*probe.tile(*probe.SELECTED, n, phase)), (0, 0, None)
                )

    def test_complete_local_invariant_and_nontrivial_negative_control(self):
        self.assertEqual(probe.invariant_links(), ((4, 0), (32, 0)))
        perturbed = ("", "ba", "", "ta")
        self.assertGreater(probe.invariant_links(helper_words=perturbed)[1][1], 0)

    def test_each_native_generator_has_a_literal_clean_endpoint_path(self):
        for phase, paths in enumerate(probe.GENERATOR_PATHS):
            pair, (_, mask) = (
                probe.tile(*probe.SELECTED, 2, phase)[0],
                probe.SELECTED[1 + phase],
            )
            clean = dict(zip(prior.words(2), prior.codes(pair)))
            self.assertEqual(set(paths), {("aa", "bb"), ("Ta", "aT")})
            for (u, v), route in paths.items():
                self.assertEqual((route[0], route[-1]), (clean[u], clean[v]))
                for x, y in itertools.pairwise(route):
                    change = x ^ y
                    slots = tuple(i for i in range(6) if change >> i & 1)
                    self.assertEqual(len(slots), 3)
                    self.assertTrue((mask >> probe.TRIPLES.index(slots)) & 1)
                    self.assertIn(x & change, (0, change))

    def test_group_separates_literal_native_components_at_fixed_length(self):
        self.assertEqual(probe.normal("TabbatTt"), probe.normal("aa"))
        self.assertNotEqual(probe.normal("Tb"), probe.normal("bT"))
        self.assertEqual(probe.normal("aa"), probe.normal(""))
        for n in range(2, 8):
            groups = prior.native_components(n)
            signatures = [{probe.normal(w) for w in g} for g in groups]
            self.assertTrue(all(len(v) == 1 for v in signatures))
            self.assertEqual(len(set.union(*signatures)), len(groups))
