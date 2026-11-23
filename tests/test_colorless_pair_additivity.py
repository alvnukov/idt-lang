"""Exact controls for the raw passive pair-additivity finite probe."""

import importlib
import importlib.util
import unittest
from fractions import Fraction as F
from itertools import chain, product

from scripts import probe_colorless_packet_arms as base


# Independent column-permutation representation on (D_L,E_L,D_R,E_R).
# A row value of matrix[j][k] denotes the image of basis column k under offer j.
_STATES = tuple(product((1, 2, 3), repeat=4))
_INDEX = {state: index for index, state in enumerate(_STATES)}
_SWAPS = {(3, 1): (1, 3), (1, 3): (3, 1)}


def _matrix_column(offer, state):
    row = list(state)
    if offer in (2, 3):
        edge = 1 if offer == 2 else 3
        row[edge] = {1: 2, 2: 1, 3: 3}[state[edge]]
    else:
        i, j = {0: (0, 1), 1: (2, 3), 4: (1, 3)}[offer]
        row[i], row[j] = _SWAPS.get((state[i], state[j]), (state[i], state[j]))
    return _INDEX[tuple(row)]


_MATRIX = tuple(tuple(_matrix_column(i, s) for s in _STATES) for i in range(5))
_SPLITTER = (0, 1, 4, 0, 1, 2, 3, 0, 1, 4)
_MIRROR = (1, 0, 3, 2, 4)


def _matrix_apply(columns, word):
    for i in word:
        columns = tuple(_MATRIX[i][x] for x in columns)
    return columns


def _matrix_final(word):
    for d_left, d_right in ((3, 1), (1, 3), (3, 3)):
        stock = tuple(_INDEX[d_left, l, d_right, r] for l, r in product((1, 2), repeat=2))
        yield frozenset(_STATES[index] for index in _matrix_apply(stock, _SPLITTER + word))


def _matrix_calibrated(stock):
    return tuple(sum(s[i] == 3 for s in stock) for i in range(4)) == (1, 1, 1, 1)


class ColorlessPairAdditivityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_colorless_pair_additivity"
        cls.p = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.p, "colorless pair-additivity probe is missing")

    def test_splitter_matches_frozen_single_launches_and_fermion_menu(self):
        p = self.p
        self.assertIs(p.base, base)
        states = p.read_suffix(())
        for arm, raw in enumerate(states[:2]):
            self.assertEqual(raw, frozenset(
                base.replay(base.initial_state(arm, seed, (0, 0)), base.SPLITTER)[-1][:6]
                for seed in base.SOURCE_SEEDS
            ))
        row = p.readout(states)
        self.assertEqual(row.site_counts, ((1, 1, 1, 1), (1, 1, 1, 1), (2, 2, 2, 2)))
        self.assertEqual(row.double_pairs, (0, 1, 1, 1, 1, 0))
        self.assertEqual(row.arm_means, ((F(1, 2), F(1, 2)), (F(1, 2), F(1, 2)), (1, 1)))
        self.assertEqual(row.additivity_gap, (0, 0))
        u, v = p.FERMION_COLUMNS
        self.assertEqual((u, v), ((F(1, 2),) * 4, (F(1, 2), F(1, 2), -F(1, 2), -F(1, 2))))
        self.assertEqual(sum(a * b for a, b in zip(u, v, strict=True)), 0)
        self.assertEqual(p.fermion_menu(), ((F(1, 4),) * 4, (F(1, 4),) * 4,
                                           (0, F(1, 4), F(1, 4), F(1, 4), F(1, 4), 0)))

    def test_earliest_witness_mirror_and_order_controls(self):
        p = self.p
        word = (2, 4)
        witness = p.readout(p.read_suffix(word))
        self.assertTrue(witness.calibrated)
        self.assertEqual(witness.site_counts[-1], (2, 3, 2, 1))
        self.assertEqual(witness.additivity_gap, (F(1, 4), -F(1, 4)))
        mirror = tuple(_MIRROR[i] for i in word)
        mirrored = p.readout(p.read_suffix(mirror))
        self.assertTrue(mirrored.calibrated)
        self.assertEqual(mirrored.site_counts[-1], (2, 1, 2, 3))
        self.assertEqual(mirrored.additivity_gap, (-F(1, 4), F(1, 4)))
        reversed_word = p.readout(p.read_suffix(word[::-1]))
        self.assertFalse(reversed_word.calibrated)
        self.assertEqual(reversed_word.site_counts, ((1, 2, 1, 0), (1, 0, 1, 2), (2, 2, 2, 2)))
        self.assertEqual(reversed_word.additivity_gap, (0, 0))
        for length in (0, 1):
            for offer_word in product(range(5), repeat=length):
                row = p.readout(p.read_suffix(offer_word))
                self.assertFalse(row.calibrated and row.additivity_gap != (0, 0))

    def test_all_short_words_match_independent_permutation_matrix(self):
        p = self.p
        words = (word for length in range(6) for word in product(range(5), repeat=length))
        for word in chain(words, ((2, 4, 1, 3, 1, 4),)):
            rows = p.read_suffix(word)
            projected = tuple(frozenset(tuple(s[i] for i in (0, 1, 3, 4)) for s in raw)
                              for raw in rows)
            self.assertEqual(projected, tuple(_matrix_final(word)), word)
            for n, raw in zip((1, 1, 2), rows, strict=True):
                self.assertEqual(len(raw), 4, word)
                self.assertTrue(all(s.count(3) == n and s[2] == s[5] == 0 for s in raw), word)

    def test_reversible_closure_bfs_certifies_shortest_maximum(self):
        p = self.p
        cert = p.certify()
        self.assertEqual(cert.double_orbit_by_left_count, (2, 9, 2))
        self.assertEqual(cert.left_mean_bound, F(3, 2))
        self.assertEqual(cert.shortest_violation, 2)
        self.assertEqual(cert.shortest_maximum, 6)
        self.assertEqual(tuple(d.distinct_triples for d in cert.depths),
                         (1, 5, 16, 45, 127, 346, 933))
        self.assertTrue(all(d.maximal == 0 for d in cert.depths[:6]))
        self.assertGreater(cert.depths[6].maximal, 0)
        row = p.readout(p.read_suffix((2, 4, 1, 3, 1, 4)))
        self.assertTrue(row.calibrated)
        self.assertEqual(row.site_counts[-1], (2, 4, 1, 1))
        self.assertEqual(row.arm_means[-1], (F(3, 2), F(1, 2)))

    def test_mask_bfs_shells_match_independent_word_enumeration(self):
        cert = self.p.certify()
        visited = set()
        for length, row in enumerate(cert.depths):
            words_here = {tuple(_matrix_final(word)) for word in product(range(5), repeat=length)}
            fresh = words_here - visited
            visited.update(words_here)
            left_counts = [sum(s[i] == 3 for s in pair for i in (0, 1))
                           for u, v, pair in fresh if _matrix_calibrated(u) and _matrix_calibrated(v)]
            self.assertEqual((row.distinct_triples, row.calibrated, row.violating, row.maximal),
                             (len(fresh), len(left_counts), sum(n != 4 for n in left_counts),
                              left_counts.count(6)), length)

    def test_invalid_offer_or_missing_raw_outcome_is_rejected(self):
        p = self.p
        for offer in (-1, 5, False):
            with self.assertRaises(ValueError):
                p.read_suffix((offer,))
        left, right, double = p.read_suffix(())
        with self.assertRaises(AssertionError):
            p.readout((left, right, frozenset(sorted(double)[1:])))

    def test_cli_states_assumptions_and_finite_limit(self):
        p = self.p
        report = p.report()
        self.assertIn("no shutters", report)
        self.assertIn("no postselection", report)
        self.assertIn("unchanged background", report)
        self.assertIn("not a Pauli test", report)
        self.assertIn("not interacting devices", report)
        self.assertIn("5/4", report)
        self.assertIn("3/2", report)
