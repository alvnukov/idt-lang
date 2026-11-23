"""Independent finite controls for the addressed nonempty-neighbor offer."""

import unittest
from collections import Counter
from hashlib import sha256
from itertools import combinations

from scripts import probe_available_link_logic as probe


class AvailableLinkLogicTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = probe.experiment()

    def test_one_toggle_not_one_toggle_per_witness(self):
        edges = tuple(combinations(range(4), 2))
        self.assertEqual(probe.K4, edges)
        generators = probe.offer_tables(edges)
        for state in range(64):
            occupied = {edge for i, edge in enumerate(edges) if state & (1 << i)}
            for i, edge in enumerate(edges):
                witnesses = [e for e in occupied - {edge} if set(e) & set(edge)]
                expected = state ^ (int(bool(witnesses)) << i)
                self.assertEqual(generators[i][state], expected)
                self.assertEqual(generators[i][expected], state)
        # Both witnesses touch endpoint 0; serial XOR would cancel.
        self.assertEqual(generators[0][6], 7)
        self.assertEqual(self.report["multiple_witness"]["serial_xor"], 6)
        self.assertTrue(self.report["multiple_witness"]["serial_xor_linear"])
        self.assertFalse(self.report["multiple_witness"]["available_affine"])

    def test_frozen_word_and_previous_compilers(self):
        witness = self.report["witness"]
        self.assertEqual(
            witness["word"], "3130301020301012013020101201302010120130230201030313"
        )
        self.assertEqual(set(witness["word"]), set("0123"))
        self.assertEqual(witness["whole_state_matches_by_work"], [16, 0, 0, 0])
        self.assertEqual(witness["dirty_states_moved"], 48)
        self.assertEqual(self.report["old_words"]["quartet_matches"], 6)
        self.assertEqual(self.report["old_words"]["cnot_matches"], 3)

    def test_monotone_saturation_certifies_nonempty_orbit(self):
        tables = probe.offer_tables(probe.K4)
        self.assertTrue(all(p[0] == 0 for p in tables))
        for start in range(1, 64):
            path = probe.saturation_word(start, tables)
            self.assertEqual(len(path), 6 - start.bit_count())
            self.assertEqual(probe.replay(start, path, tables), 63)
            self.assertEqual(probe.replay(63, reversed(path), tables), start)

    def test_full_and_restricted_groups(self):
        full = self.report["full_group"]
        self.assertEqual(full["offer_swaps"], [30] * 6)
        self.assertEqual(full["seed_cycle"], [1, 3, 2])
        self.assertEqual(full["ordered_triples"], 63 * 62 * 61)
        self.assertEqual(full["group"], "Alt(63)")
        layouts = self.report["clean_data_layouts"]
        self.assertEqual(
            Counter(row["group"] for row in layouts), {"Sym(15)": 12, "Alt(15)": 3}
        )
        for row in layouts:
            slots = row["data_edge_indices"]
            support = tuple(probe.K4[i] for i in slots)
            degrees = sorted(sum(v in e for e in support) for v in range(4))
            self.assertEqual(
                row["shape"],
                "four_cycle" if degrees == [2] * 4 else "triangle_with_pendant",
            )
            self.assertEqual(row["quartet_reachable"], degrees == [1, 2, 2, 3])
            embedded = [
                sum(1 << e for j, e in enumerate(slots) if k >> j & 1)
                for k in range(16)
            ]
            clean, full_tables = (
                probe.offer_tables(support),
                probe.offer_tables(probe.K4),
            )
            for j, e in enumerate(slots):
                self.assertEqual(
                    [embedded[t] for t in clean[j]],
                    [full_tables[e][k] for k in embedded],
                )
            self.assertEqual(row["ordered_triples"], 15 * 14 * 13)
            self.assertEqual(row["group"] == "Sym(15)", 7 in row["offer_swaps"])
            self.assertEqual(row["group"] == "Alt(15)", row["offer_swaps"] == [6] * 4)
        self.assertEqual(layouts[0]["offer_swaps"], [7, 7, 6, 6])
        self.assertEqual(
            self.report["occupied_pair_unconditional_data_offers"], [True] * 4
        )

    def test_extension_claims_use_distinct_targets(self):
        row = self.report["extensions"]
        self.assertEqual(row["clean_target_swaps"], 3)
        self.assertEqual(row["identity_outside_min_dirty_moved"], 2)
        self.assertTrue(row["four_copy_target_even"])
        self.assertTrue(row["four_copy_reachable_with_all_six_offers"])

    def test_explicit_extension_words_with_independent_set_replay(self):
        rows = self.report["extensions"]["word_certificates"]
        self.assertEqual([len(row["word"]) for row in rows], [88, 264])
        self.assertEqual(
            [sha256(row["word"].encode("ascii")).hexdigest() for row in rows],
            [
                "d2abf882be26e35a111ce2ecedb1b6bb4bf6f17ceffc2d708d2e1d24dcb8d395",
                "3007ed75c266e838747e4704fa763696d65dd04e270f3efddf449ec1a4e48609",
            ],
        )
        edges = tuple(combinations(range(4), 2))
        for idx, row in enumerate(rows):
            for s in range(64):
                active = {e for j, e in enumerate(edges) if s >> j & 1}
                for e in (edges[int(i)] for i in row["word"]):
                    if any(a != e and (e[0] in a or e[1] in a) for a in active):
                        active.symmetric_difference_update({e})
                end = sum(1 << j for j, e in enumerate(edges) if e in active)
                target = s ^ 15 if (s & 15).bit_count() == 2 else s
                if idx == 0 and s >= 16:
                    target = s ^ 1 if s in (16, 17) else s
                self.assertEqual(end, target)

    def test_ambient_leaf_cover_turns_internal_words_into_translations(self):
        row = self.report["ambient_control"]
        self.assertEqual(row["persistent_leaves"], ((0, 4), (1, 5), (2, 6)))
        self.assertEqual(row["unconditional_internal_offers"], 6)
        self.assertEqual(row["whole_internal_inputs_checked"], 64)
        self.assertEqual(row["best_clean_matches_any_internal_word"], 10)

    def test_all_powers_of_all_once_per_edge_sweeps(self):
        self.assertEqual(
            [
                (x["orders"], x["best_clean_matches"])
                for x in self.report["repeated_sweeps"]
            ],
            [(24, 10), (720, 11)],
        )
        for row in self.report["repeated_sweeps"]:
            tables = probe.offer_tables(probe.K4)
            word = row["best_order"] * row["best_power"]
            targets = [s ^ 15 if s.bit_count() == 2 else s for s in range(16)]
            self.assertEqual(
                sum(probe.replay(s, word, tables) == t for s, t in enumerate(targets)),
                row["best_clean_matches"],
            )
