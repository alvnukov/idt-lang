"""Finite microscopic controls for the single-relation quartet probe."""

import unittest
from itertools import combinations

from scripts import probe_single_relation_quartet as probe


class SingleRelationQuartetTest(unittest.TestCase):
    def test_pair_rules_against_independent_symmetric_matrix_replay(self) -> None:
        size = 4
        layout = probe.Relation(size)
        pairs = tuple(combinations(range(size), 2))
        for sites in range(1 << size):
            for bond_mask in range(1 << len(pairs)):
                bonds = {pair for idx, pair in enumerate(pairs) if bond_mask >> idx & 1}
                before = probe.State(sites, bond_mask)
                for i, j in pairs:
                    degree_i = sum(i in bond for bond in bonds)
                    degree_j = sum(j in bond for bond in bonds)
                    unlike = bool(sites >> i & 1) != bool(sites >> j & 1)
                    for rule in probe.Rule:
                        comparable = (
                            degree_i == degree_j
                            if rule is probe.Rule.DEGREE
                            else degree_i % 2 == degree_j % 2
                        )
                        new_sites = sites
                        new_bonds = bonds
                        if unlike and comparable:
                            new_bonds = bonds ^ {(i, j)}
                        elif unlike and (i, j) in bonds:
                            new_sites ^= (1 << i) | (1 << j)
                        result = layout.offer(before, (j, i), rule)
                        self.assertEqual(result, layout.state(new_sites, new_bonds))
                        self.assertEqual(layout.offer(result, (i, j), rule), before)

    def test_frozen_parity_word_and_single_edit_controls(self) -> None:
        layout = probe.Relation(4)
        compiler = layout.compile_word(probe.PARITY_WORD)
        for sites in range(16):
            clean = probe.State(sites, 0)
            target = sites ^ 15 if sites.bit_count() == 2 else sites
            self.assertEqual(compiler(clean), probe.State(target, 0))
            _, effective = layout.replay(clean, probe.PARITY_WORD)
            self.assertEqual(effective, (0, 4, 8, 4, 0)[sites.bit_count()])
        self.assertEqual(probe.single_edit_scan(layout), (0, 15, 0, 75))

    def test_sparse_contacts_and_four_site_census_boundary(self) -> None:
        layout = probe.Relation(4, [(2, 0)])
        clean = layout.state(0b1)
        self.assertEqual(
            layout.compile_word(((2, 0), (0, 1)))(clean), layout.state(0b1, [(0, 2)])
        )
        with self.assertRaisesRegex(ValueError, "complete four-site"):
            probe.parity_round_robin(layout)

    def test_laws_and_degree_cap(self) -> None:
        self.assertEqual(probe.audit_offer_laws(probe.Relation(4)), 12_288)
        self.assertEqual(probe.audit_degree_cap(), 73_760)

    def test_clean_orbits_and_branching_separator(self) -> None:
        self.assertEqual(
            probe.clean_orbit(probe.Relation(4), probe.Rule.PARITY),
            probe.CleanOrbit(32, (0, 8)),
        )
        self.assertEqual(
            probe.clean_orbit(probe.Relation(5), probe.Rule.PARITY),
            probe.CleanOrbit(5110, (0, 8, 8, 8, 10, 10, 10, 10, 10, 10)),
        )
        self.assertEqual(
            probe.clean_orbit(probe.Relation(5), probe.Rule.DEGREE),
            probe.CleanOrbit(400, (0, 8, 8, 8, 14, 14, 14, 14, 14, 14)),
        )
        separation = probe.branching_separator()
        layout = probe.Relation(5)
        self.assertEqual(separation.first_offer, 5)
        self.assertEqual(separation.parity, probe.State(0b01001, 0))
        self.assertEqual(separation.degree, layout.state(0b00011, [(1, 2)]))
        self.assertEqual(separation.degrees, (2, 0))

    def test_capped_table_census(self) -> None:
        census = probe.capped_table_census(probe.Relation(4))
        self.assertEqual(
            census.hits,
            ((4, 2, 4), (4, 2, 6), (4, 2, 8), (5, 2, 4), (5, 2, 6), (5, 2, 8)),
        )
        self.assertEqual(
            census.correct_inputs, {0: 711, 2: 297, 4: 330, 6: 54, 10: 330, 16: 6}
        )

    def test_no_degree_word_and_same_value_activity(self) -> None:
        layout = probe.Relation(4)
        census = probe.no_degree_word_census(layout)
        self.assertEqual(census.period, 32)
        self.assertEqual(census.target_motifs, (16,))
        self.assertEqual(census.all_equal_effective, (144, 144))
        self.assertEqual(
            probe.scan_no_degree_controls(layout),
            ((0, 2, 4, 6, 8, 10), (1, 3, 5, 9, 11)),
        )

    def test_round_robin_challenges_use_distinct_observation_contracts(self) -> None:
        layout = probe.Relation(4)
        self.assertEqual(
            probe.parity_round_robin(layout), {None: 480, 15: 48, 16: 96, 17: 96}
        )
        census = probe.no_degree_round_robin(layout)
        self.assertEqual(census, probe.RoundRobinCensus(0, 720, 0))

    def test_non_coprime_round_phase_control(self) -> None:
        self.assertTrue(probe._common_round_exists([(2, 6), (5, 9)]))  # round 14
        self.assertFalse(probe._common_round_exists([(2, 6), (4, 9)]))


if __name__ == "__main__":
    unittest.main()
