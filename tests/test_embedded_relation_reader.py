"""Independent boundary and census checks for the programmed embedded reader."""

import unittest

from scripts import probe_embedded_relation_reader as probe
from scripts.probe_single_relation_quartet import PARITY_WORD, Relation, Rule


class EmbeddedRelationReaderTest(unittest.TestCase):
    def test_all_external_offset_masks_are_reported(self) -> None:
        census = probe.offset_census()
        self.assertEqual(sum(census.histogram.values()), 16)
        self.assertEqual(census.histogram, {2: 4, 4: 4, 6: 6, 16: 2})
        self.assertEqual(census.exact_masks, (0b0000, 0b1111))
        self.assertEqual(len(census.correct_by_mask), 16)

    def test_fixed_external_parity_not_exact_degree_preserves_every_raw_step(
        self,
    ) -> None:
        isolated, embedded = Relation(4), Relation(8)
        outside = ((0, 4), (1, 4), (1, 5), (1, 6), (2, 7), (3, 5))
        exterior_bits = 0b1010_0000
        for sites in range(16):
            before = isolated.state(sites)
            after = embedded.state(exterior_bits | sites, outside)
            exterior_mask = after.bonds
            self.assertEqual(embedded.degrees(after)[:4], (1, 3, 1, 1))
            for pair in probe.quartet_word((0, 1, 2, 3)):
                before = isolated.offer(before, pair, Rule.PARITY)
                after = embedded.offer(after, pair, Rule.PARITY)
                self.assertEqual(after.sites, exterior_bits | before.sites)
                core = [
                    p for idx, p in enumerate(isolated.pairs) if before.bonds >> idx & 1
                ]
                self.assertEqual(
                    after.bonds, embedded.state(after.sites, core).bonds | exterior_mask
                )

    def test_comparator_uses_real_offers_and_preserves_protected_bits(self) -> None:
        census = probe.comparator_census()
        self.assertEqual(
            (census.raw_offers, census.changed, census.unchanged), (18, 128, 128)
        )
        layout = Relation(9)
        bonds = probe.star_bonds(tuple(range(8)), 8)
        m = probe.comparator_word(0, 4, 5, 6, 8)
        self.assertEqual(len(m), 18)
        self.assertEqual(m[-3:], ((0, 8), (4, 8), (0, 8)))
        apply = layout.compile_word(m, Rule.PARITY)
        for sites in range(512):
            if (sites >> 5 & 1) == (sites >> 6 & 1):
                continue
            with self.subTest(sites=sites):
                before = layout.state(sites, bonds)
                expected = sites ^ (
                    0b110_0000 if (sites & 1) != (sites >> 4 & 1) else 0
                )
                self.assertEqual(apply(before), layout.state(expected, bonds))

    def test_record_replays_without_initial_source_copy(self) -> None:
        record = probe.record_census()
        self.assertEqual(record.raw_offers, 51)
        self.assertEqual((record.changed, record.unchanged), (96, 160))
        self.assertEqual(record.initially_unequal_reference, 128)

        layout = Relation(9)
        bonds = probe.star_bonds(tuple(range(8)), 8)
        # 0 is initially zero, 4 is one: the reference is not an old-source copy.
        before = layout.state(0b1_1011_0110, bonds)
        after = layout.compile_word(probe.RECORD_WORD, Rule.PARITY)(before)
        self.assertEqual(after, layout.state(before.sites ^ 0b110_1111, bonds))

    def test_destructive_control_records_change_and_restores_old_source_bit(
        self,
    ) -> None:
        result = probe.destructive_census()
        self.assertEqual(
            (result.raw_offers, result.changed, result.unchanged), (16, 6, 10)
        )
        self.assertEqual(result.source_back_actions, 6)
        layout = Relation(6)
        before = layout.state(0b000110, ((0, 4), (0, 5)))
        source_only = layout.compile_word(PARITY_WORD, Rule.PARITY)(before)
        self.assertEqual(source_only.sites, 0b001001)
        self.assertEqual(
            layout.compile_word(probe.DESTRUCTIVE_WORD, Rule.PARITY)(before),
            layout.state(0b011000, ((0, 4), (0, 5))),
        )

    def test_toffoli_checks_history_and_uncomputes_the_workspace(self) -> None:
        result = probe.toffoli_census()
        self.assertEqual(
            (result.raw_offers, result.changed, result.unchanged), (48, 8, 24)
        )
        layout = Relation(9)
        bonds = probe.star_bonds(tuple(range(8)), 8)
        before = layout.state(0b1_1010_0011, bonds)
        source, mark, uncompute = (
            probe.TOFFOLI_WORD[:15],
            probe.TOFFOLI_WORD[15:33],
            probe.TOFFOLI_WORD[33:],
        )
        flagged = layout.compile_word(source, Rule.PARITY)(before)
        self.assertEqual(flagged, layout.state(before.sites ^ 15, bonds))
        marked = layout.compile_word(mark, Rule.PARITY)(flagged)
        self.assertEqual(marked, layout.state(flagged.sites ^ 96, bonds))
        self.assertEqual(
            layout.compile_word(uncompute, Rule.PARITY)(marked),
            layout.state(before.sites ^ 96, bonds),
        )

    def test_out_of_code_and_odd_bus_witnesses_stay_visible(self) -> None:
        odd_bus, equal_rails = probe.mutation_controls()
        self.assertEqual((odd_bus.cases, odd_bus.failures), (256, 216))
        self.assertEqual((equal_rails.cases, equal_rails.failures), (256, 168))
        self.assertEqual(odd_bus.first_failure.initial.sites, 33)
        self.assertEqual(equal_rails.first_failure.initial.sites, 3)
        self.assertNotEqual(
            odd_bus.first_failure.actual, odd_bus.first_failure.expected
        )
        self.assertNotEqual(
            equal_rails.first_failure.actual, equal_rails.first_failure.expected
        )


if __name__ == "__main__":
    unittest.main()
