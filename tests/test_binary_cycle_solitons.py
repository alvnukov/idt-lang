"""Finite checks of the supplied alternating schedule on raw link occupancy."""

import unittest

from scripts import probe_available_link_logic as original
from scripts import probe_binary_cycle_solitons as probe


def mask(*sites):
    return sum(1 << i for i in sites)


class BinaryCycleSolitonsTest(unittest.TestCase):
    report = None

    def experiment(self):
        if self.__class__.report is None:
            self.__class__.report = probe.experiment()
        return self.__class__.report

    def test_incidence_masks_and_same_matching_involution(self):
        cycle = probe.Cycle(6)
        self.assertEqual(cycle.edges, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)))
        self.assertEqual(cycle.witnesses, original.witness_masks(cycle.edges))
        self.assertEqual(cycle.witnesses[0], mask(1, 5))
        tables = original.offer_tables(cycle.edges)
        for phase in (0, 1):
            matching = tuple(range(phase, cycle.n, 2))
            for state in range(1 << cycle.n):
                with self.subTest(phase=phase, state=state):
                    end = cycle.half_step(state, phase)
                    self.assertEqual(end, original.replay(state, matching, tables))
                    self.assertEqual(end, original.replay(state, reversed(matching), tables))
                    self.assertEqual(cycle.half_step(end, phase), state)
        self.assertEqual(cycle.half_step(mask(1, 5), 0), mask(0, 1, 2, 4, 5))
        for n in (-2, 0, 2, 3, 5):
            with self.assertRaises(ValueError):
                probe.Cycle(n)

    def test_bare_adjacent_pairs_translate_and_read_next_phase(self):
        cycle = probe.Cycle(30)
        for phase in (0, 1):
            for start in range(cycle.n):
                direction = 1 if start % 2 == phase else -1
                expected_counts = (1, 0) if direction == 1 else (0, 1)
                state = mask(start, (start + 1) % cycle.n)
                for step in range(2 * cycle.n + 1):
                    with self.subTest(phase=phase, start=start, step=step):
                        self.assertEqual(
                            state,
                            mask((start + step * direction) % cycle.n,
                                 (start + step * direction + 1) % cycle.n),
                        )
                        current_phase = phase ^ (step % 2)
                        self.assertEqual(cycle.counts(state, current_phase), expected_counts)
                        state = cycle.raw_half_step(state, current_phase)
        self.assertEqual(cycle.counts(mask(4), 0), (1, 1))
        self.assertEqual(cycle.counts(mask(4, 5, 6), 0), (1, 1))

    def test_charge_matches_independent_set_reader(self):
        cycle = probe.Cycle(8)
        for state in range(1 << cycle.n):
            on = {i for i in range(cycle.n) if state >> i & 1}
            isolated = sum((i - 1) % cycle.n not in on and (i + 1) % cycle.n not in on for i in on)
            bonds = {i for i in on if (i + 1) % cycle.n in on}
            for phase in (0, 1):
                right = sum(i % 2 == phase for i in bonds)
                self.assertEqual(cycle.counts(state, phase), (right + isolated, len(bonds) - right + isolated))

    def test_collision_delay_and_frozen_independent_replays(self):
        report = self.experiment()
        collision = report["collision"]
        self.assertEqual((collision["n"], collision["initial_next_phase"], collision["comparison_next_phase"]), (30, 0, 0))
        self.assertEqual(collision["occupied"][0], (4, 5, 15, 16))
        self.assertEqual(collision["occupied"][4:], (
            (8, 9, 11, 12), (9, 10, 11), (10,), (10,), (9, 10, 11),
            (8, 9, 11, 12), (7, 8, 12, 13),
        ))
        self.assertEqual(collision["counts"], ((1, 1),) * 11)
        self.assertEqual(collision["free_at_recovery"], (5, 6, 14, 15))
        self.assertEqual(collision["delay_half_steps"], 2)
        heldout = report["heldout_collision"]
        self.assertEqual((heldout["n"], heldout["initial_next_phase"], heldout["comparison_next_phase"]), (46, 0, 1))
        self.assertEqual(heldout["occupied"][0], (6, 7, 23, 24))
        self.assertEqual(heldout["occupied"][7:], (
            (13, 14, 16, 17), (14, 15, 16), (15,), (15,), (14, 15, 16),
            (13, 14, 16, 17), (12, 13, 17, 18),
        ))
        self.assertEqual(heldout["free_at_recovery"], (10, 11, 19, 20))
        self.assertEqual(heldout["delay_half_steps"], 2)
        translated = report["translated_collision"]
        self.assertEqual(translated["initial_next_phase"], 1)
        self.assertEqual(translated["occupied"], tuple(
            tuple(sorted((i + 23) % 30 for i in frame)) for frame in collision["occupied"]
        ))
        self.assertEqual(translated["delay_half_steps"], 2)

    def test_charge_local_cancellation_and_exhaustive_range(self):
        report = self.experiment()
        self.assertEqual(report["local_cancellation"], {
            "passive_triples": 8, "updated_isolation_triples": 8,
        })
        self.assertEqual(report["exhaustive"], tuple(
            {"n": n, "state_phase_checks": 2 << n} for n in range(4, 17, 2)
        ))
        self.assertEqual(report["cross_control_preserved"], {"OR": 4096, "XOR": 2632, "AND": 1080})

    def test_free_support_aliases_are_distinguished_by_next_phase(self):
        primary = probe.collision(probe.Cycle(30), 4, 15, 0, 10)
        heldout = probe.collision(probe.Cycle(46), 6, 23, 0, 13)
        self.assertEqual(primary["support_only_free_times"], (3, 8))
        self.assertEqual(heldout["support_only_free_times"], (6, 11))
        self.assertEqual(primary["phase_matched_free_time"], 8)
        self.assertEqual(heldout["phase_matched_free_time"], 11)

    def test_phase_is_external_and_single_offers_change_sector(self):
        scheduler = self.experiment()["scheduler"]
        self.assertEqual(scheduler["seed"], (4, 5))
        self.assertEqual(scheduler["even_output"], (5, 6))
        self.assertEqual(scheduler["odd_output"], (3, 4))
        self.assertEqual(scheduler["reflected_even_output"], (3, 4))
        self.assertEqual(scheduler["omitted"], ((4, (4, 5, 6), (1, 1)), (6, (5,), (1, 1))))
        self.assertEqual(scheduler["single_offer_outputs"], ((4, 5), (3, 4, 5), (5,), (4,), (4, 5, 6)))
        self.assertEqual(scheduler["raw_n8_nonempty_component"], 255)
        cycle = probe.Cycle(12)
        for state, phase in ((mask(4, 5), 0), (mask(0, 1, 2, 8, 9), 1)):
            reflected_state = cycle.reflect(state, 9)
            self.assertEqual(cycle.counts(reflected_state, 1 ^ phase), cycle.counts(state, phase)[::-1])
            self.assertEqual(
                cycle.reflect(cycle.raw_half_step(state, phase), 9),
                cycle.raw_half_step(reflected_state, 1 ^ phase),
            )


if __name__ == "__main__":
    unittest.main()
