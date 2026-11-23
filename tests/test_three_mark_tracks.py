"""Independent microscopic replays and falsifying controls for the track probe."""

import unittest

from scripts import probe_anonymous_shell_rules as shell
from scripts import probe_three_mark_tracks as tracks
from scripts.probe_neighbor_twins_flux import K5, OCTAHEDRON


class ThreeMarkGeometryTest(unittest.TestCase):
    def test_path_chord_predictor_agrees_with_raw_microscopic_rule(self) -> None:
        for name, graph in tracks.fixtures().items():
            with self.subTest(graph=name):
                states = tracks.weight_states(graph, 3)
                raw = shell._offers(shell._templates(graph, states), 16)
                self.assertEqual(tracks.chord_offers(graph, states), raw)
                census = tracks.weight_three_census(graph)
                self.assertEqual(census.states, len(states))
                self.assertLessEqual(census.max_degree, 2)

    def test_non_circulant_controls_and_cycle_census(self) -> None:
        fixtures = tracks.fixtures()
        for name, states, walks in (("K4,4", 560, {}), ("3x3-rook", 816, {2: 36})):
            with self.subTest(graph=name):
                census = tracks.weight_three_census(fixtures[name])
                self.assertEqual(census.states, states)
                self.assertEqual(census.isolates, states - 2 * walks.get(2, 0))
                self.assertEqual(census.walks, walks)
                self.assertEqual(census.cycles, {})
        self.assertIs(fixtures["K5"], K5)
        self.assertIs(fixtures["octahedron"], OCTAHEDRON)
        for n in tracks.CYCLE_SIZES:
            with self.subTest(n=n):
                census = tracks.weight_three_census(tracks.cycle_square(n))
                self.assertEqual(census.walks, {2: 3 * n, 3: n})
                self.assertEqual(census.cycles, {n: 1})
                self.assertEqual(census.isolates, census.states - 10 * n)

    def test_missing_chord_and_extra_flag_are_detected(self) -> None:
        graph = tracks.cycle_square(7)
        states = tracks.weight_states(graph, 3)
        flagged = shell._offers(shell._templates(graph, states), 17)
        with self.assertRaisesRegex(ValueError, "path/chord"):
            tracks.check_chord_offers(graph, flagged)
        original = tracks.chord_offers(graph, states)
        victim = next(state for state, moves in original.items() if moves)
        original[victim].pop(next(iter(original[victim])))
        with self.assertRaisesRegex(ValueError, "path/chord"):
            tracks.check_chord_offers(graph, original)


class SeamTrackTest(unittest.TestCase):
    def test_single_seam_boundaries_readouts_and_all_256_rules(self) -> None:
        for n in (5, 6):
            track = tracks.seam_track(n)
            self.assertNotEqual(track.graph.triangle_parities(track.seams[0]), 0)
        for n in tracks.CYCLE_SIZES:
            with self.subTest(n=n):
                track = tracks.seam_track(n)
                census = tracks.seam_census(track)
                self.assertEqual(
                    census.moving_rules, tuple(r for r in range(256) if r & 16)
                )
                self.assertEqual(
                    census.frozen_rules, tuple(r for r in range(256) if not r & 16)
                )
                self.assertEqual(census.triangle_parity, 0)
                self.assertEqual(census.winding_parity, 1)
                self.assertEqual(census.circuit_rank, n + 1)
                for i in range(n):
                    self.assertEqual(
                        track.seams[i] ^ track.seams[(i + 1) % n],
                        tracks.cut_mask(track.graph, {(i + 2) % n}),
                    )

    def test_reflection_stabilizes_seam_and_swaps_both_offers(self) -> None:
        track = tracks.seam_track(16)
        i = 5
        row = tracks.raw_row(track.graph, track.seams[i], 16)
        reflected = tracks.transport_row(track.graph, row, -1, 2 * i + 3)
        self.assertEqual(reflected, row)
        self.assertEqual(set(row), {i + 1, i + 2})
        self.assertEqual(row[i + 1], track.seams[i - 1])
        self.assertEqual(row[i + 2], track.seams[i + 1])
        mutated = {i + 1: row[i + 2], i + 2: row[i + 1]}
        with self.assertRaisesRegex(ValueError, "single-seam"):
            tracks.check_seam_row(track, i, 16, mutated)


class PairTrackTest(unittest.TestCase):
    def test_pair_census_all_positions_and_bound_cycle(self) -> None:
        for n in tracks.PAIR_SIZES:
            with self.subTest(n=n):
                panel = tracks.pair_panel(tracks.seam_track(n))
                self.assertEqual(panel.pairs, n * (n - 1) // 2)
                for rule in (16, 80, 208):
                    self.assertEqual(
                        panel.rule_degrees[rule],
                        {
                            gap: (0 if gap < 4 else 2 if gap == 4 else 4)
                            for gap in range(1, n // 2 + 1)
                        },
                    )
                for rule in (66, 130):
                    self.assertEqual(
                        panel.rule_degrees[rule],
                        {
                            gap: (2 if gap in (3, 4) else 0)
                            for gap in range(1, n // 2 + 1)
                        },
                    )
                    self.assertEqual(panel.nontrivial_component_sizes[rule], (2 * n,))

    def test_cut_and_equal_weight_readout_collision(self) -> None:
        track = tracks.seam_track(16)
        graph, seams = track.graph, track.seams
        basis = tracks.fundamental_circuits(graph)
        close, distant = seams[0] ^ seams[3], seams[0] ^ seams[5]
        self.assertEqual(tracks.cut_mask(graph, {2, 3, 4}), close)
        self.assertEqual(tracks.cut_mask(graph, {2, 3, 4, 5, 6}), distant)
        self.assertEqual(close.bit_count(), 6)
        self.assertEqual(distant.bit_count(), 6)
        self.assertEqual(
            [tracks.circuit_signature(x, basis) for x in (0, close, distant)], [0, 0, 0]
        )
        self.assertEqual(tracks.raw_row(graph, 0, 66), {})
        self.assertEqual(tracks.raw_row(graph, distant, 66), {})
        self.assertEqual(
            tracks.raw_row(graph, close, 66),
            {1: seams[15] ^ seams[3], 5: seams[0] ^ seams[4]},
        )
        with self.assertRaisesRegex(ValueError, "pair-seam"):
            tracks.check_pair_row(track, 0, 3, 66, tracks.raw_row(graph, close, 16))
        # Equal degree, weight and circuit signature cannot repair a wrong target.
        wrong = {1: seams[14] ^ seams[3], 5: seams[0] ^ seams[4]}
        with self.assertRaisesRegex(ValueError, "pair-seam"):
            tracks.check_pair_row(track, 0, 3, 66, wrong)


if __name__ == "__main__":
    unittest.main()
