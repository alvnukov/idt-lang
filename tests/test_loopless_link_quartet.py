"""Exhaustive finite controls for link-only quartet gate witnesses."""

import json
import subprocess
import sys
import unittest
from itertools import combinations

from scripts import probe_loopless_link_quartet as probe


class LooplessLinkQuartetTest(unittest.TestCase):
    def test_every_local_offer_against_independent_graph_replay(self) -> None:
        graph = probe.LooplessGraph(4)
        pairs = tuple(combinations(range(4), 2))
        self.assertEqual(graph.edges, pairs)
        for state in range(64):
            bonds = {pair for index, pair in enumerate(pairs) if state >> index & 1}
            for index, edge in enumerate(pairs):
                others = bonds - {edge}
                degree_parity_a = sum(edge[0] in bond for bond in others) % 2
                degree_parity_b = sum(edge[1] in bond for bond in others) % 2
                row = {(0, 0): 1, (1, 1): 2, (0, 1): 4, (1, 0): 4}[
                    degree_parity_a, degree_parity_b
                ]
                reached = [{edge[0]}]
                for _ in range(3):
                    previous = reached[-1]
                    reached.append(
                        previous
                        | {b for a, b in others if a in previous}
                        | {a for a, b in others if b in previous}
                    )
                for radius in (None, 2, 3):
                    for code in range(8):
                        enabled = code & row and (
                            radius is None or edge[1] in reached[radius]
                        )
                        expected = state ^ (1 << index) if enabled else state
                        result = graph.offer(state, index, code, radius)
                        self.assertEqual(result, expected)
                        self.assertEqual(
                            graph.offer(result, index, code, radius), state
                        )

    def test_short_path_excludes_the_candidate_edge(self) -> None:
        graph = probe.LooplessGraph(4)
        path = (1 << 1) | (1 << 4) | (1 << 5)
        self.assertFalse(graph.has_bypass(1, 0, 3))
        self.assertFalse(graph.has_bypass(path | 1, 0, 2))
        self.assertTrue(graph.has_bypass(path, 0, 3))
        self.assertTrue(graph.has_bypass(path | 1, 0, 3))
        for state in range(64):
            for radius in (2, 3):
                before = graph.components(state)
                for edge in range(6):
                    for code in range(8):
                        self.assertEqual(
                            graph.components(graph.offer(state, edge, code, radius)),
                            before,
                        )

    def test_addressed_words_are_clean_on_every_input(self) -> None:
        graph = probe.LooplessGraph(4)
        for witness, length, fixed in (
            (probe.BLANK_OR, 30, 0),
            (probe.BLANK_NAND, 74, 0),
            (probe.GUARDED_OR, 170, 48),
            (probe.GUARDED_NAND, 364, 48),
        ):
            with self.subTest(code=witness.code, radius=witness.radius):
                self.assertEqual(len(witness.word), length)
                self.assertEqual(witness.layout.work_state, fixed)
                permutation = witness.permutation(graph)
                self.assertEqual(sorted(permutation), list(range(64)))
                for data in range(16):
                    want = data ^ 15 if data.bit_count() == 2 else data
                    self.assertEqual(permutation[data | fixed], want | fixed)
                if fixed == 0:
                    self.assertNotIn(5, witness.word)
                    self.assertTrue(
                        any(
                            step & (1 << 4)
                            for data in range(16)
                            for step in graph.trace(data, witness.word, witness.code)
                        )
                    )
        self.assertEqual(
            probe.transpositions(probe.BLANK_OR.permutation(graph)),
            (
                (3, 12),
                (5, 10),
                (6, 9),
                (18, 29),
                (34, 45),
                (51, 60),
                (53, 58),
                (54, 57),
            ),
        )
        self.assertEqual(
            probe.transpositions(probe.GUARDED_OR.permutation(graph)),
            ((7, 13), (51, 60), (53, 58), (54, 57)),
        )
        self.assertEqual(
            probe.transpositions(probe.GUARDED_NAND.permutation(graph)),
            ((13, 14), (51, 60), (53, 58), (54, 57)),
        )

    def test_fixed_work_slice_parity_obstruction(self) -> None:
        supports = probe.fixed_work_supports(probe.LooplessGraph(4))
        self.assertEqual(len(supports), 60 * 8 * 4)
        self.assertEqual(set(supports), {0, 4, 8, 12, 16})
        target = tuple(probe.quartet_target(state) for state in range(16))
        self.assertEqual(probe.transpositions(target), ((3, 12), (5, 10), (6, 9)))

    def test_cli_reports_full_nand_cycles_beyond_the_clean_slice(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "scripts.probe_loopless_link_quartet"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        nand = json.loads(result.stdout)["addressed_witnesses"][1]
        self.assertEqual(nand["clean_inputs"], 16)
        self.assertEqual(
            nand["full_cycles"],
            [
                [3, 12],
                [5, 10],
                [6, 9],
                [16, 30, 22, 18],
                [21, 29],
                [24, 27],
                [33, 41, 45, 47],
                [34, 42],
                [36, 39],
                [51, 60],
                [53, 58],
                [54, 57],
            ],
        )

    def test_distinct_reverse_reachability_layout_counts(self) -> None:
        graph = probe.LooplessGraph(4)
        for code, radius, expected in (
            (6, None, {6: 60}),
            (5, None, {6: 60}),
            (1, None, {0: 54, 2: 6}),
            (2, None, {0: 24, 2: 36}),
            (6, 2, {0: 15, 4: 45}),
            (6, 3, {0: 15, 4: 30, 6: 15}),
            (5, 2, {0: 15, 2: 30, 6: 15}),
        ):
            with self.subTest(code=code, radius=radius):
                self.assertEqual(
                    probe.target_reachability(graph, code, radius), expected
                )

    def test_unaddressed_terminal_map_obstructed_for_every_layout(self) -> None:
        graph = probe.LooplessGraph(4)
        obstructions = probe.equivariance_obstructions(graph)
        self.assertEqual(len(obstructions), 60)
        for layout, witness in obstructions.items():
            layout_states = {
                layout.encode(data) for data in range(16) if data.bit_count() == 2
            }
            self.assertIn(witness.start, layout_states)
            self.assertEqual(witness.target, witness.start ^ layout.data_mask)
            self.assertEqual(
                graph.relabel(witness.start, witness.vertex_map), witness.start
            )
            self.assertEqual(
                graph.relabel(witness.target, witness.vertex_map), witness.moved_target
            )
            self.assertNotEqual(witness.moved_target, witness.target)
        self.assertEqual(graph.relabel(5, (0, 3, 2, 1)), 5)
        self.assertEqual(graph.relabel(10, (0, 3, 2, 1)), 34)

    def test_affine_and_conservation_controls(self) -> None:
        graph = probe.LooplessGraph(4)
        self.assertEqual(probe.affine_codes(graph), (0, 3, 4, 7))
        self.assertEqual(probe.vacuum_quiet_codes(graph), (0, 2, 4, 6))
        self.assertEqual(probe.odd_count_preserving_codes(graph), (0, 4))
        self.assertEqual(probe.link_plus_half_odd_preserving_codes(graph), (0, 2))
        target = tuple(probe.quartet_target(state) for state in range(16))
        self.assertFalse(probe.is_affine(target))


if __name__ == "__main__":
    unittest.main()
