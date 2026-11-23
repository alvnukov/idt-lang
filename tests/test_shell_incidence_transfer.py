"""Fixed-sector census and independent replay controls for the shell transfer."""

import unittest
from collections import deque
from math import comb
from typing import ClassVar

from scripts import probe_shell_incidence_transfer as transfer
from scripts.probe_anonymous_shell_rules import local_image
from scripts.probe_neighbor_twins_flux import Incidence


def replay_event(graph: Incidence, rule: int, state: int, center: int) -> int:
    """Read the incidence directly; do not use the census event tables."""
    star = tuple(i for i, edge in enumerate(graph.edges) if center in edge)
    scores = tuple(
        sum(
            (state >> j) & 1
            for j, edge in enumerate(graph.edges)
            if j != i and sum(graph.edges[i]) - center in edge
        )
        for i in star
    )
    before = sum(((state >> i) & 1) << j for j, i in enumerate(star))
    after = local_image(rule, scores, before)
    return state ^ sum(
        1 << i for j, i in enumerate(star) if (before ^ after) & (1 << j)
    )


class ShellIncidenceTransferTest(unittest.TestCase):
    sectors: ClassVar[tuple[transfer.SectorCensus, ...]]

    @classmethod
    def setUpClass(cls) -> None:
        cls.sectors = transfer.fixed_census()

    def test_exact_labeled_state_denominators_and_counts(self) -> None:
        expected = (
            ("C8^2", 8, 16, 1392, (1072, 1088, 784, 0), (192, 192, 192, 0)),
            (
                "L(K3,3)",
                8,
                18,
                19620,
                (15084, 15804, 11538, 0),
                (5850, 5850, 5850, 0),
            ),
            ("L(K3,3)", 9, 18, 0, (0, 0, 0, 0), (0, 0, 0, 0)),
            (
                "L(K3,3)",
                10,
                18,
                21465,
                (16830, 17856, 12582, 0),
                (5364, 5364, 5364, 0),
            ),
        )
        self.assertEqual(transfer.RULES, (66, 130, 80, 208))
        for row, (name, weight, edges, starts, reachable, immediate) in zip(
            self.sectors, expected, strict=True
        ):
            with self.subTest(graph=name, weight=weight):
                self.assertEqual((row.graph, row.weight), (name, weight))
                self.assertEqual(row.states, comb(edges, weight))
                self.assertEqual(row.two_odd_starts, starts)
                self.assertEqual(sum(row.odd_count_histogram.values()), row.states)
                self.assertEqual(
                    tuple(row.rules[f].reachable for f in transfer.RULES), reachable
                )
                self.assertEqual(
                    tuple(row.rules[f].immediate for f in transfer.RULES), immediate
                )

    def test_odd_rook_sector_is_a_partition_obstruction_not_a_rule_failure(
        self,
    ) -> None:
        rook = transfer.ROOK
        self.assertEqual(
            (len(rook.stars), len(rook.edges), len(rook.triangles)), (9, 18, 6)
        )
        self.assertEqual(
            tuple(
                sum(bool(t & (1 << i)) for t in rook.triangle_masks) for i in range(18)
            ),
            (1,) * 18,
        )
        cycle = transfer.C8_SQUARED
        self.assertEqual(
            (len(cycle.stars), len(cycle.edges), len(cycle.triangles)), (8, 16, 8)
        )
        self.assertFalse(self.sectors[0].triangle_edges_partition)
        self.assertEqual(
            tuple(row.odd_weight_excludes_two_odd for row in self.sectors),
            (False, False, True, False),
        )
        odd = self.sectors[2]
        self.assertEqual(odd.states, 48620)
        self.assertEqual(odd.odd_count_histogram, {1: 8910, 3: 30800, 5: 8910})
        for result in odd.rules.values():
            self.assertIsNone(result.immediate_example)
            self.assertIsNone(result.delayed_example)
            self.assertIsNone(result.blocked_example)

    def test_positive_witness_replay_and_full_star_negative_control(self) -> None:
        visited_intermediate_other_count = False
        for row in self.sectors:
            graph = transfer.C8_SQUARED if row.graph == "C8^2" else transfer.ROOK
            for flag in (66, 130, 80):
                data = row.rules[flag]
                if not row.two_odd_starts:
                    continue
                for path, length in (
                    (data.immediate_example, 1),
                    (data.delayed_example, 2),
                ):
                    if path is None:
                        self.fail(f"missing witness: {row.graph}, {row.weight}, {flag}")
                    self.assertGreaterEqual(len(path.centers), length)
                    self.assertEqual(len(path.states), len(path.centers) + 1)
                    for before, center, after in zip(
                        path.states[:-1], path.centers, path.states[1:], strict=True
                    ):
                        self.assertEqual(
                            replay_event(graph, flag, before, center), after
                        )
                        self.assertEqual(
                            replay_event(graph, flag, after, center), before
                        )
                        self.assertEqual(before.bit_count(), row.weight)
                        self.assertEqual(after.bit_count(), row.weight)
                    masks = tuple(map(graph.triangle_parities, path.states))
                    self.assertEqual(path.syndromes, masks)
                    self.assertEqual(
                        (masks[0].bit_count(), masks[-1].bit_count()), (2, 2)
                    )
                    self.assertNotEqual(masks[0], masks[-1])
                    visited_intermediate_other_count |= any(
                        m.bit_count() != 2 for m in masks
                    )
            control = row.rules[208]
            self.assertGreater(control.nontrivial_events, 0)
            self.assertEqual(control.triangle_changing_events, 0)
            self.assertEqual(row.f_nonstar_events, 0)
            self.assertEqual(row.t_f_enabled_disagreements, 0)
            self.assertIsNone(control.immediate_example)
            self.assertIsNone(control.delayed_example)
        self.assertTrue(visited_intermediate_other_count)

    def test_blocked_start_replays_entire_component(self) -> None:
        row = self.sectors[0]
        graph = transfer.C8_SQUARED
        for flag in (66, 208):
            example = row.rules[flag].blocked_example
            if example is None:
                self.fail(f"missing blocked example for rule {flag}")
            queue = deque([example.state])
            seen = {example.state}
            masks = set()
            while queue:
                state = queue.popleft()
                masks.add(graph.triangle_parities(state))
                for center in range(len(graph.stars)):
                    after = replay_event(graph, flag, state, center)
                    if after not in seen:
                        queue.append(after)
                        seen.add(after)
            self.assertEqual(len(seen), example.component_size)
            self.assertEqual(
                {m for m in masks if m.bit_count() == 2}, {example.syndrome}
            )

    def test_frozen_dependencies_match(self) -> None:
        self.assertEqual(transfer.kernel_digests(), transfer.KERNEL_SHA256)
