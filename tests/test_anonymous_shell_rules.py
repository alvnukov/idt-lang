"""Exhaustive local controls and fixed-incidence global controls."""

import unittest
from itertools import permutations, product

from scripts import probe_anonymous_shell_rules as p
from scripts.probe_neighbor_twins_flux import K5, OCTAHEDRON, Rule


def relabel_mask(mask: int, perm: tuple[int, ...]) -> int:
    return sum(((mask >> i) & 1) << j for j, i in enumerate(perm))


class AnonymousShellTest(unittest.TestCase):
    def test_centralizer_and_formulas(self) -> None:
        self.assertEqual(p.check_local_class(), (2, 2, 2, 4, 8))
        # Exhaust the microscopic score assignments and port occupancies.
        # The brute centralizer is independent of the explicit flag formulas.
        checked: set[tuple[int, ...]] = set()
        for scores in product(range(4), repeat=4):
            partition = p.partition(scores)
            if partition in checked:
                continue
            checked.add(partition)
            commuting = p.centralizer(partition)
            maps = {
                tuple(p.local_image(rule, scores, m) for m in p.MARKS)
                for rule in range(256)
            }
            self.assertEqual(maps, commuting)
            # Check transport across all port permutations, not just the
            # stabilizer. Representatives of all active flag combinations
            # suffice because inactive bits have no effect on this partition.
            for perm in permutations(range(4)):
                scores2 = tuple(scores[i] for i in perm)
                for flag in (0, 1, 2, 4, 8, 16, 32, 64, 128, 192):
                    for m in p.MARKS:
                        self.assertEqual(
                            relabel_mask(p.local_image(flag, scores, m), perm),
                            p.local_image(flag, scores2, relabel_mask(m, perm)),
                        )
        self.assertEqual(len(checked), 15)

    def test_flag_labels_and_absolute_tag_control(self) -> None:
        for flag, scores, before, after in (
            (1, (0, 0, 0, 0), 3, 12),
            (2, (0, 0, 0, 1), 6, 9),
            (4, (0, 1, 2, 3), 5, 10),
            (8, (0, 0, 1, 1), 3, 12),
            (16, (0, 0, 1, 1), 5, 10),
            (32, (0, 0, 1, 2), 3, 12),
            (64, (0, 0, 1, 2), 5, 6),
            (128, (0, 0, 1, 2), 5, 9),
        ):
            self.assertEqual(p.local_image(flag, scores, before), after)
            self.assertEqual(
                p.local_image(255 ^ flag, scores, before),
                before if flag not in (64, 128) else 15 ^ after,
            )
        for m in range(16):
            if m not in p.MARKS:
                self.assertEqual(p.local_image(255, (1, 2, 1, 3), m), m)
        left, right = (0, 0, 0, 0), (1, 1, 1, 1)
        self.assertEqual(p.partition(left), p.partition(right))
        self.assertNotEqual(p.tagged_control(left, 3), p.tagged_control(right, 3))
        with self.assertRaises(ValueError):
            p.local_image(255, (1, 1, 1, 1, 1), 3)

    def test_census_and_concrete_replays(self) -> None:
        k5, octa = p.census(K5), p.census(OCTAHEDRON)
        self.assertEqual(k5.parity_preserving, 256)
        self.assertEqual(octa.parity_preserving, 128)
        self.assertEqual(octa.transfer_counts, {0: 192, 120: 32, 168: 32})
        self.assertEqual(octa.two_odd_starts, 168)
        self.assertEqual(octa.cheapest, (66, 130))
        for flag in octa.cheapest:
            analysis = octa.examples[flag]
            self.assertEqual(analysis.distances, {6: 72, 7: 48})
            self.assertEqual(analysis.unreachable, 48)
            self.assertEqual(len(analysis.centers), 6)
            self.assertEqual(len(analysis.states), 7)
            for state, center, nxt in zip(
                analysis.states[:-1], analysis.centers, analysis.states[1:], strict=True
            ):
                # Independent incidence-level replay: no cached event table.
                edges = OCTAHEDRON.edges
                star = [i for i, e in enumerate(edges) if center in e]
                scores = tuple(
                    sum(
                        (state >> j) & 1
                        for j, other in enumerate(edges)
                        if j != i and (sum(edges[i]) - center) in other
                    )
                    for i in star
                )
                before = sum(((state >> i) & 1) << j for j, i in enumerate(star))
                out = p.local_image(flag, scores, before)
                self.assertEqual(
                    state
                    ^ sum(
                        1 << i for j, i in enumerate(star) if (before ^ out) & (1 << j)
                    ),
                    nxt,
                )
            masks = tuple(OCTAHEDRON.triangle_parities(s) for s in analysis.states)
            self.assertEqual(masks, analysis.parities)
            self.assertEqual((masks[0].bit_count(), masks[-1].bit_count()), (2, 2))
            self.assertNotEqual(masks[0], masks[-1])

    def test_frozen_neighbor_twins_are_embedded(self) -> None:
        # Original independent event implementation, every start and center.
        rules: tuple[tuple[int, Rule], ...] = ((16 + 64, "T"), (16 + 64 + 128, "F"))
        for graph in (K5, OCTAHEDRON):
            templates = p._templates(graph, graph.half_filled())
            for flag, original in rules:
                for state, row in p._offers(templates, flag).items():
                    for center in range(len(graph.stars)):
                        self.assertEqual(
                            row.get(center), graph.event(state, center, original)
                        )
