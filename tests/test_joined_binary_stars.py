"""Whole-incidence and whole-history controls for the joined binary stars."""

import unittest

from scripts import probe_available_link_logic as base
from scripts import probe_joined_binary_stars as joined


class JoinedBinaryStarsTest(unittest.TestCase):
    def test_every_short_raw_state_against_original_offer_tables(self):
        g = joined.Wiring(2, 3)
        # A and B are two degree-three vertices, never identified; path slots
        # 4,5,6 form their only literal 3-link bridge.
        self.assertEqual(tuple(map(len, g.paths)), (2, 2, 3, 2, 2))
        self.assertEqual(g.edges[0][0], g.edges[4][0])
        self.assertEqual(g.edges[6][1], g.edges[7][0])
        self.assertNotEqual(g.edges[0][0], g.edges[7][0])
        self.assertEqual(len({v for edge in g.edges for v in edge}), 12)
        tables = base.offer_tables(g.edges)
        for a in range(3):
            for b in range(3):
                phases = g.phases(a, b)
                expected = [[], [], [], [1, 3, 5, 8, 10]]
                for edge, color in (
                    (0, -a),
                    (2, 1 - a),
                    (4, 2 - a),
                    (6, 2 - b),
                    (7, -b),
                    (9, 1 - b),
                ):
                    expected[color % 3].append(edge)
                self.assertEqual(phases, tuple(tuple(p) for p in expected))
                for x in range(1 << len(g.edges)):
                    y = x
                    expected_mids = []
                    for phase in phases:
                        y = base.replay(y, reversed(phase), tables)
                        expected_mids.append(y)
                    self.assertEqual(g.sweep(x, phases), tuple(expected_mids))

    def test_passage_requires_clean_direction_and_consumes_every_bit(self):
        self.assertEqual(joined.passage(3 << 5, 3 << 3, -2), (5,))
        for x, y, d in (
            (3 << 4, 3 << 2, -2),
            (15 << 4, 15 << 6, 2),
            (1 << 4, 1 << 6, 2),
            (3 << 4, 3 << 4, 2),
            (3 << 4, (3 << 6) | 1, 2),
        ):
            with self.assertRaises(ValueError):
                joined.passage(x, y, d)

    def test_isolated_mean_and_nonlinear_two_holes(self):
        row = joined.isolated()
        self.assertEqual(row["order_rows"], 24)
        self.assertEqual(row["mean_times_three"][7], (3, 3, 3))
        self.assertEqual(
            row["hole_residual_times_three"],
            {7 - (1 << i): (0, 0, 0) for i in range(3)}
            | {1 << i: (1, 1, 1) for i in range(3)},
        )

    def test_two_offsets_absolute_and_both_passages(self):
        r = joined.experiment()
        self.assertEqual(
            r["composed_prediction_times_nine"], [(-4, -4, 2), (-4, -4, 2), (2, 2, -1)]
        )
        for offset, absolute, dr in [
            (47, 11, [(-5, -5, 1), (-6, -6, 0), (1, 1, -2)]),
            (49, 10, [(-5, -5, 1), (-4, -4, 2), (5, 5, 2)]),
        ]:
            row = r["offsets"][offset]
            self.assertEqual(row["b_reference_times_nine"], (absolute,) * 3)
            self.assertEqual(row["b_deltas_times_nine"], dr)
            self.assertEqual(
                row["first_pass_totals"],
                {
                    7: (9, 9, 11, 11, 11),
                    6: (12, 3, 12, 6, 6),
                    5: (3, 12, 11, 5, 5),
                    3: (3, 3, 9, 12, 12),
                }
                if offset == 47
                else {
                    7: (9, 9, 10, 10, 10),
                    6: (12, 3, 11, 5, 5),
                    5: (3, 12, 12, 6, 6),
                    3: (3, 3, 12, 15, 15),
                },
            )
            self.assertEqual(len(row["histories"]), 36)
            self.assertEqual(
                {(h["a"], h["b"], h["mask"]) for h in row["histories"]},
                {(a, b, m) for a in range(3) for b in range(3) for m in (7, 6, 5, 3)},
            )
            for h in row["histories"]:
                first, last = h["at35"], h["at65"]
                for t in (35, 65):
                    for p, starts in enumerate(h[f"at{t}"]):
                        d = -2 if p == 2 else 2
                        self.assertEqual(
                            h[f"at{t + 1}"][p], tuple(j + d for j in starts)
                        )
                self.assertFalse(last[2])
                for i in (0, 1):
                    self.assertEqual(sum(j < 80 for j in last[i]), len(first[2]))
                    self.assertEqual(
                        tuple(j for j in last[i] if j > 80),
                        tuple(j + 60 for j in first[i]),
                    )


if __name__ == "__main__":
    unittest.main()
