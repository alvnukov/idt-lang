"""Behavior of the fixed two-frame classified-sign replay."""

from __future__ import annotations

import subprocess
import sys
import unittest
from dataclasses import replace
from pathlib import Path

from scripts import probe_measured_asi_loop_parity as probe


def diamond() -> tuple[probe.Spin, ...]:
    # Four diagonals with vertices (-23.5,0), (0,23.5), (23.5,0), (0,-23.5).
    return tuple(
        probe.Spin(i, x, y, axis, 1)
        for i, (x, y, axis) in enumerate(
            (
                (-11.75, 11.75, 1),
                (11.75, 11.75, -1),
                (11.75, -11.75, 1),
                (-11.75, -11.75, -1),
            ),
            1,
        )
    )


class MeasuredParityTest(unittest.TestCase):
    def test_crossing_islands_do_not_define_a_planar_face_embedding(self) -> None:
        crossing = [
            probe.Island((0, 0), axis, i, i, False) for i, axis in enumerate((1, -1), 1)
        ]
        with self.assertRaisesRegex(ValueError, "crossing"):
            probe.faces(crossing, 4)

    def test_deposited_frames_and_sensitivity(self) -> None:
        a, b = probe.load_frames()
        joined = probe.match(a, b)
        self.assertEqual((len(a), len(b), len(joined)), (1061, 1063, 1063))
        self.assertEqual(sum(s.flip is True for s in joined), 42)
        for cutoff in (4.0, 5.0):
            result = probe.faces(joined, cutoff)
            self.assertEqual(result.sizes, {8: 232})
            self.assertEqual(result.flips, {0: 174, 1: 45, 2: 13})
            self.assertEqual(result.incomplete, 0)
        tight = probe.faces(joined, 3.0, diagnostic=True)
        self.assertTrue(tight.crossings)
        self.assertEqual(tight.sizes, {8: 213})
        self.assertNotIn("bounded_simple_faces", tight.summary())

    def test_single_flip_changes_parity_despite_row_reordering(self) -> None:
        a = diamond()
        b = tuple(
            replace(s, sign=-1 if i == 0 else 1, row=4 - i) for i, s in enumerate(a)
        )[::-1]
        result = probe.faces(probe.match(a, b), 4.0)
        self.assertEqual(result.flips, {1: 1})
        self.assertEqual({(x, y) for x, y, flip in result.first_odd if flip}, {(1, 4)})
        self.assertEqual(probe.faces(probe.match(b, a), 4.0).flips, {1: 1})

    def test_star_reversal_has_even_parity(self) -> None:
        a = diamond()
        b = tuple(replace(s, sign=-1 if s.row in (1, 2) else 1) for s in a)
        self.assertEqual(probe.faces(probe.match(a, b), 4.0).flips, {2: 1})

    def test_synthetic_swap_between_loop_and_stub_changes_loop_parity(self) -> None:
        # At (0,23.5) the stub (5) and a boundary island (1) exchange signs.
        a = diamond() + (probe.Spin(5, -11.75, 35.25, -1, -1),)
        b = tuple(replace(s, sign=-s.sign if s.row in (1, 5) else s.sign) for s in a)
        result = probe.faces(probe.match(a, b), 4)
        self.assertEqual(result.flips, {1: 1})
        self.assertEqual(sum(s.sign for s in a), sum(s.sign for s in b))
        # Changing the convention for one whole axis in BOTH frames has no effect.
        recoded = [
            tuple(replace(s, sign=s.sign * s.axis) for s in frame) for frame in (a, b)
        ]
        self.assertEqual(
            probe.faces(probe.match(recoded[0], recoded[1]), 4).flips, result.flips
        )

    def test_missing_sign_retains_face_as_inconclusive(self) -> None:
        a = diamond()
        for first, second in ((a, a[:-1]), (a[:-1], a)):
            result = probe.faces(probe.match(first, second), 4.0)
            self.assertEqual(result.sizes, {4: 1})
            self.assertEqual((result.flips, result.incomplete), ({}, 1))

    def test_ambiguous_center_matching_fails_in_both_directions(self) -> None:
        a = diamond()
        b = a + (replace(a[0], row=5, x=a[0].x + 1),)
        for first, second in ((a, b), (b, a)):
            with self.assertRaisesRegex(ValueError, "ambiguous"):
                probe.match(first, second)

    def test_integrity_guard_refuses_altered_bytes(self) -> None:
        path = probe.DATA / "coordinates_000.dat"
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            probe.read_frame(path.read_bytes() + b"\n", probe.HASHES[0])

    def test_optimized_cli_identical(self) -> None:
        path = Path(probe.__file__)
        outputs = [
            subprocess.check_output([sys.executable, *flags, str(path)])
            for flags in ([], ["-O"])
        ]
        self.assertEqual(outputs[0], outputs[1])


if __name__ == "__main__":
    unittest.main()
