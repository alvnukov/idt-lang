"""Fixed within-archive transfer: distinguish a null observation from a failed guard."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory

from scripts import probe_apamea_fixed_transfer as transfer
from scripts import probe_measured_asi_loop_parity as measured


def fourfold() -> tuple[measured.Spin, ...]:
    # Diamond plus two short outward stubs at its top junction.
    return tuple(
        measured.Spin(i, x, y, axis, 1)
        for i, (x, y, axis) in enumerate(
            (
                (-11.75, 11.75, 1),
                (11.75, 11.75, -1),
                (11.75, -11.75, 1),
                (-11.75, -11.75, -1),
                (-11.75, 35.25, -1),
                (11.75, 35.25, 1),
            ),
            1,
        )
    )


class FixedTransferTest(unittest.TestCase):
    def test_null_is_usable_but_geometry_and_missing_labels_are_not_nulls(self) -> None:
        a = fourfold()
        null = transfer.analyze_pair(a, a)
        self.assertEqual((null["status"], null["odd_complete_faces"]), ("usable", 0))
        odd = transfer.analyze_pair(a, (replace(a[0], sign=-1), *a[1:]))
        self.assertEqual((odd["status"], odd["odd_complete_faces"]), ("usable", 1))
        for x, y, reason in (
            (a[:4], a[:4], "no_fourfold_vertex"),
            (a, a[1:], "no_complete_faces"),
            (a[:1], a[:1], "no_bounded_simple_faces"),
            (a, a + (replace(a[0], row=7),), "ambiguous_matching"),
        ):
            with self.subTest(reason=reason):
                row = transfer.analyze_pair(x, y)
                self.assertEqual(row["status"], "inconclusive")
                self.assertIn(reason, row["reasons"])
                self.assertIsNone(row["odd_complete_faces"])

    def test_crossing_counts_are_diagnostic_not_a_planar_face_census(self) -> None:
        a = fourfold() + (
            measured.Spin(7, 100, 100, 1, 1),
            measured.Spin(8, 100, 100, -1, 1),
        )
        row = transfer.analyze_pair(a, a)
        self.assertIn("crossed_embedding", row["reasons"])
        self.assertIsNone(row["odd_complete_faces"])
        self.assertIsNotNone(row["geometry"])
        if row["geometry"] is not None:
            self.assertIn("invalid_embedding_walk_diagnostic", row["geometry"])

    def test_missing_file_is_named_and_bad_hash_is_fatal(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            row = transfer.replay_temperature(260, root)
            self.assertEqual(row["reasons"], ["missing_source"])
            self.assertEqual(
                row["missing_members"],
                ["260K/coordinates_000.dat", "260K/coordinates_001.dat"],
            )
            (root / "260K").mkdir()
            for name in transfer.NAMES:
                (root / "260K" / name).write_bytes(b"bad")
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                transfer.replay_temperature(260, root)

    def test_optimized_cli_identical(self) -> None:
        outputs = [
            subprocess.check_output(
                [sys.executable, *flags, str(Path(transfer.__file__))]
            )
            for flags in ([], ["-O"])
        ]
        self.assertEqual(outputs[0], outputs[1])
        data = json.loads(outputs[0])
        self.assertEqual(
            [r["temperature_K"] for r in data["rows"]], [260, 270, 280, 290, 300, 310]
        )

    def test_all_six_deposited_outcomes_including_failed_frames(self) -> None:
        expected = (
            (260, [1037, 1036], 1036, 57, 59, 166, None),
            (
                270,
                [1041, 1040],
                None,
                None,
                None,
                None,
                [
                    "270K/coordinates_000.dat: unrecognized moment/axis encoding at row 6"
                ],
            ),
            (280, [1026, 1031], 1026, 57, 58, 162, None),
            (
                290,
                [1028, 1031],
                None,
                None,
                None,
                None,
                [
                    "290K/coordinates_000.dat: unrecognized moment/axis encoding at row 69",
                    "290K/coordinates_001.dat: unrecognized moment/axis encoding at row 777",
                ],
            ),
            (300, [1017, 1015], 1015, 52, 57, 164, None),
            (310, [1013, 1012], 1011, 48, 47, 175, None),
        )
        for t, counts, matched, rev, odd, even, failures in expected:
            with self.subTest(t=t):
                row = transfer.replay_temperature(t)
                self.assertEqual(row["row_counts"], counts)
                self.assertEqual(
                    (
                        row["matched"],
                        row["reversed_classifications"],
                        row["odd_complete_faces"],
                        row["even_complete_faces"],
                    ),
                    (matched, rev, odd, even),
                )
                if failures:
                    self.assertEqual(row["status"], "inconclusive")
                    self.assertEqual(row["reasons"], ["inapplicable_frame_encoding"])
                    self.assertEqual(row["detail"], failures)
                    self.assertIsNone(row["geometry"])
                else:
                    self.assertEqual((row["status"], row["reasons"]), ("usable", []))
        geometry = transfer.replay_temperature(280)["geometry"]
        self.assertIsNotNone(geometry)
        if geometry is not None:
            self.assertEqual(geometry["components"], 3)
            self.assertEqual(geometry["incomplete"], 3)
            self.assertEqual(
                geometry["flip_count_histogram"], {0: 147, 1: 55, 2: 14, 3: 3, 4: 1}
            )
