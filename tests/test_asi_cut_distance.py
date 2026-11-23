"""Replay the cut-distance certificate and checks against malformed witnesses."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path
from typing import ClassVar

from scripts import probe_asi_cut_distance as probe
from scripts import probe_measured_asi_loop_parity as measured


class CutDistanceTest(unittest.TestCase):
    graph: ClassVar[probe.InferredGraph]

    @classmethod
    def setUpClass(cls) -> None:
        cls.graph = probe.build_graph(measured.match(*measured.load_frames()))

    def test_fixed_witness_certifies_exact_distance(self) -> None:
        self.assertEqual(len(self.graph.face_rows), 232)
        self.assertTrue(all(len(rows) == 8 for rows in self.graph.face_rows))
        self.assertEqual(self.graph.face_rows, tuple(sorted(self.graph.face_rows)))
        documented_face = (8, 9, 10, 14, 35, 36, 59, 61)
        self.assertTrue(
            self.graph.odd_faces()[self.graph.face_rows.index(documented_face)]
        )
        self.assertEqual(sum(self.graph.labels.values()), 42)
        self.assertEqual(sum(self.graph.odd_faces()), 45)
        lower = probe.verify_packing(self.graph, probe.FACE_GROUPS)
        self.assertEqual(lower.minimum, 28)
        self.assertEqual(lower.capacities, (1,) * 24 + (2, 2))
        upper = probe.verify_cut(self.graph, probe.TOGGLE_ROWS)
        self.assertEqual(len(probe.TOGGLE_ROWS), 28)
        self.assertEqual(upper.checked_edges, 1061)
        self.assertEqual(upper.assigned_vertices, 832)
        self.assertEqual(upper.known_components, 3)

    def test_double_counted_or_even_faces_do_not_certify_packing(self) -> None:
        with self.assertRaisesRegex(ValueError, "disjoint"):
            probe.verify_packing(self.graph, ((2,), (2,)))
        with self.assertRaisesRegex(ValueError, "odd"):
            probe.verify_packing(self.graph, ((1,),))

    def test_upper_witness_cannot_skip_a_toggle_or_toggle_an_unknown(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a cut"):
            probe.verify_cut(self.graph, probe.TOGGLE_ROWS[:-1])
        with self.assertRaisesRegex(ValueError, "known"):
            probe.verify_cut(self.graph, (*probe.TOGGLE_ROWS, 1062))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            probe.verify_cut(self.graph, (*probe.TOGGLE_ROWS, probe.TOGGLE_ROWS[0]))

    def test_unknown_rows_are_bridges_not_labels(self) -> None:
        self.assertEqual(probe.unknown_bridge_rows(self.graph), (54, 670))
        # An unmatched edge of a four-edge circuit has an alternate path.
        diamond = [
            measured.Island((-11.75, 11.75), 1, None, 1, None),
            measured.Island((11.75, 11.75), -1, 2, 2, False),
            measured.Island((11.75, -11.75), 1, 3, 3, False),
            measured.Island((-11.75, -11.75), -1, 4, 4, False),
        ]
        with self.assertRaisesRegex(ValueError, "bridge"):
            probe.unknown_bridge_rows(probe.build_graph(diamond))

    def test_time_sliced_classifier_can_report_odd_star_only_trajectory(self) -> None:
        control = probe.asynchronous_countercontrol()
        self.assertEqual(
            control["instantaneous_edge_bits"],
            ((0, 0, 0, 0), (0, 0, 0, 0), (1, 0, 0, 1)),
        )
        self.assertEqual(control["first_sample_times"], (0, 0, 0, 0))
        self.assertEqual(control["second_sample_times"], (2, 2, 2, 1))
        self.assertEqual(control["observed_transition_bits"], (1, 0, 0, 0))
        self.assertEqual(control["instantaneous_cycle_parities"], (0, 0, 0))
        self.assertEqual(control["observed_cycle_parity"], 1)

    def test_optimized_cli_identical(self) -> None:
        path = Path(probe.__file__)
        outputs = [
            subprocess.check_output([sys.executable, *flags, str(path)])
            for flags in ([], ["-O"])
        ]
        self.assertEqual(outputs[0], outputs[1])
        report = json.loads(outputs[0])
        self.assertEqual(report["minimum_known_label_changes"], 28)
        self.assertEqual(report["only_001_unknown_bridge_rows"], [54, 670])


if __name__ == "__main__":
    unittest.main()
