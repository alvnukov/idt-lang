"""Exact incidence bounds on the accepted Apamea replay only."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts import probe_apamea_fixed_transfer as transfer
from scripts import probe_apamea_vertex_support as support
from scripts import probe_measured_asi_loop_parity as measured


class IncidenceCertificateTest(unittest.TestCase):
    def test_star_needs_one_center_not_one_per_edge(self) -> None:
        edges = ((0, 1), (0, 2), (0, 3))
        cert = support.build_certificate(edges)
        self.assertEqual(cert.cover, (0,))
        self.assertEqual(support.verify_certificate(edges, cert), 1)

    def test_non_tight_triangle_cannot_certify_an_exact_minimum(self) -> None:
        edges = ((0, 1), (0, 2), (1, 2))
        cert = support.CoverCertificate(matching=((0, 1),), cover=(0, 1))
        with self.assertRaisesRegex(ValueError, "bounds do not agree"):
            support.verify_certificate(edges, cert)
        with self.assertRaisesRegex(ValueError, "not bipartite"):
            support.build_certificate(edges)

    def test_invalid_edge_input_and_certificate_witnesses_are_rejected(self) -> None:
        for invalid in (((0, 0),), ((0, 1), (1, 0)), ((-1, 2),)):
            with self.subTest(edges=invalid), self.assertRaises(ValueError):
                support.build_certificate(invalid)
        edges = ((0, 1), (0, 2), (3, 4))
        for cert in (
            support.CoverCertificate(((0, 1), (0, 2)), (0, 3)),
            support.CoverCertificate(((0, 1), (3, 5)), (0, 3)),
            support.CoverCertificate(((0, 1), (3, 4)), (3, 4)),
            support.CoverCertificate(((0, 1), (3, 4)), (0, 5)),
            support.CoverCertificate(((0, 1), (3, 4)), (0, 0, 3)),
        ):
            with self.subTest(cert=cert), self.assertRaises(ValueError):
                support.verify_certificate(edges, cert)

    def test_augmenting_route_and_large_components(self) -> None:
        edges = ((0, 2), (0, 3), (1, 2))
        cert = support.build_certificate(edges)
        self.assertEqual(cert.matching, ((0, 3), (1, 2)))
        self.assertEqual(support.verify_certificate(edges, cert), 2)
        self.assertEqual(
            support.verify_certificate((), support.build_certificate(())), 0
        )
        long_path = tuple((i + 1, i) for i in range(1_005))
        self.assertEqual(
            support.verify_certificate(long_path, support.build_certificate(long_path)),
            503,
        )


class ApameaVertexSupportTest(unittest.TestCase):
    def test_unaccepted_or_disagreeing_primary_census_is_rejected(self) -> None:
        a, b = measured.load_frames()
        accepted = transfer.analyze_pair(a, b)
        with self.assertRaisesRegex(ValueError, "accepted frame pair"):
            support.analyze_usable_pair(a, b, transfer.empty_row())
        with self.assertRaisesRegex(
            ValueError, "disagrees with accepted primary census"
        ):
            support.analyze_usable_pair(a, a, accepted)

    def test_frozen_outcomes_and_auditable_trace(self) -> None:
        result = support.report()
        self.assertIn("retrospective", result["scope"])
        rows = result["rows"]
        self.assertEqual(
            [row["temperature_K"] for row in rows], list(range(250, 311, 10))
        )
        self.assertEqual(
            [row["first_pair_role"] for row in rows],
            ["pilot", *(["reserved_for_fixed_transfer"] * 6)],
        )
        expected = {
            250: (42, 42, 33, 34, 75, 782, 832, 861, 2, 1061, 1063),
            260: (57, 54, 40, 44, 97, 763, 813, 836, 1, 1036, 1037),
            280: (57, 57, 43, 43, 97, 764, 811, 840, 3, 1026, 1031),
            300: (52, 52, 44, 43, 94, 746, 796, 816, 1, 1015, 1017),
            310: (48, 46, 36, 36, 78, 748, 793, 831, 3, 1011, 1014),
        }
        for row in rows:
            k = row["temperature_K"]
            with self.subTest(temperature=k):
                summary = row["footprint"]
                if k not in expected:
                    self.assertIsNone(summary)
                    self.assertEqual(row["status"], "inconclusive")
                    self.assertEqual(row["reasons"], ["inapplicable_frame_encoding"])
                    continue
                self.assertEqual(row["status"], "usable")
                if summary is None:
                    self.fail("accepted row has no footprint")
                self.assertEqual(
                    (
                        summary["observed_reversals"],
                        summary["unsupported_observed_reversals"],
                        summary["unsupported_reversals_on_two_bounded_simple_faces"],
                        summary["minimum_non_fourfold_sites"],
                        summary["active_non_fourfold_sites"],
                        summary["total_non_fourfold_sites"],
                        summary["total_visible_sites"],
                        summary["known_edges_without_fourfold_endpoint"],
                        summary["unknown_edges_without_fourfold_endpoint"],
                        summary["known_transition_edges"],
                        summary["total_visible_edges"],
                    ),
                    expected[k],
                )
                unsupported = [
                    t
                    for t in summary["reversed_edges"]
                    if 4 not in t["endpoint_degrees"]
                ]
                self.assertEqual(
                    len(unsupported), summary["unsupported_observed_reversals"]
                )
                self.assertEqual(
                    support.verify_certificate(
                        tuple(t["endpoint_sites"] for t in unsupported),
                        support.CoverCertificate(
                            summary["matching_lower_bound_edge_endpoints"],
                            summary["cover_upper_bound_sites"],
                        ),
                    ),
                    summary["minimum_non_fourfold_sites"],
                )
                self.assertTrue(
                    all(None in t["frame_rows"] for t in summary["unknown_edges"])
                )
                self.assertEqual(
                    len(summary["unknown_edges"]),
                    summary["total_visible_edges"] - summary["known_transition_edges"],
                )
                if k == 250:
                    first = unsupported[0]
                    self.assertEqual(first["frame_rows"], (29, 28))
                    self.assertEqual(first["endpoint_sites"], (7, 57))
                    self.assertEqual(first["endpoint_degrees"], (3, 2))
                    self.assertEqual(first["bounded_simple_face_count"], 0)

    def test_cli_outputs_same_checked_certificates_with_optimization(self) -> None:
        script = str(Path(support.__file__))
        regular = subprocess.check_output([sys.executable, script])
        optimized = subprocess.check_output([sys.executable, "-O", script])
        self.assertEqual(regular, optimized)
        self.assertEqual(json.loads(regular)["schema"], "idt-apamea-vertex-support/1")


if __name__ == "__main__":
    unittest.main()
