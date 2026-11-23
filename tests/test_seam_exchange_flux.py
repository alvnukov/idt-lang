"""Controls for the finite two-seam exchange and flux-identifiability probe."""

import hashlib
import json
import unittest
from collections import Counter
from dataclasses import replace
from pathlib import Path

from scripts import probe_seam_exchange_flux as probe
from scripts import probe_three_mark_tracks as tracks


class SeamExchangeFluxTest(unittest.TestCase):
    def test_full_raw_orbit_and_every_center_match_separated_pair_moves(self) -> None:
        for n in (12, 13, 16):
            with self.subTest(n=n):
                pair_graph = probe.pair_graph(n)
                track = pair_graph.track
                self.assertEqual(
                    set(pair_graph.rows),
                    {
                        (a, b)
                        for a in range(n)
                        for b in range(a + 4, n)
                        if n - b + a >= 4
                    },
                )
                for (a, b), moves in pair_graph.rows.items():
                    expected = tracks.raw_row(
                        track.graph, track.seams[a] ^ track.seams[b], 16
                    )
                    self.assertEqual(
                        {
                            c: track.seams[v] ^ track.seams[w]
                            for c, (_, _, (v, w)) in moves.items()
                        },
                        expected,
                    )
                    for center, (origin, destination, target) in moves.items():
                        self.assertIn(origin, (a, b))
                        self.assertEqual(tracks.separation(origin, destination, n), 1)
                        self.assertEqual(set(target), {a, b} - {origin} | {destination})
                        step_center = origin + (
                            2 if (destination - origin) % n == 1 else 1
                        )
                        self.assertEqual(center, step_center % n)

    def test_only_actual_commuting_faces_are_counted(self) -> None:
        pair_graph = probe.pair_graph(12)
        faces = probe.square_boundaries(pair_graph)
        self.assertEqual(len(faces), 18)
        for face in faces:
            self.assertEqual(len(face), 4)
            self.assertEqual(
                set(Counter(v for edge in face for v in edge).values()), {2}
            )
        removed = faces[0][0]
        rows = {
            source: {
                center: move
                for center, move in row.items()
                if tuple(sorted((source, move.target))) != removed
            }
            for source, row in pair_graph.rows.items()
        }
        self.assertEqual(
            set(probe.square_boundaries(replace(pair_graph, rows=rows))),
            {face for face in faces if removed not in face},
        )

    def test_homology_and_lift_cut_agreement(self) -> None:
        for n, counts in ((12, (30, 48, 18)), (16, (72, 128, 56))):
            with self.subTest(n=n):
                result = probe.inspect_size(n)
                self.assertEqual(
                    (result.vertices, result.edges, result.squares), counts
                )
                self.assertEqual(
                    (result.rank_d1, result.rank_d2), (counts[0] - 1, counts[2])
                )
                self.assertEqual((result.b0, result.b1, result.b2), (1, 1, 0))
                self.assertEqual(result.shortest_exchange_length, n)
                self.assertEqual(result.deck_cut_edges_checked, counts[1])
                self.assertEqual(result.flat_loop_signs, (1, -1))

    def test_actual_local_event_matching_and_gap_blind_negative_control(self) -> None:
        for n in range(12, 25):
            with self.subTest(n=n):
                result = probe.inspect_size(n)
                self.assertEqual(result.shortest_exchange_length, n)
                self.assertEqual(
                    result.exchange_ordered[-1], result.exchange_ordered[0][::-1]
                )
                self.assertEqual(result.local_events_matched, n)
                self.assertEqual(
                    result.single_event_multiset_sha256,
                    result.exchange_event_multiset_sha256,
                )
                self.assertEqual(result.exchange_to_single_signs, (1, -1))
                if n % 2:
                    self.assertIsNone(result.retraced_ordered)
                else:
                    retraced = result.retraced_ordered
                    self.assertIsNotNone(retraced)
                    if retraced is not None:
                        self.assertEqual(retraced[0], retraced[-1])
                        self.assertEqual(
                            tuple(tracks.separation(a, b, n) for a, b in retraced),
                            result.exchange_gap_trace,
                        )
                        self.assertEqual(
                            result.exchange_gap_trace,
                            (n // 2, n // 2 - 1) * (n // 2) + (n // 2,),
                        )
                        self.assertEqual(result.retraced_loop_sign, 1)

    def test_event_key_contains_raw_center_star_and_all_neighbor_supports(self) -> None:
        track = tracks.seam_track(12)
        a, b, center = track.seams[0], track.seams[1], 2
        graph = track.graph
        masks = [sum(1 << i for i in graph.stars[center])]
        for i in graph.stars[center]:
            other = sum(graph.edges[i]) - center
            masks.append(sum(1 << j for j in graph.stars[other] if j != i))
        event = probe.local_event(track, center, a, b)
        self.assertEqual(
            event, (center, tuple(a & m for m in masks), tuple(b & m for m in masks))
        )
        neighbor_bit = next(i for i in graph.stars[1] if i not in graph.stars[center])
        self.assertNotEqual(
            probe.local_event(track, center, a ^ (1 << neighbor_bit), b), event
        )
        self.assertNotEqual(
            probe.local_event(track, center, a, b ^ (1 << neighbor_bit)), event
        )

    def test_report_declares_supplied_sign_model_and_source_target_digests(
        self,
    ) -> None:
        report = json.loads(json.dumps(probe.report((12,))))
        self.assertEqual(report["schema"], "idt-seam-exchange-flux/1")
        self.assertIn("not derived", report["claim_boundary"])
        self.assertIn("spectator", report["phase_model"])
        self.assertEqual(report["source_target_compatibility"]["track_rule"], 16)
        self.assertEqual(report["sizes"][0]["n"], 12)
        sources = report["source_target_compatibility"]["source_sha256"]
        root = Path(probe.__file__).resolve().parents[1]
        for path in (
            "scripts/probe_seam_exchange_flux.py",
            "scripts/probe_three_mark_tracks.py",
        ):
            self.assertEqual(
                sources[path], hashlib.sha256((root / path).read_bytes()).hexdigest()
            )
        self.assertRegex(report["sizes"][0]["raw_orbit_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(report["sizes"][0]["cubical_target_sha256"], r"^[0-9a-f]{64}$")


if __name__ == "__main__":
    unittest.main()
