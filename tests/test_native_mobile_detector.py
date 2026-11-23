"""Conformance and negative controls for a native B shade record."""

from itertools import product
import unittest

from scripts import probe_mobile_blank_interferometer as mobile
from scripts import probe_native_mobile_detector as detector


class NativeMobileDetectorTests(unittest.TestCase):
    def test_exact_frozen_word_and_inverse_for_all_raw_inputs(self):
        d = detector
        word = (((0, 1),), ((1, 2),), ((1, 3),), ((1, 2),), ((2, 3),), ((1, 2),))
        for x, flag in ((1, 1), (2, 1), (3, 2)):
            with self.subTest(x=x):
                trace = d.detector_trace(x)
                self.assertEqual(trace.word, word)
                self.assertEqual(trace.initial, (x, 1, 1, 0))
                self.assertEqual(trace.output, (1, flag, x, 0))
                self.assertEqual(d.reverse(trace).output, trace.initial)
                self.assertTrue(all(s[3] == 0 and s.count(3) == int(x == 3) for s in trace.states))

    def test_minimum_contact_depth_with_or_without_data_reference_edge(self):
        d = detector
        for edges, layer_sizes in ((d.EDGES, (1, 3, 5, 8, 12, 19, 28)),
                                   (d.EDGES + ((0, 3),), (1, 4, 8, 14, 25, 37, 42))):
            with self.subTest(edges=edges):
                result = d.shortest_word(edges)
                self.assertEqual(len(result.word), 6)
                self.assertEqual(result.layer_sizes, layer_sizes)
                for x, flag in ((1, 1), (2, 1), (3, 2)):
                    self.assertEqual(d.replay((x, 1, 1, 0), result.word).output, (1, flag, x, 0))
        self.assertIsNone(d.shortest_word(((0, 1), (1, 2))))

    def test_real_embedded_endpoints_compared_without_postselection(self):
        d = detector
        counts = [0, 0, 0]
        settings = set()
        for (source, plates, opened), seeds, replacements in product(
            mobile.SETTINGS, mobile.SEEDS, mobile.SEEDS
        ):
            trial = mobile.run_trial(source, plates, opened, seeds, replacements)
            embedded = trial.embed()
            readout = d.attach_detectors(trial)
            self.assertEqual(tuple(read.data for read in readout.reads),
                             embedded.detectors + sum(embedded.dumps, ()))
            self.assertEqual(readout.trace.word[:len(embedded.trace.word)], embedded.trace.word)
            self.assertEqual(readout.trace.states[readout.prefix_contacts][:len(embedded.trace.output)],
                             embedded.trace.output)
            self.assertEqual(readout.outcome, trial.outcome)
            self.assertEqual(sum(readout.outcome), 1)
            self.assertEqual(d.reverse(readout.trace).output, readout.trace.initial)
            for i, flag in enumerate(readout.outcome):
                counts[i] += flag
            settings.add((source, plates, opened))
        self.assertEqual(len(settings), 32)
        self.assertEqual(counts, [128, 128, 256])

    def test_port_only_still_exposes_raw_zero_counts_on_lost_launches(self):
        d = detector
        trial = mobile.run_trial(1, (True, False), (False, False), (2, 1), (1, 2), (2, 0, 1, 5))
        witness = d.attach_detectors(trial, include_dumps=False)
        self.assertEqual(len(witness.reads), 2)
        self.assertEqual(witness.port_flags, (0, 0))
        self.assertEqual(witness.dump_flags, ())

    def test_fresh_serial_records_preserve_one_carrier_and_uncompute(self):
        d = detector
        for x, flag in ((1, 1), (2, 1), (3, 2)):
            for count in (0, 1, 2, 6):
                with self.subTest(x=x, count=count):
                    witness = d.serial_detector(x, count)
                    current = 0
                    self.assertEqual(len(witness.trace.word), 6 * count)
                    for i, read in enumerate(witness.reads):
                        self.assertEqual(read.data, current)
                        self.assertEqual(witness.trace.output[read.record], flag)
                        self.assertEqual(witness.trace.output[read.data], 1)
                        self.assertEqual(witness.trace.output[read.reference], 0)
                        self.assertEqual(witness.trace.states[6 * (i + 1)][read.holding], x)
                        current = read.holding
                    self.assertEqual(witness.trace.output[current], x)
                    self.assertEqual(witness.trace.output.count(3), int(x == 3))
                    self.assertEqual(d.reverse(witness.trace).output, witness.trace.initial)

    def test_blank_only_single_site_difference_cannot_duplicate(self):
        d = detector
        for edges in (d.EDGES, d.EDGES + ((0, 3),)):
            report = d.blank_only_control(edges)
            self.assertEqual(report.signed_permutations, 48)
            self.assertEqual(report.stock_pairs, 12)
            self.assertEqual(report.checked_images, 576)
            self.assertEqual(report.distance_changes, 0)

    def test_dirty_record_and_holding_are_not_prepared_detections(self):
        d = detector
        controls = d.dirty_stock_control()
        for case in controls:
            data, record, holding, zero = case.initial
            self.assertEqual(zero, 0)
            self.assertEqual(case.output, d.replay(case.initial, d.WORD).output)
            self.assertNotEqual((record, holding), (1, 1))
        self.assertEqual(len(controls), 9)
        self.assertTrue(any(c.initial[0] != 3 and c.output[1] == 2 for c in controls))
        self.assertTrue(any(c.initial[0] == 3 and c.output[1] != 2 for c in controls))
        for invalid in (0, 4):
            with self.assertRaises(ValueError):
                d.detector_trace(invalid)

    def test_closed_contact_graph_is_not_a_raw_jam_or_stable_record(self):
        d = detector
        report = d.jam_control()
        self.assertEqual(report.states, 20)
        self.assertEqual(report.raw_jams, 0)
        self.assertEqual(report.nonjam_endpoints, 3)
        self.assertEqual(report.record_flips_when_offered, 3)
        self.assertEqual(report.isolated_record_checks, 3)
        self.assertEqual(report.equal_shade_memory_checks, 2)
        self.assertGreater(report.changing_edges_reversed, 0)

    def test_evidence_counts_and_scope(self):
        e = detector.verify()
        self.assertEqual((e.endpoint_launches, e.setting_rows), (512, 32))
        self.assertEqual(e.native_outcome_counts, (128, 128, 256))
        self.assertEqual(e.shortest_contact_lengths, (6, 6))
        self.assertEqual(e.serial_cases, 15)
        self.assertEqual(e.port_meter_mismatches, 0)
        self.assertEqual(e.dump_meter_mismatches, 0)
        self.assertEqual((e.dirty_stock_cases, e.dirty_false_flags, e.dirty_missed_flags), (9, 4, 2))


if __name__ == "__main__":
    unittest.main()
