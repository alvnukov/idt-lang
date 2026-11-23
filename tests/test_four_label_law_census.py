"""Frozen finite observations for the four-label law census."""

import importlib.util
import json
import unittest
from collections import Counter
from fractions import Fraction
from hashlib import sha256


class FourLabelLawCensusTests(unittest.TestCase):
    def test_exhaustive_family(self):
        module = "scripts.probe_four_label_law_census"
        self.assertIsNotNone(importlib.util.find_spec(module), "law census is not implemented")
        from scripts.probe_four_label_law_census import law_family, signed_sector, exhaustive_sector

        for representatives in ((1, 2, 6), (3, 7, 11)):
            with self.subTest(representatives=representatives):
                self.assertEqual(len(signed_sector(representatives)), 20)
                self.assertEqual(signed_sector(representatives), exhaustive_sector(representatives))
        tables = law_family()
        self.assertEqual(len(set(tables)), 400)
        self.assertEqual(tables, tuple(sorted(tables)))
        for table in tables:
            self.assertEqual(set(table), set(range(16)))
            for pair, image in enumerate(table):
                i, j = divmod(pair, 4)
                p, q = divmod(image, 4)
                self.assertEqual((i == 3) + (j == 3), (p == 3) + (q == 3))
                self.assertEqual(table[4 * j + i], 4 * q + p)
                self.assertEqual(table[image], pair)
                if i == j:
                    self.assertEqual(image, pair)

    @classmethod
    def census(cls):
        from scripts.probe_four_label_law_census import run_census

        if not hasattr(cls, "_result"):
            cls._result = run_census()
        return cls._result

    def test_central_partitions_keep_every_launch_and_calibration(self):
        from scripts.probe_colorless_packet_arms import enumerate_rows, rates

        census = self.census()
        self.assertEqual(len(census.records), 400)
        self.assertEqual(len({record.identity for record in census.records}), 400)
        self.assertEqual(census.central_group_match_counts, (400, 2, 2, 132))
        self.assertEqual(census.central_nested_match_counts, (400, 2, 2, 2))
        for record in census.records:
            self.assertEqual(len(record.central), 32)
            self.assertTrue(all(len(row) == 4 and sum(row) == 16 for row in record.central))
        self.assertTrue(any(row[3] > 0 for record in census.records for row in record.central))
        original = census.original
        self.assertEqual(tuple(row[3] for row in original.central), (0,) * 32)
        self.assertEqual(tuple(tuple(Fraction(n, 16) for n in row[:3]) for row in original.central),
                         tuple(rates(row) for row in enumerate_rows().values()))
        self.assertEqual({record.table for record in census.central_survivors},
                         {original.table, census.token_zero_variant.table})

    def test_raw_central_trace_does_not_offer_distinguishing_local_input(self):
        census = self.census()
        original, variant = census.original, census.token_zero_variant
        self.assertEqual(census.central_trace.launches, 512)
        self.assertTrue(census.central_trace.identical)
        frequencies = Counter(dict(census.central_trace.input_counts))
        self.assertEqual(sum(frequencies.values()), census.central_trace.contacts)
        self.assertGreater(census.central_trace.contacts, 512)
        self.assertEqual(frequencies[3] + frequencies[12], 0)
        self.assertEqual(tuple(i for i in range(16) if original.table[i] != variant.table[i]), (3, 12))
        self.assertEqual(census.isolated_token_zero, ((3, 0), (0, 3)))
        self.assertEqual((original.moved_types, variant.moved_types), (3, 4))

    def test_general_law_that_leaves_code_space_keeps_unread_in_the_denominator(self):
        from scripts.probe_colorless_packet_arms import meter
        from scripts.probe_four_label_law_census import raw_central_traces

        record = next(row for row in self.census().records if any(counts[3] for counts in row.central))
        traces = iter(raw_central_traces(record.table))
        for row in record.central:
            outputs = [meter(next(traces)[-1]) for _ in range(16)]
            output_counts = tuple(map(sum, zip(*outputs, strict=True)))
            self.assertEqual(row, output_counts + (sum(out == (0, 0, 0) for out in outputs),))
        self.assertIsNone(next(traces, None))

    def test_independent_pair_record_discriminates_central_survivors(self):
        census = self.census()
        self.assertEqual(census.original.pair, ((0, 4, 12), (3, 1, 12)))
        self.assertEqual(census.token_zero_variant.pair, ((4, 8, 4), (3, 9, 4)))
        self.assertEqual(len(census.pair_survivors), 16)
        self.assertEqual(census.joint_survivors, (census.original,))

    def test_exact_road_cycle_retains_controls_without_cross_candidate_merging(self):
        census = self.census()
        records = census.records
        self.assertEqual(sum(row.road.first_distinct for row in records), 240)
        self.assertEqual(sum(row.road.indefinite for row in records), 220)
        self.assertEqual(sum(row.road.indefinite for row in census.pair_survivors), 8)
        self.assertFalse(any(row.road.indefinite for row in census.central_survivors))
        control = census.shade_forwarding_control
        self.assertEqual(control.road.orbit, ((1, 2), (1, 2)))
        self.assertEqual(control.road.cycle_start, 0)
        self.assertEqual(control.moved_types, 4)
        self.assertEqual(sum(a == b for a, b in zip(control.central, census.original.central, strict=True)), 2)
        alternate = census.alternating_three_type_control
        self.assertEqual(alternate.road.orbit, ((1, 2), (1, 0), (1, 2)))
        self.assertEqual(alternate.road.cycle_start, 0)
        self.assertEqual(alternate.moved_types, 3)
        self.assertEqual(census.original.road.orbit, ((1, 2), (1, 1)))
        self.assertIsNone(census.original.road.cycle_start)

    def test_compact_signature_digest_and_full_table_replay_payload(self):
        from scripts.probe_four_label_law_census import report

        census = self.census()
        compact, expanded = report(census), report(census, enumerate_all=True)
        self.assertNotIn("records", compact)
        rows = expanded.pop("records")
        self.assertEqual(compact, expanded)
        self.assertEqual(compact["family_sha256"], sha256(json.dumps(
            rows, sort_keys=True, separators=(",", ":")).encode("ascii")).hexdigest())
        self.assertEqual(len(compact["central"]["settings"]), 32)
        self.assertEqual(compact["central"]["counts_denominator"], 16)
        self.assertEqual(compact["standalone_pair"]["counts_denominator"], 16)
        for row, reference in zip(rows, census.records, strict=True):
            self.assertEqual(tuple(int(code, 16) for code in row["id"]), reference.table)
            self.assertEqual(row["central_counts"], reference.central)
            self.assertEqual(row["pair_counts"], reference.pair)
        self.assertEqual(compact["central"]["matching_ids"],
                         tuple(row.identity for row in census.central_survivors))
        self.assertEqual(compact["central"]["named_table_matching_row_counts"]["original_plus_vacant_12_swap"], 2)
