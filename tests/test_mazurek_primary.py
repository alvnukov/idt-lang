"""Regression and failure controls for the pinned Mazurek counts replay."""

from __future__ import annotations

import gzip
import hashlib
import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts.replay_mazurek_primary import main
from theory_experiments import mazurek_primary as primary


class MazurekPrimaryTests(unittest.TestCase):
    def test_pinned_counts_and_primary_only_summary(self) -> None:
        counts = primary.load_counts()
        self.assertEqual(len(counts.runs), 100)
        self.assertEqual(hashlib.sha256(primary.canonical_bytes(counts)).hexdigest(), primary.CANONICAL_SHA256)
        self.assertEqual(counts.aggregate[6][-2:], (1249, 7639117))
        self.assertEqual(counts.runs[0][6][-2:], (74866, 13))
        self.assertEqual(counts.aggregate[7][-2:], (7685222, 1488))
        self.assertEqual(counts.runs[-1][7][-2:], (7, 76290))
        report = primary.summarize(counts)
        self.assertEqual(report["run_mean_a"], 0.9998691364438897)
        self.assertEqual(report["pooled_a"], 0.9998691621948411)
        sd, sem = report["run_sample_sd_a"], report["run_sem_a"]
        if not isinstance(sd, float) or not isinstance(sem, float):
            self.fail("expected separate sample spread and standard error")
        self.assertAlmostEqual(sd, 1.7500961997948513e-05, places=16)
        self.assertEqual(sem, sd / 10)
        self.assertEqual(report["matched_pairs_in_a"], [1, 2, 3])
        self.assertEqual(report["source_comparison"], {
            "exact_first_six_preparation_rows": True,
            "mismatched_cells_in_original_order": 16,
            "mismatched_preparation_labels": ["P_4,0", "P_4,1"],
            "matches_after_fourth_pair_row_swap_diagnostic_only": True,
            "correction_applied": False,
        })
        scope = report["scope"]
        if not isinstance(scope, str):
            self.fail("missing replay scope")
        self.assertIn("not the published secondary result", scope)
        self.assertIn("or an unconditional rejection", scope)

    def test_gzip_validation_is_bounded_and_does_not_trust_altered_counts(self) -> None:
        raw = primary.canonical_bytes(primary.load_counts())
        compressed = gzip.compress(raw, mtime=0)
        for name, blob, message in (
            ("truncation", compressed[:-1], "truncated"),
            ("CRC", compressed[:-8] + bytes((compressed[-8] ^ 1,)) + compressed[-7:], "invalid gzip"),
            ("second member", compressed + gzip.compress(b"", mtime=0), "trailing"),
            ("uncompressed size", gzip.compress(b"0" * (primary.MAX_JSON + 1), mtime=0), "oversized"),
            ("duplicate key", gzip.compress(b'{"aggregate":[],"aggregate":[]}', mtime=0), "duplicate JSON key"),
            ("noncanonical whitespace", gzip.compress(raw + b"\n", mtime=0), "digest or serialization"),
            ("valid schema wrong count", gzip.compress(raw.replace(b"7658779", b"7658780", 1), mtime=0), "digest"),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / "counts.json.gz"
                path.write_bytes(blob)
                with self.assertRaisesRegex(ValueError, message):
                    primary.load_counts(path)

    def test_counts_reject_negative_boolean_fractional_and_zero_denominator(self) -> None:
        raw = primary.canonical_bytes(primary.load_counts())
        for bad in (False, -1, 1.0, "1", primary.MAX_COUNT + 1):
            with self.subTest(bad=bad):
                data = json.loads(raw)
                data["aggregate"][0][0] = bad
                with self.assertRaisesRegex(ValueError, "nonnegative integers"):
                    primary._parse_counts(json.dumps(data).encode())
        data = json.loads(raw)
        data["aggregate"][0][:2] = [0, 0]
        with self.assertRaisesRegex(ValueError, "denominator is zero"):
            primary._parse_counts(json.dumps(data).encode())

    def test_both_sources_are_authenticated_before_opening_any_zip(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            aggregate, runs = root / "aggregate.xlsx", root / "runs.xlsx"
            aggregate.write_bytes(b"a" * primary.AGGREGATE_SOURCE.size)
            runs.write_bytes(b"r" * primary.RUN_SOURCE.size)
            with patch.object(primary, "ZipFile", side_effect=AssertionError("do not parse an unverified pair")):
                with self.assertRaisesRegex(ValueError, "aggregate|counts_photons|SHA-256"):
                    primary.extract_workbooks(aggregate, runs)
                synthetic_source = primary.Source(
                    primary.AGGREGATE_SOURCE.filename, primary.AGGREGATE_SOURCE.sheet,
                    primary.AGGREGATE_SOURCE.cell_range, primary.AGGREGATE_SOURCE.size,
                    hashlib.sha256(aggregate.read_bytes()).hexdigest(),
                )
                with (patch.object(primary, "AGGREGATE_SOURCE", synthetic_source),
                      self.assertRaisesRegex(ValueError, "counts_per_each_run.*SHA-256")):
                    primary.extract_workbooks(aggregate, runs)

    def test_workbook_rebuild_checks_literal_run_labels_and_all_denominators(self) -> None:
        counts = primary.load_counts()

        def insert(target: dict[str, int | str], row: int, values: tuple[int | str, ...]) -> None:
            for col, value in zip("ABCDEFGHIJKLMNOPQR", values):
                target[f"{col}{row}"] = value

        aggregate: dict[str, int | str] = {}
        runs: dict[str, int | str] = {}
        insert(aggregate, 2, ("Preparation", *primary.MEASUREMENTS))
        insert(runs, 2, ("Run #", "Preparation", *primary.MEASUREMENTS, *primary.DENOMINATORS))
        for i, prep in enumerate(primary.PREPARATIONS):
            insert(aggregate, 3 + i, (prep, *counts.aggregate[i]))
            for j, run in enumerate(counts.runs):
                row = run[i]
                totals = tuple(row[k] + row[k ^ 1] for k in range(8))
                insert(runs, 3 + 8 * j + i, (j + 1, prep, *row, *totals))

        def replay(expected_run_cells: dict[str, int | str]) -> primary.Counts:
            with (patch.object(primary, "_source_bytes", return_value=b""),
                  patch.object(primary, "_sheet", side_effect=(aggregate, expected_run_cells))):
                return primary.extract_workbooks(Path("aggregate.xlsx"), Path("runs.xlsx"))

        self.assertEqual(replay(runs), counts)
        for cell, value, error in (("A802", 99, "run number"), ("B802", "P_4,0", "preparation labels"),
                                   ("R802", 0, "denominators differ"), ("C2", "[1|M1]", "outcome")):
            with self.subTest(cell=cell), self.assertRaisesRegex(ValueError, error):
                replay({**runs, cell: value})

    def test_exclusive_fixture_write_and_unsafe_input_paths(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / "counts.json.gz"
            counts = primary.load_counts()
            primary.write_counts(path, counts)
            original = path.read_bytes()
            self.assertEqual(primary.load_counts(path), counts)
            with self.assertRaises(FileExistsError):
                primary.write_counts(path, counts)
            self.assertEqual(path.read_bytes(), original)
            link = root / "alias.json.gz"
            link.symlink_to(path)
            with self.assertRaises(OSError):
                primary.load_counts(link)
            with self.assertRaises(FileExistsError):
                primary.write_counts(link, counts)
            with self.assertRaisesRegex(ValueError, "regular file"):
                primary.load_counts(root)

    def test_cli_offline_and_argument_failures_do_not_write(self) -> None:
        output, error = io.StringIO(), io.StringIO()
        with redirect_stdout(output), redirect_stderr(error):
            self.assertEqual(main([]), 0)
        self.assertEqual(error.getvalue(), "")
        receipt = json.loads(output.getvalue())
        self.assertEqual(receipt["input_mode"], "pinned_offline_fixture")
        self.assertFalse(receipt["fixture_written"])
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "out.json.gz"
            for args in (["--output", str(path)], ["--aggregate-workbook", "unused.xlsx"], ["--fix", str(path)]):
                with self.subTest(args=args), redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                    main(args)
                self.assertEqual(raised.exception.code, 2)
                self.assertFalse(path.exists())


if __name__ == "__main__":
    unittest.main()
