"""Independent software oracles for descriptive digitized-voltage arithmetic."""

from __future__ import annotations

import copy
import importlib.util
import io
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from decimal import ROUND_UP, Inexact, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any
from unittest.mock import patch

from scripts.replay_gstir2021 import main
from theory_experiments import raw_signal_replay as raw


def cycle(values: list[float]) -> raw.CycleReduction:
    return raw.reduce_cycle([(mask, (value,)) for mask, value in enumerate(values)])


class RawArithmeticTests(unittest.TestCase):
    def test_independent_background_oracle_and_shuffled_masks(self) -> None:
        values = [10., 11., 12., 15., 13., 17., 19., 24.]
        result = cycle(values)
        self.assertEqual((result.epsilon, result.delta, result.kappa),
                         (Fraction(-1), Fraction(9), Fraction(-1, 9)))
        records = [(mask, (values[mask] - .5, values[mask] + .5))
                   for mask in (7, 2, 0, 6, 1, 4, 3, 5)]
        self.assertEqual(raw.reduce_cycle(records), result)

    def test_exact_binary64_not_decimal_input_interpretation(self) -> None:
        records = [(mask, (.1, .2)) for mask in range(8)]
        result = raw.reduce_cycle(records)
        self.assertEqual(result.means[0], (Fraction.from_float(.1) + Fraction.from_float(.2)) / 2)
        self.assertNotEqual(result.means[0], Fraction(3, 20))

    def test_decimal_display_ignores_ambient_rounding_traps_and_exponent_limits(self) -> None:
        expected = raw.number(Fraction(1, 3))
        with localcontext() as context:
            context.prec = 2
            context.rounding = ROUND_UP
            context.traps[Inexact] = True
            context.Emax = 1
            context.Emin = -1
            self.assertEqual(raw.number(Fraction(1, 3)), expected)

    def test_ratio_of_means_not_mean_ratios_or_delta_of_pooled_means(self) -> None:
        a = [0., 0., 0., 1., 0., 0., 0., 2.]
        b = [0., 0., 0., -3., 0., 0., 0., 3.]
        first, second = cycle(a), cycle(b)
        result = raw.aggregate([first, second])
        self.assertEqual(result["kappa"], raw.number(Fraction(7, 4)))
        assert first.kappa is not None and second.kappa is not None
        self.assertEqual((first.kappa + second.kappa) / 2, Fraction(3, 2))
        pooled = cycle([(x + y) / 2 for x, y in zip(a, b)])
        self.assertEqual(pooled.kappa, Fraction(7, 2))
        self.assertEqual(result["mean_delta_volt"], raw.number(Fraction(2)))

    def test_zero_delta_inventory_terms_are_retained(self) -> None:
        defined = cycle([0., 0., 0., 1., 0., 0., 0., 2.])
        undefined = cycle([0., 0., 0., 0., 0., 0., 0., 2.])
        self.assertIsNone(undefined.kappa)
        result = raw.aggregate([defined, undefined])
        self.assertEqual(result["cycles"], 2)
        self.assertEqual(result["zero_delta_cycles_retained"], 1)
        self.assertEqual(result["kappa"], raw.number(Fraction(3)))
        self.assertIsNone(raw.aggregate([undefined])["kappa"])
        self.assertEqual(raw.aggregate([undefined])["undefined_reason"], "zero_mean_delta")
        with self.assertRaises(ValueError):
            raw.aggregate([])

    def test_common_affine_response_and_noncommon_responses(self) -> None:
        values = [10., 11., 12., 15., 13., 17., 19., 24.]
        original = cycle(values)
        self.assertEqual(cycle([3 * x + 7 for x in values]).kappa, original.kappa)
        assert original.kappa is not None
        self.assertEqual(cycle([-3 * x + 7 for x in values]).kappa, -original.kappa)
        changed = values.copy()
        changed[7] *= 2
        self.assertNotEqual(cycle(changed).kappa, original.kappa)
        self.assertNotEqual(cycle([x * x for x in values]).kappa, original.kappa)
        # These are arithmetic controls; no routine here produces a primitive verdict.

    def test_invalid_cycle_and_nonfinite_samples_fail_as_data_errors(self) -> None:
        valid = [(i, (float(i),)) for i in range(8)]
        for records in (valid[:-1], valid + [valid[0]], valid[:-1] + [valid[0]],
                        valid[:-1] + [(7, ())], valid[:-1] + [(True, (1.,))]):
            with self.subTest(records=records), self.assertRaises(ValueError):
                raw.reduce_cycle(records)
        for value in (float("nan"), float("inf"), float("-inf")):
            with self.assertRaises(ValueError):
                raw.reduce_cycle(valid[:-1] + [(7, (value,))])

    def test_author_cut_convention_and_cycle_union_are_not_primary_cuts(self) -> None:
        sources = raw.registry()["runs"]
        for source, count in zip(sources, (328, 433)):
            retained = [i for i in range(1, source["cycles"] + 1) if not raw.cut_masks(source, i)]
            self.assertEqual(len(retained), count)
        self.assertEqual(raw.cut_masks(sources[0], 1), [1])
        self.assertEqual(raw.cut_masks(sources[0], 80), [1])
        self.assertEqual(raw.cut_masks(sources[0], 81), [])
        self.assertEqual(raw.cut_masks(sources[0], 226), [0, 4])
        self.assertEqual(raw.cut_masks(sources[1], 186), [1])
        self.assertIn("not_explicitly_confirmed", raw.CUT_CONVENTION)

    def test_calendar_validation(self) -> None:
        self.assertEqual(raw._timestamp([2020., 2., 29., 12., 0., .1])[-1], .1)
        for timestamp in ([2019., 2., 29., 12., 0., 0.], [2020., 1., 1., 24., 0., 0.],
                          [2020., 1., 1., 0., 0., 60.], [2020., 1.5, 1., 0., 0., 0.],
                          [2020., 1., 1., 0., 0., float("nan")]):
            with self.assertRaises(ValueError):
                raw._timestamp(timestamp)

    def test_ancillary_telemetry_preserves_nonfinite_classification_not_imputation(self) -> None:
        for value, reason in ((None, "not_recorded"), (float("nan"), "recorded_nonfinite_nan"),
                              (float("inf"), "recorded_nonfinite_positive_infinity"),
                              (-float("inf"), "recorded_nonfinite_negative_infinity")):
            self.assertEqual(raw.temperature_telemetry(value), (None, reason))
        self.assertEqual(raw.temperature_telemetry(.5), (raw.number(Fraction(1, 2)), "recorded_finite"))

    def test_stale_loaded_implementation_and_midrun_change_fail_closed(self) -> None:
        changed = dict(raw.LOADED_SOURCE_HASHES, stale="0" * 64)
        with patch.object(raw, "provenance", return_value=changed), patch.object(raw, "_read_run") as read:
            with self.assertRaisesRegex(ValueError, "since import"):
                raw.replay(Path("/unused"))
            read.assert_not_called()
        with (patch.object(raw, "provenance", side_effect=[raw.LOADED_SOURCE_HASHES, changed]),
              patch.object(raw, "_read_run", return_value={
                  "primary_all_cycles": {"mean_epsilon_volt": raw.number(Fraction(1))}}),
              self.assertRaisesRegex(ValueError, "during execution")):
            raw.replay(Path("/unused"))

    def test_ideal_kappa_requires_ideal_denominator_not_just_positive_recorded_delta(self) -> None:
        positive_observation = {"primary_all_cycles": {"mean_delta_volt": raw.number(Fraction(1)),
                                                     "mean_epsilon_volt": raw.number(Fraction(1))}}
        with patch.object(raw, "_read_run", return_value=positive_observation):
            report = raw.replay(Path("/unused"))
        comparison: Any = report["conditional_ideal_zero_comparison"]
        self.assertEqual(comparison["ideal_kappa_condition"], "ideal_model_delta_nonzero")
        self.assertEqual(comparison["recorded_delta_boundary"],
                         "observed_positive_or_nonzero_denominators_do_not_establish_ideal_model_nonzero_delta_or_physical_bridge")
        self.assertEqual(comparison["physical_bridge"], "unestablished")
        self.assertEqual(report["candidate_verdict"], "not_assessed")

    def test_standard_import_needs_no_h5py_and_changes_no_candidate_surface(self) -> None:
        code = ("import sys; import theory_experiments.candidate_pipeline as p; "
                "import theory_experiments.raw_signal_replay; "
                "assert 'h5py' not in sys.modules; "
                "assert not any('raw_signal' in x for x in p.SOURCE_PATHS)")
        subprocess.run([sys.executable, "-c", code], cwd=raw.ROOT, check=True, capture_output=True)

    def test_cli_error_boundary_no_partial_output_and_no_stdout_flood(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "report.json"
            error, stdout = io.StringIO(), io.StringIO()
            with redirect_stderr(error), redirect_stdout(stdout):
                status = main(["--raw-directory", directory, "--output", str(output)])
            self.assertEqual(status, 2)
            self.assertFalse(output.exists())
            self.assertEqual(stdout.getvalue(), "")
            self.assertIn("not primitive counterexample", error.getvalue())

    def test_cli_deterministic_no_overwrite(self) -> None:
        report = {"runs": [{"primary_all_cycles": {"cycles": 1}, "nuisance_assessment": {
            "target": {}, "status": "inconclusive_missing_bounds", "missing_bounds": ["sampling", "bias"],
            "candidate_verdict": "not_assessed"}}]}
        with tempfile.TemporaryDirectory() as directory, patch("scripts.replay_gstir2021.replay", return_value=report):
            output = Path(directory) / "report.json"
            args = ["--raw-directory", directory, "--output", str(output)]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main(args), 0)
                self.assertEqual(main(args), 0)
            original = output.read_bytes()
            with patch("scripts.replay_gstir2021.replay", return_value={"runs": []}), redirect_stderr(io.StringIO()):
                self.assertEqual(main(args), 2)
            self.assertEqual(output.read_bytes(), original)


@unittest.skipUnless(importlib.util.find_spec("h5py"), "optional h5py not installed")
class Hdf5BoundaryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "fixture.h5"
        self.h5py = __import__("h5py")
        self.source = copy.deepcopy(raw.registry()["runs"][0])
        self.source.update({"cycles": 1, "samples_per_context": 2,
                            "author_cut_indices_by_mask": {str(i): [] for i in range(8)}})
        with self.h5py.File(self.path, "w") as data:
            data.attrs["cycles"] = 1
            data.attrs["datapoints per comb"] = 2
            pd = data.create_dataset("PD signal", (8, 2, 1), dtype="<f8")
            pd.attrs["unit"] = "volt"
            pd.attrs["device"] = self.source["detector"]
            masks = data.create_dataset("shuttercombination", (8, 1, 1), dtype="<f8")
            times = data.create_dataset("time", (8, 2, 6), dtype="<f8")
            times.attrs["unit"] = "[YYYY, MM, DD, hh, mm, ss.ss]"
            for i, mask in enumerate((7, 1, 2, 6, 0, 3, 5, 4)):
                masks[i, 0, 0] = mask
                pd[i, :, 0] = (float(mask), float(mask) + .5)
                times[i, 0, :] = [2020, 1, 1, 0, 0, 2 * i]
                times[i, 1, :] = [2020, 1, 1, 0, 0, 2 * i + 1]
        self.pin()

    def pin(self) -> None:
        self.source.update({"size_bytes": self.path.stat().st_size, "sha256": raw.sha256(self.path)})

    def test_shuffled_original_order_windows_and_primary_inventory(self) -> None:
        report = raw._read_run(self.path, self.source)
        inventory: Any = report["cycle_inventory"]
        self.assertEqual([r["mask"] for r in inventory[0]["contexts_in_acquisition_order"]], [7, 1, 2, 6, 0, 3, 5, 4])
        self.assertEqual(inventory[0]["cycle_id_one_based"], 1)
        self.assertEqual(inventory[0]["contexts_in_acquisition_order"][0]["sample_time_end"][-1], 1.)
        self.assertEqual(report["recorded_PD_samples"], 16)
        self.assertEqual(raw.canonical_json(report), raw.canonical_json(raw._read_run(self.path, self.source)))

    def test_hash_mismatch_is_data_error_before_hdf5_import(self) -> None:
        self.source["sha256"] = "0" * 64
        with (patch("theory_experiments.raw_signal_replay.importlib.import_module", side_effect=AssertionError("must not import")),
              self.assertRaisesRegex(ValueError, "SHA256 mismatch")):
            raw._read_run(self.path, self.source)

    def test_missing_optional_dependency_is_explicit(self) -> None:
        with (patch("theory_experiments.raw_signal_replay.importlib.import_module", side_effect=ModuleNotFoundError),
              self.assertRaisesRegex(ValueError, "optional h5py required")):
            raw._read_run(self.path, self.source)

    def test_pinned_malformed_schema_units_masks_values_and_order_fail_closed(self) -> None:
        mutations = [
            ("PD signal", (0, 0, 0), float("nan")),
            ("PD signal", (0, 0, 0), float("inf")),
            ("shuttercombination", (0, 0, 0), 1.),
            ("shuttercombination", (0, 0, 0), .5),
            ("shuttercombination", (0, 0, 0), 8.),
            ("shuttercombination", (0, 0, 0), float("nan")),
            ("time", (0, 0, 0), float("inf")),
            ("time", (0, 0, 1), 13.),
            ("time", (0, 0, 5), 5.),
        ]
        for name, index, value in mutations:
            with self.subTest(name=name, index=index, value=value):
                with self.h5py.File(self.path, "r+") as data:
                    saved = data[name][index]
                    data[name][index] = value
                self.pin()
                with self.assertRaises(ValueError):
                    raw._read_run(self.path, self.source)
                with self.h5py.File(self.path, "r+") as data:
                    data[name][index] = saved
        for dataset, attr, unit in (("PD signal", "unit", "counts"), ("time", "unit", "seconds")):
            with self.h5py.File(self.path, "r+") as data:
                saved_attr = data[dataset].attrs[attr]
                data[dataset].attrs[attr] = unit
            self.pin()
            with self.assertRaisesRegex(ValueError, "metadata"):
                raw._read_run(self.path, self.source)
            with self.h5py.File(self.path, "r+") as data:
                data[dataset].attrs[attr] = saved_attr
        for name, shape, dtype in (("time", (8, 1, 6), "<f8"), ("PD signal", (8, 2, 1), "<f4")):
            with self.h5py.File(self.path, "r+") as data:
                del data[name]
                data.create_dataset(name, shape, dtype=dtype)
            self.pin()
            with self.assertRaisesRegex(ValueError, "shape/binary64"):
                raw._read_run(self.path, self.source)


@unittest.skipUnless(os.environ.get("IDT_GSTIR2021_RAW_DIRECTORY") and importlib.util.find_spec("h5py"),
                     "set IDT_GSTIR2021_RAW_DIRECTORY and install optional h5py for full replay")
class RealRawReplayTests(unittest.TestCase):
    def test_both_pinned_sources_exact_oracles_inventory_cuts_and_stable_output(self) -> None:
        directory = Path(os.environ["IDT_GSTIR2021_RAW_DIRECTORY"])
        report = raw.replay(directory)
        self.assertEqual(raw.canonical_json(report), raw.canonical_json(raw.replay(directory)))
        self.assertEqual(report["candidate_verdict"], "not_assessed")
        self.assertEqual(report["execution_status"], "complete")
        runs: Any = report["runs"]
        self.assertEqual(len(runs), 2)
        for run, cycles, cut_cycles, samples in zip(runs, (420, 450), (328, 433), (134400, 180000)):
            source = run["source"]
            self.assertEqual(raw.sha256(directory / source["filename"]), source["sha256"])
            primary = run["primary_all_cycles"]
            self.assertEqual(primary["cycles"], cycles)
            self.assertEqual(primary["zero_delta_cycles_retained"], 0)
            assessment = run["nuisance_assessment"]
            self.assertEqual(assessment["status"], "inconclusive_missing_bounds")
            self.assertEqual(assessment["missing_bounds"], ("sampling", "bias"))
            self.assertIsNone(assessment["ideal_epsilon_enclosure_volt"])
            self.assertEqual(assessment["candidate_verdict"], "not_assessed")
            self.assertNotEqual(primary["mean_epsilon_volt"]["exact"], "0")
            self.assertEqual(assessment["recorded_mean_cycle_epsilon_volt_exact"], primary["mean_epsilon_volt"]["exact"])
            for field, expected in source["independent_exact_binary64_reference"].items():
                self.assertEqual(primary[field]["exact"], expected)
            diagnostic = run["author_cut_diagnostic_unconfirmed_one_based"]
            self.assertEqual(diagnostic["index_convention"], raw.CUT_CONVENTION)
            self.assertEqual(diagnostic["aggregate"]["cycles"], cut_cycles)
            self.assertAlmostEqual(float(Fraction(diagnostic["aggregate"]["kappa"]["exact"])),
                                   float(source["independent_numpy_reference_not_exact"]["cut_diagnostic_kappa"]), places=13)
            inventory = run["cycle_inventory"]
            self.assertEqual([c["cycle_id_one_based"] for c in inventory], list(range(1, cycles + 1)))
            self.assertEqual(sum(not c["excluded_from_author_cut_diagnostic_only"] for c in inventory), cut_cycles)
            self.assertEqual(run["recorded_PD_samples"], samples)
            self.assertTrue(all(len(c["contexts_in_acquisition_order"]) == 8 for c in inventory))
        first_telemetry = runs[0]["temperature_housing_telemetry"]["counts_by_status"]
        second_telemetry = runs[1]["temperature_housing_telemetry"]["counts_by_status"]
        self.assertEqual(first_telemetry["not_recorded"], 3360)
        self.assertEqual(second_telemetry["recorded_finite"], 3599)
        self.assertEqual(second_telemetry["recorded_nonfinite_nan"], 1)
        bad_contexts = [context for c in runs[1]["cycle_inventory"] for context in c["contexts_in_acquisition_order"]
                        if context["temperature_housing_status"] == "recorded_nonfinite_nan"]
        self.assertEqual(len(bad_contexts), 1)
        self.assertEqual(bad_contexts[0]["record_id_one_based"], 1167)
        self.assertIsNone(bad_contexts[0]["temperature_housing_volt"])


if __name__ == "__main__":
    unittest.main()
