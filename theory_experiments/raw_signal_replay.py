"""Gstir2021 digitized-voltage replay, not a candidate or physical inference engine.

Pure reductions use exact rational arithmetic on the recorded binary64 values.
Only the pinned-file reader imports optional h5py; ordinary checking needs none.
"""

from __future__ import annotations

import hashlib
import importlib
import json
import math
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from datetime import date
from decimal import ROUND_HALF_EVEN, Context, Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, cast

from theory_experiments.nuisance_bounds import (
    NuisanceBounds,
    ReplayTarget,
    assert_loaded_source_unchanged,
    assess_epsilon,
)

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "data/raw_observations/gstir2021.json"
CUT_CONVENTION = "published_indices_interpreted_as_one_based_not_explicitly_confirmed"
RECIPE = {
    "id": "gstir2021_all_recorded_samples_binary64_fraction_v1",
    "context_mean": "exact_mean_of_all_recorded_binary64_PD_voltages",
    "cycle": "consecutive_eight_records_each_mask_once_original_order_retained",
    "mask": "low_bit_A_next_B_high_C",
    "epsilon": "p7-p3-p5-p6+p1+p2+p4-p0",
    "delta": "abs(p3-p1-p2+p0)+abs(p5-p1-p4+p0)+abs(p6-p2-p4+p0)",
    "aggregate": "mean_cycle_epsilon/mean_cycle_delta_not_mean_cycle_kappa",
    "zero_delta": "retain_cycle_and_aggregate_terms_kappa_undefined",
    "primary_selection": "all_cycles_no_fit_no_outlier_cuts",
    "author_cut_diagnostic": CUT_CONVENTION,
    "settling_treatment": "none_full_window_is_our_recipe_not_author_reproduction",
    "ancillary_temperature": "unused_in_reduction_preserve_nonfinite_classification_no_imputation",
    "response_assumptions": "common_positive_affine_response_preserves_kappa_negative_gain_flips_sign_not_inferred",
}


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


PROVENANCE_PATHS = (REGISTRY, Path(__file__), ROOT / "scripts/replay_gstir2021.py",
                    ROOT / "theory_experiments/nuisance_bounds.py",
                    ROOT / "Proofs/QMClosure/PublishedSorkinNull.lean",
                    ROOT / "Proofs/QMClosure/SorkinErrorBudget.lean",
                    ROOT / "Proofs/MetaLang/V8CheckerResearchProgram.lean",
                    ROOT / "lakefile.lean")


def provenance() -> dict[str, str]:
    assert_loaded_source_unchanged()
    return {str(p.relative_to(ROOT)): sha256(p) for p in PROVENANCE_PATHS}


LOADED_SOURCE_HASHES = provenance()


def number(value: Fraction) -> dict[str, str]:
    """Exact digitized arithmetic is authoritative; display has 18 significant digits."""
    with localcontext(Context(prec=18, rounding=ROUND_HALF_EVEN, Emin=-999999, Emax=999999,
                              capitals=1, clamp=0, flags=[], traps=[])):
        display = str(Decimal(value.numerator) / Decimal(value.denominator))
    return {"exact": str(value), "decimal_18_significant_digits": display}


@dataclass(frozen=True)
class CycleReduction:
    means: tuple[Fraction, ...]  # indexed by context mask, not acquisition order
    epsilon: Fraction
    delta: Fraction

    @property
    def kappa(self) -> Fraction | None:
        return self.epsilon / self.delta if self.delta else None


def reduce_cycle(records: Sequence[tuple[int, tuple[float, ...]]]) -> CycleReduction:
    """One complete eight-context cycle; no background fit or rounding."""
    if len(records) != 8 or {mask for mask, _ in records} != set(range(8)):
        raise ValueError("cycle requires each integer mask 0..7 exactly once")
    means = [Fraction(0)] * 8
    for mask, samples in records:
        if type(mask) is not int or not samples or any(not math.isfinite(x) for x in samples):
            raise ValueError("invalid mask or empty/nonfinite voltage samples")
        means[mask] = sum((Fraction.from_float(x) for x in samples), Fraction(0)) / len(samples)
    p = means
    epsilon = p[7] - p[3] - p[5] - p[6] + p[1] + p[2] + p[4] - p[0]
    delta = abs(p[3] - p[1] - p[2] + p[0]) + abs(p[5] - p[1] - p[4] + p[0])
    delta += abs(p[6] - p[2] - p[4] + p[0])
    return CycleReduction(tuple(means), epsilon, delta)


def aggregate(cycles: list[CycleReduction]) -> dict[str, object]:
    if not cycles:
        raise ValueError("cannot aggregate an empty inventory")
    epsilon = sum((c.epsilon for c in cycles), Fraction(0)) / len(cycles)
    delta = sum((c.delta for c in cycles), Fraction(0)) / len(cycles)
    return {"cycles": len(cycles), "mean_epsilon_volt": number(epsilon),
            "mean_delta_volt": number(delta),
            "kappa": number(epsilon / delta) if delta else None,
            "undefined_reason": None if delta else "zero_mean_delta",
            "zero_delta_cycles_retained": sum(c.delta == 0 for c in cycles)}


def registry() -> dict[str, Any]:
    # This is a fixed repository registry, never candidate-supplied configuration.
    result: dict[str, Any] = json.loads(REGISTRY.read_text())
    if result["schema"] != "idt-gstir2021-raw-registry/1":
        raise ValueError("unsupported fixed registry schema")
    return result


def cut_masks(source: dict[str, Any], cycle_id: int) -> list[int]:
    """Diagnostic-only convention: published cycle numbers interpreted as one-based."""
    return [int(mask) for mask, ids in source["author_cut_indices_by_mask"].items()
            if cycle_id in ids]


def temperature_telemetry(value: float | None) -> tuple[dict[str, str] | None, str]:
    """Ancillary only: do not impute, calibrate, select cycles, or infer temperature."""
    if value is None:
        return None, "not_recorded"
    if math.isnan(value):
        return None, "recorded_nonfinite_nan"
    if math.isinf(value):
        return None, "recorded_nonfinite_positive_infinity" if value > 0 else "recorded_nonfinite_negative_infinity"
    return number(Fraction.from_float(value)), "recorded_finite"


def _timestamp(raw: list[float]) -> tuple[float, ...]:
    if len(raw) != 6 or any(not math.isfinite(x) for x in raw):
        raise ValueError("nonfinite or malformed sample calendar timestamp")
    if any(x != int(x) for x in raw[:5]) or not 0 <= raw[5] < 60:
        raise ValueError("invalid sample calendar components")
    date(*(int(x) for x in raw[:3]))
    if not 0 <= raw[3] < 24 or not 0 <= raw[4] < 60:
        raise ValueError("invalid sample hour/minute; recorded timezone unspecified")
    return tuple(raw)


def _read_run(path: Path, source: dict[str, Any]) -> dict[str, object]:
    """Fail closed before returning anything; no partial successful inventory."""
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"raw input must be a regular non-symlink file: {path.name}")
    if path.stat().st_size != source["size_bytes"] or sha256(path) != source["sha256"]:
        raise ValueError(f"pinned source size/SHA256 mismatch: {path.name}")
    try:
        h5py = importlib.import_module("h5py")
    except ModuleNotFoundError as error:
        raise ValueError("optional h5py required: uv run --with h5py python scripts/replay_gstir2021.py ...") from error
    reductions: list[CycleReduction] = []
    diagnostic: list[CycleReduction] = []
    inventory: list[dict[str, object]] = []
    telemetry_counts = dict.fromkeys(("not_recorded", "recorded_finite", "recorded_nonfinite_nan",
                                    "recorded_nonfinite_positive_infinity", "recorded_nonfinite_negative_infinity"), 0)
    previous_time: tuple[float, ...] | None = None
    cycles, samples = source["cycles"], source["samples_per_context"]
    records = 8 * cycles
    with h5py.File(path, "r") as data:
        shapes = {"PD signal": (records, samples, 1), "shuttercombination": (records, 1, 1),
                  "time": (records, samples, 6)}
        if source["temperature_housing"]:
            shapes["temperature-housing"] = (records, 1, 1)
        if set(data.keys()) != set(shapes):
            raise ValueError("unexpected or missing HDF5 datasets")
        for name, shape in shapes.items():
            dataset = data[name]
            if not isinstance(dataset, h5py.Dataset) or dataset.shape != shape or dataset.dtype.str != "<f8":
                raise ValueError(f"invalid dataset shape/binary64 dtype: {name}")
        if data.attrs.get("cycles") != cycles or data.attrs.get("datapoints per comb") != samples:
            raise ValueError("HDF5 acquisition counts mismatch")
        expected_attrs = {
            "PD signal": {"unit": "volt", "device": source["detector"]},
            "time": {"unit": "[YYYY, MM, DD, hh, mm, ss.ss]"},
        }
        if source["temperature_housing"]:
            expected_attrs["temperature-housing"] = {
                "unit": "volt", "device": source["temperature_device"], "set_value": "30°C"}
        for name, attrs in expected_attrs.items():
            if any(data[name].attrs.get(key) != value for key, value in attrs.items()):
                raise ValueError(f"invalid native unit/device metadata: {name}")
        for cycle_index in range(cycles):
            context_records: list[tuple[int, tuple[float, ...]]] = []
            contexts: list[dict[str, object]] = []
            for index in range(cycle_index * 8, (cycle_index + 1) * 8):
                raw_mask = float(data["shuttercombination"][index, 0, 0])
                if not math.isfinite(raw_mask) or raw_mask != int(raw_mask) or not 0 <= raw_mask <= 7:
                    raise ValueError("invalid shutter mask")
                mask = int(raw_mask)
                values = tuple(float(x) for x in data["PD signal"][index, :, 0])
                times = [_timestamp(row) for row in data["time"][index, :, :].tolist()]
                for timestamp in times:
                    if previous_time is not None and timestamp < previous_time:
                        raise ValueError("sample timestamps out of acquisition order")
                    previous_time = timestamp
                voltage = float(data["temperature-housing"][index, 0, 0]) if source["temperature_housing"] else None
                temperature, telemetry_status = temperature_telemetry(voltage)
                telemetry_counts[telemetry_status] += 1
                context_records.append((mask, values))
                contexts.append({"record_id_one_based": index + 1, "mask": mask,
                                 "samples": len(values), "sample_time_start": times[0],
                                 "sample_time_end": times[-1],
                                 "temperature_housing_volt": temperature,
                                 "temperature_housing_status": telemetry_status})
            reduction = reduce_cycle(context_records)
            reductions.append(reduction)
            cuts = cut_masks(source, cycle_index + 1)
            if not cuts:
                diagnostic.append(reduction)
            for context in contexts:
                context_mask = context["mask"]
                assert isinstance(context_mask, int)
                context["mean_PD_volt"] = number(reduction.means[context_mask])
            inventory.append({"cycle_id_one_based": cycle_index + 1,
                              "contexts_in_acquisition_order": contexts,
                              "epsilon_volt": number(reduction.epsilon),
                              "delta_volt": number(reduction.delta),
                              "kappa": number(reduction.kappa) if reduction.kappa is not None else None,
                              "undefined_reason": None if reduction.delta else "zero_cycle_delta",
                              "author_cut_diagnostic_masks": cuts,
                              "excluded_from_author_cut_diagnostic_only": bool(cuts)})
    if sha256(path) != source["sha256"]:
        raise ValueError("raw source changed while reading")
    return {"source": source, "recorded_PD_samples": records * samples,
            "temperature_housing_telemetry": {"native_unit": "volt", "counts_by_status": telemetry_counts,
                                              "role": "ancillary_unused_in_reduction_no_temperature_calibration"},
            "primary_all_cycles": aggregate(reductions),
            "author_cut_diagnostic_unconfirmed_one_based": {
                "index_convention": CUT_CONVENTION, "not_author_reproduction": True,
                "selection": "exclude_whole_cycle_if_any_context_index_listed",
                "aggregate": aggregate(diagnostic)}, "cycle_inventory": inventory}


def replay(raw_directory: Path, *,
           bounds_by_run: Mapping[str, NuisanceBounds] | None = None) -> dict[str, object]:
    """Fixed runs; optional operator-supplied bounds, never candidate configuration."""
    hashes = provenance()
    if hashes != LOADED_SOURCE_HASHES:
        raise ValueError("replay sources changed since import; restart interpreter")
    sources = registry()
    supplied = dict(bounds_by_run) if bounds_by_run is not None else {}
    if set(supplied) - {source["id"] for source in sources["runs"]}:
        raise ValueError("bounds supplied for an unknown fixed run")
    recipe_sha = hashlib.sha256(canonical_json(RECIPE).encode()).hexdigest()
    runs = []
    for source in sources["runs"]:
        run = _read_run(raw_directory / source["filename"], source)
        primary = cast(dict[str, Any], run["primary_all_cycles"])
        target = ReplayTarget(source["id"], source["sha256"], recipe_sha)
        run["nuisance_assessment"] = assess_epsilon(
            Fraction(primary["mean_epsilon_volt"]["exact"]), target,
            supplied.get(source["id"], NuisanceBounds())).as_report()
        runs.append(run)
    if hashes != provenance():
        raise ValueError("replay implementation or registry changed during execution")
    return {"schema": "idt-gstir2021-raw-replay/2", "execution_status": "complete",
            "scientific_status": "descriptive_digitized_voltage_replay_only",
            "candidate_verdict": "not_assessed", "native_PD_unit": "volt",
            "arithmetic": "exact_fractions_of_recorded_binary64_not_exact_physical_means",
            "recipe": RECIPE,
            "recipe_sha256": recipe_sha,
            "source_and_implementation_sha256": hashes,
            "provenance": sources["provenance"],
            "nuisance_evidence_audit": sources["nuisance_evidence"],
            "conditional_ideal_zero_comparison": {
                "ideal_epsilon": "0", "ideal_kappa": "0",
                "ideal_kappa_condition": "ideal_model_delta_nonzero",
                "recorded_delta_boundary": "observed_positive_or_nonzero_denominators_do_not_establish_ideal_model_nonzero_delta_or_physical_bridge",
                "meaning": "descriptive_only_under_existing_fixed_path_quadratic_readout_assumptions",
                "artifact": "Proofs/QMClosure/PublishedSorkinNull.lean",
                "nuisance_bias": "unmodeled_not_zero", "physical_bridge": "unestablished",
                "not_universal_apparatus_prediction": True},
            "limitations": sources["limitations"], "runs": runs}
