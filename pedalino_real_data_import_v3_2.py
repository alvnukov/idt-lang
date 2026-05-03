#!/usr/bin/env python3
"""
Pedalino 2026 real-data import for inherited distinguishability v3.2.

This script imports the public Zenodo dataset and extracts raw sinusoidal
visibility estimates from the April 2025 sodium-cluster interference scans.
It deliberately does not compute a lambda_I bound: V_env is not part of the
raw data and must be supplied by a frozen prediction object.
"""

from __future__ import annotations

import argparse
import json
import math
import zipfile
from dataclasses import dataclass
from pathlib import Path
from urllib.request import urlopen


ZENODO_RECORD_URL = "https://zenodo.org/records/17502163"
ZENODO_ZIP_URL = (
    "https://zenodo.org/records/17502163/files/"
    "Na-Cluster-Interference.zip?download=1"
)
DATASET_DOI = "10.5281/zenodo.17502163"
ARTICLE_DOI = "10.1038/s41586-025-09917-9"

SCAN_PREFIX = (
    "Na-Cluster-Interference/Na-Cluster/Data_April2025/22042025/"
    "Interference Scans/"
)
SCAN_SUFFIX = "_s1.dat"
MASS_SPECTRUM_ENTRY = (
    "Na-Cluster-Interference/Na-Cluster/Data_April2025/22042025/"
    "Mass spec/Sodium_He_60sccm_Ar_161sccm_356C_425nm_L12p5cm_HP_massscan_16.dat"
)

GRATING_PERIOD_M = 133e-9
L1_M = 0.98375
L2_M = 0.98375
V_MEAN_M_PER_S = 158.0
NOMINAL_MASS_DA = 170_000.0

Vector3 = tuple[float, float, float]
Matrix3 = tuple[Vector3, Vector3, Vector3]
JsonValue = None | bool | int | float | str | list["JsonValue"] | dict[str, "JsonValue"]
JsonObject = dict[str, JsonValue]


@dataclass(frozen=True)
class ScanPoint:
    x_m: float
    counts: float


@dataclass(frozen=True)
class ScanFit:
    name: str
    points: int
    baseline_counts: float
    visibility: float
    visibility_sigma: float
    phase_rad: float
    residual_rms_counts: float


@dataclass(frozen=True)
class ImportResult:
    scans_imported: int
    points_total: int
    best_scan: ScanFit
    mean_mass_da: float
    tau_single_spacing_s: float
    tau_two_spacing_s: float
    delta_x_proxy_m: float


def download_file(url: str, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    with urlopen(url, timeout=60) as response:
        target.write_bytes(response.read())


def parse_scan_points(raw: bytes) -> list[ScanPoint]:
    points: list[ScanPoint] = []
    for line_number, raw_line in enumerate(raw.decode("utf-8").splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2:
            raise ValueError(f"unexpected scan row at line {line_number}: {line!r}")
        points.append(ScanPoint(x_m=float(parts[0]) * 1e-9, counts=float(parts[1])))
    return points


def parse_mass_spectrum_da(raw: bytes) -> list[tuple[float, float]]:
    rows: list[tuple[float, float]] = []
    lower = 0.85 * NOMINAL_MASS_DA
    upper = 1.15 * NOMINAL_MASS_DA
    for line_number, raw_line in enumerate(raw.decode("utf-8").splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2:
            raise ValueError(f"unexpected mass-spectrum row at line {line_number}: {line!r}")
        mass_da = 2.0 * float(parts[0])
        counts = float(parts[1])
        if lower < mass_da < upper:
            rows.append((mass_da, counts))
    if not rows:
        raise ValueError("mass spectrum has no rows in the expected 170 kDa window")
    return rows


def weighted_mean(rows: list[tuple[float, float]]) -> float:
    total_weight = sum(weight for _, weight in rows)
    if total_weight <= 0:
        raise ValueError("weighted mean requires positive total weight")
    return sum(value * weight for value, weight in rows) / total_weight


def solve_3x3(matrix: Matrix3, vector: Vector3) -> Vector3:
    rows = [
        [matrix[0][0], matrix[0][1], matrix[0][2], vector[0]],
        [matrix[1][0], matrix[1][1], matrix[1][2], vector[1]],
        [matrix[2][0], matrix[2][1], matrix[2][2], vector[2]],
    ]
    for col in range(3):
        pivot = max(range(col, 3), key=lambda row: abs(rows[row][col]))
        if abs(rows[pivot][col]) < 1e-12:
            raise ValueError("singular normal matrix")
        if pivot != col:
            rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        for idx in range(col, 4):
            rows[col][idx] /= scale
        for row in range(3):
            if row == col:
                continue
            factor = rows[row][col]
            for idx in range(col, 4):
                rows[row][idx] -= factor * rows[col][idx]
    return (rows[0][3], rows[1][3], rows[2][3])


def invert_3x3(matrix: Matrix3) -> Matrix3:
    col0 = solve_3x3(matrix, (1.0, 0.0, 0.0))
    col1 = solve_3x3(matrix, (0.0, 1.0, 0.0))
    col2 = solve_3x3(matrix, (0.0, 0.0, 1.0))
    return (
        (col0[0], col1[0], col2[0]),
        (col0[1], col1[1], col2[1]),
        (col0[2], col1[2], col2[2]),
    )


def quadratic_form(matrix: Matrix3, vector: Vector3) -> float:
    return sum(
        vector[row] * matrix[row][col] * vector[col]
        for row in range(3)
        for col in range(3)
    )


def fit_visibility(name: str, points: list[ScanPoint]) -> ScanFit:
    if len(points) < 4:
        raise ValueError(f"{name} has too few points for a three-parameter fit")

    m00 = m01 = m02 = m11 = m12 = m22 = 0.0
    b0 = b1 = b2 = 0.0
    rows: list[Vector3] = []
    counts: list[float] = []

    for point in points:
        angle = 2.0 * math.pi * point.x_m / GRATING_PERIOD_M
        row = (1.0, math.cos(angle), math.sin(angle))
        rows.append(row)
        counts.append(point.counts)
        m00 += row[0] * row[0]
        m01 += row[0] * row[1]
        m02 += row[0] * row[2]
        m11 += row[1] * row[1]
        m12 += row[1] * row[2]
        m22 += row[2] * row[2]
        b0 += row[0] * point.counts
        b1 += row[1] * point.counts
        b2 += row[2] * point.counts

    normal_matrix: Matrix3 = ((m00, m01, m02), (m01, m11, m12), (m02, m12, m22))
    baseline, cos_coeff, sin_coeff = solve_3x3(normal_matrix, (b0, b1, b2))
    if baseline <= 0:
        raise ValueError(f"{name} fit produced non-positive baseline")

    amplitude = math.hypot(cos_coeff, sin_coeff)
    visibility = amplitude / baseline
    residual_sum = 0.0
    for row, count in zip(rows, counts, strict=True):
        prediction = baseline + cos_coeff * row[1] + sin_coeff * row[2]
        residual_sum += (count - prediction) ** 2
    dof = len(points) - 3
    residual_variance = residual_sum / dof
    inverse_normal = invert_3x3(normal_matrix)
    covariance: Matrix3 = tuple(
        tuple(residual_variance * value for value in row) for row in inverse_normal
    )
    if amplitude > 0:
        gradient = (
            -amplitude / (baseline * baseline),
            cos_coeff / (baseline * amplitude),
            sin_coeff / (baseline * amplitude),
        )
        visibility_variance = max(0.0, quadratic_form(covariance, gradient))
        visibility_sigma = math.sqrt(visibility_variance)
    else:
        visibility_sigma = 0.0
    phase_rad = math.atan2(-sin_coeff, cos_coeff)
    residual_rms = math.sqrt(residual_sum / len(points))

    return ScanFit(
        name=name,
        points=len(points),
        baseline_counts=baseline,
        visibility=visibility,
        visibility_sigma=visibility_sigma,
        phase_rad=phase_rad,
        residual_rms_counts=residual_rms,
    )


def scan_sort_key(name: str) -> int:
    stem = Path(name).name.removesuffix(SCAN_SUFFIX)
    return int(stem.rsplit("_", maxsplit=1)[1])


def import_pedalino_zip(zip_path: Path) -> ImportResult:
    with zipfile.ZipFile(zip_path) as archive:
        scan_entries = sorted(
            (
                name
                for name in archive.namelist()
                if name.startswith(SCAN_PREFIX) and name.endswith(SCAN_SUFFIX)
            ),
            key=scan_sort_key,
        )
        if not scan_entries:
            raise ValueError(f"no Pedalino scan entries found in {zip_path}")

        fits = [
            fit_visibility(Path(entry).name, parse_scan_points(archive.read(entry)))
            for entry in scan_entries
        ]
        mass_rows = parse_mass_spectrum_da(archive.read(MASS_SPECTRUM_ENTRY))

    best_scan = max(fits, key=lambda fit: fit.visibility)
    return ImportResult(
        scans_imported=len(fits),
        points_total=sum(fit.points for fit in fits),
        best_scan=best_scan,
        mean_mass_da=weighted_mean(mass_rows),
        tau_single_spacing_s=L1_M / V_MEAN_M_PER_S,
        tau_two_spacing_s=(L1_M + L2_M) / V_MEAN_M_PER_S,
        delta_x_proxy_m=GRATING_PERIOD_M,
    )


def fit_to_json(fit: ScanFit) -> JsonObject:
    return {
        "name": fit.name,
        "points": fit.points,
        "baseline_counts": fit.baseline_counts,
        "visibility": fit.visibility,
        "visibility_sigma": fit.visibility_sigma,
        "phase_rad": fit.phase_rad,
        "residual_rms_counts": fit.residual_rms_counts,
    }


def result_to_json(result: ImportResult) -> JsonObject:
    return {
        "theory_version": "v3.2",
        "fixture": "pedalino_2026_sodium_nanoparticle_interferometry",
        "source_dataset_doi": DATASET_DOI,
        "source_article_doi": ARTICLE_DOI,
        "source_record_url": ZENODO_RECORD_URL,
        "import_status": "real_data_import_complete",
        "lambda_I_bound_status": "blocked_missing_V_env",
        "scans_imported": result.scans_imported,
        "points_total": result.points_total,
        "V_obs_raw_fit": result.best_scan.visibility,
        "sigma_V_raw_fit": result.best_scan.visibility_sigma,
        "best_scan": fit_to_json(result.best_scan),
        "mean_mass_da_from_mass_spectrum_window": result.mean_mass_da,
        "tau_single_spacing_s": result.tau_single_spacing_s,
        "tau_two_spacing_s": result.tau_two_spacing_s,
        "delta_x_proxy_m": result.delta_x_proxy_m,
        "missing_for_lambda_bound": ["V_env", "frozen_tau_policy", "frozen_delta_x_policy"],
    }


def format_sci(value: float) -> str:
    return f"{value:.6g}"


def build_markdown_report(result: ImportResult) -> str:
    best = result.best_scan
    return "\n".join(
        [
            "# Pedalino Real Data Import Report v3.2",
            "",
            "## Source",
            "",
            f"- fixture: `pedalino_2026_sodium_nanoparticle_interferometry`",
            f"- dataset DOI: `{DATASET_DOI}`",
            f"- article DOI: `{ARTICLE_DOI}`",
            f"- source record: {ZENODO_RECORD_URL}",
            "",
            "## Import Result",
            "",
            "- import_status: `real_data_import_complete`",
            f"- scans_imported: {result.scans_imported}",
            f"- points_total: {result.points_total}",
            f"- mean_mass_da_from_mass_spectrum_window: {format_sci(result.mean_mass_da)}",
            f"- tau_single_spacing_s: {format_sci(result.tau_single_spacing_s)}",
            f"- tau_two_spacing_s: {format_sci(result.tau_two_spacing_s)}",
            f"- delta_x_proxy_m: {format_sci(result.delta_x_proxy_m)}",
            "",
            "## Extracted Raw Visibility Anchor",
            "",
            f"- best_scan: `{best.name}`",
            f"- V_obs_raw_fit: {format_sci(best.visibility)}",
            f"- sigma_V_raw_fit: {format_sci(best.visibility_sigma)}",
            f"- phase_rad: {format_sci(best.phase_rad)}",
            f"- baseline_counts: {format_sci(best.baseline_counts)}",
            f"- residual_rms_counts: {format_sci(best.residual_rms_counts)}",
            "",
            "## Bound Gate",
            "",
            "- lambda_I_bound_status: `blocked_missing_V_env`",
            "- missing_for_lambda_bound: `V_env`, `frozen_tau_policy`, `frozen_delta_x_policy`",
            "",
            "No `lambda_I` bound is emitted by v3.2 import. The imported raw visibility",
            "is an observed data anchor, not an environment-corrected residual.",
            "",
        ]
    )


def resolve_zip_path(cache_dir: Path, explicit_zip: Path | None) -> Path:
    if explicit_zip is not None:
        if not explicit_zip.exists():
            raise FileNotFoundError(explicit_zip)
        return explicit_zip
    zip_path = cache_dir / "Na-Cluster-Interference.zip"
    if not zip_path.exists():
        download_file(ZENODO_ZIP_URL, zip_path)
    return zip_path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zip", dest="zip_path", type=Path, default=None)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/idt_v3_2"))
    parser.add_argument("--report", type=Path, default=Path("pedalino_real_data_report_v3_2.md"))
    parser.add_argument("--json", dest="json_path", type=Path, default=None)
    args = parser.parse_args()

    zip_path = resolve_zip_path(args.cache_dir, args.zip_path)
    result = import_pedalino_zip(zip_path)
    args.report.write_text(build_markdown_report(result), encoding="utf-8")
    if args.json_path is not None:
        args.json_path.write_text(
            json.dumps(result_to_json(result), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(f"Wrote {args.report}")


if __name__ == "__main__":
    main()
