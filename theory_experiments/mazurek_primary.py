"""Offline primary coincidence frequencies, not a secondary-procedure replay.

Mazurek et al., Nature Communications 7, 11780 (2016),
doi:10.1038/ncomms11780, CC BY 4.0. Normalized counts only: the archive
retains the original integer counts in canonical JSON, not normalized rates,
source workbooks, or the authors' analysis software.
"""

from __future__ import annotations

import gzip
import hashlib
import io
import json
import math
import os
import re
import stat
import statistics
import zlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from xml.etree import ElementTree as ET
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "data/raw_observations/mazurek2016_counts.json.gz"
SCHEMA = "idt-mazurek-primary-coincidences/1"
CANONICAL_SHA256 = "812528645ab002381cdbab3f7068fa1f8d04e4f59dec2789eee55e88424198ba"
MAX_JSON = 64 * 1024
MAX_COMPRESSED = 64 * 1024
MAX_COUNT = 10_000_000
PREPARATIONS = tuple(f"P_{m},{b}" for m in range(1, 5) for b in range(2))
MEASUREMENTS = tuple(f"[{b}|M{m}]" for m in range(1, 5) for b in range(2))
DENOMINATORS = tuple(f"M{m}" for m in range(1, 5) for _ in range(2))
_XLSX = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
_REL = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"
_PKG = "{http://schemas.openxmlformats.org/package/2006/relationships}"
_MEDIA = "https://static-content.springer.com/esm/art%3A10.1038%2Fncomms11780/MediaObjects/"

Matrix = tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class Counts:
    aggregate: Matrix
    runs: tuple[Matrix, ...]


@dataclass(frozen=True)
class Source:
    filename: str
    sheet: str
    cell_range: str
    size: int
    sha256: str

    def receipt(self) -> dict[str, object]:
        return {"filename": self.filename, "sheet": self.sheet, "range": self.cell_range,
                "size": self.size, "sha256": self.sha256, "url": _MEDIA + self.filename}


AGGREGATE_SOURCE = Source(
    "41467_2016_BFncomms11780_MOESM1462_ESM.xlsx", "counts_photons_100_runs_2s_thic", "A2:I10", 10786,
    "be168293d7755c273fbaff71c9c3d66f54773aa9d40f0ec46c39bd3765a64bfb",
)
RUN_SOURCE = Source(
    "41467_2016_BFncomms11780_MOESM1463_ESM.xlsx", "counts_per_each_run", "A2:R802", 98925,
    "11d000550a4248135a2032a2712c24a118cdf529fb0c01a1e11e4bf76993cd5e",
)


def _read_regular(path: Path, limit: int) -> bytes:
    # Refuse links to other files and avoid blocking on a pipe presented as an input.
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        meta = os.fstat(fd)
        if not stat.S_ISREG(meta.st_mode) or not 0 < meta.st_size <= limit:
            raise ValueError(f"{path.name}: expected a bounded nonempty regular file")
        with os.fdopen(fd, "rb", closefd=False) as source:
            raw = source.read(limit + 1)
    finally:
        os.close(fd)
    if len(raw) != meta.st_size:
        raise ValueError(f"{path.name}: size changed while reading")
    return raw


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _matrix(value: object) -> Matrix:
    if not isinstance(value, list) or len(value) != 8:
        raise ValueError("expected eight preparation rows")
    rows = []
    for row in value:
        if not isinstance(row, list) or len(row) != 8:
            raise ValueError("expected eight outcome columns")
        if any(type(n) is not int or not 0 <= n <= MAX_COUNT for n in row):
            raise ValueError("counts must be bounded nonnegative integers")
        if any(row[c] + row[c + 1] == 0 for c in range(0, 8, 2)):
            raise ValueError("a detected-coincidence denominator is zero")
        rows.append(tuple(row))
    return tuple(rows)


def canonical_bytes(counts: Counts) -> bytes:
    return json.dumps({"schema": SCHEMA, "aggregate": counts.aggregate, "runs": counts.runs},
                      sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _parse_counts(raw: bytes) -> Counts:
    if not 0 < len(raw) <= MAX_JSON:
        raise ValueError("canonical counts payload exceeds its byte bounds")
    value = json.loads(raw.decode("utf-8"), object_pairs_hook=_unique_object)
    if not isinstance(value, dict) or value.keys() != {"schema", "aggregate", "runs"} or value["schema"] != SCHEMA:
        raise ValueError("invalid counts schema")
    runs = value["runs"]
    if not isinstance(runs, list) or len(runs) != 100:
        raise ValueError("expected 100 runs in original order")
    counts = Counts(_matrix(value["aggregate"]), tuple(_matrix(run) for run in runs))
    if raw != canonical_bytes(counts) or hashlib.sha256(raw).hexdigest() != CANONICAL_SHA256:
        raise ValueError("canonical counts digest or serialization mismatch")
    return counts


def load_counts(path: Path = FIXTURE) -> Counts:
    """Load the pinned counts, rejecting trailing members, corruption and alternate data."""
    compressed = _read_regular(path, MAX_COMPRESSED)
    decoder = zlib.decompressobj(wbits=31)
    try:
        raw = decoder.decompress(compressed, MAX_JSON + 1)
    except zlib.error as error:
        raise ValueError("invalid gzip counts fixture") from error
    if not decoder.eof or decoder.unused_data or len(raw) > MAX_JSON:
        raise ValueError("truncated, oversized or trailing data in gzip counts fixture")
    return _parse_counts(raw)


def _source_bytes(path: Path, source: Source) -> bytes:
    raw = _read_regular(path, source.size)
    if len(raw) != source.size or hashlib.sha256(raw).hexdigest() != source.sha256:
        raise ValueError(f"{source.sheet}: workbook size or SHA-256 mismatch")
    return raw


def _xml(archive: ZipFile, name: str, limit: int) -> ET.Element:
    with archive.open(name) as source:
        raw = source.read(limit + 1)
    if len(raw) > limit or b"<!DOCTYPE" in raw or b"<!ENTITY" in raw:
        raise ValueError("invalid or oversized source workbook XML")
    return ET.fromstring(raw)


def _sheet(raw: bytes, expected_name: str) -> dict[str, str | int]:
    # Caller pins the exact workbook bytes before parsing any ZIP member.
    with ZipFile(io.BytesIO(raw)) as archive:
        names = archive.namelist()
        if len(names) > 20 or len(set(names)) != len(names):
            raise ValueError("invalid workbook member names")
        workbook = _xml(archive, "xl/workbook.xml", 4096)
        sheets = workbook.findall(f"{_XLSX}sheets/{_XLSX}sheet")
        relations = _xml(archive, "xl/_rels/workbook.xml.rels", 4096)
        if len(sheets) != 1 or sheets[0].get("name") != expected_name:
            raise ValueError("unexpected workbook sheet")
        links = [rel for rel in relations if rel.tag == _PKG + "Relationship"
                 and rel.get("Id") == sheets[0].get(_REL + "id")]
        if (len(links) != 1 or links[0].get("Target") != "worksheets/sheet1.xml"
                or links[0].get("Type") != _REL[1:-1] + "/worksheet" or links[0].get("TargetMode") is not None):
            raise ValueError("unexpected workbook worksheet relationship")
        strings = ["".join(si.itertext()) for si in _xml(archive, "xl/sharedStrings.xml", 4096)]
        sheet = _xml(archive, "xl/worksheets/sheet1.xml", 512 * 1024)
    cells: dict[str, str | int] = {}
    for cell in sheet.findall(f"{_XLSX}sheetData/{_XLSX}row/{_XLSX}c"):
        address, value = cell.get("r"), cell.findtext(_XLSX + "v")
        if value is None:
            continue  # Style-only cells outside the recorded table are not values.
        if address is None or address in cells:
            raise ValueError("missing or duplicate workbook cell address")
        if not re.fullmatch(r"[0-9]{1,9}", value):
            raise ValueError(f"{address}: expected integer or shared string index")
        number = int(value)
        if cell.get("t") == "s" and number < len(strings):
            cells[address] = strings[number]
        elif cell.get("t", "n") == "n":
            cells[address] = number  # Includes the cached run-number series, never evaluated.
        else:
            raise ValueError(f"{address}: unexpected workbook cell type")
    return cells


def _columns(cells: dict[str, str | int], row: int, columns: str) -> list[str | int]:
    values = [cells.get(f"{column}{row}") for column in columns]
    if any(value is None for value in values):
        raise ValueError(f"row {row}: missing expected workbook cell")
    return [value for value in values if value is not None]


def extract_workbooks(aggregate: Path, runs: Path) -> Counts:
    """Return counts from exactly the two publisher files; no network or writes."""
    aggregate_raw = _source_bytes(aggregate, AGGREGATE_SOURCE)
    run_raw = _source_bytes(runs, RUN_SOURCE)
    a = _sheet(aggregate_raw, AGGREGATE_SOURCE.sheet)
    r = _sheet(run_raw, RUN_SOURCE.sheet)
    if tuple(_columns(a, 2, "ABCDEFGHI")) != ("Preparation", *MEASUREMENTS):
        raise ValueError("aggregate workbook outcome labels differ")
    if tuple(_columns(r, 2, "ABCDEFGHIJKLMNOPQR")) != ("Run #", "Preparation", *MEASUREMENTS, *DENOMINATORS):
        raise ValueError("run workbook outcome or denominator labels differ")
    if tuple(a.get(f"A{3 + i}") for i in range(8)) != PREPARATIONS:
        raise ValueError("aggregate workbook preparation labels differ")
    totals = _matrix([_columns(a, row, "BCDEFGHI") for row in range(3, 11)])
    matrices = []
    for run in range(100):
        start = 3 + 8 * run
        raw_rows = [_columns(r, row, "ABCDEFGHIJKLMNOPQR") for row in range(start, start + 8)]
        if any(row[:2] != [run + 1, prep] for row, prep in zip(raw_rows, PREPARATIONS, strict=True)):
            raise ValueError(f"run {run + 1}: original run number or preparation labels differ")
        matrix = _matrix([row[2:10] for row in raw_rows])
        for source_row, row_counts in zip(raw_rows, matrix, strict=True):
            expected = [row_counts[c - c % 2] + row_counts[c - c % 2 + 1] for c in range(8)]
            if source_row[10:] != expected:
                raise ValueError(f"run {run + 1}: coincidence denominators differ")
        matrices.append(matrix)
    return _parse_counts(canonical_bytes(Counts(totals, tuple(matrices))))


def write_counts(destination: Path, counts: Counts) -> None:
    """Write a deterministic gzip fixture, exclusively, after checking its content."""
    if not destination.name.endswith(".json.gz"):
        raise ValueError("destination must end with .json.gz")
    raw = canonical_bytes(counts)
    _parse_counts(raw)
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", mtime=0, filename="") as compressed:
        compressed.write(raw)
    with destination.open("xb") as output:
        output.write(buffer.getvalue())


def _a(counts: Matrix) -> Fraction:
    # Only matched preparation/measurement pairs 1–3 enter A. The fourth
    # setting and pair were included for tomography; retain them, don't relabel them.
    return sum((Fraction(counts[i][i], counts[i][i] + counts[i][i ^ 1]) for i in range(6)), Fraction()) / 6


def summarize(counts: Counts) -> dict[str, object]:
    pooled = tuple(tuple(sum(run[i][j] for run in counts.runs) for j in range(8)) for i in range(8))
    mismatches = [(i, j) for i in range(8) for j in range(8) if counts.aggregate[i][j] != pooled[i][j]]
    scores = [_a(run) for run in counts.runs]
    sd = statistics.stdev(map(float, scores))
    return {
        "scope": "primary detected-coincidence frequencies only; not the published secondary result or an unconditional rejection",
        "doi": "10.1038/ncomms11780", "license": "CC BY 4.0", "canonical_sha256": CANONICAL_SHA256,
        "source_workbooks": {"aggregate": AGGREGATE_SOURCE.receipt(), "runs": RUN_SOURCE.receipt()},
        "preparation_labels": PREPARATIONS, "outcome_labels": MEASUREMENTS, "runs": len(scores),
        "matched_pairs_in_a": [1, 2, 3], "fourth_pair_role": "additional tomography settings, not part of A",
        "run_mean_a": float(sum(scores, Fraction()) / len(scores)), "run_sample_sd_a": sd,
        "run_sem_a": sd / math.sqrt(len(scores)), "pooled_a": float(_a(pooled)),
        "pooled_a_definition": "pool outcomes across runs within each matched cell pair, then average six rates equally",
        "source_comparison": {
            "exact_first_six_preparation_rows": all(i >= 6 for i, _ in mismatches),
            "mismatched_cells_in_original_order": len(mismatches),
            "mismatched_preparation_labels": [PREPARATIONS[i] for i in sorted({i for i, _ in mismatches})],
            "matches_after_fourth_pair_row_swap_diagnostic_only": counts.aggregate == (*pooled[:6], pooled[7], pooled[6]),
            "correction_applied": False,
        },
    }
