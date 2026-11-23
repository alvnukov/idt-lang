"""Replay a published two-detector delay histogram against a pump-indexed clock.

Münzberg et al., DOI 10.1063/5.0091867, Fig. 2(d), data DOI
10.5281/zenodo.6337697 (CC BY 4.0). The authors used resonant pi pulses on
one quantum dot at 76.2 MHz, all modulators off, and a fixed 50:50 routing
to two avalanche photodiodes. The CSV is a pre-extraction cross-correlation
histogram, NOT a complete time-ordered file of shots. This retrospective
analysis is separate from the authors' reported g²(0) = 0.016(1).

If one four-cycle tick occurs on *every pump pulse*, a fixed map from phase
to one output arm gives the same arm on pulses j and j+4. Ideal unlike-arm
coincidences at that lag are forbidden at any starting phase, even after
arbitrary deletion of true detections. This support test does not assume
that deletions are independent. Correct lag assignment, a common fixed
setting/phase evolution, and no false, multiple, or misrouted events matter.
An emission- or detection-indexed clock need not have the same prediction.
Neither the pulse-to-tick rule nor the link to an IDT field is derived.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

FILENAME = "HBT_QD5_resonant_no_AB_att_0.0043_software_delay_16-44-38.csv"
DEFAULT_FILE = Path(__file__).resolve().parents[1] / "data" / "pump_hbt" / FILENAME
SOURCE_SHA256 = "e0767eeac5644e955c35962384943e6dd4e3cfcc1347ff1c0644fd2dca463556"
SOURCE_SIZE = 68128
LAGS = (-5, -4, -3, 0, 3, 4, 5)
# At the quoted 76.2 MHz the pump period is 5,000,000 / 381 ps.
PERIOD_NUM_PS, PERIOD_DEN = 5_000_000, 381


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def read_histogram(data: bytes) -> tuple[list[tuple[int, int]], str]:
    """Accept the published bytes or their homogeneous LF-only equivalent."""
    lf = data.replace(b"\r\n", b"\n")
    official = lf.replace(b"\n", b"\r\n")
    require(data in (lf, official), "mixed line endings")
    require(len(official) == SOURCE_SIZE and hashlib.sha256(official).hexdigest() == SOURCE_SHA256,
            "file does not match the pinned Zenodo source")
    rows = csv.reader(io.StringIO(lf.decode("ascii")))
    require(next(rows) == ["Time (s)", "Counts"], "unexpected column names")
    histogram = []
    for i, (seconds, count) in enumerate(rows):
        delay_ps = Fraction(seconds) * 10**12
        require(delay_ps == -125_000 + i * 50, "delay bins are not the recorded 50 ps grid")
        require(count.isdecimal(), "expected a nonnegative integer count")
        histogram.append((int(delay_ps), int(count)))
    require(len(histogram) == 5000, "incomplete delay grid")
    return histogram, hashlib.sha256(data).hexdigest()


def count_window(histogram: list[tuple[int, int]], lag: int, half_width_ps: int) -> int:
    """Sum uncorrected coincidences in a closed interval about lag times T."""
    return sum(c for t, c in histogram
               if abs(PERIOD_DEN * t - lag * PERIOD_NUM_PS) <= PERIOD_DEN * half_width_ps)


def window_report(histogram: list[tuple[int, int]], half_width_ps: int) -> dict:
    counts = {k: count_window(histogram, k, half_width_ps) for k in LAGS}
    lag4 = counts[-4] + counts[4]
    neighbors = sum(counts[k] for k in (-5, -3, 3, 5))
    return {
        "half_width_ps": half_width_ps,
        "signed_lag_counts": counts,
        "lag4_total": lag4,
        "neighbor_total": neighbors,
        "mean_lag4_over_mean_neighbor": (2 * lag4 / neighbors if neighbors else None),
    }


def controls() -> dict:
    # All static binary arm assignments include all choices of initial phase.
    for word in product((0, 1), repeat=4):
        line = word * 3
        require(not any(line[i] != line[i + 4] for i in range(len(line) - 4)),
                "same-phase four-pump pair must have identical arm")
    # Censoring true records can only remove pairs at fixed pump indices.
    # Compare skipping one emission with just losing its tag (clock still ticks).
    emitted = (True, False, True, True, True)
    word = (0, 0, 1, 1)
    pump_clock = [word[i % 4] if e else None for i, e in enumerate(emitted)]
    event_clock = iter(word)
    emission_clock = [next(event_clock) if e else None for e in emitted]
    require((pump_clock[0], pump_clock[4]) == (0, 0) and
            (emission_clock[0], emission_clock[4]) == (0, 1), "missed-emission countercontrol")
    # A deterministic period-seven binary word has flat *directed* side counts
    # at the compared nonzero lags. Agreement of these moments is not iid.
    seven = (1, 1, 1, 0, 1, 0, 0)
    directed = {k: sum((seven[j], seven[(j + k) % 7]) == (0, 1) for j in range(7))
                for k in LAGS}
    require(all(n == (0 if k == 0 else 2) for k, n in directed.items()),
            "deterministic flat-side-peak control")
    require(count_window([(-1501, 1), (-1500, 2), (1500, 4), (1501, 8)], 0, 1500) == 6,
            "window boundary convention")
    return {"pulse_four_cycle_ideal_lag4_unlike_pairs": 0,
            "same_deleted_pulse_pump_clock": pump_clock, "emission_clock": emission_clock,
            "period_seven_word": seven, "period_seven_directed_counts": directed}


def analyze(data: bytes) -> dict:
    histogram, actual_sha = read_histogram(data)
    primary = window_report(histogram, 1500)
    return {
        "source": {"publication_doi": "10.1063/5.0091867", "figure": "2(d)",
                   "dataset_doi": "10.5281/zenodo.6337697", "file": FILENAME,
                   "license": "CC BY 4.0", "actual_sha256": actual_sha,
                   "official_crlf_sha256": SOURCE_SHA256, "bins": len(histogram),
                   "bin_width_ps": 50, "nominal_pump_frequency_MHz": 76.2},
        "primary_retrospective": primary,
        "half_width_sensitivity": [window_report(histogram, w) for w in (1000, 2000)],
        "controls": controls(),
        "observed_positive_cross_counts_at_both_lag4_signs":
            all(primary["signed_lag_counts"][k] > 0 for k in (-4, 4)),
        "scope": "Pulse-locked four-cycle with a fixed exclusive arm map predicts a missing "
                 "lag-4 cross peak even under deletion-only loss. No iid test, confidence "
                 "level, emission-index exclusion, or universal click law is inferred. "
                 "Blinking, background, re-excitation, wrong lag assignments, phase slips, "
                 "or detector artifacts are not bounded by this histogram alone.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-file", type=Path, default=DEFAULT_FILE,
                        help="official source CSV or its LF copy (default: bundled data)")
    args = parser.parse_args()
    with args.raw_file.open("rb") as f:
        data = f.read(SOURCE_SIZE + 1)
    require(len(data) <= SOURCE_SIZE, "oversized input")
    print(json.dumps(analyze(data), ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
