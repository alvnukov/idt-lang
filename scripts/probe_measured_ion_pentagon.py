"""Replay the five-edge trapped-ion KCBS observations in the pinned ETH summary.

Offline: python3 -B -m scripts.probe_measured_ion_pentagon --json
Original-data check: add --zip PATH_TO_ETH_ARCHIVE. Never downloads or extracts files.

With bright=1, S is half the sum of both endpoint bright probabilities over
the five edges, J is the sum of the joint bright probabilities, and C sums
the sign-product means. X=S-J=(5-C)/4, irrespective of a global sign flip.
For a setting-independent common coupling X <= 2 + E[D]/2 (see
probe_native_pentagon_contexts). The observed edges do not give actual D.
"""

import argparse
import csv
import hashlib
import io
import json
import math
import sys
import zipfile
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import zip_longest
from pathlib import Path


FIXTURE = Path(__file__).resolve().parents[1] / "data" / "ion_pentagon_2018_summary.json"
FIXTURE_SHA = "2b6faa41d9424cd42ddf706d3e7129e99ee81d41aa7537721593592db006cd93"
TIMES = tuple(F(t, 10) for t in range(104, 110))
CSV_HEADER = ["observable pair", "rot time", "det1", "det2", "corr",
              "var det 1", "var det 2", "var corr"]
BOUNDARY = ("External empirical comparison only. The D floor is necessary for a proposed "
            "common-stock coupling reproducing these edge frequencies. It is not an observed D "
            "or a population confidence bound; sharpness is not asserted. Marginal differences are not D. "
            "Reverse order is a control on the same apparatus, not an independent replication. "
            "No native detector law, physical model status, or p-value follows.")


class ProvenanceError(ValueError):
    """Source or readout contract failure, not a physical candidate rejection."""


def require(condition, message):
    if not condition:
        raise ProvenanceError(message)


def checked_bytes(data, digest, label):
    require(hashlib.sha256(data).hexdigest() == digest, f"{label} SHA-256 mismatch")
    return data


def load_fixture():
    return json.loads(checked_bytes(FIXTURE.read_bytes(), FIXTURE_SHA, "aggregate fixture"))


def score(rows, step):
    """rows[i] describes vertex i first, vertex (i+step) second, in cell order 00,01,10,11."""
    require(step in (1, -1) and len(rows) == 5, "expected a five-edge ordered cycle")
    require(all(len(row) == 4 and all(type(x) is int and x >= 0 for x in row)
                and sum(row) == 10000 for row in rows), "expected four counts and 10000 shots per edge")
    first = [F(c + d, 10000) for a, b, c, d in rows]
    second = [F(b + d, 10000) for a, b, c, d in rows]
    products = [F(a - b - c + d, 10000) for a, b, c, d in rows]
    corr = sum(products)
    s, j = (sum(first) + sum(second)) / 2, F(sum(row[3] for row in rows), 10000)
    x = s - j
    require(x == (5 - corr) / 4, "joint-count and correlation arithmetic disagree")
    tv = sum(abs(first[i] - second[(i-step) % 5]) for i in range(5))
    # Independent-shot plug-in variance estimate for each mean: (1-c_i^2)/(n_i-1).
    se = math.sqrt(sum((1-float(c)**2) / 9999 for c in products))
    return {"shots": 50000, "unlike": sum(b+c for a, b, c, d in rows),
            "S": str(s), "J": str(j), "C": str(corr), "X": str(x),
            "conditional_D_floor": str(max(F(0), 2*(x-2))), "marginal_TV_sum": str(tv),
            "SE_X_if_independent_shots_and_edges": se / 4}


def check_block(raw, summary):
    """Return ordered frequencies only after raw and archived means agree for this block."""
    require(len(raw) == 203 and raw[2] == "200", "expected 200 detections per 100-shot block")
    require(len(summary) == 8, "expected eight thresholded fields")
    try:
        obs, t = F(raw[0]), F(raw[1])
        require((obs, t) == (F(summary[0]), F(summary[1])) and obs in range(1, 6)
                and t in TIMES, "raw/thresholded block key mismatch")
        nums = list(map(int, raw[3:]))
        require(min(nums) >= 0, "negative photon count")
        cells = [0] * 4
        for first, second in zip(nums[::2], nums[1::2], strict=True):
            cells[2*(first >= 7) + (second >= 7)] += 1
        m, n, c = map(F, summary[2:5])
        published = [25*(1+a*m+b*n+a*b*c) for a, b in ((-1,-1), (-1,1), (1,-1), (1,1))]
        require(cells == published, "PMT threshold disagrees with archived block means")
    except ProvenanceError:
        raise
    except (ValueError, ZeroDivisionError) as e:
        raise ProvenanceError("invalid numeric field in block") from e
    return (int(obs), t), cells


def select_time(blocks):
    expected = {(i, t): 100 for i in range(1, 6) for t in TIMES}
    require(dict(blocks) == expected, "incomplete or unexpected 3000-block setting grid")
    observed = sorted({t for _, t in blocks})
    return observed[(len(observed)-1)//2]


def replay_order(archive, rec):
    def reader(label):
        spec = rec[label]
        member = checked_bytes(archive.read(spec["member"]), spec["sha256"], label)
        return csv.reader(io.StringIO(member.decode("ascii"), newline=""))

    raw, summary = reader("raw"), reader("thresholded")
    require(next(summary, None) == CSV_HEADER, "thresholded header mismatch")
    blocks = Counter()
    totals = defaultdict(lambda: [0]*4)
    for a, b in zip_longest(raw, summary):
        require(a is not None and b is not None, "unpaired source block")
        key, cells = check_block(a, b)
        blocks[key] += 1
        for col, count in enumerate(cells):
            totals[key][col] += count
    t = select_time(blocks)
    require(t == F("10.6"), "lower-median pulse time mismatch")
    require([totals[i, t] for i in range(1, 6)] == rec["counts"],
            "selected raw counts differ from the frozen ordered table")
    return {"rotation_time": str(float(t)), "blocks_compared": sum(blocks.values()),
            "selected_blocks": sum(blocks[i, t] for i in range(1, 6))}


def replay_archive(stream, fixture):
    source = fixture["source"]
    raw = stream.read(source["archive_bytes"] + 1)
    require(len(raw) == source["archive_bytes"], "archive byte length mismatch")
    checked_bytes(raw, source["archive_sha256"], "archive")
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        return {order: replay_order(archive, rec) for order, rec in fixture["orders"].items()}


def verify(zip_path=None):
    fixture = load_fixture()
    result = {"rotation_time": fixture["selection"]["rotation_time_selected"],
              "orders": {}, "boundary": BOUNDARY}
    for order, step in (("normal", 1), ("reverse", -1)):
        rec = fixture["orders"][order]
        require(rec["ordered_edges"] == [[i+1, (i+step) % 5+1] for i in range(5)],
                "unexpected ordered edge labels")
        result["orders"][order] = score(rec["counts"], step)
    if zip_path is not None:
        with Path(zip_path).open("rb") as stream:
            result["archive_replay"] = replay_archive(stream, fixture)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zip", "--local-zip", type=Path, help="optional original local ETH ZIP")
    parser.add_argument("--json", action="store_true", help="compact JSON")
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.zip), indent=None if args.json else 2))
    except (OSError, ProvenanceError, zipfile.BadZipFile) as e:
        print(f"Provenance error: {e}", file=sys.stderr)
        sys.exit(2)
