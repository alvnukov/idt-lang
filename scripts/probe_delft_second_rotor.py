"""What can the second Delft Bell record say about a specified 0011 clock?

No-data default: synthetic controls only. Use --raw-file path/to/data.zip
(or --raw-file - for stdin) with the *second* experiment's 4TU v1 release:
https://doi.org/10.4121/uuid:53644d31-d862-4f9f-9ad2-0b571874b829 .
Authors' selection and binary readout: bell_open_data_2_analysis_example.py
in that archive, lines 19–135. See https://doi.org/10.1038/srep30289 .
Read-only, no download or raw redistribution, no author code executed.
4TU lists General Terms of Use; we do not infer an open redistribution license.

Retrospective, not preregistered. On Alice's accepted records only, an ideal
0011 rotor advances once per appearance of the named context and stays still
otherwise. Each context starts at its own unknown phase in each detector era,
day and run. Primary: the context includes both settings and the heralded
state. Secondary sensitivity analysis, specified after the primary result:
Alice indexes only her own setting. It cannot supersede the primary result.
The minimum number of fixed-position bit substitutions is a property of these
observed words, not a p-value or a spin-readout error estimate. A skipped
tick, different reset rule, noisy readout, or clock advancing on rejected or
unreported attempts defines a different model. This is not a physical bridge
from Delft spin readout to IDT's one-stage signed-ticket circuit.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import sys
import zipfile
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

PACK_SIZE = 131394
PACK_SHA = "876967e1cbe402b775d25392b773386325499b2343b18bf401d1825f2008a176"
# size, SHA-256, channel-0 window start (ps); the APD replacement changed its delay.
FILES = {
    "old": (95012, "96d51ccfe8d2155b18a8c1d6ed4f620ac5befe152d08d429a74060584b24fc83", 5426000),
    "new": (260839, "1d07d08266f7dab0a41d44c75264c05a237448ae7ba457a893f519444a5ba864", 5425300),
}
ROTOR = (0, 0, 1, 1)


def check(ok: bool, what: str) -> None:
    if not ok:
        raise ValueError(what)


def pinned(data: bytes, size: int, sha: str, name: str) -> None:
    check(len(data) == size and hashlib.sha256(data).hexdigest() == sha,
          f"{name}: unexpected size/SHA-256")


def min_changes(word: list[int] | tuple[int, ...]) -> int:
    return min(sum(x != ROTOR[(j + phase) % 4] for j, x in enumerate(word))
               for phase in range(4))


def assess(words: dict[tuple, list[int]]) -> dict:
    lengths, costs = Counter(), Counter()
    for word in words.values():
        lengths[len(word)] += 1
        costs[min_changes(word)] += 1
    return {
        "strata": len(words), "length_counts": dict(sorted(lengths.items())),
        "min_change_counts": dict(sorted(costs.items())),
        "min_substitutions": sum(k * n for k, n in costs.items()),
        "records": sum(k * n for k, n in lengths.items()),
        "discriminating_strata": sum(n for k, n in lengths.items() if k >= 3),
    }


def accepted(start0: int, fields: list[int]) -> bool:
    _, _, t1, ch1, t2, ch2, _, _, _, _, _, _, exc_a, exc_b, inv_a, inv_b = fields
    starts = (start0, 5425100)
    width2 = (4000, 2500)[ch2] if ch1 == ch2 else 50000
    return (starts[ch1] <= t1 < starts[ch1] + 50000
            and starts[ch2] + 250000 <= t2 < starts[ch2] + 250000 + width2
            and (inv_a == 0 or inv_a > 250) and (inv_b == 0 or inv_b > 250)
            and exc_a == exc_b == 0)


def click(time_ns: int) -> int:
    return int(10620 < time_ns <= 14320)


def controls() -> None:
    for k in (0, 1, 2):
        check(all(min_changes(w) == 0 for w in product((0, 1), repeat=k)),
              "every binary word of length at most two occurs")
    bad = {w for w in product((0, 1), repeat=3) if min_changes(w) == 1}
    check(bad == {(0, 0, 0), (0, 1, 0), (1, 0, 1), (1, 1, 1)},
          "exact three-bit countercontrols")
    check(min_changes((1, 0, 0, 1, 1, 0)) == 0, "unknown phase, multiple cycles")
    check(assess({(0,): [0, 0, 0], (1,): [1, 1]})["min_substitutions"] == 1,
          "independent phases; no cross-stratum joins")
    check([click(t) for t in (0, 10620, 10621, 14320, 14321)] == [0, 0, 1, 1, 0],
          "readout window endpoints")
    for _, _, start0 in FILES.values():
        starts = (start0, 5425100)
        for c1, c2 in product(range(2), repeat=2):
            f = [0] * 16
            f[2:6] = [starts[c1], c1, starts[c2] + 250000, c2]
            width = (4000, 2500)[c2] if c1 == c2 else 50000
            check(accepted(start0, f), "inclusive herald window starts")
            for pos, value, expected in (
                (2, starts[c1] - 1, False), (2, starts[c1] + 49999, True),
                (2, starts[c1] + 50000, False), (4, f[4] - 1, False),
                (4, f[4] + width - 1, True), (4, f[4] + width, False),
                (12, 1, False), (13, 1, False), (14, 250, False), (15, 251, True),
            ):
                changed = f.copy()
                changed[pos] = value
                check(accepted(start0, changed) == expected, "herald/veto boundaries")


def analyze(packed: bytes) -> dict:
    pinned(packed, PACK_SIZE, PACK_SHA, "4TU second-experiment archive")
    full, local = defaultdict(list), defaultdict(list)
    eras = {}
    scores = {"psi_minus": [0, 0], "psi_plus": [0, 0]}  # wins, trials
    with zipfile.ZipFile(io.BytesIO(packed)) as z:
        for era, (size, sha, start0) in FILES.items():
            name = f"bell_open_data_2_{era}_detector.txt"
            check(z.namelist().count(name) == 1 and z.getinfo(name).file_size == size,
                  f"{name}: archive member missing, duplicated or wrong size")
            with z.open(name) as member:
                raw = member.read(size + 1)
            pinned(raw, size, sha, name)
            previous, kept, count = "", 0, 0
            for count, row in enumerate(csv.reader(io.StringIO(raw.decode("ascii"))), 1):
                check(len(row) == 17 and row[0] >= previous, "columns/chronology")
                previous = row[0]
                f = list(map(int, row[1:]))
                day, run, _, c1, _, c2, a, b = f[:8]
                check(all(v in (0, 1) for v in (c1, c2, a, b)), "channel/setting")
                if not accepted(start0, f):
                    continue
                kept += 1
                plus = int(c1 == c2)
                x, y = click(f[10]), click(f[11])
                full[era, day, run, a, b, plus].append(x)
                local[era, day, run, a].append(x)
                score = scores["psi_plus" if plus else "psi_minus"]
                score[0] += int((x ^ y) == (a & (b ^ plus)))
                score[1] += 1
            eras[era] = {"broad_candidates": count, "accepted": kept}
    check(scores == {"psi_minus": [179, 228], "psi_plus": [58, 72]},
          "published cross-check: 237 wins in 300 trials; unexpected breakdown")
    return {"empirical_status": "pinned_archive_replayed", "eras": eras,
            "chsh_wins_trials": scores, "full_context_primary": assess(full),
            "alice_setting_only_secondary": assess(local)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-file", help="official second-experiment v1 data.zip, or - for stdin")
    args = parser.parse_args()
    try:
        controls()
        report = {"synthetic_controls": "passed", "empirical_status": "not_tested"}
        if args.raw_file:
            if args.raw_file == "-":
                data = sys.stdin.buffer.read(PACK_SIZE + 1)
            else:
                with Path(args.raw_file).open("rb") as f:
                    data = f.read(PACK_SIZE + 1)
            report.update(analyze(data))
        print(json.dumps(report, sort_keys=True))
        return 0
    except (OSError, ValueError, zipfile.BadZipFile) as error:
        print(f"Input/check error (not a physics rejection): {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
