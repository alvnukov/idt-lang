"""Complete finite census of unrestricted eight-row deterministic local cell rules.

No reciprocity, conservation, swap, or square-time rule is imposed on the
local table. Blank storage, one launched mark, through-going unmarked hub
returns, integer hop time and the synthetic acceptance contracts are supplied.
The decision tree counts every completion of unvisited rows separately.
Run as python3 -B -m scripts.probe_unrestricted_cell_tables [--emit-census].
"""

import argparse
import hashlib
import json
from collections import Counter
from itertools import product
from pathlib import Path

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_reversible_cell_census import lift_stateless, passage

CASES = ((2, 1), (3, 1), (2, -1), (3, -1), *product(range(4, 13), (-1, 1)))
LONG = (*range(13, 36), 64)
MODES = ("time", "full")


def encode_id(rule):
    return sum(out << (3 * i) for i, out in enumerate(rule))


def decode_id(value):
    if type(value) is not int or not 0 <= value < 8**8:
        raise ValueError("expected an eight-row table ID in 0..16777215")
    return tuple((value >> (3*i)) & 7 for i in range(8))


def expand(cube):
    """Yield complete table tuples; a star is one arbitrary output digit."""
    return product(*(range(8) if x == "*" else (int(x),) for x in cube))


def ids_digest(ids):
    return hashlib.sha256(",".join(map(str, sorted(ids))).encode("ascii")).hexdigest()


def decide(partial, n, initial_direction, full):
    """Return (unknown row, False) or (-1, deterministic outcome) on this fresh trial."""
    d, x = initial_direction, 0 if initial_direction == 1 else n
    lane, memory = 1, 0
    for tick in range(1, n*n + 1):
        x += d
        if x == 0 or x == n:
            if lane:
                return -1, tick == n*n and (not full or (d == initial_direction and not memory))
            x = 0 if d == 1 else n
        elif tick < n*n:  # No first marked arrival by the deadline on this branch otherwise.
            bit = 1 << (x-1)
            address = 4*(d == -1) + 2*lane + bool(memory & bit)
            out = partial[address]
            if out < 0:
                return address, False
            lane = (out >> 1) & 1
            d = 1 if out & 4 else -1
            memory = memory | bit if out & 1 else memory & ~bit
    return -1, False


def tree(mode):
    full = mode == "full"
    partial = [-1] * 8
    misses = [0] * len(CASES)
    wins = []

    def visit(stage, free):
        while stage < len(CASES):
            row, ok = decide(partial, *CASES[stage], full)
            if row >= 0:
                for out in range(8):
                    partial[row] = out
                    visit(stage, free-1)
                partial[row] = -1
                return
            if not ok:
                misses[stage] += 8**free
                return
            stage += 1
        wins.append("".join("*" if digit < 0 else str(digit) for digit in partial))

    visit(0, 8)
    wins.sort()
    ids = [encode_id(rule) for cube in wins for rule in expand(cube)]
    need(len(set(ids)) == len(ids) and sum(misses) + len(ids) == 8**8, "disjoint census coverage")
    bijective = sorted(value for value in ids if len(set(decode_id(value))) == 8)
    reciprocal = []
    for value in bijective:
        table = decode_id(value)
        if all(table[out] == i for i, out in enumerate(table)):
            reciprocal.append(value)
    return ({"first_failure_counts": misses, "trained_count": 8**8 - sum(misses[:2]),
             "survivor_count": len(ids), "winning_cubes": wins, "survivor_ids_sha256": ids_digest(ids),
             "bijective_winning_ids": bijective, "involutive_winning_ids": reciprocal},
            set(ids))


def accepts(result, n, direction, mode):
    return result == (n*n, direction, 0) if mode == "full" else result is not None and result[0] == n*n


def first_failure(rule, mode):
    """Independent complete-table replay using the existing literal passage model."""
    for stage, (n, d) in enumerate(CASES):
        result, _ = passage(rule, n, d)
        if not accepts(result, n, d, mode):
            return stage
    return None


def stateless():
    misses = {mode: [0] * len(CASES) for mode in MODES}
    for raw in product(range(4), repeat=4):
        rule = lift_stateless(raw)  # spectator storage is never changed or used by this table
        for mode in MODES:
            fail = first_failure(rule, mode)
            if fail is not None:
                misses[mode][fail] += 1
    return {"total": 4**4, "modes": {mode: {"first_failure_counts": counts,
            "trained_count": 4**4 - sum(counts[:2]), "survivor_count": 4**4 - sum(counts)}
            for mode, counts in misses.items()},
            "bound": "Without storage or an external clock a one-cursor deterministic ring has at most "
                     "2*n*K directed arrival/control states (K=2 lanes here). A first marked hub "
                     "arrival, if any, occurs before an arrival state repeats, hence by 2*n*K hops. "
                     "Fixed K cannot produce first returns at n^2 for unbounded n."}


def probes(ids):
    patterns = Counter()
    repeat_misses = Counter()
    examples = {}
    for value in sorted(ids):
        rule = decode_id(value)
        # Large-length tests always launch from fresh blank storage, never
        # from the state left by a different length or a previous table.
        long_ok = True
        long_first = None
        for n, d in product(LONG, (-1, 1)):
            result, _ = passage(rule, n, d)
            if not accepts(result, n, d, "time"):
                long_ok = False
                long_first = [n, d, result]
                break
        # At each first marked return continue through the single-rail hub:
        # retain the actual direction, mark and storage; no reset or reorientation.
        repeat_ok = True
        repeat_first = None
        for n, initial in product(range(2, 13), (-1, 1)):
            d, memory = initial, 0
            for k in (1, 2, 3):
                result, _ = passage(rule, n, d, memory)
                if not accepts(result, n, d, "time"):
                    need(k != 1, "winner disagrees with fresh literal first passage")
                    repeat_ok = False
                    repeat_first = [n, initial, k, d, memory, result]
                    repeat_misses[n, initial, k, 0 if result is None else result[0]] += 1
                    break
                _, d, memory = result
            if not repeat_ok:
                break
        label = f"fresh_long_{'match' if long_ok else 'miss'}__three_unreset_{'match' if repeat_ok else 'miss'}"
        patterns[label] += 1
        if label not in examples:
            examples[label] = {"id": value, "first_fresh_miss": long_first, "first_unreset_miss": repeat_first}
    return {"counts": dict(sorted(patterns.items())), "first_id_examples": examples,
            "first_unreset_miss_histogram":
                [{"length": n, "launch_direction": d, "passage": k, "hops": t or None, "table_count": count}
                 for (n, d, k, t), count in sorted(repeat_misses.items())]}


def registry():
    modes, groups = {}, {}
    for mode in MODES:
        modes[mode], groups[mode] = tree(mode)
    need(groups["full"] <= groups["time"], "reset winners must also satisfy timing")
    for value in groups["time"]:
        for mode in MODES:
            need((first_failure(decode_id(value), mode) is None) == (value in groups[mode]),
                 "literal replay disagrees on time-winning table")
    return {"schema": "idt-unrestricted-cell-census/1", "table_count": 8**8,
            "encoding": "row i=4*(direction==-1)+2*carried+stored; output z chooses outgoing "
                        "direction +1 if bit 2 else -1; bit 1 is carried, bit 0 stored; "
                        "id=sum(z_i*8^i), row 0 least significant; cube characters in row order",
            "id_digest": "SHA256 of comma-separated sorted decimal IDs in ASCII, no trailing comma or newline",
            "case_order": CASES, "training_case_count": 2,
            "replay": "Each case starts fresh: x=0 forward or n backward, marked lane, blank cells. "
                      "Step by current direction; at interior scatter by the addressed row. At a hub "
                      "continue unmarked to the opposite port without changing direction; stop at first marked "
                      "arrival. TIME requires that arrival at exactly n^2; FULL additionally requires initial "
                      "direction and zero memory. Stop each table at its first failed case. Split only a row "
                      "first needed by this execution, in output order 0..7. At rejection count 8^free "
                      "completions; final winning cubes keep all unvisited rows free. Use --replay-id ID "
                      "to recover the first failed case of any of the complete tables.",
            "modes": modes, "stateless": stateless(),
            "followup": {"scope": "Diagnostics only, outside the selecting contract; first mismatch stops that test.",
                         "fresh_long_lengths": LONG, "unreset_lengths": list(range(2, 13)),
                         "directions": [-1, 1], "unreset_passages": 3,
                         "miss_encoding": "null result = no marked return by n^2, not nonreturn forever; "
                                          "result = [hops, direction, memory]. Unreset example records "
                                          "[n, initial_direction, passage_number, current_direction, initial_memory, result].",
                         "time_not_full": probes(groups["time"] - groups["full"]),
                         "full": probes(groups["full"])}}


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = p.add_mutually_exclusive_group()
    group.add_argument("--emit-census", action="store_true")
    group.add_argument("--replay-id", type=int)
    args = p.parse_args()
    if args.replay_id is not None:
        if not 0 <= args.replay_id < 8**8:
            p.error("--replay-id expects a table ID from 0 through 16777215")
        rule = decode_id(args.replay_id)
        result = {"id": args.replay_id, "rows": rule}
        for mode in MODES:
            bad = first_failure(rule, mode)
            result[mode] = {"first_failure_index": bad, "first_failure_case": None if bad is None else CASES[bad]}
        print(json.dumps(result, separators=(",", ":")))
        return
    out = registry()
    if args.emit_census:
        print(json.dumps(out, separators=(",", ":")))
    else:
        saved = Path(__file__).resolve().parents[1]/"data"/"unrestricted_cell_census.json"
        need(json.loads(saved.read_text()) == json.loads(json.dumps(out)), "unrestricted census changed")
        for mode,row in out["modes"].items():
            print(f"{mode}: {row['trained_count']} after the two training inputs; "
                  f"{row['survivor_count']} after the full case list; {len(row['winning_cubes'])} cubes")
        print("Unreset follow-up on timing-only extras:",out["followup"]["time_not_full"]["counts"])


if __name__ == "__main__":
    main()
