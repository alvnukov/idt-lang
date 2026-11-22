"""A zero-error memory witness from driven event strings; no iid assumption.

A fixed deterministic transducer sees the supplied input symbol on every
tick; its output and next state are functions of that symbol and its current
state. Arbitrary start states per run are allowed. For a fixed input word,
at most M output words can emerge from M different start states. Thus a
collection of observed output words on that one input gives a replayable
lower bound, even if trials or settings were chosen adaptively. No claim
that the bound is tight, or is a confidence bound for noisy observations.

For a partition into disjoint windows of a fixed length and offset, even
choosing the M most frequent output words separately per input word leaves
a definite number of windows unexplained. Each requires a wrong symbol,
hidden tick/input, or other violation of the specified ideal contract in
that window; arbitrary state at every window start was already allowed.
Missing clock events elsewhere cannot rescue a contradictory intact window.
Take a maximum, NEVER a sum across overlapping alternative partitions.

Optional Hensen 2015 diagnostic, fixed before reading chronological output:
use both parties, lengths 1..8 and all fixed offsets, pooling across day/run
boundaries only as separate initial states of the SAME transducer. Report
(i) accepted-only clock per day/run and (ii) segments additionally cut at
every rejected released row. For each, reveal either the local setting
alone or both settings. Whole-block outputs are never pooled across a reset.
Even adjacent released rows need not be consecutive physical attempts.
The fresh source state, detection timetags and apparatus internals are not
observed as inputs to such a transducer. Therefore this is NOT an empirical
lower bound on detector memory alone, a test of physical determinism, an
entropy certificate, a Bell test, or an independent replication. The
default uses only synthetic cases. Raw data are not redistributed here.
"""

import argparse
import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

from theory_experiments.bell_trial_test import (
    assert_loaded_sources,
    read_pinned_raw,
    reduce_records,
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def evidence(segments, max_word=8, caps=(1, 2, 3, 4)):
    """A segment contains ordered pairs (input, output); start state is free."""
    need(1 <= max_word <= 16 and all(type(m) is int and 1 <= m <= 256 for m in caps),
         "invalid witness limits")
    bound = 0
    witness = None
    bad = dict.fromkeys(caps, 0)
    partitions = {}
    for length in range(1, max_word+1):
        outputs = defaultdict(dict)
        for offset in range(length):
            frequencies = defaultdict(Counter)
            windows = 0
            for sid, segment in enumerate(segments):
                for t in range(offset, len(segment)-length+1, length):
                    word = segment[t:t+length]
                    x = tuple(q[0] for q in word)
                    y = tuple(q[1] for q in word)
                    frequencies[x][y] += 1
                    outputs[x].setdefault(y, (sid, t))
                    windows += 1
            for m in caps:
                exc = sum(sum(hist.values())-sum(n for _, n in hist.most_common(m))
                          for hist in frequencies.values())
                if exc > bad[m]:
                    bad[m] = exc
                    partitions[m] = (length, offset, windows)
        # Overlap is harmless for a noiseless SAME-state argument; it was
        # disallowed within each of the error-count partitions above.
        for x, ys in outputs.items():
            if len(ys) > bound:
                bound = len(ys)
                witness = {"input_word": x, "output_starts": sorted(ys.items())}
    return {"state_lower_bound": bound, "witness": witness, "bad_disjoint_windows": bad,
            "winning_partitions_length_offset_windows": partitions}


def verify_witness(segments, report):
    w = report["witness"]
    if w is None:
        return report["state_lower_bound"] == 0 and not any(segments)
    x = tuple(w["input_word"])
    ys = set()
    for y, (sid,t) in w["output_starts"]:
        if not 0 <= sid < len(segments) or t < 0:
            return False
        block = segments[sid][t:t+len(x)]
        if tuple(q[0] for q in block) != x or tuple(q[1] for q in block) != tuple(y):
            return False
        ys.add(tuple(y))
    return len(ys) == len(w["output_starts"]) == report["state_lower_bound"]


def synthetic():
    # All 8 possible answers to the same three requests, three captures
    # apiece. A k=2 cap leaves at least 18 disjoint wrong blocks.
    words = [[(0,b) for b in bits] for bits in product((0,1), repeat=3)]*3
    r = evidence(words)
    need(verify_witness(words, r) and r["state_lower_bound"] == 8, "missing prefix witness")
    need(r["bad_disjoint_windows"][2] == 18, "wrong edit lower bound")
    # A single unobserved fresh input bit can explain every output without
    # persistent memory: the exposed-input control must never reject that.
    revealed = [[((x,y),y) for x,y in row] for row in words]
    s = evidence(revealed)
    need(s["state_lower_bound"] == 1 and max(s["bad_disjoint_windows"].values()) == 0,
         "extra input should resolve deterministic ambiguity")
    # Direct constructive check: no witness contradicts ANY of the 256
    # two-state binary deterministic devices under variable input / resets.
    order = (0,1,1,0,0,1,0,1,1,1,0,0,0,1,1)
    for device in product(range(4), repeat=4):
        segs = []
        for state in range(2):
            seg = []
            for x in order:
                state, y = divmod(device[2*state+x],2)
                seg.append((x,y))
            segs.append(seg)
        r = evidence(segs, 4, (2,))
        need(verify_witness(segs,r) and r["state_lower_bound"] <= 2 and not r["bad_disjoint_windows"][2],
             "rejected a generating two-state device")
    return {"two_state_devices_preserved": 256, "synthetic_state_bound": 8,
            "two_state_bad_blocks": 18, "with_revealed_fresh_inputs": 1}


def selected_segments(records, party, both, cut_gaps):
    segments = []
    previous = None
    for row in records:
        key = tuple(row["source_fields"][1:3])
        if (key != previous or (cut_gaps and not row["accepted"])) and segments and segments[-1]:
            segments.append([])
        previous = key
        if row["accepted"]:
            if not segments:
                segments.append([])
            x = 2*row["a"]+row["b"] if both else row["a" if party == "A" else "b"]
            y = int(row["x" if party == "A" else "y"] == 1)
            segments[-1].append((x,y))
    return [s for s in segments if s]


def empirical(path):
    raw = read_pinned_raw(path)
    assert_loaded_sources()
    data = reduce_records(raw.decode("utf-8"))
    need((data["N"],data["K"]) == (245,196), "published reduction did not reproduce")
    results = {}
    for party, both, cut_gaps in product("AB", (False,True), (False,True)):
        segs = selected_segments(data["records"],party,both,cut_gaps)
        r = evidence(segs)
        need(verify_witness(segs,r) and sum(map(len,segs)) == 245, "bad empirical witness")
        key = f"{party}_{'both' if both else 'local'}_{'gap_reset' if cut_gaps else 'accepted_clock'}"
        results[key] = dict(r, segments=len(segs), max_length=max(map(len,segs)))
    return {"source": "Hensen 2015, checksum-pinned preselected record, retrospective diagnostic",
            "accepted": 245, "results": results}


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--raw-file",type=Path)
    args = p.parse_args()
    out = {"synthetic": synthetic(), "empirical": empirical(args.raw_file) if args.raw_file else "not_tested"}
    print(json.dumps(out,sort_keys=True))


if __name__ == "__main__":
    main()
