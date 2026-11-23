"""Exact trivalent count reflection from finite windows of unsigned four-leg pairs.

Exactly two of four input legs are occupied; complement the four bits and
reflect the fourth output back one tick later. Prepare the mirror empty; in
each two-tick block the three external legs must form a double then a single.
The mirror returns empty. Unequal-duration raw counts, equal-duration rates,
time-resolved wave amplitudes and a physical interference measurement are
different observables. Ports, pair preparations, a positive delayed mirror,
and comparison of repeated windows are supplied. No signed bit is supplied.
"""

from __future__ import annotations

import json
from itertools import product

ONE = (1, 1, 1)
BITS = tuple(product((0, 1), repeat=3))
DOUBLES = tuple(z for z in BITS if sum(z) == 2)
SINGLES = tuple(z for z in BITS if sum(z) == 1)
BLOCKS = tuple(product(DOUBLES, SINGLES))


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def hist(rows):
    return tuple(sum(x) for x in zip(*rows, strict=True)) if rows else (0, 0, 0)


def difference(x, y):
    return tuple(a - b for a, b in zip(x, y, strict=True))


def raw(rows, mirror=0):
    out = []
    for x in rows:
        if len(x) != 3 or any(a not in (0, 1) for a in x) or sum(x) + mirror != 2:
            raise ValueError("not a pair of distinct occupied legs")
        out.append(tuple(1 - a for a in x))
        mirror = 1 - mirror
    return tuple(out), mirror


def legal(rows, t):
    try:
        raw(rows, t)
    except ValueError:
        return False
    return True


def cone(k, m):
    return k >= 0 and sum(m) == 3 * k and all(0 <= a <= 2 * k for a in m)


def realize(k, m):
    """Each block is 1+e_i-e_j: double omits j and single occupies i."""
    need(cone(k, m), "infeasible requested marginal")
    d = tuple(v - k for v in m)
    more = [i for i, v in enumerate(d) for _ in range(max(v, 0))]
    less = [i for i, v in enumerate(d) for _ in range(max(-v, 0))]
    # For three coordinates summing to zero at least one side has at most
    # one nonzero index; every |d_i|<=k, so total positive excess <=k.
    need(len(more) == len(less) <= k, "three-coordinate root budget")
    pairs = list(zip(more, less, strict=True)) + [(0, 0)] * (k - len(more))
    word = tuple(
        z
        for i, j in pairs
        for z in (
            tuple(int(n != j) for n in range(3)),
            tuple(int(n == i) for n in range(3)),
        )
    )
    out, t = raw(word)
    need(
        t == 0 and hist(word) == m and hist(out) == tuple(2 * k - a for a in m),
        "native unsigned realization",
    )
    return word, out


def window_inventory():
    results = {}
    atoms = {hist(b) for b in BLOCKS}
    need(len(BLOCKS) == 9 and len(atoms) == 7, "balanced block or six roots")
    for k in range(5):
        seen = set()
        for blocks in product(BLOCKS, repeat=k):
            x = tuple(z for b in blocks for z in b)
            y, t = raw(x)
            m = hist(x)
            need(
                t == 0 and cone(k, m) and hist(y) == tuple(2 * k - a for a in m),
                "block window law",
            )
            seen.add(m)
        target = {m for m in product(range(2 * k + 1), repeat=3) if cone(k, m)}
        need(seen == target, "incomplete or extra cone points")
        for m in seen:
            realize(k, m)
        results[k] = {"raw_windows": len(BLOCKS) ** k, "different_marginals": len(seen)}
    return results


def unequal_windows():
    a, b = realize(1, ONE), realize(2, (4, 1, 1))
    delta = [difference(hist(b[i]), hist(a[i])) for i in (0, 1)]
    need(delta == [(3, 0, 0), (-1, 2, 2)], "unequal-window witness")
    # For arbitrary integer v of total 3h use m0=k*1, m1=m0+v and
    # k1=k+h. The three inequalities below put the second in its own cone.
    checked = 0
    for v in product(range(-4, 5), repeat=3):
        if sum(v) % 3:
            continue
        h = sum(v) // 3
        k = max(1, 1 - h, -min(v), max(v) - 2 * h)
        left = realize(k, (k,) * 3)
        right = realize(k + h, tuple(k + vi for vi in v))
        diffs = [difference(hist(right[i]), hist(left[i])) for i in (0, 1)]
        need(
            diffs == [v, tuple(2 * h - vi for vi in v)], "difference-lattice reflection"
        )
        checked += 1
    return {
        "raw_in_out_differences": delta,
        "integer_lattice_controls": checked,
        "boundary": "equal active length gives only zero-sum differences and -I. A common wall-clock window for unequal active durations needs explicit inactive slots, not extra legal balanced blocks. This is subtraction of records, not single-tick negative occupancy.",
    }


def overlap_order():
    # H=(0,1,2); G=(1,2,3), with external wire 3 unchanged by H.
    spectator = (0, 1)
    good = ((1, 0, 1), (0, 1, 0))
    bad = ((0, 1, 1), (1, 0, 0))

    def feeds_g(drive):
        y, _ = raw(drive)
        return tuple((z[1], z[2], s) for z, s in zip(y, spectator, strict=True))

    g, b = feeds_g(good), feeds_g(bad)
    need(hist(good) == hist(bad) == hist(g) == hist(b) == ONE, "mismatched marginal")
    need(g == ((1, 0, 0), (0, 1, 1)) and legal(g, 1), "missing live continuation")
    need(
        b == ((0, 0, 0), (1, 1, 1))
        and all(not legal((row,), t) for row in b for t in (0, 1)),
        "irreparable immediate tick",
    )
    # Buffer the two ticks and change only wire 1's order before releasing G;
    # a global reordering of the whole rows still leaves BOTH rows illegal.
    repaired = ((b[1][0], *b[0][1:]), (b[0][0], *b[1][1:]))
    need(
        repaired == g and not any(legal(b[::-1], t) for t in (0, 1)),
        "wire-selective repacketization vs whole-row delay",
    )
    return {
        "same_spectator": spectator,
        "H_good": good,
        "H_bad": bad,
        "G_good": g,
        "G_bad": b,
        "boundary": "a buffer can rematch after collecting both ticks. The wall concerns immediate raw overlaps, not all synchronized sources or buffered grammars.",
    }


def backlog_control():
    # Build the two bursts from actual legal H inputs (double then single).
    hi, _ = raw(((1, 0, 1), (1, 0, 0)))
    lo, _ = raw(((0, 1, 1), (0, 1, 0)))
    hi_g = tuple((z[1], z[2], 1) for z in hi)
    lo_g = tuple((z[1], z[2], 0) for z in lo)
    need(
        hi_g == ((1, 0, 1), (1, 1, 1)) and lo_g == ((0, 0, 0), (0, 1, 0)),
        "bursts not generated by legal upstream traffic",
    )
    samples = {}
    for n in (1, 2, 3, 8, 31):
        g = n * hi_g + n * lo_g
        need(
            hist(g) == (2 * n,) * 3 and cone(2 * n, hist(g)), "global total infeasible"
        )
        # Even freely choosing when to fire cannot reset a held mirror bit.
        # f external consumptions alternate 1,2 or 2,1; allow BOTH starts.
        capacity = max(
            sum(2 - (start ^ (i % 2)) for i in range(f))
            for f in range(2 * n + 1)
            for start in (0, 1)
        )
        arrivals = sum(hist(g[: 2 * n]))
        need(capacity == 3 * n and arrivals == 5 * n, "prefix capacity or input")
        samples[n] = arrivals - capacity
    return {
        "burst_prefix_backlog_lower_bounds": samples,
        "arbitrary_n": "n high two-tick blocks then n low: 5n arrivals by tick 2n; at most 3n consumed in at most 2n fires, despite a balanced 4n-tick total. At least 2n raw marks are outstanding; this lower-bounds storage counted in unconsumed marks, not physical memory bits for a compressed count.",
        "conditions": "one downstream raw contact at most once per upstream tick, no backpressure, omission, spare service or resetting the held mirror on a skipped firing. More storage, slower input, faster service, or a restricted schedule changes the question.",
    }


def probe():
    return {
        "reachable_burst": backlog_control(),
        "windows": window_inventory(),
        "unequal_active_windows": unequal_windows(),
        "order_witness": overlap_order(),
        "scope": "exact nonnegative count map m -> 2k*1-m = (2J/3-I)m when sum(m)=3k. No square law, autonomous signed signal or event probability follows.",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
