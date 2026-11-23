"""What the occupied-neighbor link toggle does on a supplied bare star.

Bit j of arm i is the occupation of its j-th link counted from the center.
Only links are updated; traveling pairs and the charge Q are readouts, not
objects in the dynamics. An even half-step visits arms in the supplied order;
all odd links then form one matching. On a straight tail this is staggered
Rule 54: a selected bit toggles iff either neighbor is occupied.

An algebraic explanation (not a Lean proof): let E be the state after even
offers. In Q(x)+Q(E), group terms around each passive occupied odd link.
Each of its two even neighbors flips exactly once, so the two signed sums
cancel. Only an unpaired remote odd end can remain. Likewise Q(E)+Q(next)
groups around passive occupied even links: the near end contributes E[0],
and a remote even end contributes -E[last]. Subtraction gives the full
step law Q(next)-Q(x)=E[0]-E[last], including finite-end flux.

With fixed repeated port order, the previous d central emissions are the
current center bits. The oldest flips under OR of the other d-1 bits and
the firing arm's outer neighbor. Starting empty, a first 1 after at least
d-1 zeros forces the next d-1 zeros in the old window to toggle to ones;
the following d-1 old ones must toggle to zeros. At the next firing the
external bit can matter again. Thus each complete burst has length d and
visits every port once. Between empty-center cuts with untouched remote
ends the charges increase equally. Clean odd-start incoming pairs count -1,
even-start outgoing pairs +1: O_i+I_i=K, where K is the number of bursts.
In particular O_i-O_j=-(I_i-I_j). A single input has two outputs on the
three-arm star, excluding both preservation of squared pulse-count norm
and the universal reflector prescription K=2 mean(I).
This conditional identity does not itself guarantee asymptotic cleaning.

Only the wiring, clock, preparations and specified finite cuts are tested.
No energy conservation, Grover amplitude, Born probability, gauge field,
endogenous clock, spatial embedding or physical theory status follows.

Run: python3 -m scripts.probe_binary_star_contrast
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import pairwise, permutations, product


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def evens(width):
    return ((1 << (2 * ((width + 1) // 2))) - 1) // 3


def charge(x):
    pairs = x & (x >> 1)
    return 2 * (pairs & evens(pairs.bit_length())).bit_count() - pairs.bit_count()


def sweep(state, width, order):
    """Return both half-step states, without clipping active sites at a readout cut."""
    d = len(state)
    require(
        d >= 2 and tuple(sorted(order)) == tuple(range(d)),
        "not a star port permutation",
    )
    require(
        width >= 2 and all(0 <= x < 1 << width for x in state), "invalid arm extent"
    )
    even = evens(width)
    odd = ((1 << width) - 1) ^ even
    mid = list(state)
    for i in order:
        x = mid[i]
        central_witness = int(any(k != i and y & 1 for k, y in enumerate(mid)))
        mid[i] ^= ((x << 1) | (x >> 1) | central_witness) & even
    end = tuple(x ^ (((x << 1) | (x >> 1)) & odd) for x in mid)
    return tuple(mid), end


def check_balance(start, mid, end, width):
    """Check each half-step, including remote flux at either endpoint parity."""
    for a, e, z in zip(start, mid, end):
        outer = e >> (width - 1)
        odd_end = (width - 1) % 2
        require(charge(a) + charge(e) == outer * odd_end, "even half-step flux")
        require(
            charge(e) + charge(z) == (e & 1) - outer * (1 - odd_end),
            "odd half-step flux",
        )


def raw_balance(d, width):
    count = remote = 0
    for state in product(range(1 << width), repeat=d):
        mid, end = sweep(state, width, range(d))
        check_balance(state, mid, end, width)
        remote += any(e >> (width - 1) for e in mid)
        count += 1
    return {
        "degree": d,
        "width": width,
        "states": count,
        "states_with_remote_flux": remote,
    }


def outgoing(x):
    """Reject any core mark, unmatched or incorrectly phased run; consume all bits."""
    require(not x & 1, "not a clean empty-center cut")
    starts = []
    while x:
        j = (x & -x).bit_length() - 1
        require(j % 2 == 0 and (x >> j) & 7 == 3, "not clean outward-separated pairs")
        starts.append(j)
        x ^= 3 << j
    return tuple(starts)


def complete_bursts(stream, d):
    """Count complete runs only; this reader is used between empty-center cuts."""
    k = pos = 0
    while pos < len(stream):
        if not stream[pos]:
            pos += 1
            continue
        require(tuple(stream[pos : pos + d]) == (1,) * d, "incomplete central burst")
        pos += d
        require(
            not any(stream[pos : pos + d - 1]), "insufficient zero gap between bursts"
        )
        pos += d - 1
        k += 1
    return k


def scatter(prep, width, steps, orders):
    """Replay every bit; charge and emission diagnostics never drive the dynamics."""
    require(orders and steps >= 0, "empty clock or negative steps")
    d = len(prep)
    for starts in prep:
        require(
            all(j > 0 and j % 2 and j + 1 < width for j in starts)
            and all(b - a >= 4 for a, b in pairwise(starts)),
            "invalid incoming pairs",
        )
    state = tuple(sum(3 << j for j in starts) for starts in prep)
    inc = tuple(map(len, prep))
    require(
        tuple(charge(x) for x in state) == tuple(-v for v in inc), "incoming charge"
    )
    states, stream = [state], []
    cyclic = all(tuple(order) == tuple(orders[0]) for order in orders)
    history = [0] * d
    for t in range(steps):
        order = orders[t % len(orders)]
        mid, end = sweep(state, width, order)
        require(
            not any(x >> (width - 1) for phase in (state, mid, end) for x in phase),
            "remote endpoint reached",
        )
        check_balance(state, mid, end, width)
        for i in order:
            y = mid[i] & 1
            if cyclic:
                predicted = history[0] ^ int(bool((state[i] & 2) or any(history[1:])))
                require(y == predicted, "central emission recurrence")
                history = history[1:] + [y]
            stream.append(y)
        states.append(end)
        state = end
    pairs = tuple(outgoing(x) for x in state)
    out = tuple(map(len, pairs))
    require(out == tuple(charge(x) for x in state), "outgoing charge")
    total = tuple(a + b for a, b in zip(inc, out))
    k = None
    if cyclic:
        k = complete_bursts(stream, d)
        require(total == (k,) * d, "relative scattering or burst count failed")
    return {
        "in": inc,
        "out": out,
        "sum": total,
        "bursts": k,
        "out_starts": pairs,
        "states": states,
        "emissions": stream,
    }


def compact_case(prep, width, steps, orders):
    r = scatter(prep, width, steps, orders)
    return {k: v for k, v in r.items() if k not in ("states", "emissions")}


def weight_control(rows):
    """Single-port rows fix incoming weights from outgoing. One pair fixes their sum."""
    for i in range(3):
        require(
            rows[1 << i]["out"] == tuple(int(j != i) for j in range(3)), "single fanout"
        )
    require(
        rows[3]["out"] == (0, 0, 1) and rows[6]["out"] == (1, 0, 0), "adjacent inputs"
    )
    # If output weights are b, singles force a_i=sum(b)-b_i. Row 3 then
    # forces sum(b)=0; conversely any sum-zero b and a=-b works on all
    # measured rows since O+I is constant. This is a signed 2D kernel.
    for row in rows:
        require(len(set(row["sum"])) == 1, "signed weight control")
    return {
        "only_nonnegative_solution_is_zero": True,
        "signed_kernel_dimension": 2,
        "signed_solutions": "a=-b, sum(b)=0 (a incoming, b outgoing)",
    }


def experiment():
    clock = ((0, 1, 2),)
    preps = [tuple((5,) if m >> i & 1 else () for i in range(3)) for m in range(8)]
    masks = [compact_case(p, 40, 10, clock) for p in preps]
    expected = ("000", "011", "101", "001", "110", "121", "100", "111")
    require(
        tuple("".join(map(str, r["out"])) for r in masks) == expected,
        "frozen mask rows",
    )
    options = ((), (5,), (7,), (9,), (5, 9))
    grid = Counter(
        scatter(p, 64, 18, clock)["bursts"] for p in product(options, repeat=3)
    )
    # Frozen holdouts: delayed trains; all six orders on the original star;
    # trivial two-arm geometry and larger stars, distant ends and later cut.
    held = Counter()
    for d in (2, 3, 4, 5):
        orders = (
            permutations(range(d))
            if d == 3
            else (tuple(range(d)), tuple(reversed(range(d))))
        )
        for order in orders:
            for shift in range(d):
                train = ((11, 19), (15,), (), (13, 21), (11,))
                prep = tuple(train[(i + shift) % d] for i in range(d))
                scatter(prep, 100, 32, (order,))
                held[d] += 1
    alt = compact_case(preps[1], 40, 10, ((0, 1, 2), (2, 1, 0)))
    require(alt["sum"] == (2, 1, 1), "alternating clock countercontrol changed")
    delayed = compact_case(((7,), (), (5,)), 40, 10, clock)
    require(
        delayed["in"] == masks[5]["in"] and delayed["out"] == (0, 1, 0),
        "same counts, changed arrival timing countercontrol",
    )
    return {
        "masks": masks,
        "prepared_grid": {"cases": sum(grid.values()), "burst_histogram": dict(grid)},
        "held_out": {"degrees": list(held), "cases_by_degree": dict(held)},
        "raw": [raw_balance(3, n) for n in (3, 4)],
        "clock_control": alt,
        "timing_control": {"synchronous": masks[5], "delayed": delayed},
        "weight_control": weight_control(masks),
        "boundary": "finite binary dynamics under supplied wiring, clock and preparation; no physics-status upgrade",
    }


if __name__ == "__main__":
    print(json.dumps(experiment(), sort_keys=True, indent=2))
