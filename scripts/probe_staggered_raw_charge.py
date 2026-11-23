"""Raw charges of ONE frozen staggered unclocked E template, on open paths.

Question fixed before computation: can the clean count of T be conserved
(i) as a signed event current, (ii) as a nonnegative total on *all* raw states
that is a sum of arbitrary bounded-diameter local functions, or (iii) with
nonnegative individual local summands even just on clean-generated states?
Only the existing masks, codes, stocks and open-chain incidence are used.
No clock, probabilistic scheduler, detector rule, or new move is supplied.

Signed linear family (unused AB helper slots ignored). Give A rails weights
(x,y). AB triples 013 and 123 force B rails to be (x,-x-y). The BA triples
014 and 045 then force BA helper weights (y,-x-y); the two other equations
are satisfied. Thus x=1,y=0 counts clean T; x=0,y=1 counts A-b minus B-b.
Each triple contains weight types x,y,-x-y once each. At x=1,y=0 an event
transfers one signed unit between two slots. Complement the occupation on
every negative slot and this is a literal nonnegative occupancy hop, but the
all-a vacuum then carries one unit per negative slot. No time scale follows.

Arbitrary-range argument, separate from finite checks: start B-first in the
all-a vacuum V. The first BA incidence 245 can flip 000 to 111, giving a T
on the right with both helpers dirty. Use the frozen local Ta->aT paths on
fresh bonds to move T to the last site. Call the result D. Let P be the
clean single T at that same position, and H the all-a state with just the
first helper pair dirty. Each local table whose support does not meet BOTH
the distant T and the dirty helper pair satisfies f(D)+f(V)=f(P)+f(H).
Hence any sum F of bounded-diameter tables, even signed, obeys this identity
on a sufficiently long chain. F(V)=0, F(P)=1 and raw conservation F(D)=0
force F(H)=-1. So no such raw total is nonnegative on all configurations.
H is not a clean-generated state: its signed T charge is -1. For the stronger
requirement of individually nonnegative terms one needs positivity only on
the clean-generated V and D: all terms must vanish there. Every term on P
has the same local input as on V or D, so must vanish there too; contradiction.
No translation invariance, linearity of each table, or common coefficients
across different chain lengths are assumed. The conclusion concerns additive
snapshot densities with a uniform range bound, not arbitrary nonlocal charges,
history variables, other templates, or positive particles relative to a sea.

Run: python3 -m scripts.probe_staggered_raw_charge [--sites 7]
"""

import argparse
import json
from itertools import pairwise

from scripts import probe_staggered_binary_codebooks as books
from scripts import probe_two_helper_staggered_search as frozen

TRIPLES_BY_PHASE = tuple(
    tuple(t for j, t in enumerate(frozen.TRIPLES) if mask >> j & 1)
    for _, mask in frozen.SELECTED[1:]
)


def local_weights(phase, x=1, y=0):
    a, b, h = (x, y), (x, -x - y), (y, -x - y)
    return (*b, *a, *h) if phase else (*a, *b, 0, 0)


def slots(n, edge):
    return (*range(2 * edge, 2 * edge + 4), 2 * n + 2 * edge, 2 * n + 2 * edge + 1)


def global_moves(n, first):
    return tuple(
        sum(1 << slots(n, e)[i] for i in t)
        for e in range(n - 1)
        for t in TRIPLES_BY_PHASE[(first + e) % 2]
    )


def embed(local, n, edge):
    return sum(((local >> k) & 1) << i for k, i in enumerate(slots(n, edge)))


def global_weights(n, first, x=1, y=0):
    rails = [(x, y), (x, -x - y)]
    data = tuple(w for i in range(n) for w in rails[(first + i) % 2])
    helpers = tuple(
        w for e in range(n - 1) for w in local_weights((first + e) % 2, x, y)[4:]
    )
    return data + helpers


def charge(state, n, first, x=1, y=0):
    return sum(
        w * ((state >> k) & 1) for k, w in enumerate(global_weights(n, first, x, y))
    )


def coordinates(n):
    """Both rails at 2*i; private helper bits at their edge midpoint 2*i+1."""
    return tuple(c for i in range(n) for c in (2 * i, 2 * i)) + tuple(
        c for i in range(n - 1) for c in (2 * i + 1, 2 * i + 1)
    )


def occupancy(state, weights):
    return tuple(
        ((state >> i) & 1) if w == 1 else 1 - ((state >> i) & 1) if w == -1 else 0
        for i, w in enumerate(weights)
    )


def current_check():
    """All local links in each direction; compare oriented prefix flux to raw charge change."""
    positions = coordinates(2)
    rows, counts = [], []
    events = bad_cuts = bad_hops = 0
    for phase, triples in enumerate(TRIPLES_BY_PHASE):
        weights = local_weights(phase)
        links = 0
        for tri in triples:
            (dest,) = (i for i in tri if weights[i] == 1)
            (source,) = (i for i in tri if weights[i] == -1)
            mask = sum(1 << i for i in tri)
            rows.append(
                {
                    "phase": phase,
                    "triple": tri,
                    "up_event_from_to_slots": (source, dest),
                    "spatial_from_to": (positions[source], positions[dest]),
                }
            )
            for base in range(64 if phase else 16):
                if base & mask:
                    continue
                links += 1
                for x, y, origin, target in (
                    (base, base | mask, source, dest),
                    (base | mask, base, dest, source),
                ):
                    events += 1
                    old, new = occupancy(x, weights), occupancy(y, weights)
                    bad_hops += (
                        old[origin],
                        old[target],
                        new[origin],
                        new[target],
                    ) != (1, 0, 0, 1) or any(
                        old[k] != new[k] for k in range(6) if k not in (origin, target)
                    )
                    for cut in range(-1, 3):
                        # Positive rightward flux = one unit leaves the prefix.
                        flux = int(positions[origin] <= cut) - int(
                            positions[target] <= cut
                        )
                        delta = sum(
                            w * (((y >> k) & 1) - ((x >> k) & 1))
                            for k, w in enumerate(weights)
                            if positions[k] <= cut
                        )
                        bad_cuts += delta != -flux
        counts.append(links)
    return {
        "links_by_phase": tuple(counts),
        "oriented_events": events,
        "cut_violations": bad_cuts,
        "occupancy_hop_violations": bad_hops,
        "up_event_currents": rows,
    }


def clean_check(n):
    checked = errors = 0
    for first in (0, 1):
        sites = tuple(frozen.SELECTED[0][(first + i) % 2] for i in range(n))
        for w, state in zip(books.words(n), books.codes(sites)):
            alternate = sum(
                1 if (i + first) % 2 == 0 else -1 for i, ch in enumerate(w) if ch == "b"
            )
            errors += (
                charge(state, n, first) != w.count("T")
                or charge(state, n, first, 0, 1) != alternate
            )
            checked += 1
    return checked, errors


def four_states(n):
    """Construct one raw trace, not just a projected T count, on a B-first path."""
    if n < 2:
        raise ValueError("at least two sites are needed")
    return _emit(n, (0,), n - 1)


def repeated_four_states(m, k):
    """k disjoint blocks: every dirty helper pair is at least 2m-1 from every T.

    If clean F=C_n+#T, the same rectangle identity now gives F(H)=C_n-k.
    Global nonnegativity forces C_n>=k. Even with positivity only termwise
    on V,D, every summand at P comes from V or D, so C_n+k<=2*C_n.
    At fixed m this is an extensive lower bound, not a fit to small chains.
    """
    if min(m, k) < 1:
        raise ValueError("positive block parameters required")
    return _emit(2 * m * k, range(0, 2 * m * k, 2 * m), m)


def _emit(n, starts, distance):
    path, moves = [0], []

    def flip(edge, delta):
        m = embed(delta, n, edge)
        if path[-1] & m not in (0, m):
            raise AssertionError("disabled raw E move")
        moves.append(m)
        path.append(path[-1] ^ m)

    particle = hole = 0
    for start in starts:
        flip(start, 52)  # data slot 2 and both helpers on a fresh BA bond
        for e in range(start + 1, start + distance):
            phase = (1 + e) % 2
            route = frozen.GENERATOR_PATHS[phase]["Ta", "aT"]
            for x, y in pairwise(route):
                flip(e, x ^ y)
        particle |= 1 << (2 * (start + distance))
        hole |= embed(48, n, start)
    if path[-1] != particle | hole:
        raise AssertionError("trace did not leave exactly the two separated defects")
    return {
        "n": n,
        "V": 0,
        "P": particle,
        "H": hole,
        "D": path[-1],
        "path": path,
        "moves": moves,
    }


def table_obstruction(cert, span):
    """Exact certificate on coefficients of every indicator table on every interval.

    For ANY function on a window, the four-point identity holds iff the two
    multisets of restricted raw inputs coincide. Subsets of those intervals
    inherit the identity. Thus no fit, discretization or LP tolerance enters.
    """
    n = cert["n"]
    pos = coordinates(n)
    checked = uncancelled = 0
    for lo in range(2 * n - 1):
        for hi in range(lo, min(lo + span + 1, 2 * n - 1)):
            mask = sum(1 << k for k, c in enumerate(pos) if lo <= c <= hi)
            lhs = sorted(cert[k] & mask for k in ("V", "D"))
            rhs = sorted(cert[k] & mask for k in ("P", "H"))
            uncancelled += lhs != rhs
            checked += 1
    return {
        "max_fine_grid_diameter": span,
        "intervals_checked": checked,
        "uncancelled_intervals": uncancelled,
    }


def report(n):
    cert = four_states(n)
    sep = 2 * (n - 1) - 1
    vals = [charge(cert[k], n, 1) for k in ("V", "P", "H", "D")]
    weights = global_weights(n, 1)
    return {
        "sites_B_first": n,
        "raw_trace_events": len(cert["moves"]),
        "separation": sep,
        "signed_charge_VPHD": vals,
        "truncated_nonlocal_VPHD": [max(v, 0) for v in vals],
        "positive_occupancy_VPHD": [
            sum(occupancy(cert[k], weights)) for k in ("V", "P", "H", "D")
        ],
        "baseline": weights.count(-1),
        "bounded_local_table_certificate": table_obstruction(cert, sep - 1),
        "spanning_control": table_obstruction(cert, sep),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sites", type=int, default=7)
    args = p.parse_args()
    if not 2 <= args.sites <= 64:
        p.error("choose 2..64 sites for the finite window replay")
    print(
        json.dumps(
            {
                "local_currents": current_check(),
                "clean_check_n6": clean_check(6),
                "separation": report(args.sites),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
