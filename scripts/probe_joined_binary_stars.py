"""Native pulse-count response of two binary stars sharing one 41-link path.

Run: python3 -m scripts.probe_joined_binary_stars

Bit j on each exterior path is j links from the center (the incident link
has j=0); bridge coordinates increase from A to B. Every microphase is a
supplied matching. Each offered link toggles iff another occupied link meets
one of its endpoints. The histories never consult the packet reader, the
isolated-star response, or the mean-field prediction.

All means here are equal-weight enumerations of fixed cyclic starts, not
microscopic probabilities. No inferred amplitude, energy, or physics upgrade.
"""

import json
from itertools import product

from scripts import probe_available_link_logic as base
from scripts import probe_binary_star_contrast as star

require = star.require
MASKS = (7, 6, 5, 3)  # full, then omit A0, A1, A2 respectively


def rotation(start):
    return tuple((start + j) % 3 for j in range(3))


def reflect3(v):
    """3R on three ports, R = (2/3)J - I."""
    return tuple(2 * sum(v) - 3 * x for x in v)


def isolated():
    sums = {}
    for mask in range(8):
        inc = tuple((mask >> i) & 1 for i in range(3))
        prep = tuple((5,) if x else () for x in inc)
        rows = []
        for a in range(3):
            order = rotation(a)
            row = star.scatter(prep, 40, 10, (order,))
            k = int(any(inc)) + inc[order[0]] * inc[order[-1]]
            require(k == row["bursts"], "single-star simultaneous burst formula")
            rows.append(row["out"])
        sums[mask] = tuple(map(sum, zip(*rows)))
    require(sums[7] == (3, 3, 3), "isolated full reference")
    residuals = {}
    for mask in (6, 5, 3, 1, 2, 4):
        di = tuple(((mask >> j) & 1) - 1 for j in range(3))
        pred = reflect3(di)
        residuals[mask] = tuple(
            x - ref - p for x, ref, p in zip(sums[mask], sums[7], pred)
        )
        require(residuals[mask] == (int(sum(di) == -2),) * 3, "single/two-hole control")
    return {
        "order_rows": 24,
        "mean_times_three": sums,
        "hole_residual_times_three": residuals,
    }


class Wiring:
    """Physical link enumeration: A0, A1, common A→B bridge, B0, B1."""

    def __init__(self, exterior=180, bridge=41):
        require(
            exterior >= 2 and bridge >= 3 and bridge % 2 == 1, "invalid path extents"
        )
        edges, paths = [], []
        next_vertex = 2  # vertices 0 and 1 are A and B
        for p, n in enumerate((exterior, exterior, bridge, exterior, exterior)):
            path = tuple(range(len(edges), len(edges) + n))
            paths.append(path)
            v = int(p >= 3)
            for j in range(n):
                if p == 2 and j == n - 1:
                    w = 1
                else:
                    w = next_vertex
                    next_vertex += 1
                edges.append((v, w))
                v = w
        self.edges, self.paths = tuple(edges), tuple(paths)
        self.bits = tuple(1 << i for i in range(len(edges)))
        self.witnesses = base.witness_masks(self.edges)
        self.remote = sum(self.bits[path[-1]] for p, path in enumerate(paths) if p != 2)

    def phases(self, a, b):
        require(a in range(3) and b in range(3), "invalid cyclic start")
        phases = [[], [], [], []]
        for p, path in enumerate(self.paths):
            for j, edge in enumerate(path):
                if j % 2:
                    phase = 3
                elif p < 2:
                    phase = (p - a) % 3
                elif p > 2:
                    phase = (p - 3 - b) % 3
                elif j in (0, len(path) - 1):
                    phase = (2 - (a if j == 0 else b)) % 3
                else:
                    phase = 0
                phases[phase].append(edge)
        require(
            sorted(i for phase in phases for i in phase)
            == list(range(len(self.edges))),
            "missing or repeated offered link",
        )
        for phase in phases:
            vertices = [v for i in phase for v in self.edges[i]]
            require(len(vertices) == len(set(vertices)), "phase is not a matching")
        return tuple(tuple(p) for p in phases)

    def sweep(self, state, phases):
        mids = []
        for phase in phases:
            for i in phase:
                if state & self.witnesses[i]:
                    state ^= self.bits[i]
            mids.append(state)
        return tuple(mids)

    def unpack(self, state):
        return tuple((state >> p[0]) & ((1 << len(p)) - 1) for p in self.paths)

    def initial(self, mask, offset):
        require(mask in MASKS and offset in (47, 49), "unregistered preparation")
        state = 0
        for p, path in enumerate(self.paths):
            if p < 3 and not (mask >> p) & 1:
                continue
            j = 5 if p < 3 else offset
            state |= self.bits[path[j]] | self.bits[path[j + 1]]
        return state


def clean_starts(x, direction):
    """Consume each bit as exactly one slot of a separated, phased pair."""
    require(direction in (-2, 2) and x >= 0, "invalid directed state")
    starts = []
    while x:
        j = (x & -x).bit_length() - 1
        require(
            j > 0 and j % 2 == int(direction == -2) and ((x >> j) & 7) == 3,
            "unclean directed pair",
        )
        starts.append(j)
        x ^= 3 << j
    return tuple(starts)


def passage(x, y, direction):
    """Exact translation on the entire bitset, including empty tails."""
    heads = clean_starts(x, direction)
    next_heads = clean_starts(y, direction)
    require(
        next_heads == tuple(j + direction for j in heads), "inexact packet translation"
    )
    return heads


def trace(g, phases, a, b, mask, offset):
    state = g.initial(mask, offset)
    cuts = {}
    for t in range(1, 67):
        mids = g.sweep(state, phases)
        require(not any(x & g.remote for x in mids), "remote endpoint reached")
        state = mids[-1]
        if t in (35, 36, 65, 66):
            cuts[t] = g.unpack(state)
    starts = {}
    for t in (35, 65):
        starts[t] = tuple(
            passage(x, y, -2 if p == 2 else 2)
            for p, (x, y) in enumerate(zip(cuts[t], cuts[t + 1]))
        )
        starts[t + 1] = tuple(
            clean_starts(y, -2 if p == 2 else 2) for p, y in enumerate(cuts[t + 1])
        )
    early, late = starts[35], starts[65]
    require(not late[2], "return passage left bridge debris")
    echo = []
    for i in (0, 1):
        lo = tuple(j for j in late[i] if j + 1 < 80)
        hi = tuple(j for j in late[i] if j > 80)
        require(lo + hi == late[i] and len(lo) == len(early[2]), "unresolved A echo")
        require(hi == tuple(j + 60 for j in early[i]), "A direct trace changed")
        echo.append(len(lo))
    for i in (3, 4):
        require(late[i] == tuple(j + 60 for j in early[i]), "B exterior trace changed")
    return {
        "a": a,
        "b": b,
        "mask": mask,
        **{f"at{t}": s for t, s in starts.items()},
        "a_echo_counts": tuple(echo),
    }


def experiment():
    g = Wiring()
    phases = {(a, b): g.phases(a, b) for a, b in product(range(3), repeat=2)}
    pred = []
    for i in range(3):
        a = reflect3(tuple(-int(j == i) for j in range(3)))
        pred.append(reflect3((0, 0, a[2])))  # B ports: exterior 0, exterior 1, bridge
    offsets = {}
    for offset in (47, 49):
        histories = [
            trace(g, clock, a, b, m, offset)
            for (a, b), clock in phases.items()
            for m in MASKS
        ]
        totals = {
            m: tuple(
                sum(len(h["at35"][p]) for h in histories if h["mask"] == m)
                for p in range(5)
            )
            for m in MASKS
        }
        ref = tuple(totals[7][p] for p in (3, 4, 2))
        deltas = [
            tuple(totals[m][p] - totals[7][p] for p in (3, 4, 2)) for m in MASKS[1:]
        ]
        residual = [
            tuple(x - y for x, y in zip(row, prediction))
            for row, prediction in zip(deltas, pred)
        ]
        require(all(len(set(r)) == 1 for r in residual), "contrast response changed")
        expected = (
            [(-5, -5, 1), (-6, -6, 0), (1, 1, -2)]
            if offset == 47
            else [(-5, -5, 1), (-4, -4, 2), (5, 5, 2)]
        )
        require(
            deltas == expected and ref == ((11 if offset == 47 else 10),) * 3,
            "joined response or baseline changed",
        )
        offsets[offset] = {
            "histories": histories,
            "first_pass_totals": totals,
            "b_reference_times_nine": ref,
            "b_deltas_times_nine": deltas,
            "b_residuals_times_nine": residual,
        }
    return {
        "isolated": isolated(),
        "composed_prediction_times_nine": pred,
        "offsets": offsets,
        "path_order": ["A0", "A1", "bridge_A_to_B", "B0", "B1"],
        "b_response_order": ["B0", "B1", "bridge"],
        "boundary": "Finite native count contrasts on supplied graphs, clocks and preparations; no amplitude or probability.",
    }


if __name__ == "__main__":
    print(json.dumps(experiment(), sort_keys=True))
