"""Sharp common-coupling intervals for the pinned measured-ion pentagon tables.

Run: python3 -B -m scripts.probe_ion_coupling_certificates --json

For ordered edge i, bits 2i and 2i+1 record its chronological first and second
outcomes (bright=1). D counts vertices whose two copies disagree, not edges
whose detectors disagree. The endpoint laws were found by a linear program
with 20 joint-cell constraints and 1024 nonnegative variables. The solver is
not used or trusted in replay: all atom weights, marginals and inequalities
are checked with integer arithmetic. Mixtures of the two laws preserve every
cell and interpolate E[D], including every real point in the closed interval.
"""

import argparse
import json
from fractions import Fraction

if __package__:
    from .probe_measured_ion_pentagon import load_fixture, require
else:
    from probe_measured_ion_pentagon import load_fixture, require


TICKS = 10000
# Each pair is (ten-bit mask, numerator of probability with denominator TICKS).
CERTIFICATES = {
    "normal": {
        "lower": ((102, 1077), (358, 144), (390, 1070), (406, 220),
                  (408, 1028), (409, 2048), (414, 10), (486, 7),
                  (537, 1001), (601, 246), (609, 1084), (613, 147),
                  (614, 1885), (615, 4), (633, 22), (921, 7)),
        "upper": ((34, 613), (41, 196), (74, 52), (168, 216),
                  (296, 164), (331, 4), (341, 4359), (562, 21),
                  (596, 194), (650, 1014), (672, 443), (682, 2699),
                  (684, 10), (692, 1), (722, 7), (810, 7)),
    },
    "reverse": {
        "lower": ((153, 1014), (294, 994), (358, 92), (402, 1080),
                  (406, 139), (409, 2223), (411, 9), (438, 15),
                  (585, 1084), (601, 8), (612, 1042), (613, 138),
                  (614, 2135), (621, 9), (729, 12), (870, 6)),
        "upper": ((22, 375), (34, 211), (106, 413), (168, 6),
                  (227, 9), (341, 4101), (424, 448), (481, 3),
                  (540, 9), (545, 384), (568, 15), (644, 85),
                  (650, 999), (672, 473), (682, 2463), (936, 6)),
    },
}
BOUNDARY = ("D is a discrepancy between copies in a hypothetical common coupling, "
            "not measured physical disturbance. This is the sharp range for the "
            "empirical ordered tables, not a population confidence interval or "
            "evidence that the apparatus realizes any particular coupling.")


def verify_order(rec, certificates):
    """Certify attainment of both bounds for this table; not a general LP solver."""
    edges, rows = rec["ordered_edges"], rec["counts"]
    require(len(edges) == len(rows) == 5, "expected five ordered edges and tables")
    require(all(len(row) == 4 and all(type(x) is int and x >= 0 for x in row)
                and sum(row) == TICKS for row in rows), "invalid four-cell count table")
    first = {a: i for i, (a, b) in enumerate(edges)}
    second = {b: i for i, (a, b) in enumerate(edges)}
    require(first.keys() == second.keys() == set(range(1, 6))
            and all(a != b for a, b in edges)
            and len({frozenset(edge) for edge in edges}) == 5, "expected a simple pentagon")
    # Connect copies by explicit observable label, including in reverse acquisition.
    paired = [(2*first[v], 2*second[v]+1) for v in first]
    states = []
    for mask in range(1024):
        bits = [(mask >> j) & 1 for j in range(10)]
        cells = [2*x+y for x, y in zip(bits[::2], bits[1::2])]
        d = sum(bits[x] != bits[y] for x, y in paired)
        bright, both = sum(bits), cells.count(3)
        # Pointwise dual bounds: 2S = bright, J = both.
        require(bright - 2*both - 4 <= d <= bright, "pointwise bound failed")
        states.append((cells, d))

    bright_ticks = sum(b+c+2*d for a, b, c, d in rows)
    both_ticks = sum(row[3] for row in rows)
    marginal_ticks = sum(abs(sum(rows[first[v]][2:]) -
                             (rows[second[v]][1] + rows[second[v]][3])) for v in first)
    bounds = {"lower": max(marginal_ticks, bright_ticks - 2*both_ticks - 4*TICKS),
              "upper": bright_ticks}
    for key, bound in bounds.items():
        law = certificates[key]
        cells = [[0]*4 for _ in edges]
        total = objective = 0
        for mask, ticks in law:
            require(type(mask) is int and 0 <= mask < 1024, "invalid assignment mask")
            require(type(ticks) is int and ticks > 0, "invalid nonzero probability weight")
            assignment, d = states[mask]
            for i, cell in enumerate(assignment):
                cells[i][cell] += ticks
            total += ticks
            objective += ticks*d
        require(total == TICKS, "probability weights do not sum to one")
        require(cells == rows, "law fails to reproduce all ordered joint cells")
        require(objective == bound, f"{key} law does not saturate its bound")
    return {"E_D_interval": [str(Fraction(bounds[key], TICKS)) for key in ("lower", "upper")],
            "marginal_TV_sum": str(Fraction(marginal_ticks, TICKS)),
            "assignments_checked": len(states)}


def experiment():
    orders = load_fixture()["orders"]
    return {"orders": {name: verify_order(orders[name], cert)
                       for name, cert in CERTIFICATES.items()}, "boundary": BOUNDARY}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="compact JSON")
    args = parser.parse_args()
    print(json.dumps(experiment(), indent=None if args.json else 2))
