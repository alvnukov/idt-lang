"""Three sharp, distinct robustness costs for the pinned ordered-ion pentagon.

Run: python3 -B -m scripts.probe_ion_edit_robustness --json

A (hypothetical) stock supplies one pair for each of the five ordered settings.
A global assignment supplies one bit per vertex; exclusivity additionally
forbids any bright-bright edge. Write T for the common row total, U for total
unlike pairs, and B for total bright endpoints. A global five-cycle has at
most four unlike edges: its number of changes is even. Any other stock has at
most five, so the mismatch mass is at least U/T - 4, even for real weights.
One pair relabel can remove at most one unlike edge, so U - 4T pairs must be
relabeled to obtain globally assignable tables. An exclusive assignment has
at most two bright vertices, each encountered twice; one bit flip removes at
most one bright endpoint, so at least B - 4T bit flips are needed.

These are lower bounds, not general formulas for minima. Attainment here
comes from a sparse integer witness checked against all 20 *original* cells.
One witness row is [ten_bit_source, global_pair_target, global_bit_target,
positive_weight]. Source bit 2i is the first endpoint and bit 2i+1 the second;
target bit v-1 is vertex v. The two targets are *separate* alternatives.
Integer weights give a transport of actual counts, not fractional row edits.
"""

import argparse
import json
from fractions import Fraction

if __package__:
    from .probe_ion_coupling_certificates import CERTIFICATES, TICKS
    from .probe_measured_ion_pentagon import load_fixture, require
else:
    from probe_ion_coupling_certificates import CERTIFICATES, TICKS
    from probe_measured_ion_pentagon import load_fixture, require


BOUNDARY = ("Hypothetical common-stock couplings and counterfactual relabelings of fixed "
            "empirical tables; not observed physical disturbance, actual detector errors "
            "or matched events across settings. This is not a population bound or "
            "p-value. Reverse order is not an independent replication. No IDT detector "
            "law or derivation of QM follows.")


def make_transport(edges, source_law):
    """Choose targets using distances on packed ten-bit words; no LP or float."""
    candidates = {}
    for mask in range(32):
        word = sum(((mask >> (v-1)) & 1) << (2*i+j)
                   for i, edge in enumerate(edges) for j, v in enumerate(edge))
        candidates[mask] = word
    first_bits = 0b0101010101
    exclusive = [m for m, w in candidates.items() if not (w & (w >> 1) & first_bits)]
    transport = []
    for source, weight in source_law:
        def pair_cost(target):
            diff = source ^ candidates[target]
            return ((diff | (diff >> 1)) & first_bits).bit_count()
        pair = min(candidates, key=pair_cost)
        bit = min(exclusive, key=lambda m: (source ^ candidates[m]).bit_count())
        transport.append((source, pair, bit, weight))
    return transport


def verify_order(rec, transport):
    """Reconstruct marginals and costs without trusting the target search or lower law."""
    edges, rows = rec["ordered_edges"], rec["counts"]
    require(len(edges) == len(rows) == 5, "expected five settings")
    require(all(len(e) == 2 and all(type(v) is int and 1 <= v <= 5 for v in e)
                and e[0] != e[1] for e in edges), "invalid ordered endpoints")
    require(len({frozenset(e) for e in edges}) == 5
            and all(sum(v in e for e in edges) == 2 for v in range(1, 6)),
            "edges must form a simple pentagon")
    require(all(len(r) == 4 and all(type(x) is int and x >= 0 for x in r)
                and sum(r) == TICKS for r in rows), "invalid four-cell counts")
    # Independently project five-bit assignments onto ordered cell indices.
    global_cells = {mask: tuple(2*((mask >> (a-1)) & 1) + ((mask >> (b-1)) & 1)
                                for a, b in edges) for mask in range(32)}
    is_global = set(global_cells.values())
    is_exclusive = {m for m, cells in global_cells.items() if 3 not in cells}
    require(max(sum(c in (1, 2) for c in t) for t in is_global) == 4
            and max(sum(c.bit_count() for c in global_cells[m]) for m in is_exclusive) == 4,
            "global pentagon cap failed")
    counts = [[0]*4 for _ in edges]
    mismatches = pair_edits = bit_flips = 0
    for src, pair, bit, weight in transport:
        require(type(src) is int and 0 <= src < 1024, "invalid ten-bit source")
        require(all(type(m) is int and m in global_cells for m in (pair, bit)),
                "invalid global target")
        require(bit in is_exclusive, "bit target is not exclusive")
        require(type(weight) is int and weight > 0, "invalid integer transport weight")
        cells = tuple(2*((src >> (2*i)) & 1) + ((src >> (2*i+1)) & 1) for i in range(5))
        mismatches += weight * (cells not in is_global)
        for i, c in enumerate(cells):
            counts[i][c] += weight
            pair_edits += weight * (c != global_cells[pair][i])
            bit_flips += weight * (c ^ global_cells[bit][i]).bit_count()
    require(counts == rows, "transport fails to reproduce all 20 original cells")
    unlike = sum(b+c for a, b, c, d in rows)
    bright = sum(b+c+2*d for a, b, c, d in rows)
    def minimum(cost, lower, denominator, name):
        require(cost == max(0, lower), f"{name}: witness does not saturate lower bound")
        return {"count": cost, "denominator": denominator, "fraction": str(Fraction(cost, denominator))}
    return {"unlike_pairs": unlike, "bright_endpoints": bright,
            "minima": {
                "mismatched_stocks": minimum(mismatches, unlike-4*TICKS, TICKS, "mismatch"),
                "relabeled_pairs": minimum(pair_edits, unlike-4*TICKS, 5*TICKS, "pair edits"),
                "exclusive_bit_flips": minimum(bit_flips, bright-4*TICKS, 10*TICKS, "bit flips")},
            "transport": transport}


def experiment():
    orders = {}
    for name, rec in load_fixture()["orders"].items():
        witness = make_transport(rec["ordered_edges"], CERTIFICATES[name]["lower"])
        orders[name] = verify_order(rec, witness)
    return {"orders": orders, "boundary": BOUNDARY}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="compact JSON")
    args = parser.parse_args()
    print(json.dumps(experiment(), indent=None if args.json else 2))
