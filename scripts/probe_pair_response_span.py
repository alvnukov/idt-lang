"""Exact readout sufficiency on mixtures of a specified finite preparation menu.

The observable rows and target must use the same column (preparation) order.
This tests the supplied response and kernel only, not a primitive or lab model.
"""
import json
from fractions import Fraction as Q
from itertools import combinations

if __package__:
    from .probe_conserved_bond_gait import Ports, cycle_square, link, offers
else:
    from probe_conserved_bond_gait import Ports, cycle_square, link, offers


def response_span(rows, target):
    """Incremental rational row elimination with an affine decoder or null witness.

    If y is in the row span of B=[1;rows], a decoder works on all mixtures.
    Otherwise a kernel vector distinguishes y; its two signs have equal mass
    thanks to normalization, hence give an actual pair of probability mixtures.
    """
    n = len(target)
    if not n or "normalization" in rows:
        raise ValueError("nonempty preparation menu and unreserved row names required")

    def vector(xs):
        if len(xs) != n or any(type(x) not in (int, Q) for x in xs):
            raise ValueError("every row and target must contain one exact rational per preparation")
        return list(map(Q, xs))

    basis = {}  # pivot -> (unit-pivot row, its expression in original rows)

    def reduce(xs, expression):
        residual = vector(xs)
        for pivot in sorted(basis):
            factor = residual[pivot]
            if factor:
                row, coeff = basis[pivot]
                residual = [x - factor * b for x, b in zip(residual, row)]
                for key, value in coeff.items():
                    expression[key] = expression.get(key, 0) - factor * value
        return residual, expression

    for key, xs in {"normalization": [1] * n, **rows}.items():
        residual, coeff = reduce(xs, {key: 1})
        pivot = next((i for i, x in enumerate(residual) if x), None)
        if pivot is not None:
            factor = residual[pivot]
            basis[pivot] = ([x / factor for x in residual],
                            {k: v / factor for k, v in coeff.items() if v})

    residual, coeff = reduce(target, {})
    free = next((i for i, x in enumerate(residual) if x), None)
    if free is None:
        return {"status": "sufficient", "rank": len(basis),
                "decoder": {k: -v for k, v in coeff.items() if v}}
    null = [Q(0)] * n
    null[free] = Q(1)
    for pivot in sorted(basis, reverse=True):
        row, _ = basis[pivot]
        null[pivot] = -sum(x * z for x, z in zip(row[pivot + 1:], null[pivot + 1:]))
    mass = sum(x for x in null if x > 0)
    return {"status": "not_sufficient", "rank": len(basis), "null": null,
            "left": [max(0, x) / mass for x in null],
            "right": [max(0, -x) / mass for x in null]}


# S_i = {i,i+1}, L_i = {i,i+2}; each prepared state below is averaged over D16.
MENU = {"A": (0, 4, 1, 9), "B": (0, 4, 5, 13),
        "idle45": (0, 1, 4, 5), "idle69": (0, 1, 6, 9),
        "idle47": (0, 1, 4, 7), "idle56": (0, 1, 5, 6)}


def c16_table():
    ports = Ports.from_graph(cycle_square(16))
    # Coordinates label only preparations and readout; offers uses incidence.
    edges = {f"{label}{i}": link(i, (i + step) % 16)
             for label, step in (("S", 1), ("L", 2)) for i in range(16)}
    labels = {bond: key for key, bond in edges.items()}
    rows = {",".join(names): [] for arity in (1, 2) for names in combinations(edges, arity)}
    future = {key: [] for key in ("next:S0,S3", "next:short_count", "current:S0,L3,L4")}
    pair = {edges["S0"], edges["S3"]}
    triple = {edges[key] for key in ("S0", "L3", "L4")}
    order = {key: i for i, key in enumerate(edges)}
    for a, b, c, d in MENU.values():
        counts = dict.fromkeys(rows, 0)
        pair_hits = short_count = triple_hits = Q(0)
        for h in (-1, 1):
            for t in range(16):
                state = frozenset(link((h*i+t) % 16, (h*(i+k)+t) % 16)
                                  for i, k in ((a, 1), (b, 1), (c, 2), (d, 2)))
                marked = sorted((labels[e] for e in state), key=order.__getitem__)
                for key in marked:
                    counts[key] += 1
                for two in combinations(marked, 2):
                    counts[",".join(two)] += 1
                triple_hits += int(triple <= state)
                events = offers(ports, state)
                outcomes = [event.apply(state) for event in events] or [state]
                pair_hits += Q(sum(pair <= s for s in outcomes), len(outcomes))
                short_count += Q(sum(len(ports.short_links & s) for s in outcomes), len(outcomes))
        for key in rows:
            rows[key].append(Q(counts[key], 32))
        future["next:S0,S3"].append(pair_hits / 32)
        future["next:short_count"].append(short_count / 32)
        future["current:S0,L3,L4"].append(triple_hits / 32)
    return rows, future


def main():
    rows, future = c16_table()
    print(json.dumps({"scope": "all mixtures of listed D16-uniform preparations only",
                      "preparation_order": list(MENU), "preparations_S_S_L_L": MENU,
                      "observations": len(rows),
                      "readouts": {key: {"values": y, **response_span(rows, y)}
                                   for key, y in future.items()}}, default=str, indent=2))


if __name__ == "__main__":
    main()
