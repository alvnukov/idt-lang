"""Compile explicit graph/bit models, preserving their finite reference and failures.

The canonical graph labels are used here ONLY to write a finite device and
independently specify a comparison table from the older additive convention.
The relational_germ_observer evaluator cannot inspect cube coordinates,
lookup charges or call this compiler. A matched prediction is about this
compiled device and its stated finite measurement only. Source records
remain separate and physically unassessed.
"""

from itertools import product

from scripts.probe_anonymous_folded_carrier import cube


def device(name, graph, route, same, different, target):
    return {"id": name, "family": "relational_germ_observer",
            "adjacency": [sorted(v) for v in graph], "marked_route": list(route),
            "recorder": {"flip_on_same": same, "flip_on_different": different},
            "references": [{"vertex": i, "lower": lo, "upper": hi} for i, lo, hi in target]}


def points(xs):
    return [(i, val, val) for i, val in enumerate(xs)]


def reference(mask):
    # Root 0, mark after directions 0 and 1, primitive convention.
    return 3*(mask & 3).bit_count()-2*(mask & 28).bit_count()


def controls():
    g = cube(5, fold=True)
    route = (0, 1, 3)
    refs = points([reference(i if i.bit_count() % 2 == 0 else i ^ 31) for i in range(16)])
    # The second graph is the full cover, not an equivalent relabeling: a
    # different recorder is allowed there and odd-weight endpoints exist.
    full = cube(5)
    offsets = ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1))
    shr = [{4*((i+a) % 4)+(j+b) % 4 for a, b in offsets} for i, j in product(range(4), repeat=2)]
    rook = [{b for b in range(25) if b != a and (b//5 == a//5 or b % 5 == a % 5)}
            for a in range(25)]
    return [
        device("folded_five_flat_binary_ballots", g, route, False, True, refs),
        device("folded_blank_bit_misses_contrast", g, route, False, False, refs),
        device("folded_parallel_record_remembers_history", g, route, True, False, refs),
        device("folded_blank_bit_blank_comparison", g, route, False, False, points([0]*16)),
        device("unfolded_parallel_recorder", full, route, True, False, points(list(map(reference, range(32))))),
        device("empty_fourth_corner", [{1, 2}, {0, 2}, {0, 1}], (0, 1, 2), False, True, [(2, 0, 0)]),
        device("ambiguous_fourth_corner", rook, (0, 1, 2), False, True, [(2, 0, 0)]),
        device("direction_holonomy_and_flat_blank_bit", shr, (0, 1, 2), False, False, points([0]*16)),
    ]


if __name__ == "__main__":
    import json

    print(json.dumps(controls(), separators=(",", ":")))
