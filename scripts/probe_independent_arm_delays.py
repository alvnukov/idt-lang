"""Change each corridor length independently; carry both raw bonds across each gate.

Run: python3 -m scripts.probe_independent_arm_delays
"""

import json
from fractions import Fraction

if __package__:
    from . import probe_raw_bond_junction_rates as base
else:
    import probe_raw_bond_junction_rates as base


def fixture(lengths):
    """Two crossing nodes shared by both rails; corridor IDs are near-end IDs."""
    def point(axis, i):
        minus, plus = lengths[2*axis:2*axis+2]
        k = i % (minus + plus)
        if k == 0 or k == plus:
            return (-1, int(k == plus))
        return (axis, k)

    graph = {}
    for axis in (0, 1):
        for i in range(sum(lengths[2*axis:2*axis+2])):
            neighbors = graph.setdefault(point(axis, i), set())
            neighbors.update(point(axis, i+d) for d in (-2, -1, 1, 2))

    def far_point(axis, i):
        return point(axis, lengths[2*axis+1]+i)

    return {v: frozenset(ns) for v, ns in graph.items()}, point, far_point


def census(lengths):
    graph, point, far_point = fixture(lengths)
    seeds = [base.phase_a(point, ax, side*6, -side) for ax, side in base.ARMS]
    trans, terminal = base.event_graph(base.FreeAlternatives(graph), seeds,
        base.gates(point, 0), base.gates(far_point, 0, far=True))
    values, _ = base.first_event(trans, terminal, trap_label=base.recorded_trap)
    rows = []
    for i, seed in enumerate(seeds):
        joint = values[None, seed]
        jam = sum((v for k, v in joint.items() if k.rsplit(":", 1)[-1] == "jam"), Fraction())
        rows.append({"input": i, "joint": {k: str(v) for k, v in sorted(joint.items())},
                     "jam": str(jam)})
    return rows


def report():
    rows = []
    for mask in range(16):
        lengths = [14 + ((mask >> j) & 1) for j in range(4)]
        rows.extend(dict(r, mask=mask, lengths=lengths) for r in census(lengths))
    transfer = [21, 24, 19, 28]
    return {"arm_order": base.ARMS, "rows": rows,
            "transfer": {"lengths": transfer, "rows": census(transfer)},
            "scope": "Exact finite uniform active-offer census, including loss. The path "
                     "label is a passive simulation tracer, not an implemented detector "
                     "or physical which-path record. Length changes alter the native gait "
                     "and can cause jam; they do not implement a lossless complex phase "
                     "knob, a physical clock, or an interference test for other rules."}


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
