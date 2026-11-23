"""An arm and contact time do not determine a raw two-bond junction response.

Exhaust first-touch states on an isolated cycle square, then place each at the
same collar on three supplied junction fixtures. Propagate the frozen raw
rules under uniform choice among distinct offered moves. A passive first-hit
recorder stops at the established outward gates or a jam.

Run: python3 -m scripts.probe_two_bond_entrance_collar
"""

import json
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations

if __package__:
    from . import probe_raw_bond_junction_rates as base
    from .probe_conserved_bond_gait import cycle_square, link, need
    from .probe_independent_arm_delays import fixture as two_junction_fixture
else:
    import probe_raw_bond_junction_rates as base
    from probe_conserved_bond_gait import cycle_square, link, need
    from probe_independent_arm_delays import fixture as two_junction_fixture


COLLAR_DISTANCE = 6
PHASES = {"A": ((-3, -1), (-1, 0)), "B": ((-4, -2), (-1, 0))}
PREDECESSORS = {"A": ((-3, -1), (-2, -1)), "B": ((-4, -2), (-2, -1))}


def marks(point, offsets):
    return frozenset(link(point(a), point(b)) for a, b in offsets)


def touches(state, vertex):
    return any(vertex in bond for bond in state)


def isolated_first_touch():
    """Every edge-pair transition that crosses from q-avoiding to touching q."""
    n, q = 71, 32
    raw = base.FreeAlternatives(cycle_square(n))
    edges = [bond for bond in raw.shorts | raw.longs if q not in bond]
    actual = {}
    for pair in combinations(edges, 2):
        state = frozenset(pair)
        for move in raw.offers(state):
            target = move.apply(state)
            if touches(target, q):
                need((state, target) not in actual, "duplicate isolated first-touch offer")
                actual[state, target] = move

    expected, rows = set(), []
    for h in (-1, 1):
        def point(offset):
            return (q + h*offset) % n

        for phase in PHASES:
            before = marks(point, PREDECESSORS[phase])
            after = marks(point, PHASES[phase])
            expected.add((before, after))
            need((before, after) in actual, "missing isolated collar first touch")
            move = actual[before, after]
            rows.append({
                "phase": phase, "direction": h, "pivot": move.center,
                "before": sorted(sorted(bond) for bond in before),
                "after": sorted(sorted(bond) for bond in after),
            })
    need(set(actual) == expected, "unexpected isolated collar first touch")
    return {"order": n, "q": q, "q_avoiding_pairs": len(edges)*(len(edges) - 1)//2,
            "transitions": rows}


def collar_coordinate(point, input_arm, *, far=False):
    axis, near_side = base.ARMS[input_arm]
    # Far local orientations are reversed, while labels still name the same
    # corridors by their near-end sides.
    inward = near_side if far else -near_side
    return lambda offset: point(axis, inward*(offset - COLLAR_DISTANCE))


def preparation(point, input_arm, phase, *, far=False):
    return marks(collar_coordinate(point, input_arm, far=far), PHASES[phase])


def first_junction_touch(rule, seed, junction):
    # This is a check on the corridor, not a clock supplied to the rule.
    state, seen = seed, set()
    while not touches(state, junction):
        need(state not in seen, "closed orbit before junction touch")
        seen.add(state)
        moves = rule.offers(state)
        need(len(moves) == 1, "pre-junction corridor is not deterministic")
        move, = moves
        state = move.apply(state)
    return len(seen)


def propagate(trans, terminal, seed, horizon):
    """Exact first-hit masses through horizon and live mass at that time."""
    need(horizon >= 0, "negative first-hit horizon")
    current, hits = {seed: F(1)}, defaultdict(F)
    for t in range(horizon + 1):
        later, live = defaultdict(F), F(0)
        for state, mass in current.items():
            targets = trans[state]
            if state in terminal:
                need(not targets, "first-hit terminal is not absorbing")
                hits[t, terminal[state]] += mass
            else:
                need(bool(targets), "dead end not recorded as terminal")
                live += mass
                if t < horizon:
                    for target in targets:
                        later[target] += mass / len(targets)
        current = later
    need(sum(hits.values()) + live == 1, "first-hit propagation lost mass")
    return dict(hits), live


def certify_geometric(trans, terminal, seed, *, start, outcomes, first, ratio):
    """Certify all times, not just the explicitly propagated prefix.

    Write p_o(t)=e Q**(t-1) g_o for t>=1, with Q the nonterminal
    transition matrix and g_o the one-step probabilities into outcome o.
    Then p_o(t+1)-ratio*p_o(t)=e Q**(t-1) (Q-ratio*I) g_o satisfies the
    characteristic recurrence of Q. If its first d values from t=start
    vanish, all subsequent values vanish too, where d is the dimension of
    Q. For unlisted outcomes use the same zero-prefix check: their geometric
    coefficient is zero. The verified total of the series is one.
    """
    dimension = len(trans) - len(terminal)
    need(dimension > 0 and seed not in terminal, "geometric law needs a live seed")
    need(start >= 1 and 0 < ratio < 1 and first > 0, "invalid geometric law parameters")
    need(len(outcomes) == len(set(outcomes)) and len(outcomes)*first/(1 - ratio) == 1,
         "geometric law does not normalize")
    horizon = start + dimension
    hits, live = propagate(trans, terminal, seed, horizon)
    expected = {(t, out): first * ratio**(t - start)
                for t in range(start, horizon + 1) for out in outcomes}
    need(hits == expected, "geometric first-hit law disagrees with exact prefix")
    return {
        "geometric": {"outcomes": list(outcomes), "start": start,
                      "first_mass": str(first), "ratio": str(ratio)},
        "transient_states": dimension,
        "residual_steps": dimension,
        "checked_through": horizon,
        "live_at_check": str(live),
    }


def certify_atoms(trans, terminal, seed, expected):
    horizon = max(t for t, _ in expected)
    hits, live = propagate(trans, terminal, seed, horizon)
    need(hits == expected and live == 0, "finite first-hit law disagrees with exact replay")
    return {"atoms": [[t, out, str(mass)] for (t, out), mass in sorted(hits.items())],
            "checked_through": horizon, "live_at_check": str(live)}


def fixture_rows(graph, point, lengths, *, far=False):
    raw, line = base.FreeAlternatives(graph), base.compile_lines(graph)
    gates = base.gates(point, 0, far=far)
    junction = point(0, 0)
    need(junction == point(1, 0), "rails do not share junction vertex")
    for arm in range(4):
        local = collar_coordinate(point, arm, far=far)
        for phase in PHASES:
            seed = preparation(point, arm, phase, far=far)
            before = marks(local, PREDECESSORS[phase])
            need(not touches(before, local(0)) and touches(seed, local(0)),
                 "preparation does not first touch the collar")
            need(not touches(seed, junction) and seed not in gates,
                 "collar preparation already touches junction or outward gate")
            first_touch = first_junction_touch(raw, seed, junction)
            need(first_touch == 9 and first_junction_touch(line, seed, junction) == first_touch,
                 "corridor time to junction differs")
            row = {
                "fixture": "far_junction" if far else "wedge", "lengths": lengths,
                "input": arm, "phase": phase, "first_contact_time": 0,
                "first_junction_touch_time": first_touch,
            }
            straight = str(arm ^ 1)
            for name, rule in (("free", raw), ("line", line)):
                moves = rule.offers(before)
                need(len(moves) == 1 and next(iter(moves)).apply(before) == seed,
                     "placed preparation is not the deterministic first touch")
                trans, terminal = base.event_graph(rule, [seed], gates, None)
                need(all(len(state) == 2 and len(state & raw.shorts) == 1
                         and len(state & raw.longs) == 1 for _, state in trans),
                     "two-bond type counts changed")
                start = (None, seed)
                if name == "free" and phase == "B":
                    outcomes = tuple(str(i) for i in range(4) if i != arm)
                    row[name] = certify_geometric(trans, terminal, start, start=20,
                                                  outcomes=outcomes, first=F(1, 9), ratio=F(2, 3))
                else:
                    if name == "free":
                        expected = {(11, "jam"): F(2, 3), (21, straight): F(1, 3)}
                    else:
                        expected = {(21 if phase == "A" else 20, straight): F(1)}
                    row[name] = certify_atoms(trans, terminal, start, expected)
            yield row


def report():
    rows = []
    for sizes in ((31, 37), (47, 53)):
        def point(axis, i):
            return base.wedge_point(axis, i, sizes[axis])

        rows.extend(fixture_rows(base.wedge_graph(*sizes), point, sizes))
    lengths = (21, 24, 19, 28)
    graph, _, far = two_junction_fixture(lengths)
    rows.extend(fixture_rows(graph, far, lengths, far=True))
    return {
        "arm_order": base.ARMS,
        "collar_distance": COLLAR_DISTANCE,
        "isolated_first_touch": isolated_first_touch(),
        "rows": rows,
        "assumptions": [
            "A separated homogeneous empty corridor up to the collar.",
            "The raw state is two bonds; no extra persistent state or memory.",
            "The compared preparations have the same fixed input and arrival-time law.",
            "Each active move is drawn uniformly from the distinct raw offers.",
        ],
        "scope": "Time zero is first touch of the collar, not first touch of the junction. "
                 "Time counts active moves, not idle attempts or physical time. "
                 "The labels and times are passive first-hit records; neither law receives them. "
                 "This finite witness rules out an arm-and-arrival-time description of these "
                 "raw responses under the stated assumptions. It does not rule out other "
                 "preparation models or establish native amplitudes, interference, or QM.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
