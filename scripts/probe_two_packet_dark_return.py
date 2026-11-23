"""Two initially dark ports in a literal four-mark FreeAlternatives state.

The passive witness and the consuming instrument are different observations.
The former follows a frozen prefix with no changes to the raw state; the
latter removes outward gate marks and counts every trial at a finite horizon.
Neither observation uses a packet label in the raw motion kernel.

Run: python3 -m scripts.probe_two_packet_dark_return
"""

from __future__ import annotations

import json
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from itertools import combinations, permutations, product
from math import lcm, prod

if __package__:
    from . import probe_raw_bond_junction_rates as base
    from .probe_conserved_bond_gait import Marks, Move, link, need
else:
    import probe_raw_bond_junction_rates as base
    from probe_conserved_bond_gait import Marks, Move, link, need


WITNESS_SIZES = (101, 103)
HELDOUT_SIZES = (139, 149)
INSTRUMENT_SIZES = (31, 37)
ENTRANCE_OFFSET = 6
GATE_OFFSETS = (4, 5)
PASSIVE_OUTPUT_OFFSETS = (4, 10)
INSTRUMENT_HORIZON = 36
LOWER_BOUND_TIME = 24
ARMS = range(len(base.ARMS))

# Abstract slots: +k is k out on the return arm, -k is k out on the
# other input arm, and 0 is the common junction. In each row, pivot moves
# (pivot, old tip) to (pivot, new tip). The order is a witness, not a policy.
# Deterministic BFS on the witness wedge supplied it offline; replay is local.
ITINERARY = (
    (-3, -4, -2), (-4, -6, -2), (-2, -3, -1), (-1, -2, 0), (-2, -4, 0),
    (0, -1, 1), (1, 0, 2), (0, -2, 2), (2, 1, 3),
    (4, 6, 2),
    (4, 3, 5), (5, 4, 6), (4, 2, 6), (6, 5, 7), (7, 6, 8), (6, 4, 8),
    (8, 7, 9), (9, 8, 10), (8, 6, 10), (10, 9, 11), (11, 10, 12),
    (10, 8, 12), (12, 11, 13),
    (3, 2, 4), (2, 0, 4), (4, 3, 5), (5, 4, 6), (4, 2, 6), (6, 5, 7),
)


class Wedge:
    def __init__(self, sizes):
        self.sizes = tuple(sizes)
        self.rule = base.FreeAlternatives(base.wedge_graph(*self.sizes))
        self.gates = {
            self.packet(arm, offset, outward=True): str(arm)
            for arm, offset in product(ARMS, GATE_OFFSETS)
        }
        need(self.gates == base.gates(self.point, 0), "detector geometry disagrees with one-body gate")

    def point(self, axis, coord):
        return base.wedge_point(axis, coord, self.sizes[axis])

    def slot(self, arm, distance):
        axis, side = base.ARMS[arm]
        return self.point(axis, side * distance)

    def packet(self, arm, distance=ENTRANCE_OFFSET, *, outward=False):
        axis, side = base.ARMS[arm]
        return base.phase_a(self.point, axis, side * distance, side if outward else -side)


def pair_seed(fixture, inputs):
    a, b = inputs
    if a not in ARMS or b not in ARMS or a == b:
        raise ValueError("expected distinct input arms")
    packets = fixture.packet(a), fixture.packet(b)
    need(not (packets[0] & packets[1]), "input packets share a mark")
    return packets


@dataclass(frozen=True)
class Witness:
    degrees: tuple[int, ...]
    joint_only_steps: tuple[int, ...]
    final: Marks
    offer_menus: tuple[frozenset, ...]

    @property
    def prefix_mass(self):
        return F(1, prod(self.degrees))


def passive_witness(fixture, returning, other):
    """Replay the complete raw offer menus; use geometry only to name moves."""
    packets = list(pair_seed(fixture, (returning, other)))
    state = packets[0] | packets[1]
    return_axis, return_side = base.ARMS[returning]
    other_axis, other_side = base.ARMS[other]

    def slot(coord):
        return fixture.slot(returning if coord >= 0 else other, abs(coord))

    def local(vertex):
        # Compare whole menus across fixtures and ordered source pairs, not
        # just the chosen offer. This is a checked local correspondence, not
        # a claim that unequal cycle lengths admit a global axis swap.
        axis, index = vertex
        if index == 0:
            return (0, 0)
        size = fixture.sizes[axis]
        signed = index if 2 * index < size else index - size
        need(abs(signed) < 16, "an offered move left the witness's local chart")
        side = return_side if axis == return_axis else other_side if other_axis == axis else 1
        return (int(axis != return_axis), signed * side)

    def local_move(move):
        return (local(move.center), frozenset(map(local, move.old)), frozenset(map(local, move.new)))

    degrees, menus, joint_only = [], [], []
    for time, (pivot, old, new) in enumerate(ITINERARY, 1):
        move = Move(slot(pivot), link(slot(pivot), slot(old)), link(slot(pivot), slot(new)))
        offers = fixture.rule.offers(state)
        need(move in offers, f"witness event {time} is not a raw offer")
        degrees.append(len(offers))
        menu = frozenset(map(local_move, offers))
        need(len(menu) == len(offers), "local chart identified distinct raw offers")
        menus.append(menu)
        # This split is a diagnostic for the chosen prefix only. It is not
        # stored or supplied to any actual four-mark transition.
        owner, = [i for i, packet in enumerate(packets) if move.old in packet]
        if all(move not in fixture.rule.offers(packet) for packet in packets):
            joint_only.append(time)
        packets[owner] = move.apply(packets[owner])
        state = move.apply(state)
        need(state == (packets[0] | packets[1]), "diagnostic split changed raw state")
        need(len(state) == 4 and len(state & fixture.rule.shorts) == 2
             and len(state & fixture.rule.longs) == 2, "raw mark counts changed")
        if time == 9:
            need(tuple(packets) == (fixture.packet(returning), fixture.packet(returning, 0, outward=True)),
                 "the other packet did not reach the return arm before contact")
    expected = tuple(fixture.packet(returning, offset, outward=True)
                     for offset in reversed(PASSIVE_OUTPUT_OFFSETS))
    need(tuple(packets) == expected, "passive prefix did not finish at two outward phase-A pairs")
    need(joint_only == [10], "expected one chosen move unavailable in either isolated pair")
    return Witness(tuple(degrees), tuple(joint_only), state, tuple(menus))


def one_body_rows(fixture):
    """Exact all-time first-hit law of the very same fixture and raw rule."""
    seeds = [fixture.packet(arm) for arm in ARMS]
    trans, terminals = base.event_graph(fixture.rule, seeds, fixture.gates, None)
    values, _ = base.first_event(trans, terminals)
    rows = []
    for arm, seed in enumerate(seeds):
        expected = {str(j): F(1, 3) for j in ARMS if j != arm}
        need(values[None, seed] == expected, "one-body calibration is not dark on the diagonal")
        rows.append(tuple(expected.get(str(j), F(0)) for j in ARMS))
    return tuple(rows)


def independent_pair(rows, inputs):
    """Independent two-copy lift, folded only by unlabeled output occupation."""
    a, b = inputs
    result = defaultdict(F)
    for j, k in product(ARMS, repeat=2):
        result[tuple(sorted((j, k)))] += rows[a][j] * rows[b][k]
    return dict(result)


def absorbing_successors(fixture, state, ports):
    """Consume disjoint matched gate marks before selecting any next move."""
    matches = [(gate, int(arm)) for gate, arm in fixture.gates.items() if gate <= state]
    removed = frozenset().union(*(gate for gate, _ in matches))
    if len(removed) != 2 * len(matches):
        return ("overlap", ports), ()  # do not choose between competing removals
    ports = tuple(sorted(ports + tuple(arm for _, arm in matches)))
    state -= removed
    need(len(state) == 2 * (2 - len(ports)), "an absorption removed the wrong mark count")
    if len(ports) == 2:
        return ("detected", ports), ()
    # Keep every distinct raw Move even when several have the same successor.
    # No offers is a jam; no phantom clock ticks or conditioning on escape.
    offers = fixture.rule.offers(state)
    if not offers:
        return ("jam", ports), ()
    return ("unresolved", ports), tuple((move.apply(state), ports) for move in offers)


def consuming_row(fixture, inputs, *, horizon=INSTRUMENT_HORIZON):
    """All outcomes at an active-event horizon, with integer forward weights.

    At time t, every integer weight shares one denominator. Multiply by the
    LCM of all continuing offer degrees at t to propagate another exact step.
    Gate checks and jams at the deadline are evaluated before unresolved mass.
    """
    if horizon < 0:
        raise ValueError("expected nonnegative horizon")
    a, b = pair_seed(fixture, inputs)
    frontier, denominator, outcomes = {(a | b, ()): 1}, 1, {}

    @cache
    def inspect(state, ports):
        return absorbing_successors(fixture, state, ports)

    for time in range(horizon + 1):
        outgoing = []
        for (state, ports), weight in frontier.items():
            outcome, successors = inspect(state, ports)
            if successors and time < horizon:
                outgoing.append((successors, weight))
            else:
                outcomes[outcome] = outcomes.get(outcome, 0) + weight
        if not outgoing:
            break
        factor = lcm(*(len(successors) for successors, _ in outgoing))
        denominator *= factor
        outcomes = {outcome: weight * factor for outcome, weight in outcomes.items()}
        later = defaultdict(int)
        for successors, weight in outgoing:
            part = weight * (factor // len(successors))
            for successor in successors:
                later[successor] += part
        frontier = later
        need(sum(frontier.values()) + sum(outcomes.values()) == denominator,
             "consuming instrument lost mass during propagation")
    need(sum(outcomes.values()) == denominator, "consuming instrument lost final mass")
    return {outcome: F(weight, denominator) for outcome, weight in outcomes.items()}


def report():
    witness_rows, menus_by_class = [], {}
    for sizes in (WITNESS_SIZES, HELDOUT_SIZES):
        fixture = Wedge(sizes)
        for returning, other in permutations(ARMS, 2):
            witness = passive_witness(fixture, returning, other)
            same_line = (returning ^ other) == 1
            reference = menus_by_class.setdefault(same_line, witness.offer_menus)
            need(witness.offer_menus == reference, "local raw offer menus disagree by ordered pair")
            witness_rows.append({"sizes": sizes, "return_arm": returning, "other_input": other,
                                 "same_line": same_line, "degrees": witness.degrees,
                                 "joint_only_steps": witness.joint_only_steps,
                                 "prefix_mass": str(witness.prefix_mass)})

    fixture = Wedge(INSTRUMENT_SIZES)
    single = one_body_rows(fixture)
    pair_rows = []
    for inputs in combinations(ARMS, 2):
        early = consuming_row(fixture, inputs, horizon=LOWER_BOUND_TIME)
        final = consuming_row(fixture, inputs)
        independent = independent_pair(single, inputs)
        lower = [early.get(("detected", (port, port)), F(0)) for port in inputs]
        need(all(value > 0 for value in lower), "dark return lower bound is not positive")
        need(all(independent[port, port] == 0 for port in inputs), "independent return is not dark")
        pair_rows.append({
            "inputs": inputs,
            "occupied_port_double_hits_by_24": [str(value) for value in lower],
            "independent_occupied_port_double_hits": [str(independent[i, i]) for i in inputs],
            "outcomes": [[status, ports, str(value)] for (status, ports), value in sorted(final.items())],
        })
    return {
        "arm_order": base.ARMS,
        "entrance_offset": ENTRANCE_OFFSET,
        "passive": {"steps": len(ITINERARY), "output_offsets": PASSIVE_OUTPUT_OFFSETS,
                    "itinerary": ITINERARY, "rows": witness_rows},
        "consuming": {"sizes": INSTRUMENT_SIZES, "gate_offsets": GATE_OFFSETS,
                      "horizon": INSTRUMENT_HORIZON, "lower_bound_time": LOWER_BOUND_TIME,
                      "one_body_rows_input_then_output": [list(map(str, row)) for row in single],
                      "rows": pair_rows},
        "scope": [
            "The passive prefix is one positive-probability raw trajectory, not a measured rate or a rule.",
            "The consuming readout removes matched marks; its finite-horizon rate is a different observable.",
            "Active time uses uniform distinct raw offers. Jam, unresolved and any competing removal stay in the denominator.",
            "An independent lift has zero double return to an occupied input port. In a mode-preserving passive linear lift calibrated to the same one-body law for both packets, every assignment to that double output has a zero diagonal amplitude factor, independently of symmetrization.",
            "No native linear optics, photon mode identification, or quantum statistics is inferred.",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
