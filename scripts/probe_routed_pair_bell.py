"""Finite CHSH event routing on one eight-rail composite cloud.

Inputs are a joint configuration-space gate and preparation, supplied integer
local analyzers, uniform seed laws, and fixed exit-rail bit readout. The tags
follow signed-child cancellation routes; no Born probabilities are supplied.
The analyzers are local as matrices, not as a Bell-local hidden-variable model:
the cloud and routing context are joint. These finite checks do not explain QM
or imply real-world superluminal signalling. Apart from the equal-gain A0
global phase, the matrices are real; the phase does not affect these readouts.

Run from the repository root: python3 -O -m scripts.probe_routed_pair_bell
"""

import sys
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import NamedTuple

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_cancellation_event_router import (
    Cloud,
    Matrix,
    Pair,
    need,
    pairs,
    route_block,
)

Rail = tuple[int, int, int]
Ticket = tuple[int, int, int]  # preparation seed, Alice's seed, Bob's seed
Outcome = tuple[int, int]  # Alice's bit, Bob's bit
Order = tuple[int, int]
Setting = tuple[int, int]
Witness = tuple[Ticket, int, int]

BITS = range(2)
RAILS: tuple[Rail, ...] = tuple(product(BITS, BITS, BITS))  # (a, b, real/imag)
SETTINGS: tuple[Setting, ...] = tuple(product(BITS, BITS))
TICKETS: tuple[Ticket, ...] = tuple(product(BITS, BITS, range(5)))
A_FIRST: Order = (0, 1)
B_FIRST: Order = (1, 0)

H2: Matrix = ((1, 1), (1, -1))
A0: Matrix = ((1, -1), (1, 1))  # (1+i) on each amplitude, computational (Z) readout
B0: Matrix = ((2, 1), (-1, 2))
B1: Matrix = ((2, -1), (1, 2))


def lift(gate: Matrix, slot: int) -> Matrix:
    return tuple(
        tuple(
            gate[dst[slot]][src[slot]]
            if all(dst[i] == src[i] for i in range(3) if i != slot)
            else 0
            for src in RAILS
        )
        for dst in RAILS
    )


PREP_H = lift(H2, 0)
CNOT: Matrix = tuple(
    tuple(int(dst == (a, a ^ b, k)) for a, b, k in RAILS) for dst in RAILS
)
ANALYZERS = ((lift(A0, 2), lift(H2, 0)), (lift(B0, 1), lift(B1, 1)))


class Run(NamedTuple):
    outcomes: dict[Ticket, Outcome]
    rail_counts: Counter[int]


def prepare(entangled: bool) -> tuple[Cloud, tuple[Pair, ...]]:
    cloud, route, h, _ = route_block(((0, 1),), PREP_H)
    need(h == 2, "preparation seed law does not match gate gain")
    tags = tuple(route[(0, 0), seed] for seed in range(h))
    if entangled:
        cloud, route, h, _ = route_block(cloud, CNOT)
        need(h == 1, "CNOT is not a unit-gain permutation")
        tags = tuple(route[tag, 0] for tag in tags)
    need(set(tags) == pairs(cloud), "preparation tags do not cover the cloud")
    return cloud, tags


def run_setting(
    prep: tuple[Cloud, tuple[Pair, ...]], setting: Setting, order: Order
) -> Run:
    cloud, initial_tags = prep
    stages: list[tuple[Cloud, dict[tuple[Pair, int], Pair]]] = []
    for party in order:
        cloud, route, h, _ = route_block(cloud, ANALYZERS[party][setting[party]])
        need(h == (2, 5)[party], "analyzer seed law does not match gate gain")
        stages.append((cloud, route))

    first, second = order
    (first_cloud, first_route), (_, second_route) = stages

    outcomes: dict[Ticket, Outcome] = {}
    exits: set[Pair] = set()
    rail_counts: Counter[int] = Counter()
    for ticket in TICKETS:
        # The same party seed travels with its analyzer under order reversal.
        mid_tag = first_route[initial_tags[ticket[0]], ticket[first + 1]]
        first_bit = RAILS[first_cloud[mid_tag[0]][0]][first]
        tag = second_route[mid_tag, ticket[second + 1]]
        i, j = tag
        rail_i, rail_j = cloud[i][0], cloud[j][0]
        need(rail_i == rail_j, "one tag does not define a coincident exit rail")
        need(tag not in exits, "duplicate exit event")
        exits.add(tag)
        rail_counts[rail_i] += 1
        a, b, _ = RAILS[rail_i]
        need((a, b)[first] == first_bit, "second analyzer rewrote the first output bit")
        outcomes[ticket] = a, b

    need(exits == pairs(cloud), "some live exit events were not routed")
    need(rail_counts.total() == len(TICKETS) == 20, "missing or rejected seed trial")
    return Run(outcomes, rail_counts)


def raw_counts(run: Run) -> tuple[int, ...]:
    counts: Counter[Outcome] = Counter()
    for rail, n in run.rail_counts.items():
        a, b, _ = RAILS[rail]
        counts[a, b] += n
    return tuple(counts[a, b] for a, b in SETTINGS)


def summarise(run: Run) -> tuple[Fraction, Fraction, Fraction]:
    n00, n01, n10, n11 = raw_counts(run)
    n = len(TICKETS)  # all trials, not just a selected detection sample
    return (
        Fraction(n00 - n01 - n10 + n11, n),
        Fraction(n00 + n01, n),
        Fraction(n00 + n10, n),
    )


def remote_changes(
    runs: dict[Setting, Run], own_party: int, own_setting: int
) -> list[Witness]:
    keys = (
        ((own_setting, 0), (own_setting, 1))
        if own_party == 0
        else ((0, own_setting), (1, own_setting))
    )
    lo, hi = (runs[key].outcomes for key in keys)
    return [
        (ticket, lo[ticket][own_party], hi[ticket][own_party])
        for ticket in TICKETS
        if lo[ticket][own_party] != hi[ticket][own_party]
    ]


def check_microscopic(runs: dict[Setting, Run], order: Order) -> None:
    first, second = order
    name_first, name_second = "AB"[first], "AB"[second]
    first_changes = [len(remote_changes(runs, first, s)) for s in range(2)]
    need(first_changes == [0, 0], "first outcome changed under later setting")
    print(f"{name_first}-first, {name_first}: remote-setting flips {first_changes}/20")
    changes = [remote_changes(runs, second, s) for s in range(2)]
    need(any(changes), "no fixed-seed witness of later-side remote-setting dependence")
    for s, witnesses in enumerate(changes):
        example = (
            f"; example (seeds, old bit, new bit): {witnesses[0]}" if witnesses else ""
        )
        print(
            f"{name_first}-first, {name_second}{s}: {len(witnesses)}/20 flips "
            f"when {name_first}'s setting changes 0→1{example}"
        )


def check_experiment(entangled: bool) -> None:
    prep = prepare(entangled)
    ab = {s: run_setting(prep, s, A_FIRST) for s in SETTINGS}
    ba = {s: run_setting(prep, s, B_FIRST) for s in SETTINGS}
    label = "joint CNOT preparation" if entangled else "product (no CNOT) control"
    print(f"{label} (exit counts in 00, 01, 10, 11 order):")
    rows = []
    for s in SETTINGS:
        need(
            ab[s].rail_counts == ba[s].rail_counts, "order changed ensemble rail counts"
        )
        summary = summarise(ab[s])
        rows.append(summary)
        e, a0, b0 = summary
        print(f"  {s}: counts {raw_counts(ab[s])}; E={e}, P(A=0)={a0}, P(B=0)={b0}")

    e00, e01, e10, e11 = (row[0] for row in rows)
    chsh = e00 + e01 + e10 - e11
    print(f"  CHSH={chsh}; both orders match; all 20 trials per setting read out")
    if entangled:
        need(
            (e00, e01, e10, e11)
            == (Fraction(3, 5), Fraction(3, 5), Fraction(4, 5), Fraction(-4, 5)),
            "unexpected routed correlations",
        )
        need(chsh == Fraction(14, 5), "unexpected CHSH value")
        need(
            all(a0 == b0 == Fraction(1, 2) for _, a0, b0 in rows),
            "unbalanced marginals",
        )
        check_microscopic(ab, A_FIRST)
        check_microscopic(ba, B_FIRST)
    else:
        need(abs(chsh) <= 2, "product control exceeded the CHSH bound")
        for s in SETTINGS:
            _, pa, pb = summarise(ab[s])
            n00, *_ = raw_counts(ab[s])
            need(
                Fraction(n00, len(TICKETS)) == pa * pb, "product control did not factor"
            )


def main() -> None:
    check_experiment(entangled=True)
    check_experiment(entangled=False)


if __name__ == "__main__":
    main()
