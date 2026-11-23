"""Finite first-order binary gait on a supplied square of an undirected cycle.

This is a new directed copy/erase rule, not an execution of flag16. The carrier
and an oriented two-mark seed are supplied. The raw rule receives no last
event, direction, cycle positions, scheduled center, or update-phase variable.
Enumerating all offered local events describes a transition relation; it does
not furnish a physical clock or a scheduler for off-sector states.
"""

from __future__ import annotations

import json
from collections.abc import Hashable, Mapping
from dataclasses import dataclass
from random import Random

Vertex = Hashable
Link = frozenset[Vertex]
Marks = frozenset[Link]
Graph = Mapping[Vertex, frozenset[Vertex]]


def link(v: Vertex, w: Vertex) -> Link:
    return frozenset((v, w))


@dataclass(frozen=True)
class Offer:
    center: Vertex
    kind: str
    links: Marks

    def apply(self, marks: Marks) -> Marks:
        """Apply this locally offered copy or erase to the state that offered it."""
        return marks | self.links if self.kind == "copy" else marks - self.links


def star_offer(graph: Graph, marks: Marks, v: Vertex) -> Offer | None:
    """Inspect one star and its local witnesses; do not inspect other events."""
    def marked(at: Vertex) -> set[Vertex]:
        return {w for w in graph[at] if link(at, w) in marks}

    def ports(at: Vertex, common: int) -> set[Vertex]:
        return {w for w in graph[at] if len(graph[at] & graph[w]) == common}

    active = marked(v)
    if len(active) not in (1, 2):
        return None
    short = ports(v, 2)
    long = ports(v, 1)
    if len(short) != 2 or len(long) != 2 or short | long != graph[v]:
        return None
    marked_short = active & short
    if len(marked_short) != 1:
        return None
    z, = marked_short
    at_z = marked(z)
    if len(active) == 1 and len(at_z) == 2 and len(at_z & ports(z, 1)) == 1:
        # z -- v -- y are short. x -- z -- v are short, x -- v is long.
        y, = short - {z}
        other_short = ports(z, 2) - {v}
        if len(other_short) == 1:
            x, = other_short
            if x in long:
                return Offer(v, "copy", frozenset((link(v, y), link(v, x))))
    if len(active) == 2 and len(active & long) == 1 and len(at_z) == 3:
        return Offer(v, "erase", frozenset(link(v, w) for w in active))
    return None


def offers(graph: Graph, marks: Marks) -> tuple[Offer, ...]:
    return tuple(move for v in graph if (move := star_offer(graph, marks, v)) is not None)


# Everything below is preparation or external verification, not the raw rule.
def cycle_square(n: int) -> Graph:
    if n < 5:
        raise ValueError("this probe requires distinct +/-1 and +/-2 neighbors")
    return {v: frozenset((v+d) % n for d in (-2, -1, 1, 2)) for v in range(n)}


def seed(n: int, i: int, h: int) -> Marks:
    return frozenset((link(i % n, (i + 2*h) % n), link((i + 2*h) % n, (i + 3*h) % n)))


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def sector(n: int) -> dict:
    if n < 7:
        raise ValueError("the clean-sector oracle applies only at n >= 7")
    graph = cycle_square(n)
    labels = [f"anonymous-{i}" for i in range(n)]
    Random(743+n).shuffle(labels)
    renamed = {labels[v]: frozenset(labels[w] for w in graph[v]) for v in reversed(graph)}

    def rename(marks: Marks) -> Marks:
        return frozenset(frozenset(labels[v] for v in e) for e in marks)

    all_states = set()
    lengths = []
    sizes = set()
    for h in (-1, 1):
        origin = seed(n, 0, h)
        state = origin
        seen = set()
        while state not in seen:
            t = len(seen)
            need(t < 2*n, "no raw return by the expected period")
            seen.add(state)
            sizes.add(len(state))
            moves = offers(graph, state)
            need(len(moves) == 1, "not exactly one enabled star")
            move, = moves
            after = move.apply(state)
            # Independent coordinate oracle observes; it never chooses a star.
            i = (t//2 * h) % n
            ahead = seed(n, i+h, h)
            target = ahead if t % 2 else state | ahead
            center = (i + (2 if t % 2 else 3)*h) % n
            kind = "erase" if t % 2 else "copy"
            need((move.center, move.kind, after) == (center, kind, target),
                 "raw event disagrees with shift oracle")
            renamed_moves = offers(renamed, rename(state))
            need(renamed_moves == (Offer(labels[center], kind, rename(move.links)),),
                 "relabeling changed the set of offered events")
            state = after
        need(state == origin and len(seen) == 2*n, "not a clean 2n-cycle")
        need(all_states.isdisjoint(seen), "the two heading cycles overlap")
        all_states.update(seen)
        lengths.append(len(seen))
    need(sizes == {2, 4}, "mark-budget witness changed")
    return {"n": n, "distinct_states": len(all_states), "cycle_lengths": lengths,
            "marked_link_counts": sorted(sizes), "all_relabelled_offers_agree": True}


def report() -> dict:
    small = []
    for n, expected in ((5, 3), (6, 2)):
        graph = cycle_square(n)
        types = {len(graph[v] & graph[w]) for v in graph for w in graph[v]}
        need(types == {expected} and not offers(graph, seed(n, 0, 1)),
             "small-carrier geometry control changed")
        small.append({"n": n, "common_neighbor_counts": sorted(types),
                      "interpretation": "required local distinction unavailable"})
    graph = cycle_square(16)
    separated = seed(16, 0, 1) | seed(16, 8, 1)
    moves = offers(graph, separated)
    centers = sorted(m.center for m in moves)
    need(centers == [3, 11] and len({m.apply(separated) for m in moves}) == 2,
         "separated copies must have two distinct possible successors")
    need(not offers(graph, frozenset()), "empty state unexpectedly offers a move")
    return {
        "status": "finite_conditional_moving_sector",
        "supplied": ["cycle-square carrier", "directed local copy/erase rule", "chiral seed"],
        "clean_sectors": [sector(n) for n in (7, 8, 9, 10, 12, 16, 23, 32)],
        "small_carriers": small,
        "off_sector": {"n": 16, "empty_offers": 0, "separated_seed_offers": centers},
        "boundary": "Sector permutation only; no global scheduler, conserved mark count, "
                    "physical time, inferred dimension, or derivation of QM.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
