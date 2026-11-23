"""Finite conserved-bond gait on a supplied undirected cycle-square carrier.

Supplied: a local chase/escape rule with visibility of common neighbors, the
short adjacency between two marked bonds, and whether a destination is free.
Those incidence tests need more visibility than four anonymous incident bits.
No direction, last center, object ID, traveling phase, clock, or tie-breaker
enters the event kernel. Two elementary bonds persist by type; the changed
bond pivots at one common endpoint. This is not the separate copy/erase law.

Run: python3 -m scripts.probe_conserved_bond_gait
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import combinations
from math import gcd
from random import Random

if __package__:
    from .probe_binary_shape_gait import (
        Graph,
        Link,
        Marks,
        Vertex,
        cycle_square,
        link,
        need,
    )
else:
    from probe_binary_shape_gait import (
        Graph,
        Link,
        Marks,
        Vertex,
        cycle_square,
        link,
        need,
    )


@dataclass(frozen=True)
class Move:
    center: Vertex
    old: Link
    new: Link

    def apply(self, marks: Marks) -> Marks:
        return (marks - {self.old}) | {self.new}


@dataclass(frozen=True)
class Ports:
    """Compile static, bounded incidence around each long bond, never a trajectory."""
    short_links: frozenset[Link]
    motifs: dict[Link, tuple[tuple[Link, Move], ...]]

    @classmethod
    def from_graph(cls, graph: Graph) -> Ports:
        if any(v in ws or any(w not in graph or v not in graph[w] for w in ws)
               for v, ws in graph.items()):
            raise ValueError("requires simple undirected incidence")
        short = {v: {w for w in ws if len(ws & graph[w]) == 2} for v, ws in graph.items()}
        long = {v: {w for w in ws if len(ws & graph[w]) == 1} for v, ws in graph.items()}
        if any(len(short[v]) != 2 or len(long[v]) != 2 or len(ws) != 4
               for v, ws in graph.items()):
            raise ValueError("requires two short and two long incidence-defined ports")
        short_links = frozenset(link(v, w) for v in graph for w in short[v])
        long_links = frozenset(link(v, w) for v in graph for w in long[v])
        motifs = {}
        for bond in long_links:
            a, b = bond
            midpoint, = graph[a] & graph[b]
            # Every possible partner either touches this bond or touches one
            # of its short neighbors. Distant edges cannot affect these offers.
            region = bond | short[a] | short[b]
            candidates = {link(v, w) for v in region for w in short[v]}
            row = []
            for s in candidates:
                shared = s & bond
                if shared:
                    z, = shared
                    t, = s - {z}
                    pivot = z if t == midpoint else t
                    dest, = short[pivot] - s
                    move = Move(pivot, s, link(pivot, dest))
                else:
                    near = [v for v in bond if short[v] & s]
                    if len(near) != 1:
                        continue
                    pivot, = near
                    dest, = long[pivot] - bond
                    move = Move(pivot, bond, link(pivot, dest))
                row.append((s, move))
            motifs[bond] = tuple(row)
        return cls(short_links, motifs)


def offers(ports: Ports, marks: Marks) -> frozenset[Move]:
    """All distinct events, including distinct outcomes at the same center."""
    return frozenset(move for bond in marks for s, move in ports.motifs.get(bond, ())
                     if s in marks and move.new not in marks)


# Coordinates enter only in fixture preparation and validation, below.
def fixture(n: int, i: int, h: int) -> tuple[Marks, Marks, Marks]:
    def edge(a: int, b: int) -> Link:
        return link((i+h*a) % n, (i+h*b) % n)
    return (frozenset((edge(0, 2), edge(2, 3))), frozenset((edge(0, 2), edge(3, 4))),
            frozenset((edge(2, 4), edge(3, 4))))


def sector(n: int) -> dict:
    graph = cycle_square(n)
    ports = Ports.from_graph(graph)
    names = [f"alias-{i}" for i in range(n)]
    Random(1973+n).shuffle(names)
    renamed = Ports.from_graph({names[v]: frozenset(names[w] for w in graph[v])
                                for v in reversed(graph)})
    def rename(e: Link) -> Link:
        return frozenset(names[v] for v in e)

    # Exhaust the entire two-bond shell, *including* all same-type pairs.
    edges = ports.short_links | ports.motifs.keys()
    transitions = {}
    idle = 0
    for pair in combinations(edges, 2):
        marks = frozenset(pair)
        moves = offers(ports, marks)
        if not moves:
            idle += 1
            continue
        need(len(moves) == 1, "ambiguous event in the two-bond shell")
        move, = moves
        target = move.apply(marks)
        need(len(target) == 2 and len(target & ports.short_links) == len(marks & ports.short_links),
             "type-resolved bond counts changed")
        transitions[marks] = (move.center, target)
        need(offers(renamed, frozenset(map(rename, marks))) ==
             {Move(names[move.center], rename(move.old), rename(move.new))},
             "arbitrary relabeling changed an active offer")
    expected = {}
    for i in range(n):
        for h in (-1, 1):
            a, b, c = fixture(n, i, h)
            expected[a] = ((i+3*h) % n, b)
            expected[b] = ((i+2*h) % n, c)
            expected[c] = ((i+4*h) % n, fixture(n, i+2*h, h)[0])
    need(len(expected) == 6*n and transitions == expected,
         "raw active shell does not equal the independent phase/pivot oracle")
    remaining = set(transitions)
    lengths = []
    while remaining:
        start = next(iter(remaining))
        state = start
        count = 0
        while state in remaining:
            remaining.remove(state)
            count += 1
            state = transitions[state][1]
        need(state == start, "active shell is not a disjoint cycle union")
        lengths.append(count)
    need(lengths == [3*n//gcd(n, 2)] * (2*gcd(n, 2)), "cycle structure changed")
    return {"n": n, "active": len(transitions), "idle": idle, "cycle_lengths": sorted(lengths)}


def multi_controls() -> dict:
    n = 16
    ports = Ports.from_graph(cycle_square(n))
    a = fixture(n, 0, 1)[0]
    short_move = Move(3, link(2, 3), link(3, 4))
    examples = (
        ("separated", fixture(n, 8, 1)[0], {short_move, Move(11, link(10, 11), link(11, 12))}),
        ("nearby", fixture(n, 4, 1)[0], {short_move, Move(7, link(6, 7), link(7, 8)),
                                         Move(4, link(4, 6), link(2, 4))}),
        ("same_center", fixture(n, 1, 1)[1], {short_move, Move(3, link(1, 3), link(3, 5))}),
    )
    output = {}
    for name, other, expected in examples:
        state = a | other
        moves = offers(ports, state)
        need(moves == expected and len({m.apply(state) for m in moves}) == len(expected),
             f"{name}: incorrect events or conflated outcomes")
        need(all(len(m.apply(state)) == len(state) and
                 len(m.apply(state) & ports.short_links) == len(state & ports.short_links)
                 for m in moves), f"{name}: bond counts changed")
        output[name] = {"centers": sorted(m.center for m in moves), "successors": len(moves)}
    saturated = frozenset(ports.short_links | ports.motifs.keys())
    need(not offers(ports, saturated), "an occupied destination was offered")
    output["all_destinations_occupied"] = {"marked_bonds": len(saturated), "successors": 0}
    return output


def report() -> dict:
    return {
        "status": "finite_conserved_bond_sector",
        "supplied": ["cycle-square incidence", "local chase/escape rule", "oriented seed"],
        "clean_sectors": [sector(n) for n in (7, 8, 9, 10, 11, 12, 13, 16, 31, 64, 101)],
        "controls": multi_controls(),
        "boundary": "Each raw move preserves short and long bond counts. The two-bond "
                    "active sector is a permutation; inactive states offer no event. "
                    "Multiple seeds can interact or compete even at one center. "
                    "No global choice, time, recovered dimension, or QM follows.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
