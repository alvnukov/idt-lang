"""Whole tickets for unshifted unsigned counts, and a two-collision preparation wall.

An edge packet contains one unsigned mark on each of two distinct legs.
Two ordered packet addresses p,q carry one ticket per common leg. After
complementing both edges, the number of common legs is unchanged. A ticket
therefore travels to exactly one output without postselection, replacement
of a preparation, population doubling or extra random seeds. The law is on
RAW counts n_i^2, not on deviations (n_i-B)^2. It requires a supplied
uniform initial ticket for a probability interpretation. A single port
with no background cannot feed two overlapping splitters, even if its
common signal scale and initial phase were free.
"""

from __future__ import annotations

import sys
from collections import Counter
from collections.abc import Iterable
from fractions import Fraction as F
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_complement_collision_mixer import (
    EDGES,
    Counts,
    Edge,
    collide,
    counts,
    output,
    pairing,
)

Ticket = tuple[int, int, int]


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def tickets(packet: tuple[Edge, ...]) -> set[Ticket]:
    if any(len(set(e)) != 2 or set(e) - set(range(4)) for e in packet):
        raise ValueError("each packet needs two distinct leg addresses")
    return {
        (i, j, k)
        for i, j in product(range(len(packet)), repeat=2)
        for k in set(packet[i]) & set(packet[j])
    }


def turned(packet: tuple[Edge, ...]) -> tuple[Edge, ...]:
    out: list[Edge] = []
    for edge in packet:
        u, v = collide(*edge)
        i, j = (u - 1) % 4, (v - 1) % 4
        out.append((min(i, j), max(i, j)))
    return tuple(out)


def route(
    packet: tuple[Edge, ...], ticket: Ticket, *, reverse_tie: bool = False
) -> Ticket:
    p, q, k = ticket
    if not 0 <= p < len(packet) or not 0 <= q < len(packet):
        raise ValueError("invalid address")
    left, right = set(packet[p]), set(packet[q])
    source = sorted(left & right)
    dest = sorted(set(range(4)) - (left | right), reverse=reverse_tie)
    if k not in source or len(source) != len(dest):
        raise ValueError("invalid ticket or non-edge packet")
    return p, q, (dest[source.index(k)] - 1) % 4


def histogram(items: Iterable[Ticket]) -> Counts:
    c = Counter(k for _, _, k in items)
    return c[0], c[1], c[2], c[3]


def verify_packets() -> tuple[int, int]:
    number = moved = 0
    for k in range(5):
        for packet in combinations_with_replacement(EDGES, k):
            start = tickets(packet)
            dest = turned(packet)
            require(counts(dest) == output(packet), "component count")
            true_end = tickets(dest)
            for tie in (False, True):
                image = {route(packet, t, reverse_tie=tie) for t in start}
                require(
                    image == true_end and len(image) == len(start),
                    "whole-ticket bijection",
                )
                require(
                    tuple(n * n for n in counts(dest)) == histogram(image), "raw square"
                )
            moved += sum(
                route(packet, t) != route(packet, t, reverse_tie=True) for t in start
            )
            number += 1
    return number, moved


def zero_background(m: int) -> tuple[Counts, Counts]:
    if m <= 0:
        raise ValueError("nonempty source")
    # Single input port occupies legs 0/1, second port blank. Unlike-pair
    # completion requires each nonzero leg count to equal half the total.
    n = (m, m, 0, 0)
    after = output(pairing(n))
    require(after == (0, m, m, 0), "outgoing phases")
    attempted = (after[2], after[3], 0, 0)
    require(
        2 * max(attempted) > sum(attempted), "second junction would have no unlike pair"
    )
    return after, attempted


def controls() -> None:
    for l, r in product(range(11), repeat=2):
        if l + r:
            require((2 * max(l, r) <= l + r) == (l == r), "initial phase condition")
    for m in range(1, 11):
        zero_background(m)
    # No deterministic leg-level complement tie is equivariant under
    # complete leg relabeling. A transposition of the two unused legs
    # fixes each input leg yet exchanges both possible images.
    for target in (2, 3):
        require(
            any(
                p[0] == 0 and p[1] == 1 and p[target] != target
                for p in permutations(range(4))
            ),
            "missing tie stabilizer",
        )
    n = (5, 3, 4, 4)
    raw = tuple(F(v * v, sum(x * x for x in n)) for v in n)
    centered = tuple(F((v - 4) ** 2, 2) for v in n)
    require(
        sum(raw) == sum(centered) == 1
        and all(raw[i] > 0 == centered[i] for i in (2, 3)),
        "physical background versus signed deviations",
    )
    # Quadratic tickets are not forced by complement alone: single actual
    # marks can also be transported by an arbitrary per-edge bijection,
    # with unchanged TOTAL population but a linear output histogram.
    require(tuple(F(v, sum(n)) for v in n) != raw, "linear mark detector")


def main() -> None:
    number, moved = verify_packets()
    controls()
    print(
        f"All-ticket transport on {number} unsigned edge packet multisets: raw squared counts, no extra seed, no lost tickets; reversing the unresolved endpoint ties changes {moved} individual routes."
    )
    print(
        "Zero background: any admissible nonempty single-port input is (m,m,0,0) and splits into (0,m,m,0); supplying its second port to a fresh blank junction cannot make even one unlike pair."
    )
    print(
        "Raw-square tickets are NOT centered-square clicks on a positive background; the same collision also admits a single-mark detector. An extra readout or correlation resource is required."
    )


if __name__ == "__main__":
    main()
