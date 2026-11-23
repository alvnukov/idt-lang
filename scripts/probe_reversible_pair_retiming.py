"""How much history must an exact reversible closed-window repacketizer retain?

H is a four-leg complementer on an unsigned pair with a mirrored fourth bit,
initially zero. In 2k active ticks the exposed H outputs alternate singleton,
double, starting with singleton. Two named wires b,c reach G; a third spectator
wire arrives independently. Restrict to exactly k arrivals on each named wire.
G's own mirror starts empty, so it needs double then singleton. Both mirrors
restore their phases. The problem is to preserve the three window totals,
produce a legal G input in the SAME 2k labeled ticks, and recover the entire
original arrival word, not just its marginals. No phase/timing side channel.

Among H's singleton ticks, each (b,c) is 00,10,01. At double ticks the
OMITTED pair is likewise 00,10,01. Both wire totals equal k iff the two
category-count triples agree. Thus there are M_k=sum(multinomial(k;i,j,l)^2)
over i+j+l=k overlap histories, and M_k*binom(2k,k) full input words. Legal
balanced G words have M_k choices, since once b,c are fixed G's third wire
is forced, with total k. Pigeonhole requires at least binom(2k,k) distinguishable
recoverable side states for injective recoding. This is a history-cardinality
bound, not the number of stored marks, irreversible erasure cost, or a claim
about retimers with dissipative, timing, environmental, or other side channels.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, product
from math import comb


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


def balanced(word):
    if (
        not word
        or len(word) % 2
        or any(len(z) != 3 or any(x not in (0, 1) for x in z) for z in word)
    ):
        raise ValueError("nonempty even window of three bits required")
    k = len(word) // 2
    if tuple(map(sum, zip(*word, strict=True))) != (k, k, k):
        raise ValueError("unbalanced external marginals")
    return k


def upstream(word):
    """Reconstruct actual H input word; its untouched wire is uniquely fixed."""
    balanced(word)
    drive = []
    t = 0
    for index, (b, c, _) in enumerate(word):
        w = 1 + index % 2 - b - c
        if w not in (0, 1):
            raise ValueError("overlap impossible in this H phase")
        x = (1 - w, 1 - b, 1 - c)
        need(sum(x) + t == 2 and (1 - x[1], 1 - x[2]) == (b, c), "invalid H replay")
        drive.append(x)
        t = 1 - t
    need(t == 0, "H mirror not restored")
    return tuple(drive)


def destination(word):
    balanced(word)
    if any(sum(z) + i % 2 != 2 for i, z in enumerate(word)):
        raise ValueError("not a legal G word for its fixed initial empty mirror")


def exchange_times(pairs):
    return tuple(pairs[i ^ 1] for i in range(len(pairs)))


def encode(word):
    upstream(word)
    pairs = exchange_times(tuple((b, c) for b, c, _ in word))
    g = tuple((b, c, 2 - i % 2 - b - c) for i, (b, c) in enumerate(pairs))
    destination(g)
    return g, tuple(v for _, _, v in word)


def decode(g, saved):
    destination(g)
    if (
        len(saved) != len(g)
        or any(v not in (0, 1) for v in saved)
        or sum(saved) * 2 != len(g)
    ):
        raise ValueError("invalid saved balanced spectator word")
    pairs = exchange_times(tuple((b, c) for b, c, _ in g))
    word = tuple((*bc, v) for bc, v in zip(pairs, saved, strict=True))
    upstream(word)
    return word


def inventories(k):
    if k < 1:
        raise ValueError("positive k")
    bits = tuple(product((0, 1), repeat=3))
    single = tuple(z for z in bits if sum(z) == 1)
    double = tuple(z for z in bits if sum(z) == 2)
    legal_g = set()
    overlaps = set()
    for blocks in product(tuple(product(double, single)), repeat=k):
        drive = tuple(z for block in blocks for z in block)
        # drive is directly a legal G input, or independently a legal H
        # input whose complementary physical outputs expose the overlap.
        if tuple(map(sum, zip(*drive, strict=True))) == (k,) * 3:
            legal_g.add(drive)
        bc = tuple((1 - z[1], 1 - z[2]) for z in drive)
        if tuple(map(sum, zip(*bc, strict=True))) == (k, k):
            overlaps.add(bc)
    signals = set()
    for ones in combinations(range(2 * k), k):
        slots = set(ones)
        signals.add(tuple(int(i in slots) for i in range(2 * k)))
    observed = set()
    fibers = Counter()
    for bc, signal in product(overlaps, signals):
        word = tuple((*p, s) for p, s in zip(bc, signal, strict=True))
        h = upstream(word)
        need(
            tuple((1 - x[1], 1 - x[2]) for x in h) == bc,
            "not the actual upstream output",
        )
        pair = encode(word)
        need(pair not in observed and decode(*pair) == word, "not reversible")
        observed.add(pair)
        fibers[pair[0]] += 1
    M = sum(
        (comb(k, i) * comb(k - i, j)) ** 2
        for i in range(k + 1)
        for j in range(k - i + 1)
    )
    C = comb(2 * k, k)
    need(
        len(overlaps) == len(legal_g) == M and len(signals) == C,
        "independent inventories",
    )
    need(
        observed == set(product(legal_g, signals)) and set(fibers.values()) == {C},
        "not a bijection onto all fixed-phase G words and side states",
    )
    return {
        "valid_balanced_G_words": M,
        "reachable_balanced_arrival_words": M * C,
        "sharp_side_states": C,
        "fixed_width_side_bits": (C - 1).bit_length(),
    }


def controls():
    g = ((1, 1, 0), (0, 0, 1))
    a, b = ((0, 0, 0), (1, 1, 1)), ((0, 0, 1), (1, 1, 0))
    need(
        encode(a) == (g, (0, 1)) and encode(b) == (g, (1, 0)),
        "discarded-history collision",
    )
    errors = 0
    for fn, args in (
        (encode, (g,)),
        (encode, (a[:1],)),
        (decode, (a, (0, 1))),
        (decode, (g, (1, 1))),
        (decode, (g, (2, -1))),
        (decode, (g, (1,))),
    ):
        try:
            fn(*args)
        except ValueError:
            errors += 1
    need(errors == 6, "missing validation or phase confusion")
    return {
        "same_legal_output": g,
        "distinct_saved_spectators": ((0, 1), (1, 0)),
        "rejected_malformed_or_wrong_phase": errors,
    }


def probe():
    return {
        "k": {k: inventories(k) for k in (1, 2, 3)},
        "controls": controls(),
        "scope": "Offline pairwise retiming of the shared wires and replacement of G's spectator by its forced bit, retaining the original spectator. No physical reversible router, zero-latency delivery or native spectator path preservation is inferred.",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
