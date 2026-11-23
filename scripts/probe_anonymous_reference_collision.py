"""A four-packet relational encounter, its additive laws, and a composition wall.

Work on multisets of even five-germ records with a supplied 3+2 partition.
There is NO distinguished zero packet, spatial embedding, firing schedule,
noise law or spontaneous preparation here. C uses only multiplicities and
XOR differences. From (r,r,r,r^d) for mixed two-bit d, keep one r at rest
and hop the remaining three via d's large port. Which label stayed is not
determined and is not needed for multisets. Reverse at the 2+1+1 endpoint
by distinguishing its two singleton differences from the double by weight.

For I_f=sum_{i<j} f(x_i XOR x_j), f is an arbitrary function of the FULL
difference record, not just its Hamming weight. A and B below are optional
extra supplied channels: on a closed pair swap two same-block bits of one
record relative to a held reference; on a closed triple hold one reference
and exchange selected columns of the other two when parity allows. These
have selected input roles, unlike anonymous C. An extension which applies A
inside larger tuples is tested separately: spectators are not silently
discarded. Neither existence of a kernel nor an after-the-fact match to a
known ballot constitutes charge dynamics or a first-principles derivation.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_blind_collision_charge import (
    INDEX,
    LARGE,
    PAIRS,
    SMALL,
    STATES,
    check_span,
    difference,
    exchange,
    kernel,
    need,
    occ,
    primitive,
    relabel,
    shuffle,
)

QUARTETS = tuple(combinations_with_replacement(STATES, 4))
ONES = (1,) * 16


def canon(xs):
    return tuple(sorted(xs))


def step(xs, held_block=LARGE):
    """Raw reversible rule (or idle); a small-held alternative is also executable."""
    counts = Counter(xs)
    sizes = sorted(counts.values())
    if sizes == [1, 3]:
        r, = (x for x, n in counts.items() if n == 3)
        v, = (x for x in counts if x != r)
        d = v ^ r
        if occ(d) == (1, 1):
            h, = (j for j in held_block if d & (1 << j))
            g = 31 ^ (1 << h)
            return canon((r, r ^ g, r ^ g, v ^ g))
    elif sizes == [1, 1, 2]:
        y, = (x for x, n in counts.items() if n == 2)
        singles = sorted((x for x in counts if x != y), key=lambda x: (x ^ y).bit_count())
        v, r = singles
        d, g = y ^ v, y ^ r
        if occ(d) == (1, 1):
            h, = (j for j in held_block if d & (1 << j))
            if g == (31 ^ (1 << h)):
                return canon((r, r, r, r ^ d))
    return canon(xs)


def diffs(xs):
    return tuple(a ^ b for a, b in combinations(xs, 2))


def pair_row(src, dst):
    return difference(diffs(src), diffs(dst))


def field_sum(xs, field):
    return sum(field[INDEX[x]] for x in diffs(xs))


def census(held_block):
    moves = {x: step(x, held_block) for x in QUARTETS}
    need(all(moves[y] == x for x, y in moves.items()), "multiset involution failed")
    support = {x: y for x, y in moves.items() if x != y}
    need(len(moves) == 3876 and len(support) == 192, "quartet census")
    for x, y in support.items():
        for p in set(permutations(x)):
            need(step(p, held_block) == y, "slot-order leakage")
        for shift in STATES:
            need(moves[canon(v ^ shift for v in x)] == canon(v ^ shift for v in y), "absolute origin leakage")
        for a, b in product(permutations(LARGE), permutations(SMALL)):
            image = a + b
            need(moves[canon(relabel(v, image) for v in x)] == canon(relabel(v, image) for v in y),
                 "within-block names leak")
    # On the fixed complement, covariance follows from support bijectivity.
    return {x: y for x, y in support.items() if 3 in Counter(x).values()}


def relative_layers():
    a, b, unary_a, unary_b, embedded_a, embedded_b = (set() for _ in range(6))
    for x, (i, j) in product(STATES, PAIRS):
        v = shuffle(x, i, j)
        if x != v:
            a.add(pair_row((0, x), (0, v)))
            for root in STATES:
                unary_a.add(difference((root ^ x,), (root ^ v,)))
            # Translation covariance lets the held reference be encoded as
            # zero when constructing difference rows; neither A nor B tests
            # absolute zero. Include every possible pair of spectators.
            for z, w in combinations_with_replacement(STATES, 2):
                embedded_a.add(pair_row((0, x, z, w), (0, v, z, w)))
    for (x, y), (i, j) in product(combinations_with_replacement(STATES, 2), PAIRS):
        v, w = exchange((x, y), i, j)
        if canon((v, w)) != (x, y):
            b.add(pair_row((0, x, y), (0, v, w)))
            unary_b.add(difference((x, y), (v, w)))
            for z in STATES:
                embedded_b.add(pair_row((0, x, y, z), (0, v, w, z)))
    return a, b, unary_a | unary_b, embedded_a | embedded_b


def nonconstant_field(rows):
    basis = kernel(rows | {(1,) + (0,) * 15})
    need(len(basis) == 1, "expected only one line modulo constants")
    field = primitive(basis[0])
    return field if field[INDEX[24]] > 0 else tuple(-v for v in field)


def probe():
    moves, alternative = map(census, (LARGE, SMALL))
    c = {pair_row(x, y) for x, y in moves.items()}
    small_c = {pair_row(x, y) for x, y in alternative.items()}
    unary_c = {difference(x, y) for x, y in moves.items()}
    fifth = {pair_row((*x, z), (*y, z)) for x, y in moves.items() for z in STATES}
    a, b, unary_ab, embedded = relative_layers()
    ws = tuple(occ(x)[1] for x in STATES)
    cs = tuple(occ(x)[0] for x in STATES)
    parity = tuple(w % 2 for w in ws)
    # Restricting f itself to be invariant under the supplied block
    # permutations is weaker than imposing the two closed-arity channels.
    symmetry = {difference((x,), (shuffle(x, i, j),)) for x, (i, j) in product(STATES, PAIRS)}
    need(len(kernel(symmetry)) == 6 and len(kernel(c | symmetry)) == 5, "block-anonymous field space")
    # For any real difference-table f, the six independent C equations
    # solve for its six distinct mixed weight-two entries; all other ten
    # are free. Check each equation by constructing its actual row.
    explicit_rows = set()
    for h, s in product(LARGE, SMALL):
        d, g = (1 << h) ^ (1 << s), 31 ^ (1 << h)
        explicit_rows.add(difference((0, 0, d), (g, g, d ^ g)))
    need(c == explicit_rows and len(c) == 6 and len(kernel(c)) == 10, "raw C equations")
    check_span(a | b, [ONES, cs, ws])
    unique = nonconstant_field(a | b | c)
    alternative_field = nonconstant_field(a | b | small_c)
    check_span(a | b | c, [ONES, unique])
    check_span(a | b | small_c, [ONES, alternative_field])
    # Only now compare the solved fields with the externally known ballot.
    q = tuple(3*w - 2*l for l, w in zip(cs, ws, strict=True))
    ballot = tuple(sum((int(i in SMALL) - int(j in SMALL)) * (((x >> i) & 1) - ((x >> j) & 1))
                       for i, j in PAIRS) for x in STATES)
    need(unique == q == ballot and
         tuple(2*v for v in alternative_field) == tuple(7*w - 3*l for l, w in zip(cs, ws, strict=True)),
         "post-solution slope comparison")
    check_span(c | fifth, [ONES, parity])
    check_span(a | b | c | fifth, [ONES])
    check_span(unary_c, [ONES, parity])
    check_span(unary_c | unary_ab, [ONES])
    check_span(c | embedded, [ONES])

    x = (0, 0, 0, 9)
    y = moves[x]
    need(y == (0, 23, 30, 30) and alternative[x] == (0, 23, 23, 30), "large/small alternatives")
    z = 3
    q4 = [field_sum(t, q) for t in (x, y)]
    q5 = [field_sum((*t, z), q) for t in (x, y)]
    need(q4 == [3, 3] and q5 == [-8, 4], "spectator counterexample")
    # With no active-quartet association, the same five-packet input may
    # have two distinct legal nonidle endpoints. No conflict scheduler is
    # smuggled into the spectator control.
    unbound = (0, 0, 0, 9, 10)
    exits = {canon((*step(unbound[:i] + unbound[i+1:]), spectator)) for i, spectator in enumerate(unbound)}
    exits.discard(unbound)
    need(len(exits) == 2, "undesignated quartet is not a single five-body command")
    # Concrete A embedding: even valid closed-pair moves do not imply
    # preservation of all pairwise differences to uncontrolled spectators.
    xa = (0, 9, 3, 3)
    ya = (0, shuffle(9, 0, 2), 3, 3)
    a2 = [field_sum(t[:2], q) for t in (xa, ya)]
    a4 = [field_sum(t, q) for t in (xa, ya)]
    need(a2[0] == a2[1] and a4[0] != a4[1], "A spectator countercontrol")
    # An all-equal cold preparation cannot trigger C. A controlled two-hop
    # operation on one of four co-located packets supplies the mixed seed.
    route = (0, 30, 30 ^ (31 ^ 8))
    need(route[-1] == 9 and step((0, 0, 0, 0)) == (0, 0, 0, 0), "preparation control")
    return {"scope": "exact_finite_multiset_dynamics_not_physical_charge", "unordered_quartets": len(QUARTETS),
            "swaps": len(moves), "idle": len(QUARTETS)-2*len(moves),
            "pair_law_dimensions": {"anonymous_C": 10, "C_with_block_symmetric_f": 5,
                                    "relative_closed_A_B": 3, "relative_closed_A_B_C": 2,
                                    "C_and_C_plus_any_spectator": 2, "closed_A_B_C_plus_any_spectator": 1,
                                    "quartet_embedded_A_B_plus_C": 1},
            "record_additive_law_dimensions": {"C": 2, "C_plus_relative_A_B": 1},
            "closed_pair_field_mod_constants": {"large": -2, "small": 3},
            "small_held_alternative_field": {"large_numerator": -3, "small_numerator": 7, "denominator": 2},
            "preparation_control_route": route, "quartet": [x, y], "inert_fifth": z,
            "internal_pair_sums": q4, "whole_five_pair_sums": q5,
            "unassociated_alternatives": {"preparation": unbound, "possible_moving_endpoints": sorted(exits)},
            "embedded_A_control": {"inputs_outputs": [xa, ya], "internal": a2, "whole": a4},
            "composition_boundary": "Using only internal pairs preserves the closed value by definition but requires "
            "a supplied association; unassociated cross-pair contributions change.",
            "label_boundary": "A slot-equivariant deterministic labeled lift cannot select one of three equal inputs: "
            "their stabilizer permutes all three, whereas the output has no triple. No such label is needed on multisets."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
