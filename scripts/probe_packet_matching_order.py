"""Finite raw packet-order fixture, not a quantum readout.

On each 2m-site ring, supply two alternating perfect matchings. A site
contains two physical bits; prepare one 11 packet among 00 sites. A supplied
context selects a matching, within which only the 11/00 edge is eligible for
H (complement all four bits). Empty edges are not attempted contacts. Words
run left to right. For cyclic bookkeeping, A sends an even index i to i+1
and B then sends i+1 to i+2; odd indices move by -2 under AB. Thus rotation
AB has order m; A and B conjugate it to its inverse. With A and B involutions,
the elementary commutator is Z=(AB)^2 and is central iff (AB)^4 is identity.
For disjoint components the order is the lcm of the component orders, and
nontrivial central Z requires order four, hence at least one eight-site ring.

Raw maps are unsigned permutations. On the octagon Z reverses the sign of
antipode-odd occupancy contrasts. Since AB is BA followed by Z, AB and BA
induce opposite maps on those contrasts. Any multiplicative scalar
character into an abelian group sends a commutator to one, by reordering its
four factors; the contrast is not a character on the raw one-packet states.
An optional graph spur (01 or 10) is attached to the prepared packet's site.
Distances are computed on the supplied combinatorial graph, not measured by
contact dynamics; no physical spatial embedding, named endpoint, or elapsed
time is needed. The topology, initial preparation, anchor, and context
choices are supplied; no randomness or quantum interference is derived.
"""

from __future__ import annotations

import json
from collections import deque
from itertools import product
from math import lcm

Edge = tuple[int, int]
Matching = tuple[Edge, ...]
Permutation = tuple[int, ...]
Contrast = tuple[int, ...]
MAX_WORD_LENGTH = 8
CONNECTED_M = (1, 2, 3, 4, 5, 6, 8)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def compose(first: Permutation, second: Permutation) -> Permutation:
    """Apply first, then second, as for words in the raw trace."""
    return tuple(second[i] for i in first)


def permutation_order(mapping: Permutation) -> int:
    visited: set[int] = set()
    order = 1
    for i in range(len(mapping)):
        end, cycle_length = i, 0
        while end not in visited:
            visited.add(end)
            cycle_length += 1
            end = mapping[end]
        if cycle_length:
            require(end == i, "mapping does not consist of cycles")
            order = lcm(order, cycle_length)
    return order


def packet_at(site: int) -> int:
    return 0b11 << (2 * site)


def ring_matching(components: tuple[int, ...], offset: int) -> Matching:
    edges: list[Edge] = []
    base = 0
    for m in components:
        n = 2 * m
        for i in range(0, n, 2):
            left, right = base + (i + offset) % n, base + (i + offset + 1) % n
            edges.append((min(left, right), max(left, right)))
        base += n
    return tuple(edges)


def eligible(mask: int, edge: Edge) -> bool:
    i, j = edge
    return (mask & (packet_at(i) | packet_at(j))).bit_count() == 2


def raw_step(mask: int, matching: Matching) -> int:
    candidates = tuple(edge for edge in matching if eligible(mask, edge))
    require(
        len(candidates) == 1, "selected context must have exactly one eligible contact"
    )
    i, j = candidates[0]
    return mask ^ (packet_at(i) | packet_at(j))


def raw_permutation(matching: Matching, size: int) -> Permutation:
    packet_positions = {packet_at(i): i for i in range(size)}
    mapping = tuple(
        packet_positions[raw_step(packet_at(i), matching)] for i in range(size)
    )
    require(
        set(mapping) == set(range(size)),
        "raw contacts did not give an unsigned permutation",
    )
    return mapping


def expected_ab(components: tuple[int, ...]) -> Permutation:
    result: list[int] = []
    base = 0
    for m in components:
        size = 2 * m
        result.extend(
            base + (i + (2 if i % 2 == 0 else -2)) % size for i in range(size)
        )
        base += size
    return tuple(result)


def central(mapping: Permutation, generators: tuple[Permutation, Permutation]) -> bool:
    return all(compose(mapping, g) == compose(g, mapping) for g in generators)


def check_words(
    matchings: tuple[Matching, Matching],
    generators: tuple[Permutation, Permutation],
    start: int,
    spur: tuple[Edge, int] | None = None,
) -> int:
    anchor_mask = 0 if spur is None else spur[1]
    pending = [(packet_at(start) | anchor_mask, start, 0)]
    visited_words = 0
    while pending:
        mask, site, length = pending.pop()
        require(
            mask == packet_at(site) | anchor_mask,
            "word changed packet or anchor support",
        )
        if spur is not None:
            require(not eligible(mask, spur[0]), "spur edge was eligible for H")
        visited_words += 1
        if length < MAX_WORD_LENGTH:
            for matching, expected in zip(matchings, generators, strict=True):
                pending.append((raw_step(mask, matching), expected[site], length + 1))
    require(
        visited_words == 2 ** (MAX_WORD_LENGTH + 1) - 1, "incomplete context word tree"
    )
    return visited_words


def graph_distance(edges: Matching, source: int, target: int) -> int:
    pending = deque([(source, 0)])
    seen = {source}
    while pending:
        site, distance = pending.popleft()
        if site == target:
            return distance
        for a, b in edges:
            neighbor = b if a == site else a if b == site else None
            if neighbor is not None and neighbor not in seen:
                seen.add(neighbor)
                pending.append((neighbor, distance + 1))
    raise ArithmeticError("missing graph distance")


def push(mapping: Permutation, occupancy: Contrast) -> Contrast:
    output = [0] * len(mapping)
    for site, count in enumerate(occupancy):
        output[mapping[site]] = count
    return tuple(output)


def differences(occupancy: Contrast) -> Contrast:
    half = len(occupancy) // 2
    return tuple(occupancy[i] - occupancy[i + half] for i in range(half))


def negative(vector: Contrast) -> Contrast:
    return tuple(-value for value in vector)


def inspect_octagon(
    matchings: tuple[Matching, Matching], generators: tuple[Permutation, Permutation]
) -> dict[str, object]:
    a, b = generators
    identity = tuple(range(8))
    ab, ba = compose(a, b), compose(b, a)
    abba, abab = compose(ab, ba), compose(ab, ab)
    abababab = compose(abab, abab)
    require(abba == abababab == identity, "echo did not restore all eight sites")
    require(
        abab == tuple((i + 4) % 8 for i in identity),
        "ABAB did not send every site to antipode",
    )

    def basis(site: int) -> Contrast:
        return tuple(int(i == site) for i in identity)

    z_negative = all(
        differences(push(abab, basis(i))) == negative(differences(basis(i)))
        for i in identity
    )
    ab_negative_ba = all(
        differences(push(ab, basis(i))) == negative(differences(push(ba, basis(i))))
        for i in identity
    )
    contrast_dimension = len({differences(basis(i)) for i in range(4)})
    require(
        z_negative and ab_negative_ba and contrast_dimension == 4,
        "antipode contrast failure",
    )
    scalar_checks = all(
        a_sign * b_sign * a_sign * b_sign == 1
        for a_sign, b_sign in product((-1, 1), repeat=2)
    )
    require(scalar_checks, "involutive scalar signs did not commute")

    distances = {"AB": 3, "BA": 3, "ABBA": 1, "ABAB": 5}
    preparations_checked = 0
    words = 0
    for start in identity:
        spur_edge = (start, len(identity))
        graph = (*matchings[0], *matchings[1], spur_edge)
        for state in (0b01, 0b10):
            words = check_words(
                matchings, generators, start, (spur_edge, state << (2 * len(identity)))
            )
            preparations_checked += 1
        endpoints = {
            "AB": ab[start],
            "BA": ba[start],
            "ABBA": abba[start],
            "ABAB": abab[start],
        }
        observed = {
            word: graph_distance(graph, len(identity), end)
            for word, end in endpoints.items()
        }
        require(
            observed == distances,
            "rooted-spur distance did not distinguish equal-length words",
        )
    return {
        "abab": abab,
        "abba": abba,
        "abababab": abababab,
        "contrast_dimension": contrast_dimension,
        "z_negates_contrast": z_negative,
        "ab_negates_ba_contrast": ab_negative_ba,
        "all_involutive_scalar_character_checks_trivial": scalar_checks,
        "rooted_spur": {
            "preparations_checked": preparations_checked,
            "words_per_preparation": words,
            "never_eligible": True,
            "distances": distances,
        },
    }


def inspect_components(
    components: tuple[int, ...],
) -> tuple[
    dict[str, int | bool], tuple[Matching, Matching], tuple[Permutation, Permutation]
]:
    size = 2 * sum(components)
    a_match, b_match = ring_matching(components, 0), ring_matching(components, 1)
    matchings = a_match, b_match
    a, b = raw_permutation(a_match, size), raw_permutation(b_match, size)
    generators = a, b
    identity = tuple(range(size))
    require(
        compose(a, a) == compose(b, b) == identity, "raw generators must be involutions"
    )
    ab, ba = compose(a, b), compose(b, a)
    require(
        ab == expected_ab(components), "raw AB did not follow the parity transport law"
    )
    require(compose(ab, ba) == identity, "BA is not the inverse of AB")
    order = permutation_order(ab)
    expected_order = lcm(*components)
    require(order == expected_order, "wrong connected or disconnected rotation order")
    z = compose(ab, ab)
    z_central = central(z, generators)
    z_nontrivial = z != identity
    require(z_central == (4 % order == 0), "central-square criterion")
    require(z_nontrivial == (2 % order != 0), "nontrivial-square criterion")
    words_per_site = 0
    for site in range(size):
        words_per_site = check_words(matchings, generators, site)
    return (
        {
            "initial_sites": size,
            "words_per_site": words_per_site,
            "ab_order": order,
            "expected_lcm": expected_order,
            "elementary_commutator_central": z_central,
            "elementary_commutator_nontrivial": z_nontrivial,
            "central_nontrivial_elementary_commutator": z_central and z_nontrivial,
        },
        matchings,
        generators,
    )


def small_compositions(total: int) -> tuple[tuple[int, ...], ...]:
    if total == 0:
        return ((),)
    return tuple(
        (head, *tail)
        for head in range(1, total + 1)
        for tail in small_compositions(total - head)
    )


def inspect_other_mechanisms(
    m6: tuple[Permutation, Permutation], m8: tuple[Permutation, Permutation]
) -> dict[str, bool]:
    rotation = compose(*m6)
    cube = compose(rotation, compose(rotation, rotation))
    m6_check = cube != tuple(range(12)) and central(cube, m6)

    # The 16-site ring admits period-8 occupancy profiles. These are a
    # linear restriction, not a second raw one-packet claim on this ring.
    ab, ba = compose(*m8), compose(m8[1], m8[0])
    m8_check = True
    for rep in range(8):
        profile = tuple(int(i % 8 == rep) for i in range(16))
        profiles = (push(ab, profile), push(ba, profile))
        for output in profiles:
            m8_check &= output[:8] == output[8:]
        m8_check &= differences(profiles[0][:8]) == negative(
            differences(profiles[1][:8])
        )
        m8_check &= any(differences(profiles[0][:8]))
    require(m6_check and m8_check, "higher-power or periodic-mode control failed")
    return {
        "m6_central_nontrivial_rotation_cubed": m6_check,
        "m8_periodic_contrast_has_ab_negates_ba": m8_check,
    }


def run_probe() -> dict[str, object]:
    cases = {m: inspect_components((m,)) for m in CONNECTED_M}
    require(
        cases[1][1][0] == cases[1][1][1], "shared-edge control uses two different edges"
    )
    connected = [{"m": m, **row} for m, (row, _, _) in cases.items()]
    require(
        [
            row["m"]
            for row in connected
            if row["central_nontrivial_elementary_commutator"]
        ]
        == [4],
        "connected controls did not isolate the octagon",
    )
    small = {
        parts
        for total in range(1, 4)
        for parts in small_compositions(total)
        if len(parts) > 1
    }
    other = {(2, 2), (2, 3), (1, 4), (2, 4), (4, 8)}
    disconnected = {
        parts: inspect_components(parts)[0] for parts in sorted(small | other)
    }
    smaller_hit = any(
        row["central_nontrivial_elementary_commutator"] and row["initial_sites"] < 8
        for row in (*disconnected.values(), *connected)
    )
    require(
        not smaller_hit, "found fewer than eight packet sites with nontrivial central Z"
    )

    return {
        "connected": connected,
        "octagon": inspect_octagon(cases[4][1], cases[4][2]),
        "disconnected": {
            "controls": [
                {"components_m": parts, **row} for parts, row in disconnected.items()
            ],
            "global_minimum_packet_sites": 8,
            "fewer_sites_hit": smaller_hit,
        },
        "other_mechanisms": inspect_other_mechanisms(cases[6][2], cases[8][2]),
    }


if __name__ == "__main__":
    print(json.dumps(run_probe(), indent=2, sort_keys=True))
