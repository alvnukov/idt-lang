"""A three-mark path translates on a supplied (undirected) cycle square.

For n >= 5 give vertex j the four neighbors j ± 1, j ± 2 mod n.
Prepare W_i with links (i-2,i), (i,i-1), (i-1,i+1). Only i and i-1
have two marked ports. At i, in order (-2,-1,+1,+2), external scores
are (0,1,1,0) and the first two ports are marked. Selector bit 16
therefore complements the entire star, giving W_(i+1). Reflection about
the central link exchanges its endpoints and gives the reverse offer.
This local calculation applies at every i; the finite checks below use
the existing raw kernel, *without* restricting which centers it can offer.

The distinct W_i are identifiable by their marked-degree-two core edges.
In this sector the raw event graph is C_n. Its two alternatives do not
complete a commuting square. Reflection fixes the entire input while
exchanging the alternatives, obstructing a deterministic equivariant
heading from that input. With the *added* non-undo law, a supplied incoming
event selects the other offer, hence iterates in either direction. This
uses memory, not a clock derived from incidence. More generally, whenever
a reversible single event s -> t is the unique offer at s and the offer
at t is unique too, its inverse forces t -> s: persistent uniqueness can
give period at most two (including a self-loop if allowed).

Supplied incidence, marked preparation, and event-count distance are
not a derivation of physical time, dimension, particles or quantum laws.
Run: python3 -m scripts.probe_three_link_translation
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from itertools import combinations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_facilitated_forest_signal import Incidence, distances, edge, need
from scripts.probe_localized_shell_packets import RawShell

SELECTOR = 16
ORDERS = (5, 6, 7, 8, 11, 16, 31)


def cycle_square(n: int) -> Incidence:
    if n < 5:
        raise ValueError("four distinct neighbors require n >= 5")
    return Incidence.from_edges(
        n, ((i, (i + d) % n) for i in range(n) for d in (1, 2)), 4
    )


def packet(g: Incidence, i: int) -> int:
    n = len(g.stars)
    return sum(
        g.edge_bits[edge((i + a) % n, (i + b) % n)]
        for a, b in ((-2, 0), (0, -1), (-1, 1))
    )


def support_core(g: Incidence, state: int) -> tuple[set[int], set[int]]:
    """A raw incidence readout; neither the index i nor cyclic order is an input."""
    degrees = [(state & star).bit_count() for star in g.stars]
    return (
        {v for v, d in enumerate(degrees) if d},
        {v for v, d in enumerate(degrees) if d == 2},
    )


def nonundo(offers: dict[int, int], last_center: int) -> tuple[int, int]:
    """Extra selected law for this sector; undefined on ambiguous or dead inputs."""
    if len(offers) != 2 or last_center not in offers:
        raise ValueError("expected the inverse and exactly one other enabled event")
    return next(
        (center, state) for center, state in offers.items() if center != last_center
    )


@dataclass(frozen=True)
class Sector:
    n: int
    raw_states: int
    directed_events: int
    event_diameter: int
    core_separations: tuple[int, ...]
    oriented_periods: tuple[int, int]
    reflection_swaps_offers: bool


def check_sector(n: int) -> Sector:
    g = cycle_square(n)
    states = tuple(packet(g, i) for i in range(n))
    rows = RawShell(g).orbit(states[0], SELECTOR)  # unrestricted raw BFS
    need(len(set(states)) == n and set(rows) == set(states), "wrong raw orbit")
    centers0 = support_core(g, states[0])[1]
    base_distances = [distances(dict(enumerate(g.neighbors)), v) for v in centers0]
    separations = set()
    for i, state in enumerate(states):
        left, right = (i - 1) % n, i
        support, core = support_core(g, state)
        need(state.bit_count() == 3 and len(support) == 4, "packet not localized")
        need(core == {left, right} and set(rows[state]) == core, "wrong core")
        need(
            rows[state] == {left: states[left], right: states[(i + 1) % n]},
            "incorrect translated successor or extra offer",
        )
        # Distinct alternatives have no common successor except the raw start.
        a, b = rows[state].values()
        need(set(rows[a].values()) & set(rows[b].values()) == {state}, "square")
        separations.add(min(ds[v] for ds in base_distances for v in core))

        def reflect(v: int, axis: int = 2 * i - 1) -> int:
            return (axis - v) % n

        def image(links: int) -> int:
            return sum(
                g.edge_bits[edge(reflect(u), reflect(v))]
                for (u, v), bit in g.edge_bits.items()
                if links & bit
            )

        need(
            {edge(reflect(u), reflect(v)) for u, v in g.edge_bits} == set(g.edge_bits)
            and image(state) == state
            and reflect(left) == right
            and image(rows[state][left]) == rows[state][right],
            "reflection did not exchange translated offers while fixing input",
        )
    event_distances = distances({s: row.values() for s, row in rows.items()}, states[0])
    need(
        all(event_distances[s] == min(i, n - i) for i, s in enumerate(states)),
        "event distances disagree with the orbit cycle",
    )
    periods = []
    # Both supplied incoming edges. No indexed successor is used by nonundo.
    for last_center in rows[states[0]]:
        initial = (states[0], last_center)
        state, last = initial
        seen = set()
        while (state, last) not in seen:
            seen.add((state, last))
            last, state = nonundo(rows[state], last)
        need((state, last) == initial and len(seen) == n, "wrong lifted return")
        periods.append(len(seen))
    return Sector(
        n,
        len(rows),
        sum(map(len, rows.values())),
        max(event_distances.values()),
        tuple(sorted(separations)),
        (periods[0], periods[1]),
        True,
    )


def census(n: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Compare all 256 rules on every reached word, including partial-star alternatives."""
    g = cycle_square(n)
    shell = RawShell(g)
    orbit = shell.orbit(packet(g, 0), SELECTOR)
    matching, idle = [], []
    for flag in range(256):
        offers = {state: shell.offers(state, flag) for state in orbit}
        if offers == orbit:
            matching.append(flag)
        elif not any(offers.values()):
            idle.append(flag)
    return tuple(matching), tuple(idle)


def pair_control() -> dict:
    """One supplied two-packet fixture, not a postulate of exclusion or scattering."""
    n = 16
    g = cycle_square(n)
    shell = RawShell(g)
    packets = [packet(g, i) for i in range(n)]
    orbit = shell.orbit(packets[0] | packets[8], SELECTOR)
    # Independent comparison: unordered pairs of positions at cyclic gap >= 4.
    pair_words = {
        (i, j): packets[i] | packets[j]
        for i, j in combinations(range(n), 2)
        if min(j - i, n - j + i) >= 4
    }
    need(len(set(pair_words.values())) == len(pair_words), "ambiguous pair decoding")
    need(set(orbit) == set(pair_words.values()), "extra or missing raw pair words")
    for (i, j), state in pair_words.items():
        expected = {}
        for mover, rest in ((i, j), (j, i)):
            for step in (-1, 1):
                target = tuple(sorted(((mover + step) % n, rest)))
                if target in pair_words:
                    expected[(mover + min(0, step)) % n] = pair_words[target]
        need(orbit[state] == expected, "unexpected or missing two-packet offer")
    # Check the *reachable* contact word directly with both anonymous rules.
    contact = pair_words[0, 4]
    other = shell.offers(contact, SELECTOR | 2)
    need(
        other
        == {**orbit[contact], 0: packets[1] | packets[4], 3: packets[0] | packets[3]},
        "contact alias did not split as expected",
    )
    remaining_aliases = [
        f
        for f in range(256)
        if f & SELECTOR
        and all(shell.offers(state, f) == row for state, row in orbit.items())
    ]
    need(
        remaining_aliases == [f for f in range(256) if f & SELECTOR and not f & 2],
        "unexpected corpus split on pair sector",
    )
    return {
        "carrier": "C16^2; external preparation W0 union W8",
        "raw_states": len(orbit),
        "outdegree_counts": dict(Counter(map(len, orbit.values()))),
        "contact_word": "W0 union W4",
        "contact_offers_16": sorted(orbit[contact]),
        "contact_offers_18": sorted(other),
        "isolated_aliases_remaining_on_pair_rows": len(remaining_aliases),
    }


def experiment() -> dict:
    sectors = [asdict(check_sector(n)) for n in ORDERS]
    alias_counts = {}
    for n in (5, 11):
        matching, idle = census(n)
        need(matching == tuple(f for f in range(256) if f & SELECTOR), "alias census")
        need(idle == tuple(f for f in range(256) if not f & SELECTOR), "idle census")
        alias_counts[n] = {"same_raw_rows": len(matching), "idle": len(idle)}
    return {
        "sectors": sectors,
        "core_separations": "minimum supplied-carrier graph distance between degree-two cores",
        "corpus": alias_counts,
        "two_packet_control": pair_control(),
        "scope": "prepared three-link sector on supplied C_n^2; no intrinsic heading, clock, dimension or QM",
        "nonundo": "requires a supplied incoming event and an added last-center memory law",
        "reversible_uniqueness_wall": "if each step has only one offer, its inverse is the next offer; period at most two",
    }


if __name__ == "__main__":
    print(json.dumps(experiment(), indent=2))
