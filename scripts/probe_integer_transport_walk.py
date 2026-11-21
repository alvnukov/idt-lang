"""Finite transport on a supplied integer two-rail lattice.

Each site first mixes L/R by C = ((a, -b), (b, a)), then sends L left and R
right. The signed field is integer-valued; normalization per step is sqrt(h),
where h = a*a + b*b. In the complex convention R_complex = i*R_real, C is
((a, i*b), (i*b, a)); this walk cannot distinguish real from complex carriers.

The exact compressed walk and component recurrence are separate from the
explicit three-step replay. Replay uses occupied sites' actual signed clouds,
the existing cancellation router, and one uniform h-way seed at each step.
Each route uses its site's full cloud, not an independently moving point with
only a seed. Neither locality of the lattice rule nor the spectral check derives
spacetime, a continuum law, a physical mass scale, hbar, or observed data.

Run from the repository root: python3 -O -m scripts.probe_integer_transport_walk
"""

import sys
from collections import defaultdict
from fractions import Fraction
from math import atan2
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

Vector = tuple[int, int]
Field = dict[int, Vector]
Word = tuple[int, ...]
PathRecord = tuple[tuple[int, int], ...]  # (site, rail) observed at each layer

LEFT = 0
RIGHT = 1
SHIFT = (-1, 1)
ZERO: Vector = (0, 0)
LEFT_START: Field = {0: (1, 0)}
COMPRESSED_STEPS = 40
REPLAY_STEPS = 3


class Event(NamedTuple):
    site: int
    pair: Pair


class Replay(NamedTuple):
    rail_counts: tuple[Field, ...]
    paths: dict[Word, PathRecord]
    longest_cancel_route: int


def pack(values: dict[int, list[int]]) -> Field:
    return {x: (left, right) for x, (left, right) in values.items() if left or right}


def advance(field: Field, a: int, b: int) -> Field:
    """Signed coin plus one chiral shift, with no event tables."""
    nxt: dict[int, list[int]] = defaultdict(lambda: [0, 0])
    for x, (left, right) in field.items():
        nxt[x - 1][LEFT] = a * left - b * right
        nxt[x + 1][RIGHT] = b * left + a * right
    return pack(nxt)


def recurrence(older: Field, newer: Field, a: int, h: int) -> Field:
    """Second-order scalar lattice recurrence applied to both signed rails."""
    sites = set(older) | {x + dx for x in newer for dx in SHIFT}
    out: Field = {}
    for x in sites:
        pl, pr = newer.get(x - 1, ZERO)
        nl, nr = newer.get(x + 1, ZERO)
        ol, or_ = older.get(x, ZERO)
        left, right = a * (pl + nl) - h * ol, a * (pr + nr) - h * or_
        if left or right:
            out[x] = left, right
    return out


def readout(field: Field) -> Field:
    return {x: (left * left, right * right) for x, (left, right) in field.items()}


def coin(a: int, b: int) -> Matrix:
    return ((a, -b), (b, a))


def position_counts(rails: Field, t: int) -> tuple[int, ...]:
    return tuple(sum(rails.get(x, ZERO)) for x in range(-t, t + 1, 2))


def dephased(field: Field, a: int, b: int) -> Field:
    """Independent classical persistent-coin control; coins act on counts."""
    stay, turn = a * a, b * b
    nxt: dict[int, list[int]] = defaultdict(lambda: [0, 0])
    for x, (left, right) in field.items():
        nxt[x - 1][LEFT] += stay * left + turn * right
        nxt[x + 1][RIGHT] += turn * left + stay * right
    return pack(nxt)


def check_compressed(a: int, b: int) -> tuple[Field, ...]:
    h = a * a + b * b
    direct = [LEFT_START]
    site = [LEFT_START, {x: v for x, v in ((-1, (a, 0)), (1, (0, b))) if v != ZERO}]
    for t in range(COMPRESSED_STEPS + 1):
        if t:
            direct.append(advance(direct[-1], a, b))
        if t >= 2:
            site.append(recurrence(site[-2], site[-1], a, h))
        current = direct[t]
        need(current == site[t], f"component recurrence disagrees at t={t}")
        need(
            all(abs(x) <= t and (x - t) % 2 == 0 for x in current), "light cone/parity"
        )
        norm = sum(left * left + right * right for left, right in current.values())
        need(norm == h**t, f"wrong integer norm at t={t}")
        if t and a > 0 and b > 0:
            need(current[-t] == (a**t, 0), "leftmost support is not the chiral front")
            need(
                current[t] == (0, b * a ** (t - 1)),
                "rightmost support is not the front",
            )
    return tuple(direct)


def replay(a: int, b: int, *, reverse_matching: bool) -> Replay:
    gate = coin(a, b)
    h = a * a + b * b
    clouds: dict[int, Cloud] = {0: ((LEFT, 1),)}
    events: dict[Word, Event] = {(): Event(0, (0, 0))}
    paths: dict[Word, PathRecord] = {(): ((0, LEFT),)}
    rail_counts = [LEFT_START]
    longest = 0
    for t in range(1, REPLAY_STEPS + 1):
        # Construct each coin's cancellation map from its signed local cloud.
        routes: dict[int, dict[tuple[Pair, int], Pair]] = {}
        incoming: dict[int, list[tuple[int, int]]] = defaultdict(list)
        shift: dict[tuple[int, int], tuple[int, int]] = {}
        for x, cloud in sorted(clouds.items()):
            out, routes[x], gain, length = route_block(cloud, gate, reverse_matching)
            need(gain == h, "router and seed stock disagree")
            longest = max(longest, length)
            for idx, mark in enumerate(out):
                dest = x + SHIFT[mark[0]]
                shift[x, idx] = dest, len(incoming[dest])
                incoming[dest].append(mark)
        need(len(set(shift.values())) == len(shift), "shift merged live marks")
        clouds = {x: tuple(marks) for x, marks in incoming.items()}

        # Follow each existing pair for every next seed through the local
        # route and the index permutation; count only the actual exit events.
        next_events: dict[Word, Event] = {}
        next_paths: dict[Word, PathRecord] = {}
        exits: set[Event] = set()
        counts: dict[int, list[int]] = defaultdict(lambda: [0, 0])
        for word, (x, pair) in events.items():
            for seed in range(h):
                u, v = routes[x][pair, seed]
                dest, i = shift[x, u]
                other_dest, j = shift[x, v]
                need(dest == other_dest, "coin pair split between sites")
                rail = clouds[dest][i][0]
                need(rail == clouds[dest][j][0], "pair is not coincident on one rail")
                end = Event(dest, (i, j))
                need(end not in exits, "two seed prefixes routed to one exit")
                exits.add(end)
                new_word = (*word, seed)
                next_events[new_word] = end
                next_paths[new_word] = (*paths[word], (dest, rail))
                counts[dest][rail] += 1
        all_pairs = {
            Event(x, pair) for x, cloud in clouds.items() for pair in pairs(cloud)
        }
        need(exits == all_pairs, f"some surviving pairs were not replayed at t={t}")
        need(len(next_events) == len(next_paths) == h**t, "not all seed words replayed")
        events, paths = next_events, next_paths
        rail_counts.append(pack(counts))
    return Replay(tuple(rail_counts), paths, longest)


def check_spectrum(a: int, b: int) -> str:
    # Choose Fourier sign so a left shift multiplies by z^-1, z = exp(ik).
    # The unnormalized symbol entries are (coefficient, exponent) monomials.
    symbol = tuple(
        tuple((coefficient, power) for coefficient in row)
        for row, power in zip(coin(a, b), SHIFT, strict=True)
    )
    ((aa, p), (bb, q)), ((cc, r), (dd, s)) = symbol
    h = a * a + b * b
    need(p == -1 and s == 1 and aa == dd == a, "wrong Laurent trace")
    need(p + s == q + r == 0 and aa * dd - bb * cc == h, "wrong determinant")
    need(all(power % 2 for row in symbol for _, power in row), "missing π alias")
    # Dividing by sqrt(h) makes det = 1 and the trace 2*a*cos(k)/sqrt(h).
    # Thus cos(ω) = (a/sqrt(h))*cos(k). U(k+π) = -U(k), so the gap
    # from ω=0 at k=0 equals the gap from ω=π at k=π (principal branch).
    rho2 = Fraction(a * a, h)
    for cos2 in (Fraction(0), Fraction(1, 25), Fraction(9, 25), Fraction(1)):
        # Differentiate on a gapped branch. The nonnegative closed form
        # for rho²-v² proves the bound for every cos²(k) in [0, 1]; these
        # rational test points sanity-check both formulas and endpoints.
        denominator = 1 - rho2 * cos2
        v2 = rho2 * (1 - cos2) / denominator
        gap2 = rho2 * (1 - rho2) * cos2 / denominator
        need(0 <= v2 <= rho2 and rho2 - v2 == gap2, "group velocity bound")
        need((v2 == rho2) == (cos2 == 0), "wrong maximum group velocity")
    # The numerical gap is display only; atan2(b, a) is exact as an expression.
    return f"gap to 0/π={atan2(b, a):.6f} rad, max |v_g|=sqrt({rho2}), support speed=1"


def check_mixed_coin(
    a: int, b: int, expected: tuple[int, ...], expected_dephased: tuple[int, ...]
) -> None:
    direct = check_compressed(a, b)
    explicit = tuple(
        replay(a, b, reverse_matching=reverse) for reverse in (False, True)
    )
    h = a * a + b * b
    measured = explicit[0].rail_counts
    classical = LEFT_START
    for t, rails in enumerate(measured):
        need(
            all(run.rail_counts[t] == rails for run in explicit),
            "matching changes counts",
        )
        need(
            rails == readout(direct[t]), f"independent squared field disagrees at t={t}"
        )
        coherent_positions = position_counts(rails, t)
        classical_positions = position_counts(classical, t)
        need(
            sum(coherent_positions) == sum(classical_positions) == h**t,
            "wrong ticket mass",
        )
        if t < REPLAY_STEPS:
            need(rails == classical, "earlier-than-t=3 coherent/dephased separation")
            classical = dephased(classical, a, b)
        else:
            need(coherent_positions == expected, "incorrect t=3 coherent fixture")
            need(
                classical_positions == expected_dephased,
                "incorrect t=3 control fixture",
            )
    need(expected != expected_dephased, "control failed to separate")
    for run in explicit:
        need(run.longest_cancel_route > 0, "no replay used a cancellation route")
    standard, alternate = explicit
    changed = sum(
        path != alternate.paths[word] for word, path in standard.paths.items()
    )
    print(f"a,b={a},{b}; t=3 x=(-3,-1,1,3), common denominator={h**REPLAY_STEPS}")
    print(f"  routed={expected}; dephased={expected_dephased}; equal through t=2")
    print(f"  all {len(standard.paths)} seed histories replayed per matching")
    print(
        f"  histories whose (site, rail) traces changed under reverse matching: {changed}"
    )
    print(f"  {check_spectrum(a, b)}")


def check_degenerate_controls() -> None:
    for rail, dx in enumerate(SHIFT):
        initial = (1, 0) if rail == LEFT else (0, 1)
        orthogonal = (0, 1) if rail == LEFT else (-1, 0)
        straight: Field = {0: initial}
        swapped: Field = {0: initial}
        for t in range(1, COMPRESSED_STEPS + 1):
            straight = advance(straight, 1, 0)
            swapped = advance(swapped, 0, 1)
            need(straight == {dx * t: initial}, "pure shift is not chiral")
            phase = (-1) ** (t // 2)
            x, v = (-dx, orthogonal) if t % 2 else (0, initial)
            need(swapped == {x: (phase * v[0], phase * v[1])}, "signed swap return")
    check_compressed(1, 0)
    check_compressed(0, 1)
    print(
        "controls: pure chiral shift; signed swap returns in two steps with a minus sign"
    )


def main() -> None:
    check_mixed_coin(1, 1, (1, 5, 1, 1), (1, 3, 3, 1))
    check_mixed_coin(2, 1, (64, 32, 13, 16), (64, 24, 21, 16))
    check_degenerate_controls()
    print(
        f"signed recurrence, norm, parity and light cone checked through t={COMPRESSED_STEPS}"
    )
    print(
        "spectral facts concern this supplied lattice; low momentum alone is not a continuum limit"
    )


if __name__ == "__main__":
    main()
