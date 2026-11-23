"""Rule 54 as offered-link occupancy on an externally clocked even cycle.

Site i is the occupancy of edge (i, i+1) of a supplied cyclic carrier. The
supplied alternating perfect matchings update one parity at a time. The
result is the known staggered Rule 54, not an endogenous clock, a new rule,
or a claim about physical particles, spatial dimension or quantum dynamics.

Run: python3 -m scripts.probe_binary_cycle_solitons
"""

from __future__ import annotations

import json
from collections.abc import Iterable
from dataclasses import dataclass, field
from itertools import product
from typing import Literal

from scripts import probe_available_link_logic as original

Gate = Literal["OR", "XOR", "AND"]
EXHAUSTIVE_LENGTHS = tuple(range(4, 17, 2))
PRIMARY_NEAR_COLLISION = (
    (8, 9, 11, 12), (9, 10, 11), (10,), (10,), (9, 10, 11),
    (8, 9, 11, 12), (7, 8, 12, 13),
)
HELDOUT_NEAR_COLLISION = (
    (13, 14, 16, 17), (14, 15, 16), (15,), (15,), (14, 15, 16),
    (13, 14, 16, 17), (12, 13, 17, 18),
)


@dataclass(frozen=True)
class Cycle:
    """Bit-packed edge states with phase referring to the *next* matching."""

    n: int
    edges: tuple[tuple[int, int], ...] = field(init=False)
    witnesses: tuple[int, ...] = field(init=False)
    full: int = field(init=False)
    matching_masks: tuple[int, int] = field(init=False)

    def __post_init__(self) -> None:
        if self.n < 4 or self.n % 2:
            raise ValueError("cycle length must be even and at least 4")
        edges = tuple((i, (i + 1) % self.n) for i in range(self.n))
        even = sum(1 << i for i in range(0, self.n, 2))
        object.__setattr__(self, "edges", edges)
        object.__setattr__(self, "witnesses", original.witness_masks(edges))
        object.__setattr__(self, "full", (1 << self.n) - 1)
        object.__setattr__(self, "matching_masks", (even, even << 1))

    def sites(self, state: int) -> tuple[int, ...]:
        return tuple(i for i in range(self.n) if state & (1 << i))

    def mask(self, sites: Iterable[int]) -> int:
        return sum(1 << i for i in set(sites))

    def reflect(self, state: int, offset: int) -> int:
        return self.mask((offset - i) % self.n for i in self.sites(state))

    def neighbors(self, state: int) -> tuple[int, int]:
        return (
            ((state << 1) & self.full) | (state >> (self.n - 1)),
            (state >> 1) | ((state & 1) << (self.n - 1)),
        )

    def half_step(self, state: int, phase: int, gate: Gate = "OR") -> int:
        left, right = self.neighbors(state)
        if gate == "OR":
            trigger = left | right
        elif gate == "XOR":
            trigger = left ^ right
        elif gate == "AND":
            trigger = left & right
        else:
            raise ValueError(f"unknown witness gate: {gate}")
        return state ^ (self.matching_masks[phase] & trigger)

    def raw_offer(self, state: int, site: int) -> int:
        # Original offer_tables law without allocating a full table at n=30,46.
        return state ^ (1 << site) if state & self.witnesses[site] else state

    def raw_half_step(self, state: int, phase: int, omit: int | None = None) -> int:
        for site in range(phase, self.n, 2):
            if site != omit:
                state = self.raw_offer(state, site)
        return state

    def counts(self, state: int, phase: int) -> tuple[int, int]:
        """(N_R, N_L): oriented 11 bonds plus one of each per isolated 010."""
        left, right = self.neighbors(state)
        isolated = (state & ~(left | right)).bit_count()
        bonds = state & right
        return (
            (bonds & self.matching_masks[phase]).bit_count() + isolated,
            (bonds & self.matching_masks[phase ^ 1]).bit_count() + isolated,
        )


def local_cancellation() -> dict[str, int]:
    """Each passive site accounts for one bond of each orientation.

    For an occupied passive center b between updated a,c, the old right-bond
    weight is a and the new one is c'=1-c (left uses c and a'). The bond
    increment 1-a-c cancels the passive isolation increment a+c-1 for each
    species. A vacant passive center stays vacant and contributes neither.
    At any updated site, passive occupied neighbors exclude isolation before
    and after; without them the site is unchanged. This groups every term on
    any supplied even cycle; the probe checks the local binary cases.
    """
    for a, b, c in product((0, 1), repeat=3):
        new_a, new_c = a ^ b, c ^ b
        isolation_delta = b * ((1 - new_a) * (1 - new_c) - (1 - a) * (1 - c))
        bond_deltas = (b * (new_c - a), b * (new_a - c))
        original.require(isolation_delta == b * (a + c - 1), "passive isolation")
        original.require(bond_deltas == (b * (1 - a - c),) * 2, "passive bonds")
        original.require(all(d + isolation_delta == 0 for d in bond_deltas), "charge cancellation")

        new_b = b ^ (a | c)
        original.require(
            b * (1 - a) * (1 - c) == new_b * (1 - a) * (1 - c),
            "updated isolation",
        )
    return {"passive_triples": 8, "updated_isolation_triples": 8}


def exhaustive_cycle(n: int) -> dict[str, int]:
    cycle = Cycle(n)
    for site, mask in enumerate(cycle.witnesses):
        expected = (1 << ((site - 1) % n)) | (1 << ((site + 1) % n))
        original.require(mask == expected, f"unexpected incidence at n={n}, site={site}")
    tables = original.offer_tables(cycle.edges)
    for phase in (0, 1):
        word = tuple(range(phase, n, 2))
        for state in range(1 << n):
            end = cycle.half_step(state, phase)
            if not (
                end == original.replay(state, word, tables)
                and end == cycle.raw_half_step(state, phase)
                and cycle.half_step(end, phase) == state
                and cycle.counts(end, phase ^ 1) == cycle.counts(state, phase)
            ):
                raise RuntimeError(f"cycle replay, involution or charge failed at {n=}, {phase=}, {state=}")
    return {"n": n, "state_phase_checks": 2 << n}


def cross_control() -> dict[str, int]:
    cycle = Cycle(12)
    gates: tuple[Gate, ...] = ("OR", "XOR", "AND")
    result = dict.fromkeys(gates, 0)
    for state in range(1 << cycle.n):
        before = cycle.counts(state, 0)
        for gate in gates:
            result[gate] += cycle.counts(cycle.half_step(state, 0, gate), 1) == before
    original.require(result == {"OR": 4096, "XOR": 2632, "AND": 1080}, "witness controls changed")
    return result


def verify_single_pairs(cycle: Cycle) -> int:
    """Replay every indexed adjacent seed, both phases, through one ring lap."""
    for phase, start in product((0, 1), range(cycle.n)):
        forward = start % 2 == phase
        direction = 1 if forward else -1
        count = (1, 0) if forward else (0, 1)
        state = cycle.mask((start, (start + 1) % cycle.n))
        for step in range(cycle.n + 1):
            current_phase = phase ^ (step % 2)
            s = (start + step * direction) % cycle.n
            if not (
                state == cycle.mask((s, (s + 1) % cycle.n))
                and cycle.counts(state, current_phase) == count
            ):
                raise RuntimeError(f"single pair mismatch at n={cycle.n}, {phase=}, {start=}, {step=}")
            state = cycle.raw_half_step(state, current_phase)
    return 2 * cycle.n


def collision(cycle: Cycle, right: int, left: int, phase: int, time: int) -> dict:
    """Compare against independent free trajectories, not tagged constituents."""
    n = cycle.n

    def free(elapsed: int) -> int:
        return cycle.mask((i % n for i in (
            right + elapsed, right + elapsed + 1, left - elapsed, left - elapsed + 1,
        )))

    state = free(0)
    occupied, counts = [], []
    reflection_offset = 9
    reflected = cycle.reflect(state, reflection_offset)
    for step in range(time + 1):
        current_phase = phase ^ (step % 2)
        occupied.append(cycle.sites(state))
        counts.append(cycle.counts(state, current_phase))
        original.require(counts[-1] == (1, 1), f"collision lost charge at {n=}, {step=}")
        original.require(reflected == cycle.reflect(state, reflection_offset), "reflected orbit changed")
        if step < time:
            next_state = cycle.raw_half_step(state, current_phase)
            original.require(next_state == cycle.half_step(state, current_phase), "collision rule mismatch")
            state = next_state
            reflected = cycle.raw_half_step(reflected, current_phase ^ 1)
    # The approaching and receding supports can coincide. Next phase is
    # needed to tell which disjoint bond is right-moving without adding tags.
    support_matches = tuple(t for t in range(time + 1) if state == free(t))
    phase_matches = tuple(t for t in support_matches if (time - t) % 2 == 0)
    original.require(phase_matches == (time - 2,), f"phase-matched free replay changed at {n=}")
    return {
        "n": n,
        "initial_next_phase": phase,
        "comparison_next_phase": phase ^ (time % 2),
        "comparison_time": time,
        "occupied": tuple(occupied),
        "counts": tuple(counts),
        "free_at_recovery": cycle.sites(free(time)),
        "support_only_free_times": support_matches,
        "phase_matched_free_time": phase_matches[0],
        "delay_half_steps": time - phase_matches[0],
    }


def scheduler_control() -> dict:
    cycle = Cycle(12)
    seed = cycle.mask((4, 5))
    even = cycle.raw_half_step(seed, 0)
    odd = cycle.raw_half_step(seed, 1)
    original.require(cycle.counts(even, 1) == (1, 0), "full matching wrong sector")
    original.require(cycle.raw_half_step(even, 0) == seed, "same matching should undo")
    original.require(cycle.reflect(seed, 9) == seed, "reflection moved seed")
    original.require(even != odd and cycle.reflect(even, 9) == odd, "phase choice not reflected")
    omitted = []
    for i in (4, 6):
        output = cycle.raw_half_step(seed, 0, omit=i)
        count = cycle.counts(output, 1)
        original.require(count == (1, 1), f"omitting site {i} should change the sector")
        omitted.append((i, cycle.sites(output), count))
    single = dict.fromkeys(cycle.raw_offer(seed, i) for i in range(cycle.n))
    original.require(even not in single, "one asynchronous offer reproduced the matching")

    # The unconstrained one-site offer graph is a different dynamics. Even
    # at n=8 it connects all nonzero states and leaves the blank state alone.
    tables = original.offer_tables(Cycle(8).edges)
    original.require(all(p[0] == 0 for p in tables), "the raw blank state moved")
    seen, todo = {seed}, [seed]
    while todo:
        current = todo.pop()
        for offer in tables:
            end = offer[current]
            if end not in seen:
                seen.add(end)
                todo.append(end)
    original.require(seen == set(range(1, 256)), "raw nonempty orbit changed")
    return {
        "seed": cycle.sites(seed),
        "even_output": cycle.sites(even),
        "odd_output": cycle.sites(odd),
        "reflected_even_output": cycle.sites(cycle.reflect(even, 9)),
        "omitted": tuple(omitted),
        "single_offer_outputs": tuple(cycle.sites(s) for s in single),
        "raw_n8_nonempty_component": len(seen),
    }


def experiment() -> dict:
    primary, heldout = Cycle(30), Cycle(46)
    reference = collision(primary, 4, 15, 0, 10)
    comparison = collision(heldout, 6, 23, 0, 13)
    translated = collision(primary, 27, 8, 1, 10)
    original.require(reference["occupied"][4:] == PRIMARY_NEAR_COLLISION, "primary frames changed")
    original.require(comparison["occupied"][7:] == HELDOUT_NEAR_COLLISION, "held-out frames changed")
    original.require(translated["occupied"] == tuple(
        tuple(sorted((i + 23) % primary.n for i in frame)) for frame in reference["occupied"]
    ), "translation plus phase shift did not commute")
    return {
        "boundary": "known Rule 54 under supplied cycle and alternating matching; no physical derivation",
        "single_pair_seeds_checked": (verify_single_pairs(primary), verify_single_pairs(heldout)),
        "collision": reference,
        "heldout_collision": comparison,
        "translated_collision": translated,
        "local_cancellation": local_cancellation(),
        "exhaustive": tuple(exhaustive_cycle(n) for n in EXHAUSTIVE_LENGTHS),
        "cross_control_preserved": cross_control(),
        "scheduler": scheduler_control(),
    }


if __name__ == "__main__":
    print(json.dumps(experiment(), indent=2, sort_keys=True))
