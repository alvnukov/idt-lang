"""Exhaust a supplied two-contact grant and an unchanged open FIFO.

Closed: on (a,b,c,d,h,g), H touches (a,b,c,h), G touches (b,c,d,g).
A legal contact has two marks and complements only its four slots. The grant
H if b=0, G otherwise makes two four-cycles on the eight states supporting
HGH. Each device always sees its own fixed ordered shared pair, not a free
signal. The grant and overlap wiring are supplied, not derived.

Open: H outputs (w,b,c); G receives (b,c,s) with an independent spectator s.
Only an active contact toggles its own mirror. Since w+b+c=1+h after H
fires, G is legal precisely when s-w=1-h-g, with h,g the pre-fire phases.
Waiting on the unchanged head cannot alter its mirror phase. Enumeration
covers the previous balanced arrival family for k=1,2,3, not all feeds or
repacketizers. Reconnecting s=w at opposite phase echoes the H input with a
fixed permutation after two complements; this is not an arbitrary signal
transport result or a physical readout.
"""

from __future__ import annotations

import json
from itertools import combinations, product
from typing import Final, Literal, TypedDict

Triple = tuple[int, int, int]
ClosedState = tuple[int, int, int, int, int, int]
Contact = Literal["H", "G"]
BITS: Final = (0, 1)
TRIPLES: Final = tuple(product(BITS, BITS, BITS))


class ClosedInventory(TypedDict):
    states: int
    legal_prefixes: dict[str, int]
    one_per_pair_states: int
    grant_cycles: list[tuple[ClosedState, ...]]
    H_shared_input: tuple[int, int]
    G_shared_input: tuple[int, int]


class OpenInventory(TypedDict):
    total: int
    same_phase: int
    opposite_phase: int
    neither: int
    row_phase_checks: int


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


def closed_fire(state: ClosedState, contact: Contact) -> ClosedState | None:
    a, b, c, d, h, g = state
    if contact == "H":
        return (1 - a, 1 - b, 1 - c, d, 1 - h, g) if a + b + c + h == 2 else None
    return (a, 1 - b, 1 - c, 1 - d, h, 1 - g) if b + c + d + g == 2 else None


def closed_inventory() -> ClosedInventory:
    states = tuple(product(BITS, BITS, BITS, BITS, BITS, BITS))
    contacts: tuple[Contact, ...] = ("H", "G", "H", "G")
    runs: dict[ClosedState, ClosedState] = {state: state for state in states}
    supports: list[set[ClosedState]] = []
    prefixes: dict[str, int] = {}
    for step, contact in enumerate(contacts, 1):
        runs = {
            start: after
            for start, state in runs.items()
            if (after := closed_fire(state, contact)) is not None
        }
        supports.append(set(runs))
        prefixes["".join(contacts[:step])] = len(runs)

    one_per_pair = {
        (a, b, c, d, h, g)
        for a, b, c, d, h, g in states
        if b + c == a + h == d + g == 1
    }
    need(
        len(states) == 64 and tuple(prefixes.values()) == (24, 10, 8, 8),
        "closed prefix inventory",
    )
    need(
        supports[2] == supports[3] == one_per_pair,
        "closed support is not one mark in each pair",
    )

    moves: dict[ClosedState, ClosedState] = {}
    h_seen, g_seen = set[tuple[int, int]](), set[tuple[int, int]]()
    for state in one_per_pair:
        pair = state[1], state[2]
        contact = "H" if pair[0] == 0 else "G"
        (h_seen if contact == "H" else g_seen).add(pair)
        after = closed_fire(state, contact)
        if after is None or after not in one_per_pair:
            raise ArithmeticError("grant leaves recurrent support")
        moves[state] = after
    need(
        h_seen == {(0, 1)} and g_seen == {(1, 0)},
        "grant unexpectedly varies or swaps roles",
    )
    need(set(moves.values()) == one_per_pair, "grant not a permutation")
    unseen = one_per_pair.copy()
    cycles: list[tuple[ClosedState, ...]] = []
    while unseen:
        start = current = min(unseen)
        cycle = []
        while current in unseen:
            cycle.append(current)
            unseen.remove(current)
            current = moves[current]
        need(current == start and len(cycle) == 4, "grant orbit is not a four-cycle")
        cycles.append(tuple(cycle))
    need(len(cycles) == 2, "grant orbit count")
    return {
        "states": len(states),
        "legal_prefixes": prefixes,
        "one_per_pair_states": len(one_per_pair),
        "grant_cycles": cycles,
        "H_shared_input": min(h_seen),
        "G_shared_input": min(g_seen),
    }


def tick(row: Triple | None, mirror: int) -> tuple[Triple | None, int]:
    """A half-filled contact fires; absence or a failed attempt leaves it unchanged."""
    if row is None or sum(row) + mirror != 2:
        return None, mirror
    x, y, z = row
    return (1 - x, 1 - y, 1 - z), 1 - mirror


def two_device_tick(
    drive: Triple, h: int, g: int, spectator: int
) -> tuple[Triple | None, int, int]:
    """Attempt G on the literal H output; an inactive H does not present a row."""
    h_out, after_h = tick(drive, h)
    if h_out is None:
        return None, after_h, g
    _, b, c = h_out
    g_out, after_g = tick((b, c, spectator), g)
    return g_out, after_h, after_g


def fifo_replay(word: tuple[Triple, ...], phase: int, *, waits: int) -> tuple[int, int]:
    """Try each unchanged head in order, inserting idle ticks and retrying any block."""
    for i, row in enumerate(word):
        for _ in range(waits):
            idle, after = tick(None, phase)
            need(idle is None and after == phase, "waiting changes FIFO mirror")
            phase = after
        out, after = tick(row, phase)
        if out is None:
            need(
                after == phase and tick(row, after) == (None, phase),
                "blocked head changes on retry",
            )
            return i, after
        phase = after
    return len(word), phase


def open_inventory(k: int) -> OpenInventory:
    if k < 1:
        raise ValueError("positive k required")
    doubles = tuple(row for row in TRIPLES if sum(row) == 2)
    singles = tuple(row for row in TRIPLES if sum(row) == 1)
    words: set[tuple[Triple, ...]] = set()
    same = opposite = neither = checks = 0
    for blocks in product(tuple(product(doubles, singles)), repeat=k):
        drive = tuple(row for block in blocks for row in block)
        exposed: list[Triple] = []
        h = 0
        for row in drive:
            actual, after = tick(row, h)
            if actual is None:
                raise ArithmeticError("illegal upstream drive")
            need(tick(None, h) == (None, h) and after == 1 - h, "upstream wait/toggle")
            exposed.append(actual)
            h = after
        need(h == 0, "upstream mirror not restored")
        if sum(row[1] for row in exposed) != k or sum(row[2] for row in exposed) != k:
            continue

        for marked in combinations(range(2 * k), k):
            word = tuple(
                (b, c, int(i in marked)) for i, (_, b, c) in enumerate(exposed)
            )
            need(word not in words, "upstream overlap histories are not unique")
            words.add(word)
            accepted = []
            for start in BITS:
                prefix = len(word)
                for i, ((w, _, _), (_, _, s), row) in enumerate(
                    zip(exposed, word, drive, strict=True)
                ):
                    # Use the phases at row i conditional on serving its prefix.
                    # Compare both phase possibilities for every row, even beyond a block.
                    h, g = i % 2, start ^ (i % 2)
                    legal = s - w == 1 - h - g
                    output, after_h, after_g = two_device_tick(row, h, g, s)
                    need(
                        (output is not None) == legal,
                        "open row criterion disagrees with literal update",
                    )
                    need(
                        after_h == 1 - h and after_g == (1 - g if legal else g),
                        "active-only mirror updates",
                    )
                    if not legal and prefix == len(word):
                        prefix = i
                    checks += 1
                replay = (prefix, start ^ (prefix % 2))
                need(
                    fifo_replay(word, start, waits=0) == replay,
                    "literal FIFO prefix differs",
                )
                need(
                    fifo_replay(word, start, waits=2) == replay,
                    "inserted waits repair a blocked head",
                )
                accepted.append(prefix == len(word))
            need(not all(accepted), "a nonempty word accepts both initial phases")
            same += accepted[0]
            opposite += accepted[1]
            neither += not any(accepted)
    need(same + opposite + neither == len(words), "incomplete FIFO partition")
    return {
        "total": len(words),
        "same_phase": same,
        "opposite_phase": opposite,
        "neither": neither,
        "row_phase_checks": checks,
    }


def echo_inventory() -> int:
    rows = 0
    for h, drive in product(BITS, TRIPLES):
        out, _ = tick(drive, h)
        if out is None:
            continue
        a, b, c = drive
        need(
            two_device_tick(drive, h, 1 - h, out[0]) == ((b, c, a), 1 - h, h),
            "echo is not double complement with rotation",
        )
        rows += 1
    need(rows == 6, "echo inventory")
    return rows


def probe() -> dict[str, object]:
    open_results = {k: open_inventory(k) for k in (1, 2, 3)}
    expected = {1: (6, 2, 3, 1), 2: (90, 6, 15, 69), 3: (1860, 20, 93, 1747)}
    for k, r in open_results.items():
        need(
            (r["total"], r["same_phase"], r["opposite_phase"], r["neither"])
            == expected[k],
            "balanced arrival inventory",
        )
    bad = ((0, 0, 0), (1, 1, 1))
    for phase in BITS:
        need(
            all(tick(row, phase) == (None, phase) for row in bad),
            "invalid solid row accepted",
        )
        need(fifo_replay(bad, phase, waits=3) == (0, phase), "bad FIFO head could pass")
    return {
        "closed": closed_inventory(),
        "open": open_results,
        "echo_legal_rows": echo_inventory(),
        "bad_fifo_accepted_phases": [],
        "scope": "Supplied closed overlap and grant; open unchanged row FIFO with no phase reset. No arbitrary signal routing, physical update rule or readout derived.",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
