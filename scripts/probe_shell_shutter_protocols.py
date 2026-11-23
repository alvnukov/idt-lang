"""Four classical shutter protocols on the frozen rule-32, one-root cube orbit.

The preparation, clock/schedule, choice of three gates and exact-time singleton
readout are supplied. Weights are per initial preparation, never conditioned on
arrival, survival, or a first label. The differences across openings are not
experimental interference, amplitudes, or a test/derivation of the Born rule.

Run: python3 -m scripts.probe_shell_shutter_protocols
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

from scripts.probe_facilitated_forest_signal import Moves, lift, need
from scripts.probe_localized_shell_packets import RawShell, fixtures

MASKS = range(8)
BITS = (1, 2, 4)
FEEDBACK_WORD = (1, 3, 4, 0, 5, 4, 6, 5)
PROTOCOLS = {
    "A": "Uniform raw-center offers; disabled or blocked offers idle.",
    "B": "Uniform among enabled unblocked centers; an empty choice idles.",
    "C": "Fixed fully open A process; kill on first successful blocked toggle.",
    "D": "Fixed fully open A process; filter first successful slit label only; "
    "unlabeled histories common to all contexts. Not a permanent shutter.",
}


@dataclass(frozen=True)
class Fixture:
    moves: Moves
    centers: int
    slits: tuple[int, ...]
    start: int
    sink: int


def cube_fixture() -> Fixture:
    base = fixtures()["cube"]
    raw, rungs = lift(base)
    start, sink = (sum(rungs) ^ raw.stars[v] for v in (0, 6))
    moves = RawShell(raw).orbit(start, 32)
    slits = tuple(sorted(base.neighbors[0]))
    need(sink in moves and len(moves) == 20 and slits == (1, 3, 4), "wrong fixture")
    return Fixture(moves, len(raw.stars), slits, start, sink)


@dataclass(frozen=True)
class Readout:
    sink: tuple[Fraction, ...]
    retained: tuple[Fraction, ...]  # includes histories away from the sink

    @property
    def i2(self) -> tuple[Fraction, ...]:
        p = self.sink
        return tuple(p[a | b] - p[a] - p[b] + p[0] for a, b in combinations(BITS, 2))

    @property
    def i3(self) -> Fraction:
        p = self.sink
        return p[7] - p[3] - p[5] - p[6] + p[1] + p[2] + p[4] - p[0]


def gate_timelines(f: Fixture, steps: int) -> dict[str, list[Readout]]:
    """A counts equiprobable raw words; B propagates unequal fractional weights."""
    sink_a = [[] for _ in range(steps + 1)]
    sink_b = [[] for _ in range(steps + 1)]
    for mask in MASKS:
        blocked = {v for bit, v in zip(BITS, f.slits) if not mask & bit}
        live = {
            s: [dest for v, dest in row.items() if v not in blocked]
            for s, row in f.moves.items()
        }
        words = Counter({f.start: 1})
        mass = Counter({f.start: Fraction(1)})
        for t in range(steps + 1):
            need(
                sum(words.values()) == f.centers**t and sum(mass.values()) == 1,
                "physical gate lost preparation weight",
            )
            sink_a[t].append(Fraction(words[f.sink], f.centers**t))
            sink_b[t].append(Fraction(mass[f.sink]))
            if t == steps:
                break
            next_words, next_mass = Counter(), Counter()
            for state, count in words.items():
                dests = live[state]
                next_words[state] += count * (f.centers - len(dests))
                for dest in dests:
                    next_words[dest] += count
            for state, weight in mass.items():
                dests = live[state] or [state]
                share = weight / len(dests)
                for dest in dests:
                    next_mass[dest] += share
            words, mass = next_words, next_mass
    unit = (Fraction(1),) * 8
    return {
        name: [Readout(tuple(p), unit) for p in timeline]
        for name, timeline in (("A", sink_a), ("B", sink_b))
    }


def history_timelines(f: Fixture, steps: int) -> dict[str, list[Readout]]:
    """Count raw words once, tracking both support and first successful slit."""
    rows = {"C": [], "D": []}
    label = dict(zip(f.slits, BITS))
    tagged = Counter({(f.start, 0, 0): 1})
    for t in range(steps + 1):
        denom = f.centers**t
        need(sum(tagged.values()) == denom, "fully open histories lost mass")
        support_at_sink = Counter()
        for name, timeline in rows.items():
            kept, sink = [0] * 8, [0] * 8
            for (state, support, first), n in tagged.items():
                tag = support if name == "C" else first
                if name == "C" and state == f.sink:
                    support_at_sink[support] += n
                for mask in MASKS:
                    if tag & ~mask == 0:
                        kept[mask] += n
                        if state == f.sink:
                            sink[mask] += n
            timeline.append(
                Readout(
                    tuple(Fraction(n, denom) for n in sink),
                    tuple(Fraction(n, denom) for n in kept),
                )
            )
        need(
            rows["C"][-1].i3 == Fraction(support_at_sink[7], denom),
            "all-touched support did not reproduce third difference",
        )
        if t == steps:
            break
        following = Counter()
        for (state, support, first), n in tagged.items():
            enabled = f.moves[state]
            following[state, support, first] += n * (f.centers - len(enabled))
            for center, dest in enabled.items():
                bit = label.get(center, 0)
                following[dest, support | bit, first or bit] += n
        tagged = following
    return rows


def probe_shell_shutters(steps: int = 12) -> dict[str, list[Readout]]:
    if steps < 0:
        raise ValueError("negative tick count")
    fixture = cube_fixture()
    return gate_timelines(fixture, steps) | history_timelines(fixture, steps)


def replay(f: Fixture, mask: int, word: tuple[int, ...]) -> tuple[int, frozenset[int]]:
    """A: replay one common offer word under one gate context."""
    state = f.start
    touched = set()
    blocked = {v for bit, v in zip(BITS, f.slits) if not mask & bit}
    for center in word:
        if center not in blocked and center in f.moves[state]:
            state = f.moves[state][center]
            if center in f.slits:
                touched.add(center)
    return state, frozenset(touched)


def main() -> None:
    f = cube_fixture()
    timelines = probe_shell_shutters()
    print(
        json.dumps(
            {
                "scope": "Finite classical path weights on a supplied preparation, schedule, "
                "gate placement and clocked readout; no Born claim.",
                "fixture": {
                    "rule": 32,
                    "states": len(f.moves),
                    "centers": f.centers,
                    "root": 0,
                    "sink": 6,
                    "slits_in_mask_bit_order": f.slits,
                },
                "i2_mask_pairs": list(combinations(BITS, 2)),
                "feedback_word": {
                    "centers": FEEDBACK_WORD,
                    "sink_masks": [
                        m for m in MASKS if replay(f, m, FEEDBACK_WORD)[0] == f.sink
                    ],
                },
                "protocols": {
                    name: {
                        "law": PROTOCOLS[name],
                        "timeline": [
                            {
                                "tick": t,
                                "sink_by_mask": list(map(str, r.sink)),
                                "retained_by_mask": list(map(str, r.retained)),
                                "i2": list(map(str, r.i2)),
                                "i3": str(r.i3),
                            }
                            for t, r in enumerate(rows)
                        ],
                    }
                    for name, rows in timelines.items()
                },
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
