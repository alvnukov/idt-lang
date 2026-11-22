"""A real six-dial reset escape, and a single additional setting that rejects it.

The first detector is D; the three color inputs can be restored by its
native recorder. Undisturbed stored output is not used to select the next
operation. A supplied fair pair of bits selects one of four schedules
independently of both preparation and outcome. Each is compiled entirely
from the old color contact (all working memories blank), on fresh ports.
These are not four randomly loaded offsets of one fixed linear program.
Both the prepared nonbackground reference and independent scheduling are
resources. Reversible garbage need not be erased.

The escape produces exactly P0/P3 conditional statistics on the six
original W dials, not the actual preparation or full measurement update.
With exact old endpoint statistics at W^0 and W^3, every independent
mixture of affine maps from the input plane to arbitrary raw triples
fails a single right-contact follow-up. This holds on an explicit pool
of the archived preparations, without reading hidden input phases.
No experimental counts, general instrument claim or approximate bound.
Replay: python3 -B -m scripts.probe_affine_reset_escape  (also with -O).
"""

from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product

from scripts.probe_affine_contact_fringe import Six, cycle, detector, need
from scripts.probe_affine_contact_record import Word, colors
from scripts.probe_affine_projective_reset import Basis, combine, lower_rank
from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    Perm,
    Triple,
    contacts,
    encode,
    gates,
    power,
    then,
)

MAPS: tuple[Basis, ...] = (
    ((0, 1, 1), (4, 4, 4), (3, 2, 2)),
    ((1, 0, 0), (4, 3, 3), (2, 1, 1)),
    ((1, 1, 2), (1, 1, 2), (3, 3, 4)),
    ((1, 1, 4), (1, 1, 4), (1, 1, 0)),
)
BANK = 30  # data 0..2, nonbackground reference 3, outputs 4..6, fresh blanks, two pad ports


def direct(table: Basis, s: Triple, a: int, b: int) -> Triple:
    def coord(row: Triple) -> int:
        u, v, w = row
        return (b + u * (s[0] - b) + v * (s[1] - b) + w * (a - b)) % 5

    return coord(table[0]), coord(table[1]), coord(table[2])


def transfer() -> str:
    goal = tuple(encode((u + t - h) % 5, t, (2 * h - t) % 5) for u, t, h in TAGS)
    alphabet = tuple(zip("LR", contacts(), strict=True))
    paths = {IDENT: ""}
    queue = [IDENT]
    for g in queue:
        if g == goal:
            need(paths[g] == "LRLLLRLLR", "shortest positive neighbor transfer")
            return paths[g]
        for mark, step in alphabet:
            h = then(g, step)
            if h not in paths:
                paths[h] = paths[g] + mark
                queue.append(h)
    raise ValueError("transfer absent")


def compile_map(table: Basis, add: str) -> Word:
    # Export t-b into output u. Leave source t unchanged; the fresh h=b
    # now stores b-(t-b), so neither conservation nor reversibility is lost.
    word = []
    fresh = 7
    for k, row in enumerate(table, 4):
        for source, reps in zip((0, 1, 3), row, strict=True):
            for _ in range(reps):
                for mark in add:
                    word.append((k, source) if mark == "L" else (source, fresh))
                fresh += 1
    need(fresh <= BANK - 2, "blank allocation")
    return tuple(word)


def run(bank: list[int], word: Word) -> list[int]:
    result = bank.copy()
    for i, j in word:
        result[i], result[j] = colors(result[i], result[j])
    return result


def nearest(word: Word) -> Word:
    # Each literal wire swap is two positive contacts. Bring the pair
    # adjacent, pulse, and undo the swaps. The gate commutes with SWAP.
    result: list[tuple[int, int]] = []
    for i, j in word:
        a, b = sorted((i, j))
        swaps = [(k, k + 1) for k in range(b - 1, a, -1) for _ in range(2)]
        result.extend((*swaps, (a, a + 1), *reversed(swaps)))
    return tuple(result)


def compiler() -> None:
    add = transfer()
    compact = tuple(compile_map(table, add) for table in MAPS)
    need(tuple(map(len, compact)) == (189, 135, 162, 126), "addressed program sizes")
    for table, program in zip(MAPS, compact, strict=True):
        # Identical initial bank and 189 clocks in each independently
        # selected schedule. The two pad cells both stay at background.
        word = program + ((BANK - 2, BANK - 1),) * (189 - len(program))
        line = nearest(word)
        need(all(j == i + 1 for i, j in line), "not a line compilation")
        # Both compiled full-bank maps are linear, so these basis vectors
        # certify the routing on every raw bank, not just the preparation.
        for pos in range(BANK):
            basis = [int(i == pos) for i in range(BANK)]
            need(run(basis, line) == run(basis, word), "line routing")
        for a, b in product(range(5), repeat=2):
            for s in TAGS:
                bank = [*s, a, *([b] * (BANK - 4))]
                result = run(bank, word)
                need(
                    result[:4] == bank[:4]
                    and tuple(result[4:7]) == direct(table, s, a, b),
                    "compiled frame/output",
                )


def branches() -> tuple[tuple[Triple, ...], tuple[Perm, ...], frozenset[int]]:
    orbit = tuple(cycle((0, 1, 0), Six))
    w, _ = gates()
    return (
        orbit,
        tuple(power(w, k) for k in range(6)),
        frozenset(i for i, s in enumerate(TAGS) if detector(s, 0)),
    )


def concrete(
    orbit: tuple[Triple, ...], dials: tuple[Perm, ...], d: frozenset[int]
) -> None:
    left, right = contacts()
    oi = tuple(encode(*s) for s in orbit)
    native = tuple(
        tuple(encode(*direct(table, s, 1, 0)) for table in MAPS) for s in orbit
    )
    for j, g in enumerate((*dials, left, right)):
        raw = tuple(sum(g[t] in d for t in row) for row in native)
        target = tuple(
            sum(g[oi[(3 * (i >= 3) + k) % 6]] in d for k in (0, 1, 1, 2))
            for i in range(6)
        )
        if j < 6:
            need(raw == target, "six postdial escape failed")
        else:
            expected = (1, 1, 1, 2, 2, 2) if j == 6 else (3, 3, 3, 1, 1, 1)
            need(
                target == expected and raw == (2, 2, 2, 1, 1, 1),
                "extra setting failed to separate concrete escape",
            )


def discriminator(
    orbit: tuple[Triple, ...], dials: tuple[Perm, ...], d: frozenset[int]
) -> None:
    _, right = contacts()
    # For each archived Pk, its four input tickets must give the target
    # conditional branch rates. Restricted ticket rows have rank three;
    # clearing each conditioning denominator therefore forces the same
    # rates on the individual raw inputs in that branch for common kernels.
    tickets = [Counter((k + j) % 6 for j in (0, 1, 1, 2)) for k in range(6)]
    for start in (0, 3):
        need(
            lower_rank(
                [tuple(row[i] for i in range(start, start + 3)) for row in tickets]
            )
            == 3,
            "branch ticket identifiability",
        )
    bright = [TAGS[i] for i in IDENT if i in d and dials[3][i] not in d]
    dark = {i for i in IDENT if i not in d and dials[3][i] in d}
    need(len(bright) == len(dark) == 28, "endpoint-compatible raw outputs")
    src = (orbit[0], orbit[1], orbit[2])
    basis = {
        combine(((1 - a - b) % 5, a, b), src): ((1 - a - b) % 5, a, b)
        for a, b in product(range(5), repeat=2)
    }
    need(len(basis) == 25, "affinely independent sources")
    coords = tuple(basis[s] for s in orbit)
    by_slope: dict[tuple[int, ...], list[int]] = defaultdict(list)
    right_totals: Counter[int] = Counter()
    for u, v, w in product(bright, repeat=3):
        targets = (u, v, w)
        image = tuple(encode(*combine(c, targets)) for c in coords)
        if not all(i in dark for i in image[3:]):
            continue
        # Differences of images in an affine basis determine its linear
        # part; fixing them permits every offset, not merely native ones.
        slope = tuple((s[j] - u[j]) % 5 for s in (v, w) for j in range(3))
        by_slope[slope].append(int(dials[1][image[0]] in d))
        right_totals[sum(right[i] in d for i in image[:3])] += 1
    need(Counter(map(len, by_slope.values())) == {1: 416, 2: 8}, "fixed-slope fibers")
    need(
        Counter(tuple(sorted(set(bits))) for bits in by_slope.values())
        == {(0,): 120, (1,): 304},
        "fixed slope and random offset can be fractional",
    )
    oi = tuple(encode(*s) for s in orbit)
    p0 = (oi[0], oi[1], oi[1], oi[2])
    need(sum(dials[1][i] in d for i in p0) == 3, "fixed slope target is not 3/4")
    need(right_totals == {1: 120, 2: 312}, "global affine right-contact certificate")
    need(sum(right[i] in d for i in p0) == 3, "right target is not 3/4")
    pool = tickets[0] + tickets[2] + tickets[4]
    need(
        pool == Counter({k: 2 for k in range(6)})
        and tuple(i in d for i in oi) == (True, True, True, False, False, False),
        "observable uniform bright pool",
    )
    # Uniform bright inputs average the right_totals count divided by 3:
    # <=2/3 for every mixture, versus P0's 3/4. The difference is >=1/12.


def main() -> None:
    compiler()
    orbit, dials, d = branches()
    concrete(orbit, dials, d)
    discriminator(orbit, dials, d)
    print(
        "Four independently selected native schedules match all 36 conditional six-dial counts."
    )
    print(
        "Transfer LRLLLRLLR; common 30-cell bank, 189 addressed clocks after padding; adjacent routing checked."
    )
    print(
        "One fixed linear part + independent raw offsets cannot match: at phase 0, W^1 every allowed offset agrees, target 3/4."
    )
    print("Concrete extra L or R: (2,2,2,1,1,1)/4. Target R: (3,3,3,1,1,1)/4.")
    print(
        "Every endpoint-compatible affine map: right successes across 3 bright inputs 1 (120 maps) or 2 (312)."
    )
    print(
        "Equally pooled P0,P2,P4, conditioned on first bright: native mixtures <=2/3 vs requested 3/4; exact gap >=1/12."
    )


if __name__ == "__main__":
    main()
