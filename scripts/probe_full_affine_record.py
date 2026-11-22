"""Full-space comparison of two F5 readers; no new detector calibration.

The original six-phase fringe does not identify a detector on all 125
inputs. The 17-contact native recorder implements the union N of two
coordinate planes, not the original now-or-one-inverse predicate D.
We replay the final scratch AND record, the archived equal mixtures,
and the entire positive two-contact setting family. Equal effect families
do not make corresponding named settings equal.

Exhaustive negative: with zero signal memory and one or two fixed ready
background references, no fixed 0..3-contact word realizes D by memory
alone on the whole input space: some opposite-D inputs have identical
color-equality transcripts. This does not bound longer words.

Two positive constructions (not shortest): a four-contact change of
data variables feeds the frozen native recorder, or two separate native
equality records feed a two-contact OR. Both restore the three signals
and the ready reference. Disposable scratch is not reset, and ordinary
preparations, ports, clock, controlled branch tables and meaning of the
bit remain supplied. No measured frequencies or physics-status change.
Run: python3 -B -m scripts.probe_full_affine_record  (also with -O).
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, product

from scripts.probe_affine_contact_fringe import Six, detector, need
from scripts.probe_affine_contact_record import (
    COPY,
    WRITE,
    Root,
    Scene,
    Word,
    all_roots,
    apply,
    colors,
)
from scripts.probe_affine_pulse_holdouts import (
    FRINGE,
    IDENT,
    TAGS,
    Perm,
    Triple,
    contacts,
    encode,
    gates,
    measure,
    power,
    then,
)

W: Word = tuple((i, i + 1) for i in Six)
PRE: Word = ((0, 1), (0, 2), (1, 2), (0, 2))


def undo(word: Word) -> Word:
    """The same positive gate three times implements its inverse."""
    return tuple(edge for edge in reversed(word) for _ in range(3))


def clean_flag(p: int, q: int) -> Word:
    source_ready = ((0, 3),)
    ports = {0: 0, 4: p, 5: q}
    copy_flag = tuple((ports[i], ports[j]) for i, j in COPY)
    return source_ready + copy_flag + undo(source_ready)


def literal_control(eq: Root, ne: Root) -> Word:
    # Both flags are (background, bit), so the two-contact OR always
    # acts with the equality branch, not an external decision or lookup.
    gate_or: Word = ((5, 7), (5, 8))
    for a, b in product(range(2), repeat=2):
        s: Scene = ((0, a), (0, b), (0, 0))
        need(
            apply(s, ((0, 1), (0, 2)), eq, ne)[2] == (0, int(bool(a or b))), "native OR"
        )
    for background, x in product(range(5), repeat=2):
        s = ((x, 0), (0, 0), (0, 0), (background, 1), (background, 0), (background, 0))
        t = apply(s, clean_flag(4, 5), eq, ne)
        need(
            t[:4] == s[:4] and t[5] == (background, int(x == background)),
            "native equality",
        )
    return clean_flag(4, 5) + undo(W) + clean_flag(6, 7) + W + gate_or


def records() -> tuple[frozenset[int], frozenset[int]]:
    roots = all_roots()
    eq, ne = roots[52], roots[2]
    native = WRITE + COPY + undo(WRITE)
    transformed = PRE + native + undo(PRE)
    separate = literal_control(eq, ne)
    need((len(native), len(transformed), len(separate)) == (17, 33, 36), "contact cost")
    d_set: set[int] = set()
    n_set: set[int] = set()
    joint: Counter[tuple[int, int]] = Counter()
    scratch: Counter[int] = Counter()
    for background in range(5):
        for i, s in enumerate(TAGS):
            x, y, z = s
            d = int(detector(s, background))
            n = int(x == background or z == background)
            need(
                d == int(x == background or (x + 2 * y + 3 * z) % 5 == background),
                "inverse-pulse plane",
            )
            start: Scene = (
                tuple((v, 0) for v in s) + ((background, 1),) + ((background, 0),) * 2
            )
            m = apply(start, PRE, eq, ne)
            need(
                tuple(c for c, _ in m[:3])
                == (x, (4 * x + 4 * y + 3 * z) % 5, (x + 2 * y + 3 * z) % 5),
                "variable change",
            )
            end = apply(start, native, eq, ne)
            need(
                end[:4] == start[:4] and end[5] == (background, n),
                "17-contact native readout",
            )
            corrected = apply(start, transformed, eq, ne)
            need(
                corrected[:4] == start[:4] and corrected[5] == (background, d),
                "33-contact D",
            )
            other = apply(start + ((background, 0),) * 3, separate, eq, ne)
            need(other[:4] == start[:4] and other[8] == (background, d), "36-contact D")
            if background == 0:
                if d:
                    d_set.add(i)
                if end[5][1] == 1:
                    n_set.add(i)
                joint[d, end[5][1]] += 1
                scratch[end[4][1]] += 1
    need(
        joint == {(0, 0): 64, (0, 1): 16, (1, 0): 16, (1, 1): 29},
        "full readout comparison",
    )
    need(scratch == {0: 80, 2: 40, 3: 5}, "scratch is not the binary output")
    return frozenset(d_set), frozenset(n_set)


def transcript(s: Triple, n: int, word: Word) -> int:
    c = [*s, *([0] * (n - 3))]
    trace = 0
    for i, j in word:
        trace = 2 * trace + int(c[i] == c[j])
        c[i], c[j] = colors(c[i], c[j])
    return trace


def short_wall(d_set: frozenset[int]) -> None:
    for n, expected in ((4, 259), (5, 1111)):
        checked = 0
        for length in range(4):
            for word in product(combinations(range(n), 2), repeat=length):
                traces: list[set[int]] = [set(), set()]
                for i, s in enumerate(TAGS):
                    bit = int(i in d_set)
                    trace = transcript(s, n, word)
                    if trace in traces[1 - bit]:
                        break
                    traces[bit].add(trace)
                else:
                    raise ValueError(f"possibly separating word needs testing: {word}")
                checked += 1
        need(checked == expected, "incomplete fixed-word wall")


def pullback(g: Perm, effect: frozenset[int]) -> frozenset[int]:
    return frozenset(i for i in IDENT if g[i] in effect)


def holdout(d: frozenset[int], n: frozenset[int]) -> None:
    w, group = gates()
    left, right = contacts()
    swap = then(left, left)
    dials = tuple(power(w, k) for k in range(6))
    orbit = tuple(g[encode(0, 1, 0)] for g in dials)
    stocks = tuple(tuple(orbit[(k + j) % 6] for j in (0, 1, 1, 2)) for k in range(6))
    mixes = tuple(stocks[k] + stocks[k + 3] for k in range(3))
    for effect, expected in (
        (d, ((3, 2, 3), (4, 3, 5), (1, 2, 1))),
        (n, ((2, 3, 3), (3, 2, 3), (3, 5, 4))),
    ):
        need(
            tuple(measure(stocks[0], effect, g) for g in dials) == FRINGE,
            "solo setting drift",
        )
        need(
            all(
                tuple(measure(m, effect, g) for m in mixes) == (4, 4, 4) for g in dials
            ),
            "mixed dial drift",
        )
        actual = tuple(
            tuple(measure(m, effect, g) for m in mixes) for g in (left, right, swap)
        )
        need(actual == expected, "frozen stock ordered setting drift")
    # Native neighbor prewords produce the same unordered effect family.
    effects = {pullback(g, n) for g in group}
    need(
        len(group) == 480
        and len(effects) == 240
        and effects == {pullback(g, d) for g in group},
        "effect orbit",
    )
    shortest = "LRRLRLRR"
    for size in range(len(shortest) + 1):
        witnesses = []
        for word in product("LR", repeat=size):
            g = IDENT
            for c in word:
                g = then(g, left if c == "L" else right)
            if pullback(g, n) == d:
                witnesses.append("".join(word))
        need(
            witnesses == ([shortest] if size == len(shortest) else []),
            "neighbor conjugating preword",
        )


def main() -> None:
    d, n = records()
    short_wall(d)
    holdout(d, n)
    print(
        "All 125 raw inputs: 17-contact N outputs only 0/1 (80/45); 29 common bright, 16 each mismatch, 64 common dark."
    )
    print(
        "N tests x or z against background; old D tests x or x+2y+3z. Only terminal scratch has labels 2/3."
    )
    print(
        "One/two ready references, any <=3 fixed contacts: opposite D values share a whole equality transcript."
    )
    print(
        "Same physical gate: 33-contact change/record/rewind or 36-contact two-test OR restores data and records D, all 625 input/frame cases."
    )
    print(
        "Archived stock: same solo 4,3,1,0,1,3 /4 and opposite dial mixtures 4,4,4 /8. Native N left/right/swap: (2,3,3)/(3,2,3)/(3,5,4) out of eight."
    )
    print(
        "Named settings differ, but all 480 distinct native maps yield the same family of 240 effects. No new stock-wide bound."
    )


if __name__ == "__main__":
    main()
