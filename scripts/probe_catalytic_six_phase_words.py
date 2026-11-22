"""Finite clean transport on three wires of the frozen six-phase lift.

Wire order is target, prepared occupied reference, prepared vacant reference.
The only clocked actions are A=T on wires 0,1 and B=T on wires 1,2. A and B
have order four; inverse notation abbreviates three forward pulses. The same
word is applied without reading the input or changing either reference stock.
The lift, raw completion, reference preparation, wire addresses and external
timing are supplied. Only the final target and the two final reference labels
are specified; intermediate cells can change. No universal gate synthesis,
shortest word, endogenous actuation, preparation mechanism or QM is inferred.

Default: exhaustive single-state orbit census and literal replay of ONE common
word. Add --joint-census to construct and replay an explicit common word for
the first eligible stock of every surviving lift (slower, not an inference
from the individual orbits). --rediscover repeats the bounded cycle search
that supplied the shorter featured certificate.

Replay: python3 -B -m scripts.probe_catalytic_six_phase_words [--joint-census]
"""

import argparse
from collections import Counter
from itertools import groupby, product
from math import gcd, lcm
from random import Random

from scripts import probe_vacuum_phase_lifts as lifts

Word = tuple[int, ...]
Maps = list[list[int]]
ACTIVE, need = lifts.ACTIVE, lifts.need


def edges(free: tuple[int, int, int]) -> Maps:
    raw = [16 * x + y for x, y in lifts.complete(lifts.lift(free))]
    need(all(raw[raw[q]] == 16 * (q % 16) + q // 16 for q in range(256)), "T² != SWAP")
    return [
        [16 * raw[q // 16] + q % 16 for q in range(4096)],
        [q // 256 * 256 + raw[q % 256] for q in range(4096)],
    ]


def rows(r: int, s: int, shift: int) -> list[int]:
    return [
        256 * (8 * o + (i + shift) % 6) + 16 * (8 + r) + s
        for o, i in product(range(2), ACTIVE)
    ]


def components(maps: Maps) -> list[int]:
    """Forward reachability is an equivalence: each inverse is three pulses."""
    ids = [-1] * len(maps[0])
    for x in range(len(ids)):
        if ids[x] != -1:
            continue
        seen = [x]
        ids[x] = x
        for z in seen:
            for mapping in maps:
                y = mapping[z]
                if ids[y] == -1:
                    ids[y] = x
                    seen.append(y)
    return ids


def good_counts(ids: list[int], shift: int) -> list[int]:
    return [
        sum(
            ids[x] == ids[y]
            for x, y in zip(rows(r, s, 0), rows(r, s, shift), strict=True)
        )
        for r, s in product(range(8), repeat=2)
    ]


def rev(pulses: str) -> str:
    """Positive pulse spelling for the inverse, merging neighboring runs."""
    return "".join(c * (-len(list(part)) % 4) for c, part in groupby(reversed(pulses)))


def cycle_data(mapping: list[int]) -> tuple[list[int], list[int], list[int]]:
    size = len(mapping)
    ids, pos, periods = [-1] * size, [0] * size, [0] * size
    for q in range(size):
        if ids[q] >= 0:
            continue
        x = q
        path: list[int] = []
        while ids[x] == -1:
            ids[x] = q
            pos[x] = len(path)
            path.append(x)
            x = mapping[x]
        for x in path:
            periods[x] = len(path)
    return ids, pos, periods


Block = tuple[str, str, int]

# Each row spells Q, W repeated k times, inverse(Q), in chronological order.
# This is a fixed wiring schedule. No data from a run ever chooses a letter.
CERTIFICATE: list[Block] = [
    ("", "BAAABBA", 1),
    ("BABBABAB", "AABABABABAB", 2),
    ("BBABBABABBBAAABAAABBB", "AABABBBAB", 3),
    ("AABBAABABBBABABBBAABABBABA", "AABBABBBABBB", 40),
    ("BAAAB", "BBBAAABBBAABBBAAABBBA", 58),
    ("ABBABABABBABA", "ABABBABB", 360),
    ("ABBAABBBAABABABAABABA", "AB", 1180),
    ("BAAABBABAABABBB", "BBAAABBBABBBA", 1027),
    ("ABBAAABBABAAABAABAABBAAABAABAAB", "AABBBAB", 5832),
    ("AAABAABAABAABABBABAABAABAABABAAB", "AAAB", 16800),
    ("BBBAAABAAABABABAAABAAABAABBAAABBAAABA", "BAAABA", 60984),
    ("ABBABBABBBAABBBAA", "ABABABBABBB", 22330),
]


def power(mapping: list[int], count: int) -> list[int]:
    need(count >= 0, "negative native repeat count")
    out = list(range(len(mapping)))
    while count:
        if count & 1:
            out = [mapping[x] for x in out]
        mapping = [mapping[x] for x in mapping]
        count //= 2
    return out


def spell(raw: Maps, pulses: str) -> list[int]:
    return realize(raw, tuple("AB".index(ch) for ch in pulses))


def verify_blocks(
    raw: Maps, blocks: list[Block], start: list[int]
) -> tuple[list[int], int]:
    total = 0
    state = start.copy()
    for conj, base, exp in blocks:
        perm = power(spell(raw, base), exp)
        for g in (spell(raw, conj), perm, spell(raw, rev(conj))):
            state = [g[x] for x in state]
        total += len(conj) + exp * len(base) + len(rev(conj))
    return state, total


def search_blocks(raw: Maps, start: list[int], end: list[int]) -> list[Block]:
    """Try Q W^k Q^-1. Cycle positions determine a CRT transporter for k."""
    # Bound the library before checking its successes, and keep the raw word
    # search separate from the fixed certificate. Failure of the library
    # would not prove non-reachability.
    data: list[tuple[str, list[int], list[int], list[int]]] = []
    for size in range(1, 13):
        for chars in product("AB", repeat=size):
            w = "".join(chars)
            if w[0] != "A" or w[-1] != "B" or "AAAA" in w or "BBBB" in w:
                continue
            if any(w[j:] + w[:j] < w for j in range(1, len(w))):
                continue
            data.append((w, *cycle_data(spell(raw, w))))
    rng = Random(0)
    blocks: list[Block] = []
    state = start.copy()
    for i, y in enumerate(end):
        if state[i] == y:
            continue
        best: tuple[int, Block] | None = None
        for trial in range(1024):
            q = (
                ""
                if trial == 0
                else "".join(rng.choice("AB") for _ in range(rng.randrange(4, 48)))
            )
            xs = [*end[:i], state[i], y]
            for ch in q:
                m = raw["AB".index(ch)]
                xs = [m[x] for x in xs]
            for w, ids, pos, sizes in data:
                a, b = xs[-2:]
                if ids[a] != ids[b]:
                    continue
                n = sizes[a]
                d = (pos[b] - pos[a]) % n
                fixed = lcm(*(sizes[v] for v in xs[:-2]))
                h = gcd(n, fixed)
                if d % h:
                    continue
                k = fixed * ((d // h) * pow(fixed // h, -1, n // h) % (n // h))
                other = lcm(fixed, n) - k
                for pulse, count in ((w, k), (rev(w), other)):
                    cost = len(q) + len(rev(q)) + len(pulse) * count
                    if best is None or cost < best[0]:
                        best = (cost, (q, pulse, count))
        if best is None:
            raise RuntimeError(f"bounded transporter missed slot {i}")
        blocks.append(best[1])
        state, _ = verify_blocks(raw, [best[1]], state)
        need(state[: i + 1] == end[: i + 1], "bad transported prefix")
    return blocks


def inverse(mapping: list[int]) -> list[int]:
    out = [0] * len(mapping)
    for i, j in enumerate(mapping):
        out[j] = i
    return out


def invert(word: Word) -> Word:
    return tuple(i ^ 1 for i in reversed(word))


def realize(maps: Maps, word: Word) -> list[int]:
    out = list(range(len(maps[0])))
    for i in word:
        out = [maps[i][x] for x in out]
    return out


def tree(maps: Maps, start: int) -> dict[int, Word]:
    todo = [start]
    paths: dict[int, Word] = {start: ()}
    for x in todo:
        for i, g in enumerate(maps):
            y = g[x]
            if y not in paths:
                paths[y] = (*paths[x], i)
                todo.append(y)
    return paths


def simplify(word: Word) -> Word:
    reduced: list[int] = []
    for letter in word:
        if reduced and reduced[-1] == letter ^ 1:
            reduced.pop()
        else:
            reduced.append(letter)
    return tuple(reduced)


def subgroup(maps: Maps, paths: dict[int, Word], rng: Random) -> list[Word]:
    # Each individual loop fixes the tree root. Sampling these loops cannot
    # establish non-membership: the restricted subgroup may be too small.
    vertices = list(paths)
    if len(vertices) == 1:
        return [(i,) for i in range(0, len(maps), 2)]
    rng.shuffle(vertices)
    words: list[Word] = []
    seen: set[Word] = set()
    for x in vertices:
        i = rng.randrange(len(maps))
        loop = simplify((*paths[x], i, *invert(paths[maps[i][x]])))
        if loop and loop not in seen and invert(loop) not in seen:
            words.append(loop)
            seen.add(loop)
        if len(words) == 32:
            break
    return words


def restrict(
    maps: Maps, ids: list[int], start: list[int]
) -> tuple[Maps, dict[int, int]]:
    labels = {ids[q] for q in start}
    local = {
        x: i for i, x in enumerate(x for x, label in enumerate(ids) if label in labels)
    }
    return [[local[p[x]] for x in local] for p in maps], local


def paired_maps(positive: Maps) -> Maps:
    return [p for g in positive for p in (g, inverse(g))]


class SampleMiss(Exception):
    """A sampled subgroup need not be the full stabilizer."""


def construct(
    maps: Maps, start: list[int], end: list[int], seed: int = 0
) -> tuple[list[list[Word]], list[Word]]:
    # Words at each level are recipes over generators of the previous level;
    # no enumeration of the 12-tuple orbit and no assumption that G is Sym.
    rng = Random(seed)
    levels: list[list[Word]] = []
    corrections: list[Word] = []
    state = start.copy()
    current = paired_maps(maps)
    for i, target in enumerate(end):
        paths = tree(current, target)
        if state[i] not in paths:
            raise SampleMiss(f"sampled subgroup misses target at slot {i}")
        word = invert(paths[state[i]])
        perm = realize(current, word)
        state = [perm[x] for x in state]
        need(state[: i + 1] == end[: i + 1], "previously matched slot moved")
        corrections.append(word)
        if i + 1 < len(end):
            positive = subgroup(current, paths, rng)
            levels.append(positive)
            current = paired_maps([realize(current, q) for q in positive])
    return levels, corrections


def replay(
    raw: Maps, levels: list[list[Word]], corrections: list[Word], start: list[int]
) -> tuple[list[int], int]:
    # Independent positive-only evaluator: inverse of *any* derived word is
    # the reversed recipe with each primitive inverse expanded to T^3.
    maps = [realize(raw, w) for w in ((0,), (0, 0, 0), (1,), (1, 1, 1))]
    costs = [1, 3, 1, 3]
    state = start.copy()
    total = 0
    need(len(levels) + 1 == len(corrections), "bad recipe levels")
    for i, step in enumerate(corrections):
        for j in step:
            state = [maps[j][s] for s in state]
            total += costs[j]
        if i < len(levels):
            words = [w for q in levels[i] for w in (q, invert(q))]
            maps = [realize(maps, w) for w in words]
            costs = [sum(costs[k] for k in w) for w in words]
    return state, total


def featured() -> None:
    maps = edges((1, 1, 5))
    counts = good_counts(components(maps), 1)
    need(Counter(counts) == {0: 4, 4: 10, 8: 14, 12: 36}, "featured orbit census")
    start, end = rows(0, 0, 0), rows(0, 0, 1)
    result, length = verify_blocks(maps, CERTIFICATE, start)
    need(result == end and length == 740471, "fixed certificate or pulse count")
    # Direct chronological application is cheap for the featured word. This
    # evaluator neither uses permutation powers nor chooses pulses by state.
    literal = "".join(q + w * k + rev(q) for q, w, k in CERTIFICATE)
    need(len(literal) == length, "bad expansion of native schedule")
    state = start.copy()
    for ch in literal:
        m = maps["AB".index(ch)]
        state = [m[x] for x in state]
    need(state == end, "literal native replay failed restoration")
    for raw, r, s in ((maps, 7, 7), (edges((3, 3, 3)), 0, 0)):
        out, _ = verify_blocks(raw, CERTIFICATE, rows(r, s, 0))
        need(
            all(x != y for x, y in zip(out, rows(r, s, 1), strict=True)),
            "wrong-stock/lift control",
        )
    print("fixed free=(1,1,5), raw refs=(8,0): 12/12 clean +1, 740471 literal pulses")
    print("wrong raw refs (15,7) or old free=(3,3,3): same word 0/12 clean +1")


def census(joint: bool) -> None:
    sizes: Counter[int] = Counter()
    joint_hits: Counter[int] = Counter()
    for f in product(ACTIVE, repeat=3):
        free = (f[0], f[1], f[2])
        maps = edges(free)
        ids = components(maps)
        counts = good_counts(ids, 1)
        nstocks = counts.count(12)
        sizes[nstocks] += 1
        nonzero = sum(t % 3 != 0 for t in free)
        need(nstocks == (0, 0, 24, 36)[nonzero], "individual stock classification")
        if not nstocks:
            need(max(counts) == 4, "three-cell wall")
            continue
        if not joint:
            continue
        r, s = divmod(counts.index(12), 8)
        a, b = rows(r, s, 0), rows(r, s, 1)
        local, ix = restrict(maps, ids, a)
        start, end = [ix[x] for x in a], [ix[x] for x in b]
        for seed in (0, 1):
            try:
                levels, steps = construct(local, start, end, seed)
            except SampleMiss:
                continue
            checked, _ = replay(local, levels, steps, start)
            need(checked == end, "joint forward-only replay failed")
            joint_hits[seed] += 1
            break
        else:
            raise RuntimeError(
                f"{free} has no certificate from these samples; unresolved"
            )
    need(sizes == {0: 56, 24: 96, 36: 64}, "single-row family census")
    print(
        "all 216 lifts x 64 stocks: individually 12/12 stocks per lift 0:56, 24:96, 36:64"
    )
    if joint:
        need(sum(joint_hits.values()) == 160, "joint lifts count")
        print(
            "per-lift common words: 160 verified; 56 excluded at every stock by point orbits"
        )


def main() -> None:
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--joint-census", action="store_true")
    args.add_argument("--rediscover", action="store_true")
    opts = args.parse_args()
    featured()
    census(opts.joint_census)
    if opts.rediscover:
        maps = edges((1, 1, 5))
        start, end = rows(0, 0, 0), rows(0, 0, 1)
        blocks = search_blocks(maps, start, end)
        reached, cost = verify_blocks(maps, blocks, start)
        need(reached == end, "cycle search replay")
        print("found common word before removing redundant T⁴ runs:", cost)


if __name__ == "__main__":
    main()
