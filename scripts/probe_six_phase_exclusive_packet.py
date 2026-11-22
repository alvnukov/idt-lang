"""Six-setting interference and exclusive clicks in one finite reversible toy.

Each cell carries an occupation bit and a tag. On logical mixed inputs write
(j,a,b) for the occupied port, its tag, and the vacant tag. The SAME coupler
at both ends sends this to (j xor h(a-b), a+3, b), with h the incidence of
three consecutive marks on Z/6. Hence two couplers swap both raw cells.
Shutters are that double coupler against separate prepared vacancies. On the
full 16-label domain the homogeneous sectors need a separate square root of
swap; six or seven tags per occupation cannot suffice. The two spare tags
per occupation are real raw states; they are not part of the logical dial.

Write u=-1+i+k for two independent fair bits i,k. A third fair bit c gives
source relative tag a-b=u+3c. Since h(u)=1, j=source xor 1 xor c after the
first interaction, independently of u. With local shifts x,y and both arms
open, the final click is opposite the source iff h(u+(-1)^j (x-y))=1.
Thus the six rates come from the prior three-mark window and 1:2:1 stock,
not a setting-indexed random detector. Choosing the initial occupied or
vacant tag as a fixed origin is allowed. No path measurement is performed.
For an empty-silent local dial varied after a fair split, couple the two
settings with the same source and instrument randomness: the half visiting
the other arm is unchanged if there is no other channel for the dial choice.
A deterministic endpoint switch on a single arm requires a unit change.

The independent local dial shifts are SUPPLIED, not outputs of the coupler.
In fact the chosen raw completion conserves an additive coarse tag count,
excluding a clean +1 implemented with any number of exactly restored cells.
That wall applies to this completion; six logical marks, the preparation,
shutter stock and occupation detector are also supplied. This is neither a
microscopic particle model nor a derivation of a quantum law.

Replay: python3 -B -O -m scripts.probe_six_phase_exclusive_packet
"""

from itertools import combinations, product
from math import comb

Pair = tuple[int, int]
Table = tuple[Pair, ...]
TAGS = range(8)
ACTIVE = range(6)
RAW = range(16)
BIT = range(2)
WINDOW = frozenset((5, 0, 1))
COARSE = frozenset((0, 3, 6, 7))
QUARTERS = (4, 3, 1, 0, 1, 3)  # Benchmark used only by the checks.


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def n(cell: int) -> int:
    return cell // 8


def stock(cell: int) -> int:
    return int(cell % 8 in COARSE)


def opposite(a: int) -> int:
    return (a + 3) % 6 if a < 6 else 13 - a


def cross(a: int, b: int) -> bool:
    # Arbitrary extension on padded inputs, respecting h(F(a),b) = 1-h(a,b).
    return (a - b % 6) % 6 in WINDOW if a < 6 else a == 6


def mixed(j: int, a: int, b: int) -> Pair:
    return (b, 8 + a) if j else (8 + a, b)


def homogeneous() -> Table:
    # Pair disjoint SWAP transpositions, not necessarily disjoint tag values.
    # Splitting by coarse count deliberately makes a clean-plate wall testable.
    table = [(a, b) for a in TAGS for b in TAGS]
    for k in range(3):
        edges = [(a, b) for a, b in combinations(TAGS, 2) if stock(a) + stock(b) == k]
        for p, q in zip(edges[::2], edges[1::2], strict=True):
            cycle = (p, q, p[::-1], q[::-1])
            for (a, b), image in zip(cycle, (*cycle[1:], cycle[0]), strict=True):
                table[8 * a + b] = image
    return tuple(table)


def build() -> Table:
    local = homogeneous()
    out = []
    for l, r in product(RAW, repeat=2):
        if n(l) == n(r):
            a, b = local[8 * (l % 8) + r % 8]
            out.append((8 * n(l) + a, 8 * n(r) + b))
        else:
            j = n(r)
            a, b = (r % 8, l) if j else (l % 8, r)
            out.append(mixed(j ^ cross(a, b), opposite(a), b))
    return tuple(out)


TABLE = build()


def t(l: int, r: int) -> Pair:
    return TABLE[16 * l + r]


def dial(cell: int, shift: int) -> int:
    tag = cell % 8
    return 8 * n(cell) + (tag + shift) % 6 if tag < 6 else cell


def verify_table() -> None:
    need(len(set(TABLE)) == 256, "raw gate is not a bijection")
    for a, b in product(TAGS, repeat=2):
        need(opposite(opposite(a)) == a and opposite(a) != a, "bad antipodes")
        need(cross(opposite(a), b) != cross(a, b), "bad padded incidence law")
    for l, r in product(RAW, repeat=2):
        p, q = t(l, r)
        need(t(p, q) == (r, l), "T² is not raw swap")
        need(n(p) + n(q) == n(l) + n(r), "T changed total occupation")
        need(stock(p) + stock(q) == stock(l) + stock(r), "T changed coarse tag count")
        if l == r:
            need((p, q) == (l, r), "equal cells not fixed")
    need(
        any(max(t(l, r)) >= 6 for l, r in product(ACTIVE, repeat=2)),
        "unexpected closed six-tag homogeneous sector",
    )
    for step in ACTIVE:
        need({dial(cell, step) for cell in RAW} == set(RAW), "dial not reversible")
        for cell in RAW:
            need(n(dial(cell, step)) == n(cell), "dial changed occupation")
    # Necessary parity per conserved sector; the full table above attains 8+8.
    admissible = [
        (d0, d1)
        for d0 in range(6, 11)
        for d1 in range(6, 17 - d0)
        if all(k % 2 == 0 for k in (comb(d0, 2), d0 * d1, comb(d1, 2)))
    ]
    need(admissible == [(8, 8)], "incorrect minimum up to total size sixteen")


def swapped(l: int, d: int) -> Pair:
    return t(*t(l, d))


def trial(arms: Pair, opened: int, dump: Pair) -> int:
    """Return 0/1 for a click, 2 for loss. Never inspect tags at the detector."""
    path = n(arms[1])
    l, r = arms
    d0, d1 = dump
    if not opened & 1:
        l, d0 = swapped(l, d0)
    if not opened & 2:
        r, d1 = swapped(r, d1)
    left, right = t(l, r)  # Even when both modes are empty.
    dl, dr, losses = n(left), n(right), (n(d0), n(d1))
    need(dl + dr + sum(losses) == 1, "lost or duplicated emission")
    need(
        losses[path] == int(not opened & (1 << path)) and losses[1 - path] == 0,
        "wrong dump holds the occupation",
    )
    return 0 if dl else 1 if dr else 2


def register(a: int, b: int, *, occupied_anchor: bool) -> Pair:
    """a is a fixed absolute origin; b is the prepared relative tag."""
    return (a, (a - b) % 6) if occupied_anchor else ((a + b) % 6, a)


def verify_setting(source: int, origin: int, anchor: bool, x: int, y: int) -> int:
    quarters = QUARTERS[(x - y) % 6]
    # Masks use bits 0 and 1 for open left/right respectively. Every dump pair
    # is counted, including a dump unused at this setting; no survival filter.
    rows = [[0, 0, 0] for _ in range(4)]
    paths = [0, 0]
    bright = [0, 0]
    erased = silent = 0
    recycled = [[0, 0, 0] for _ in range(2)]
    for i, k, c in product(BIT, repeat=3):
        u = -1 + i + k
        a, b = register(origin, u + 3 * c, occupied_anchor=anchor)
        j = source ^ 1 ^ c
        first = t(*mixed(source, a, b))
        need(first == mixed(j, (a + 3) % 6, b), "incorrect first trajectory")
        paths[j] += 1
        arms = dial(first[0], x), dial(first[1], y)
        need(n(arms[j]) == 1 and n(arms[1 - j]) == 0, "dial moved occupation")
        full = trial(arms, 3, (0, 0))
        sign = 1 if j == 0 else -1
        need((full != source) == ((u + sign * (x - y)) % 6 in WINDOW), "wrong route")
        bright[j] += full != source
        # Negative control 1: random antipodal kick to the ACTUAL empty tag.
        for coin in BIT:
            randomized = list(arms)
            randomized[1 - j] = dial(randomized[1 - j], 3 * coin)
            erased += trial((randomized[0], randomized[1]), 3, (0, 0)) != source
        # Negative control 2: no action at all on the empty arm.
        frozen = mixed(j, arms[j] % 8, first[1 - j])
        silent += trial(frozen, 3, (0, 0)) != source
        for open_path in BIT:
            # Negative control 3: prepare the closed arm's dump from its OLD
            # tag. The shutter itself is unchanged; only the dump stock differs.
            reused = arms[0] % 8, arms[1] % 8
            recycled[open_path][trial(arms, 1 << open_path, reused)] += 1
        for d0, d1 in product(ACTIVE, repeat=2):
            for mask in range(4):
                rows[mask][trial(arms, mask, (d0, d1))] += 1
    need(paths == [4, 4] and bright == [quarters, quarters], "path-conditioned counts")
    per_mask = 8 * 36
    opposite_port = 1 - source
    need(
        rows[3][opposite_port] == quarters * (per_mask // 4)
        and rows[3][source] + rows[3][opposite_port] == per_mask,
        "full fringe",
    )
    need(rows[0] == [0, 0, per_mask], "both closed are not dark")
    need(rows[1] == rows[2] == [72, 72, 144], "singleton shutter counts per emission")
    need(erased == 8, "erasing the empty phase did not flatten the fringe")
    need(silent == QUARTERS[x] + QUARTERS[y], "wrong empty-silent control")
    for row in recycled:
        need(
            row[opposite_port] == quarters
            and row[source] == 4 - quarters
            and row[2] == 4,
            "wrong recycled singleton counts",
        )
        need(row != [2, 2, 4], "recycling unexpectedly retained the singleton split")
    return sum(sum(row) for row in rows)


def verify_plate_wall() -> None:
    # A conserved sum stays fixed under any word, wiring permutation and
    # exactly restored auxiliaries. One witness in either occupation suffices.
    for cell in (0, 8):
        need(stock(dial(cell, 1)) != stock(cell), "no clean +1 obstruction")
    # Independently, with only vacuum auxiliaries, the unique occupied tag
    # can never leave its opposite-pair orbit, even when pad vacancies occur.
    for a, b, j in product(TAGS, TAGS, BIT):
        pair = t(*mixed(j, a, b))
        need(pair[n(pair[1])] == 8 + opposite(a), "occupied tag escaped its orbit")


def main() -> None:
    verify_table()
    trials = sum(
        verify_setting(s, g, anchor, x, y)
        for s, g, anchor, x, y in product(BIT, ACTIVE, (False, True), ACTIVE, ACTIVE)
    )
    need(trials == 995328, "some raw cases were skipped")
    verify_plate_wall()
    print(
        "16 raw labels; 256 pairs: bijection, fixed diagonals, occupation conservation, T²=swap."
    )
    print(
        f"{trials} enumerated emission histories: both ports/anchors, all origins/dials/masks/dumps."
    )
    print(
        "Opposite-port quarters (4,3,1,0,1,3); either path alike; no intermediate readout."
    )
    print("Either shutter alone: (left,right,lost)=(1/4,1/4,1/2); both shut: (0,0,1).")
    print(
        "Fair antipodal kick to the empty tag: flat. Recycled shutter tag: half the original fringe."
    )
    print(
        "Empty-silent dials: changing one dial can affect at most the half visiting that arm;"
    )
    print(
        "the full open-arm fringe requires a unit endpoint swing. The +1 dial is supplied;"
    )
    print(
        "the chosen raw table forbids synthesizing it with exactly restored auxiliary cells."
    )


if __name__ == "__main__":
    main()
