"""Which mixed phase lifts can an occupation detector distinguish?

Assume the previous six-mark incidence h, simultaneous phase-translation
covariance, a relative half-turn, and the same square-to-wire-SWAP law. In
occupied/vacant coordinates the port update is j xor h(z), z=a-b. Squaring
to SWAP implies commuting with SWAP, so the tag update cannot depend on j.
Covariance makes the occupied increment a function g(z); the relative
half-turn forces the vacant increment to be g(z)-3. Squaring restores both
tags exactly iff g(z+3)=-g(z). Thus there are 6³ lifts of THIS ansatz. We
hold the existing raw completion fixed outside the active mixed sector.

Every lift gives the old fringe, shutter and control counts for the stated
stocks. This equivalence is for fresh *uniform* shutter tags (and the old
copied-tag control); it is not a claim about each individually labelled
dump. A discriminator uses the old source mixture without looking at paths:
close one arm with a prepared vacancy at a fixed offset from the source
origin. No plate is used. Compare per-emission left/right/loss counts for
both shutters, both source anchor conventions, and three reference offsets.
The reference and both preparations remain supplied; this is not a native
single-cell phase plate, a phase measurement, or a physical-law derivation.

Replay: python3 -B -m scripts.probe_vacuum_phase_lifts
"""

from collections import Counter
from itertools import product

from scripts import probe_six_phase_exclusive_packet as packet

Phase = tuple[int, ...]
Counts = tuple[int, int, int]
Kernel = tuple[Counts, ...]
ACTIVE, BIT, need = packet.ACTIVE, packet.BIT, packet.need


def lift(free: Phase) -> Phase:
    return (*free, *((-v) % 6 for v in free))


def complete(g: Phase) -> packet.Table:
    out = []
    for l, r in product(packet.RAW, repeat=2):
        if packet.n(l) == packet.n(r) or l % 8 >= 6 or r % 8 >= 6:
            out.append(packet.t(l, r))
            continue
        j = packet.n(r)
        a, b = (r % 8, l) if j else (l % 8, r)
        z = (a - b) % 6
        out.append(
            packet.mixed(j ^ (z in packet.WINDOW), (a + g[z]) % 6, (b + g[z] - 3) % 6)
        )
    return tuple(out)


def go(table: packet.Table, pair: packet.Pair) -> packet.Pair:
    return table[16 * pair[0] + pair[1]]


def check_raw(g: Phase, table: packet.Table) -> bool:
    need(len(set(table)) == 256, "raw gate is not invertible")
    conserved = True
    for l, r in product(packet.RAW, repeat=2):
        p, q = go(table, (l, r))
        need(go(table, (p, q)) == (r, l), "shutter is not a raw swap")
        pl, pr = packet.t(l, r)
        need(
            (packet.n(p), packet.n(q)) == (packet.n(pl), packet.n(pr)),
            "changed detector",
        )
        need(l != r or (p, q) == (l, r), "moved raw diagonal")
        conserved &= packet.stock(p) + packet.stock(q) == packet.stock(
            l
        ) + packet.stock(r)
    for j, a, b in product(BIT, ACTIVE, ACTIVE):
        old = packet.t(*packet.mixed(j, a, b))
        new = go(table, packet.mixed(j, a, b))
        # This single common rotation commutes with independent arm dials,
        # including a zero dial on the actual empty arm (empty-silent control).
        rot = g[(a - b) % 6] - 3
        need(
            new == (packet.dial(old[0], rot), packet.dial(old[1], rot)),
            "not a common shift",
        )
        path = packet.n(new[1])
        need((new[path] % 8 - new[1 - path] % 8 - a + b) % 6 == 3, "relative flip")
    return conserved


def ordinary_kernel(j: int, a: int, b: int) -> Kernel:
    arms = packet.mixed(j, a, b)
    rows: list[Counts] = []
    for mask in range(4):
        xs = [
            packet.trial(arms, mask, (left, right))
            for left, right in product(ACTIVE, repeat=2)
        ]
        rows.append((xs.count(0), xs.count(1), xs.count(2)))
    for open_port in BIT:
        copied = (arms[0] % 8, arms[1] % 8)
        x = packet.trial(arms, 1 << open_port, copied)
        rows.append((int(x == 0), int(x == 1), int(x == 2)))
    xs = [packet.trial(packet.mixed(j, a, (b + 3 * c) % 6), 3, (0, 0)) for c in BIT]
    rows.append((xs.count(0), xs.count(1), xs.count(2)))
    return tuple(rows)


def check_ordinary() -> None:
    # All completions have the same terminal occupation projection on every
    # raw pair and the same double-gate shutter. Hence this kernel applies
    # pointwise to each completion, even when both remaining arms are vacant.
    kernels = {
        (j, a, b): ordinary_kernel(j, a, b) for j, a, b in product(BIT, ACTIVE, ACTIVE)
    }
    for (j, a, b), row in kernels.items():
        for k in ACTIVE:
            need(row == kernels[j, (a + k) % 6, (b + k) % 6], "observable common shift")
    for a, k, x in product(ACTIVE, ACTIVE, ACTIVE):
        for occ in BIT:
            cell = 8 * occ + a
            need(
                packet.dial(packet.dial(cell, k), x)
                == packet.dial(packet.dial(cell, x), k),
                "rotation did not commute with a dial",
            )
    total = sum(
        packet.verify_setting(s, o, anchor, x, y)
        for s, o, anchor, x, y in product(BIT, ACTIVE, (False, True), ACTIVE, ACTIVE)
    )
    need(total == 995328, "reference stock count")


def fixed_reference(
    table: packet.Table, source: int, origin: int
) -> tuple[Counts, ...]:
    # Relay only the closed arm through the SAME gate twice, against the
    # prepared vacant reference. The stock is independent of each source
    # draw at fixed origin. No wire is chosen from an intermediate reading.
    rows = []
    for occupied_anchor, open_port, offset in product((True, False), (1, 0), range(3)):
        counts = [0, 0, 0]
        closed = 1 - open_port
        ref = (origin + offset) % 6
        for i, k, c in product(BIT, repeat=3):
            a, b = packet.register(
                origin, -1 + i + k + 3 * c, occupied_anchor=occupied_anchor
            )
            arms = list(go(table, packet.mixed(source, a, b)))
            arms[closed], dump = go(table, go(table, (arms[closed], ref)))
            left, right = go(table, (arms[0], arms[1]))
            dl, dr, lost = packet.n(left), packet.n(right), packet.n(dump)
            need(dl + dr + lost == 1, "incorrect exclusive observation")
            counts[0] += dl
            counts[1] += dr
            counts[2] += lost
        need(sum(counts) == 8 and counts[2] == 4, "lost the emission denominator")
        rows.append((counts[0], counts[1], counts[2]))
    return tuple(rows)


def main() -> None:
    packet.verify_table()
    check_ordinary()
    signatures = []
    coarse_preserving = []
    tables: set[packet.Table] = set()
    for free in product(ACTIVE, repeat=3):
        g = lift(free)
        table = complete(g)
        tables.add(table)
        if check_raw(g, table):
            coarse_preserving.append(free)
        signature = fixed_reference(table, 0, 0)
        for origin in ACTIVE:
            need(
                fixed_reference(table, 0, origin) == signature,
                "required an absolute origin",
            )
        signatures.append(signature)
    need(len(tables) == 216 and complete(lift((3, 3, 3))) == packet.TABLE, "census")
    need(coarse_preserving == list(product((0, 3), repeat=3)), "old coarse-count wall")
    occupied = Counter(s[:6] for s in signatures)
    vacant = Counter(s[6:] for s in signatures)
    need(
        len(occupied) == 85 and Counter(vacant.values()) == {1: 204, 2: 6},
        "anchor controls",
    )
    need(len(set(signatures)) == 216, "reference experiment missed a lift")
    need(
        len({s[::3] for s in signatures}) == 37,
        "zero-offset reference should not identify the whole family",
    )
    zero = fixed_reference(complete(lift((0, 0, 0))), 0, 0)
    old = fixed_reference(packet.TABLE, 0, 0)
    need((zero[0], old[0]) == ((4, 0, 4), (0, 4, 4)), "zero-offset countercontrol")
    # A sufficient subset of the twelve measured settings, not a
    # minimality assertion. No outcomes or source draws are discarded.
    selected = (0, 1, 2, 6, 7, 9, 10)
    need(
        len({tuple(s[i] for i in selected) for s in signatures}) == 216,
        "seven settings",
    )
    # On mixed active encounters the relative half-turn preserves a-b mod 3:
    # signed total phase mod 3 therefore blocks a clean unit shift with
    # restored stock in mixed-only active words. Even a logical vacuum-vacuum
    # encounter can violate that invariant in the common raw completion.
    need(packet.t(0, 1) == (0, 2), "homogeneous boundary witness")
    print(
        "216 distinct square-to-SWAP lifts; all retain the old fringe, shutter and control counts."
    )
    print(
        "Fixed reference, no plates: occupied-anchor 85 classes; vacant-anchor 210; together 216."
    )
    print(
        "Offset zero alone: 37 classes; g=0 vs g=3 give (4,0,4) vs (0,4,4) in the first row."
    )
    print(
        "Seven of twelve settings suffice; every row counts all eight emissions, four lost."
    )
    print(
        "All 216 block a clean +1 using only active mixed collisions + routing with restored stock."
    )
    print(
        "Eight retain the original raw coarse-count obstruction; no full native plate is certified."
    )


if __name__ == "__main__":
    main()
