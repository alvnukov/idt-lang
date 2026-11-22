"""Does an occupation-preserving square root of wire swap choose an absolute phase?

This is a finite resource question, not an assertion that the universe applies
this gate. On either homogeneous sector (two occupied or two empty cells)
let S be the tag alphabet, W(a,b)=(b,a), and demand T²=W on *all* raw pairs.
A successful logical fringe need not make T covariant. If naming a common
phase origin is pure convention, test the additional raw requirement
T(Ra,Rb)=(R,R)T(a,b) for an R of order six with an actual six-cycle.

The ordered antipodes (a,R³a) on each six-cycle form a free diagonal orbit
on which W is just R³. T commutes with W and R, so permutes these orbits.
A T-invariant one would require 2k=3 mod 6, impossible. They must pair;
one six-cycle plus up to five spare tags cannot work, irrespective of how R
permutes the spares. Two six-cycles suffice below. The extra sheet need not
be unobservable or exchangeable. No lattice or spacetime is presupposed.

Stronger optional symmetry: S is a finite abelian group K acting regularly
on itself by translations, including one of order six. A covariant T is
(a,a+d) -> (a+j(d), a+j(d)+t(d)). Hence t²(d)=-d and j(d)+j(t(d))=d.
If 2d=0, then t²(d)=d; comparing the last equation at d and t(d) forces
t(d)=d (commutativity is used), so d must have a half in K. The pairs
{d,-d} with d != -d must also occur in even number for inversion to have
a permutation square root. Conversely take a half for each involution and
interlace negative pairs in fours using the offsets below. These conditions
are sufficient, and the diagonal inputs can be fixed.

To obtain order six the odd part has size at least three. In the 2-primary
part every cyclic factor must have order divisible by four, otherwise its
order-two element has no half. With just one such factor, K has order 0
mod 4 and exactly two self-inverse elements: (|K|-2)/2 is odd. Therefore
at least two factors are needed, of total size at least 16. The size-48
example Z/12 x Z/4 attains the bound. This is NOT a claim about arbitrary
transitive/nonabelian actions, raw gates that do not square to W, or an
empirical minimal phase space. The algebraic argument is not a Lean proof.

Run: python3 -B -O -m scripts.probe_phase_frame_covariance
"""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from itertools import product
from math import lcm, prod

Tag = tuple[int, ...]
Pair = tuple[int, int]
Gate = dict[Pair, Pair]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rotate(s: tuple[int, ...], x: Pair) -> Pair:
    return s[x[0]], s[x[1]]


def orbit(s: tuple[int, ...], x: Pair) -> tuple[Pair, ...]:
    entries = [x]
    nxt = rotate(s, x)
    while nxt != x:
        entries.append(nxt)
        nxt = rotate(s, nxt)
    return tuple(entries)


def rotation(lengths: Sequence[int]) -> tuple[int, ...]:
    r: list[int] = []
    for length in lengths:
        start = len(r)
        r.extend(start + (i + 1) % length for i in range(length))
    return tuple(r)


def equivariant_root(r: tuple[int, ...]) -> Gate | None:
    """Construct a square root orbit by orbit, including previously unseen layouts."""
    elements = set(product(range(len(r)), range(len(r))))
    require(set(r) == set(range(len(r))), "not a tag permutation")
    index: dict[Pair, tuple[Pair, ...]] = {}
    while elements:
        o = orbit(r, min(elements))
        elements.difference_update(o)
        index.update((x, o) for x in o)
    seen: set[Pair] = set()
    swapped: dict[int, list[Pair]] = {}
    no_half: dict[tuple[int, int], list[Pair]] = {}
    result: Gate = {}
    for x in sorted(index):
        if x in seen:
            continue
        a, b = index[x], index[x[::-1]]
        seen.update(a)
        seen.update(b)
        if a != b:
            swapped.setdefault(len(a), []).append(x)
            continue
        shift = a.index(x[::-1])  # x is the lexicographic orbit base.
        halves = [k for k in range(len(a)) if 2 * k % len(a) == shift]
        if halves:
            for i, v in enumerate(a):
                result[v] = a[(i + halves[0]) % len(a)]
        else:
            no_half.setdefault((len(a), shift), []).append(x)
    if any(len(v) % 2 for v in (*swapped.values(), *no_half.values())):
        return None
    for group in swapped.values():
        for x, y in zip(group[::2], group[1::2], strict=True):
            for v, w in zip(orbit(r, x), orbit(r, y), strict=True):
                result[v], result[w] = w, v[::-1]
                result[v[::-1]], result[w[::-1]] = w[::-1], v
    for group in no_half.values():
        for x, y in zip(group[::2], group[1::2], strict=True):
            for v, w in zip(orbit(r, x), orbit(r, y), strict=True):
                result[v], result[w] = w, v[::-1]
    require(len(result) == len(index), "incomplete equivariant root")
    return result


def check_raw(gate: Gate, generators: Sequence[tuple[int, ...]]) -> None:
    require(set(gate) == set(gate.values()), "raw map not bijective")
    for x, y in gate.items():
        require(gate[y] == x[::-1], "square is not wire swap")
        if x[0] == x[1]:
            require(x == y, "diagonal altered")
        for g in generators:
            require(gate[rotate(g, x)] == rotate(g, y), "frame dependence")


def abelian_root(moduli: tuple[int, ...]) -> tuple[Gate, list[tuple[int, ...]]] | None:
    tags = list(product(*(range(n) for n in moduli)))
    where = {x: i for i, x in enumerate(tags)}
    zero = tags[0]

    def add(x: Tag, y: Tag) -> Tag:
        return tuple((a + b) % n for a, b, n in zip(x, y, moduli, strict=True))

    def neg(x: Tag) -> Tag:
        return tuple(-a % n for a, n in zip(x, moduli, strict=True))

    offsets: dict[Tag, tuple[Tag, Tag]] = {}
    representatives = [d for d in tags if d < neg(d)]
    if len(representatives) % 2:
        return None
    for d in tags:
        if d == neg(d):
            half = next((j for j in tags if add(j, j) == d), None)
            if half is None:
                return None
            offsets[d] = half, d
    for d, e in zip(representatives[::2], representatives[1::2], strict=True):
        offsets[d] = zero, e
        offsets[e] = d, neg(d)
        offsets[neg(d)] = add(e, neg(d)), neg(e)
        offsets[neg(e)] = neg(e), d
    gate: Gate = {}
    for a, d in product(tags, repeat=2):
        j, t = offsets[d]
        b = add(a, j)
        gate[where[a], where[add(a, d)]] = where[b], where[add(b, t)]
    generators = []
    for i, n in enumerate(moduli):
        unit = tuple(int(j == i) % m for j, m in enumerate(moduli))
        require(n >= 2, "trivial factor not needed")
        generators.append(tuple(where[add(x, unit)] for x in tags))
    return gate, generators


def invariant_factors(limit: int, previous: int = 1) -> Iterator[tuple[int, ...]]:
    """All invariant-factor decompositions of orders <= limit, no isomorphic duplicates."""
    for n in range(max(2, previous), limit + 1):
        if n % previous == 0:
            yield (n,)
            for rest in invariant_factors(limit // n, n):
                yield (n, *rest)


def check_mixed(r: tuple[int, ...], homogeneous: Gate) -> None:
    """One full occupation-preserving gate on 24 labels, not just a homogeneous witness."""
    n = len(r)
    require(r == rotation((6, 6)), "wrong tag action")

    def gate(x: Pair) -> Pair:
        left, right = x
        ol, a = divmod(left, n)
        rr, b = divmod(right, n)
        if ol == rr:
            y, z = homogeneous[a, b]
            return ol * n + y, rr * n + z
        j = 1 - ol
        if j:
            a, b = b, a
        turn = (a - b) % 6 in (5, 0, 1)
        occupied = n + 6 * (a // 6) + (a + 3) % 6
        return (b, occupied) if j ^ turn else (occupied, b)

    rot = r + tuple(n + k for k in r)
    for x in product(range(2 * n), range(2 * n)):
        y = gate(x)
        require(gate(y) == x[::-1], "wrong full raw square")
        require(sum(k // n for k in x) == sum(k // n for k in y), "lost occupation")
        require(gate(rotate(rot, x)) == rotate(rot, y), "mixed frame failed")


def main() -> None:
    from scripts.probe_six_phase_exclusive_packet import t as old_coupler

    small = 0
    for twos, threes, ones in product(range(3), range(2), range(6)):
        lengths = (6, *((2,) * twos), *((3,) * threes), *((1,) * ones))
        if sum(lengths) >= 12:
            continue
        small += 1
        require(equivariant_root(rotation(lengths)) is None, "small alphabet escape")
    r = rotation((6, 6))
    gate = equivariant_root(r)
    if gate is None:
        raise ValueError("twelve-tag witness missing")
    check_raw(gate, [r])
    check_mixed(r, gate)
    # Original padding is sufficient for swap but at least one raw pair
    # witnesses failure of diagonal +1 on its operating tags with fixed spares.
    old_r = rotation((6, 1, 1))
    old_raw = {x: old_coupler(*x) for x in product(range(8), range(8))}
    mismatches = [
        x
        for x in sorted(old_raw)
        if old_raw[rotate(old_r, x)] != rotate(old_r, old_raw[x])
    ]
    require(bool(mismatches), "old raw completion unexpectedly origin free")
    # On the two same-sheet antipodal orbits a root exchanges sheets with
    # offsets s0,s1 summing to 3 mod 6; they cannot be equal. An occupancy
    # detector alone cannot notice any of these twelve raw discrepancies.
    sheet = tuple((i + 6) % 12 for i in range(12))
    antipodes = [(i, 6 * (i // 6) + (i + 3) % 6) for i in range(12)]
    require(
        all(gate[rotate(sheet, x)] != rotate(sheet, gate[x]) for x in antipodes),
        "unexpected additional raw sheet symmetry",
    )
    good = []
    tested = 0
    for factors in invariant_factors(48):
        if lcm(*factors) % 6:
            continue
        tested += 1
        root = abelian_root(factors)
        if root is not None:
            check_raw(*root)
            good.append(factors)
    require(good == [(4, 12)] and prod(good[0]) == 48, "wrong abelian minimum")
    print(
        f"Diagonal C6: {small} sub-12 layouts impossible; two six-cycles pass on all 24² full pairs."
    )
    print(
        f"Original 8-tag homogeneous table: {len(mismatches)} covariance mismatches; first {mismatches[0]}."
    )
    print(
        "Twelve-tag escape: all 12 same-sheet antipodal pairs witness raw sheet-exchange failure."
    )
    print(
        f"Regular abelian relabelings: {tested} group types through 48; first witness Z4 x Z12."
    )
    print(
        "Raw covariance is an extra condition; no native phase shifter, physical minimum or status change."
    )


if __name__ == "__main__":
    main()
