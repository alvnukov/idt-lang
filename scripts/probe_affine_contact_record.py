"""Physical memory for one finite contact gate; no endogenous detector claim.

Each cell has a color c in F5 and a memory z in {0,1,2,3}. Choose two
diagonal-fixing permutation roots H of wire swap on memory pairs. A
contact applies the original color pulse and the H selected by input
color equality. Equality is unchanged by the pulse, so the whole gate
squares to raw wire swap. Both branches use *the same gate* at every
stage. The dependence on equality and the chosen H tables are supplied.

Search universe: three signal cells, one or two extra background cells
initially marked 1, every positive pair-address word of length 0..3,
and every single output wire. A canonical hit means raw 1 in phases
0,1,2 and raw 0 in phases 3,4,5, with no decoder. Reversal of the labels
and other two-value hits are counted separately from canonical hits.
Addresses are fixed edges, not coordinates. An example using just the
line edges is also checked. A longer construction uses two extra blank
cells to retain a copy and rewind the whole input; no minimality claim
is made for that construction.

The clean-rewind witness fixes all memory diagonals. Writing xy for
the ordered memory pair (x,y), its two branch tables in cycle notation:
equal   (01 12 10 21)(02 13 20 31)(03 23 30 32);
unequal (01 02 10 20)(03 21 30 12)(13 23 31 32).

All preparations, addressing, schedule, four-label memory, equality
coupling and interpretation remain inputs. No fair source, Born rule,
physical click, detector origin, or observed particle follows.
Replay: python3 -B -m scripts.probe_affine_contact_record  (also with -O).
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field
from itertools import combinations, product

from scripts.probe_affine_contact_fringe import Six, cycle, need

Pair = tuple[int, int]
Word = tuple[Pair, ...]
Root = tuple[int, ...]  # row-major: 4*left + right -> packed output pair
Wire = tuple[int, int]  # color, memory
Scene = tuple[Wire, ...]
Term = tuple[bool, int, int]
Terms = list[Term]
Sources = tuple[int, ...]
WRITE: Word = ((0, 3), (2, 3), (0, 2))
COPY: Word = ((0, 4), (4, 5), (0, 5), (0, 4), (0, 5))
LINE: Word = ((0, 1), (2, 3), (1, 2))
TARGET = (1, 1, 1, 0, 0, 0)


def colors(x: int, y: int, reverse: bool = False) -> Pair:
    a, b = (4 * x + 2 * y) % 5, (2 * x + 4 * y) % 5
    return (b, a) if reverse else (a, b)


def swap(index: int) -> int:
    return 4 * (index % 4) + index // 4


def matching_roots(edges: tuple[int, ...], table: Root) -> Iterator[Root]:
    # An off-diagonal 2-cycle of SWAP must be paired with one other
    # 2-cycle to form a 4-cycle of H; each pairing has two orientations.
    if not edges:
        yield table
        return
    a = edges[0]
    for k in range(1, len(edges)):
        for b in (edges[k], swap(edges[k])):
            t = list(table)
            t[a], t[b], t[swap(a)], t[swap(b)] = b, swap(a), swap(b), a
            yield from matching_roots(edges[1:k] + edges[k + 1 :], tuple(t))


def all_roots() -> tuple[Root, ...]:
    for q in (2, 3):
        need((q * (q - 1) // 2) % 2 == 1, "odd SWAP cannot be a permutation square")
    edges = tuple(4 * i + j for i, j in combinations(range(4), 2))
    roots = tuple(matching_roots(edges, tuple(range(16))))
    need(len(roots) == len(set(roots)) == 120, "incomplete root list")
    for t in roots:
        need(all(t[t[j]] == swap(j) for j in range(16)), "not a root")
        need(all(t[5 * j] == 5 * j for j in range(4)), "changed diagonal")
    return roots


def apply(s: Scene, word: Word, eq: Root, ne: Root, reverse: bool = False) -> Scene:
    v = list(s)
    for i, j in word:
        (x, u), (y, w) = v[i], v[j]
        a, b = colors(x, y, reverse)
        z = (eq if x == y else ne)[4 * u + w]
        v[i], v[j] = (a, z // 4), (b, z % 4)
    return tuple(v)


@dataclass
class Pool:
    # IDs 0,1 are the two prepared raw labels. Higher IDs are expressions
    # for one wire. H commutes with SWAP (SWAP=H²), hence H(v,u).left
    # supplies the right output of H(u,v). No independence approximation.
    terms: Terms = field(default_factory=list)
    ids: dict[Term, int] = field(default_factory=dict)

    def child(self, eq: bool, left: int, right: int) -> int:
        if left == right:
            return left  # all four diagonal pairs fixed
        key = (eq, left, right)
        if key not in self.ids:
            self.ids[key] = len(self.terms) + 2
            self.terms.append(key)
        return self.ids[key]


def candidates(n: int) -> tuple[Terms, list[tuple[int, Sources]]]:
    orbit = cycle((0, 1, 0), Six)
    pairs = tuple(combinations(range(n), 2))
    pool = Pool()
    wanted: list[tuple[int, Sources]] = []
    for depth in range(4):
        for word in product(pairs, repeat=depth):
            rows: list[list[int]] = []
            for s in orbit:
                c = [*s, *([0] * (n - 3))]
                z = [0, 0, 0, *([1] * (n - 3))]
                for i, j in word:
                    yes = c[i] == c[j]
                    c[i], c[j] = colors(c[i], c[j])
                    u, v = z[i], z[j]
                    z[i], z[j] = pool.child(yes, u, v), pool.child(yes, v, u)
                rows.append(z)
            for k, sig in enumerate(zip(*rows)):
                # Identical formal expressions have identical raw outputs
                # for every root pair. Different expressions are NOT assumed
                # distinguishable: they are evaluated on each actual pair.
                if set(sig[:3]).isdisjoint(sig[3:]):
                    need(depth == 3, "a shorter candidate needs evaluation")
                    wanted.append((k, sig))
    used = {v for _, sig in wanted for v in sig} | {0, 1}
    for k in reversed(range(len(pool.terms))):
        if k + 2 in used:
            _, left, right = pool.terms[k]
            used.update((left, right))
    remap = {old: new for new, old in enumerate(sorted(used))}
    compact = [
        (eq, remap[u], remap[v])
        for k, (eq, u, v) in enumerate(pool.terms, 2)
        if k in used
    ]
    return compact, [(k, tuple(remap[t] for t in sig)) for k, sig in wanted]


def census(n: int, roots: tuple[Root, ...]) -> tuple[int, ...]:
    terms, wanted = candidates(n)
    any_hits = canonical = flipped = any_gates = canonical_gates = ready_hits = 0
    for ei, eq in enumerate(roots):
        for ui, ne in enumerate(roots):
            values = [0, 1]
            for yes, u, v in terms:
                values.append((eq if yes else ne)[4 * values[u] + values[v]] // 4)
            some = exact = False
            for k, (i, j, h, l, m, o) in wanted:
                a, b = values[i], values[l]
                if not (
                    a != b
                    and a == values[j] == values[h]
                    and b == values[m] == values[o]
                ):
                    continue
                need(ei != ui, "uncontrolled memory wrote phase")
                any_hits += 1
                some = True
                if (a, b) == (1, 0):
                    canonical += 1
                    exact = True
                    ready_hits += int(k >= 3)
                flipped += int((a, b) == (0, 1))
            any_gates += int(some)
            canonical_gates += int(exact)
    return (
        len(wanted),
        any_hits,
        canonical,
        flipped,
        any_gates,
        canonical_gates,
        ready_hits,
    )


def inverse(t: Root) -> Root:
    return tuple(t.index(i) for i in range(16))


def row(
    eq: Root, ne: Root, word: Word, k: int, reverse: bool = False
) -> tuple[int, ...]:
    s: Scene = ((0, 0), (1, 0), (0, 0), (0, 1))
    w: Word = tuple((i, i + 1) for i in Six)
    result = []
    for _ in range(6):
        result.append(apply(s, word, eq, ne, reverse)[k][1])
        s = apply(s, w, eq, ne, reverse)
    return tuple(result)


def witnesses(roots: tuple[Root, ...]) -> None:
    eq, ne = roots[52], roots[2]
    need(row(eq, ne, WRITE, 0) == TARGET, "raw writer")
    need(row(roots[100], roots[36], LINE, 1) == TARGET, "line-neighbor writer")
    cells = tuple(product(range(5), range(4)))
    for left, right in product(cells, repeat=2):
        need(
            apply((left, right), ((0, 1),) * 2, eq, ne) == (right, left),
            "expanded gate square",
        )
    for x, y in product(range(5), repeat=2):
        need(
            apply(((x, 0), (y, 0)), ((0, 1),), eq, ne)
            == tuple((c, 0) for c in colors(x, y)),
            "ordinary pulse disturbed",
        )
    need(
        row(eq, eq, WRITE, 0) == (1,) * 6 and row(ne, ne, WRITE, 0) == (0,) * 6,
        "color-independent branch control",
    )
    need(
        row(inverse(eq), ne, WRITE, 0) == (2, 0, 2, 0, 0, 2),
        "equal orientation control",
    )
    need(
        row(eq, inverse(ne), WRITE, 0) == (1, 0, 3, 1, 1, 1),
        "unequal orientation control",
    )
    need(row(eq, ne, WRITE, 0, True) == (1, 1, 0, 0, 1, 0), "color orientation control")

    # Copier contract is independent of the six-state orbit. Keep the raw
    # source (including color); export the same bit into a blank cell.
    copy_ports = {0: 0, 4: 1, 5: 2}
    small_copy = tuple((copy_ports[i], copy_ports[j]) for i, j in COPY)
    for x, b, bit in product(range(5), range(5), range(2)):
        start = ((x, bit), (b, 0), (b, 0))
        projected = apply(start, small_copy, eq, ne)
        need(
            projected == ((x, bit), (b, (3 if x == b else 2) * bit), (b, bit)),
            "copy contract",
        )
    undo = tuple(edge for edge in reversed(WRITE) for _ in range(3))
    new_ports = {0: 0, 4: 6, 5: 7}
    repeat_copy = tuple((new_ports[i], new_ports[j]) for i, j in COPY)
    for a, b in product(range(5), repeat=2):
        if a == b:
            continue
        for s, bit in zip(cycle((b, a, b), Six), TARGET, strict=True):
            initial = tuple((x, 0) for x in s) + ((b, 1),)
            data = initial + ((b, 0),) * 4
            first = apply(data, WRITE + COPY + undo, eq, ne)
            need(first[:4] == initial and first[5] == (b, bit), "record lost on rewind")
            second = apply(first, WRITE + repeat_copy + undo, eq, ne)
            need(second[:6] == first[:6] and second[7] == first[5], "repeat failed")


def main() -> None:
    roots = all_roots()
    witnesses(roots)
    for n, expected in (
        (4, (20, 10782, 1450, 2840, 5164, 1370, 0)),
        (5, (72, 21564, 2900, 5680, 5164, 1370, 0)),
    ):
        actual = census(n, roots)
        need(actual == expected, f"census changed: {actual!r}")
        print(
            f"{n} wires: shortest 3; {actual[1]} two-label tuples, "
            f"{actual[2]} canonical (1 bright/0 dark) on {actual[5]} gate pairs; "
            f"{actual[6]} canonical tuples end on an initially ready wire."
        )
    print(
        "120 diagonal-fixing roots, 14,280 unequal ordered branch pairs; Q=2,3 fail swap parity."
    )
    print(
        "Raw writer 03,23,02 on wire 0; alternative line writer 01,23,12 on wire 1: 111000."
    )
    print(
        "One ready + two blank cells: five-contact copier, then rewind; 17 contacts restore all"
    )
    print(
        "four original cells and retain a raw bit at background color. Fresh blanks repeat the record."
    )
    print(
        "Finite engineered memory: color-equality coupling, preparation, ports, clock and meaning supplied."
    )


if __name__ == "__main__":
    main()
