"""Exact finite-stock reachability of individual +1 transitions of 216 raw gates.

The reaction for T(l,r)=(p,q) is e_p+e_q-e_l-e_r in Z^16. Any word with
restored stock gives an integer sum of these, on arbitrary pairs of wires.
Conversely, for a *known* input, expand an integer witness into forward and
reverse reactions (T^-1=T³). Stock each initial label deficit. After the
reactions, T² swaps put the output and every catalyst at their assigned
wires. Componentwise maxima allow one finite stock per gate across targets.
We compile then replay concrete input-specific words, without runtime reads.
Neither stock preparation nor one program working on an unknown input follows.

A fraction-free row Hermite reduction tracks generator provenance. An integer
pivot must divide the remaining target coordinate: rational span alone is
insufficient. Raw gate words are construction witnesses, not minimum costs.

Replay: python3 -B -m scripts.probe_catalytic_tag_invariants
"""

from collections import Counter
from itertools import product

from scripts import probe_six_phase_exclusive_packet as packet
from scripts.probe_vacuum_phase_lifts import complete, go, lift

Vec = list[int]
Reaction = tuple[packet.Pair, packet.Pair]
Step = tuple[packet.Pair, packet.Pair, int]
Word = list[tuple[int, int]]
need = packet.need


def combine(a: int, x: Vec, b: int, y: Vec) -> Vec:
    return [a * u + b * v for u, v in zip(x, y, strict=True)]


def bezout(a: int, b: int) -> tuple[int, int, int]:
    """Return d>0 and u,v with ua+vb=d, for a>0 and b!=0."""
    old, cur = a, b
    u, x, v, y = 1, 0, 0, 1
    while cur:
        q, r = divmod(old, cur)
        old, cur, u, x, v, y = cur, r, x, u - q * x, y, v - q * y
    sign = 1 if old > 0 else -1
    return sign * old, sign * u, sign * v


class Basis:
    def __init__(self, generators: list[Vec], width: int) -> None:
        self.size = len(generators)
        self.width = width
        # Trailing coordinates are coefficients in the original generators.
        self.rows: dict[int, Vec] = {}
        for i, generator in enumerate(generators):
            row = [*generator, *(int(k == i) for k in range(self.size))]
            for p in range(width):
                b = row[p]
                if not b:
                    continue
                if p not in self.rows:
                    self.rows[p] = row if b > 0 else [-k for k in row]
                    break
                pivot = self.rows[p]
                a = pivot[p]
                if b % a == 0:
                    row = combine(1, row, -(b // a), pivot)
                else:
                    d, u, v = bezout(a, b)
                    # The 2x2 coefficient matrix has determinant +1:
                    # integer row span is preserved, not just rational rank.
                    self.rows[p] = combine(u, pivot, v, row)
                    row = combine(-(b // d), pivot, a // d, row)
        self.pivots = sorted(self.rows)
        for p in self.pivots:
            pivot = self.rows[p]
            for k in self.pivots:
                if k >= p:
                    break
                row = self.rows[k]
                q = row[p] // pivot[p]
                if q:
                    self.rows[k] = combine(1, row, -q, pivot)
        for p in self.pivots:
            row = self.rows[p]
            need(not any(row[:p]) and row[p] > 0, "bad row pivot")
            need(
                all(0 <= self.rows[k][p] < row[p] for k in self.pivots if k < p),
                "not reduced above integer pivot",
            )
            need(
                row[:width]
                == [
                    sum(c * g[j] for c, g in zip(row[width:], generators, strict=True))
                    for j in range(width)
                ],
                "invalid generator provenance",
            )
        # Complement provenance (basis ⊆ reactions) with the reverse
        # containment. Thus our checked integer basis loses no reaction.
        need(all(self.solve(g) is not None for g in generators), "lost a generator")

    def solve(self, target: Vec) -> Vec | None:
        rem = [*target, *([0] * self.size)]
        for p in self.pivots:
            row = self.rows[p]
            q, r = divmod(rem[p], row[p])
            if r:
                return None
            if q:
                rem = combine(1, rem, -q, row)
        if any(rem[: self.width]):
            return None
        return [-v for v in rem[self.width :]]


def delta(consumed: tuple[int, ...], produced: tuple[int, ...]) -> Vec:
    v = [0] * 16
    for a in consumed:
        v[a] -= 1
    for a in produced:
        v[a] += 1
    return v


def reactions(table: packet.Table) -> tuple[list[Reaction], list[Vec]]:
    # Deduplicate only identical vectors up to sign; keep a concrete raw edge.
    selected: dict[tuple[int, ...], Reaction] = {}
    for l, r in product(packet.RAW, repeat=2):
        src = (l, r)
        dst = go(table, src)
        need(go(table, dst) == (r, l), "not square-to-SWAP")
        v = tuple(delta(src, dst))
        if any(v) and v not in selected and tuple(-x for x in v) not in selected:
            selected[v] = (src, dst)
    return list(selected.values()), [list(v) for v in selected]


def expand(edges: list[Reaction], coefficients: Vec) -> list[Step]:
    steps = []
    for (src, dst), c in zip(edges, coefficients, strict=True):
        if c:
            step = (src, dst, 1) if c > 0 else (dst, src, 3)
            steps.extend([step] * abs(c))
    return steps


def required_stock(source: int, steps: list[Step]) -> Vec:
    balance, stock = [0] * 16, [0] * 16
    balance[source] = 1
    for consumed, produced, _ in steps:
        for v in consumed:
            balance[v] -= 1
            stock[v] = max(stock[v], -balance[v])
        for v in produced:
            balance[v] += 1
    return stock


def compile_word(
    table: packet.Table, initial: Vec, expected: Vec, steps: list[Step]
) -> Word:
    state, word = initial.copy(), []

    def gate(i: int, j: int) -> None:
        need(i != j, "self interaction")
        word.append((i, j))
        state[i], state[j] = go(table, (state[i], state[j]))

    # Choose all addresses on a known simulated state. The resulting word is
    # fixed before the independent replay; it contains no tag-dependent branch.
    for (a, b), dst, repeat in steps:
        i = state.index(a)
        j = state.index(b, i + 1 if a == b else 0)
        for _ in range(repeat):
            gate(i, j)
        need((state[i], state[j]) == dst, "wrong directed reaction")
    for i, wanted in enumerate(expected):
        if state[i] != wanted:
            j = state.index(wanted, i + 1)
            gate(i, j)
            gate(i, j)
    need(state == expected, "stock not restored on its original wires")
    return word


def signed_coarse(cell: int) -> int:
    return (2 * packet.n(cell) - 1) * packet.stock(cell)


def classify(table: packet.Table, free: tuple[int, ...]) -> tuple[int, int, int, int]:
    edges, generators = reactions(table)
    basis = Basis(generators, 16)
    # When z=0 mod 3 both active coarse flags coincide, so their signed
    # changes cancel even for an arbitrary common shift. For the other two
    # residues a shift in {0,3} leaves both active flags alone. Check the
    # exact condition, including the raw padding and homogeneous sectors.
    signed_law = all(
        signed_coarse(l) + signed_coarse(r) == signed_coarse(p) + signed_coarse(q)
        for (l, r), (p, q) in zip(product(packet.RAW, repeat=2), table, strict=True)
    )
    need(signed_law == (free[1] % 3 == free[2] % 3 == 0), "signed coarse law")
    plans: list[tuple[int, int, list[Step]]] = []
    stock = [0] * 16
    for occ, a in product(packet.BIT, packet.ACTIVE):
        src, dst = 8 * occ + a, 8 * occ + (a + 1) % 6
        coeff = basis.solve(delta((src,), (dst,)))
        need(
            (coeff is not None) == (not signed_law or a in (1, 4)),
            "signed count did not identify the exact blocked targets",
        )
        if coeff is None:
            continue
        steps = expand(edges, coeff)
        stock = list(map(max, stock, required_stock(src, steps)))
        plans.append((src, dst, steps))
    ancillas = [x for x, count in enumerate(stock) for _ in range(count)]
    longest = 0
    for src, dst, plan in plans:
        initial, expected = [src, *ancillas], [dst, *ancillas]
        word = compile_word(table, initial, expected, plan)
        replay = initial.copy()
        for i, j in word:
            replay[i], replay[j] = go(table, (replay[i], replay[j]))
        need(replay == expected, "open-loop word replay did not restore every wire")
        longest = max(longest, len(word))
    return len(basis.pivots), len(plans), len(ancillas), longest


def controls() -> None:
    # Same full rational span as Z²; exact membership has index two.
    basis = Basis([[2, 0], [0, 2], [1, 1]], 2)
    need(len(basis.pivots) == 2 and basis.solve([1, 0]) is None, "ignored torsion")
    need(basis.solve([7, -3]) is not None, "discarded a valid integer witness")
    for occ in packet.BIT:
        base = 8 * occ
        for a, b in product(packet.TAGS, repeat=2):
            p, q = packet.t(base + a, base + b)
            need(packet.n(p) == packet.n(q) == occ, "left homogeneous sector")
            need(
                packet.stock(p) + packet.stock(q) == packet.stock(a) + packet.stock(b),
                "homogeneous coarse count changed",
            )
        need(
            packet.stock(base) != packet.stock(base + 1),
            "no homogeneous plate obstruction",
        )
        need(
            packet.t(base, base + 1) == (base, base + 2),
            "lost homogeneous known-input hit",
        )


def main() -> None:
    controls()
    census: Counter[tuple[int, int]] = Counter()
    largest = longest = 0
    for free in product(packet.ACTIVE, repeat=3):
        rank, count, size, length = classify(complete(lift(free)), free)
        census[rank, count] += 1
        largest, longest = max(largest, size), max(longest, length)
    need(
        census == {(12, 4): 8, (13, 4): 16, (14, 12): 192},
        "unexpected integer-lattice census",
    )
    print(
        "Raw lattice rank / individually reachable +1 targets / lifts: 12/4/8, 13/4/16, 14/12/192."
    )
    print(
        f"Replayed {sum(c * n for (_, c), n in census.items())} input-specific words; all stock restored wire by wire."
    )
    print(
        f"Constructed maxima: {largest} auxiliary wires per lift, {longest} raw gates per word; not optima."
    )
    print(
        "One stock per lift; the address sequence may depend on the known initial target label."
    )
    print(
        "The 24 incomplete lifts conserve signed coarse count; only 1→2 and 4→5 per occupation survive."
    )
    print(
        "Same-occupation stock cannot realize all six shifts; 0→1 fails, 1→2 can succeed."
    )
    print("No common unknown-input plate follows from the integer-lattice test.")


if __name__ == "__main__":
    main()
