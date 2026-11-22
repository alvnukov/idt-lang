"""Boolean gate cost of the alternating local shuttle. Run: python3 -B -O -m scripts.probe_boolean_shuttle_origin

Premises: four independently addressable cells, one shared role bit h, identical
reciprocal updates, and exact equality of the FULL configuration as the mark.
The all-configuration rigidity argument in probe_shuttle_local_reunions reduces
the noncommuting triple-reversal case to G(h,x)=(1-h,f^(+/-1)(x)). Here we
ask what encodes that branch with separated wires (h,e(x)), a fixed injective
cell encoding, and no extra persistent state. X/CNOT and arbitrary affine
wiring are free in the nonlinear count. A scalar AND costs one; Toffoli costs
one such AND. These are circuit resources, not physically measured primitives.

Lower bound independent of cell encoding: on a cycle e_0,...,e_(n-1) of f,
flipping h changes the cell output by D_i=e_(i-1) XOR e_(i+1). For an affine
map this difference is constant, so e_(i+4)=e_i. With at most one scalar AND
the whole output is Bz+c+v*L1(z)*L2(z) for affine forms L1,L2; its h-difference
therefore has at most two values a,b. Successive vertices of a step-by-two
orbit are separated by a or b. Each such orbit has length n/gcd(n,2), lives
in a coset of span(a,b), and has at most four vertices. It cannot be a
triangle: three distinct vertices have three distinct nonzero edge XORs.
Thus n/gcd(n,2) is 1,2 or 4, and n is 1,2,4 or 8. C4 and C8 below attain
the zero- and one-AND bounds. In particular one AND cannot give a factor
three, even on an admitted subset. No enumeration of all circuits is needed.
Role-dependent encodings, nonlinear decoders, uncounted memory or selecting
outputs would change this contract; a clean constant work wire would not.

To construct the ternary factor, A(u,v)=(u XOR v,u) cycles the three nonzero
binary pairs. Apply A unconditionally, then apply A when h=1: A^2=A^-1.
The second A costs two Toffolis. Combine with a toggled bit for a valid C6
on six of eight symbols, or with affine C4 for C4+C12 on ALL sixteen.
When all cell patterns must pass the short spatial echo test, every f-cycle
must have length >=4. For at most eight binary symbols the only nonempty
cycle partitions satisfying that bound at power-of-two size are (4), (8),
and (4,4); none has order divisible by 3. Four binary cell bits are minimal
under both requirements. Every even port word acts by signed powers of f on
individual cells; every odd word squares to identity. Supplying four ports,
their actuation, the vector wires and a program is not deriving those items.
No permutation on a full 2^N-state register has period six at every root:
six would divide the number of states. The four-step program below has order
six on the full space, but an orbit has period six iff at least one of its
two addressed cells belongs to C12. That is full-configuration period, not
necessarily a six-valued reading of the first cell. Counts of Toffolis refer
to one address operation, not an entire program. No fringe, physical detector,
derivation of dimension, or Lean theorem is established.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator
from dataclasses import asdict, dataclass
from itertools import pairwise, permutations, product
from math import lcm, prod

Word = tuple[int, ...]
Circuit = tuple[Word, ...]  # each operation: zero, one or two controls, then target
CellMap = tuple[int, ...]
PORTS = range(4)
SHORT = tuple(
    w
    for n in range(4)
    for w in product(PORTS, repeat=n)
    if all(a != b for a, b in pairwise(w))
)


def need(ok: bool, label: str) -> None:
    if not ok:
        raise ArithmeticError(label)


def controlled_triangle(u: int, v: int) -> Circuit:
    # Two CNOTs implement A; controlling each by the OLD bit 0 implements c-A.
    return ((v, u), (u, v), (0, v, u), (0, u, v))


# Wire 0 is h; packed cell bits begin at wire 1. Changes to h are always last.
C4: Circuit = ((1, 2), (0, 2), (1,), (0,))
C8: Circuit = ((0, 1), (0, 2), (1, 2, 3), (0, 2), (0, 1)) + C4
TRIANGLE_BIT: Circuit = controlled_triangle(2, 3) + ((1,), (0,))
TRIANGLE_C4: Circuit = controlled_triangle(3, 4) + C4


def evaluate(circuit: Circuit, width: int) -> tuple[CellMap, CellMap]:
    for op in circuit:
        need(1 <= len(op) <= 3 and len(set(op)) == len(op), "bad gate")
        need(all(0 <= w <= width for w in op), "wire outside bit register")

    def run(h: int, x: int) -> int:
        z = (x << 1) | h
        for op in circuit:
            if all((z >> control) & 1 for control in op[:-1]):
                z ^= 1 << op[-1]
        need((z & 1) == 1 - h, "role does not alternate")
        return z >> 1

    f, inv = (tuple(run(h, x) for x in range(1 << width)) for h in range(2))
    need(all(inv[y] == x and f[inv[x]] == x for x, y in enumerate(f)), "reciprocity")
    return f, inv


def cycles(f: CellMap, admitted: Word) -> tuple[Word, ...]:
    todo, parts = set(admitted), []
    need({f[x] for x in todo} == todo, "admission is not permutation invariant")
    while todo:
        x = min(todo)
        part = []
        while x in todo:
            part.append(x)
            todo.remove(x)
            x = f[x]
        need(x == part[0], "broken cycle")
        parts.append(tuple(part))
    return tuple(parts)


def endpoint(maps: tuple[CellMap, CellMap], h: int, cells: Word, w: Word) -> Word:
    state = list(cells)
    for port in w:
        state[port] = maps[h][state[port]]
        h ^= 1
    return (h, *state)


def short_ball(maps: tuple[CellMap, CellMap], h: int, start: Word) -> bool:
    # Equality of all length <=3 prefixes tests all echoes through six ticks
    # by reciprocity. Only three-step paths coincide with their reversals.
    by_key: dict[Word, Word] = {}
    by_end: dict[Word, Word] = {}
    for w in SHORT:
        key = min(w, w[::-1]) if len(w) == 3 else w
        end = endpoint(maps, h, start, w)
        if by_key.setdefault(key, end) != end or by_end.setdefault(end, key) != key:
            return False
    return True


def native_period(maps: tuple[CellMap, CellMap], h: int, start: Word, w: Word) -> int:
    role, cells = h, start
    for k in range(1, 2 * len(maps[0]) ** 4 + 1):
        out = endpoint(maps, role, cells, w)
        role, cells = out[0], out[1:]
        if (role, cells) == (h, start):
            return k
    raise ArithmeticError("program never returned")


@dataclass(frozen=True)
class Result:
    admitted_symbols: int
    scalar_nonlinear_gates: int
    cycle_lengths: Word
    cell_role_xor_values: Word
    short_ball_passing_roots: int
    total_roots: int
    native_word: Word
    native_period_counts: dict[int, int]


def inspect(circuit: Circuit, width: int, admitted: Word, word: Word) -> Result:
    maps = evaluate(circuit, width)
    f, inv = maps
    parts = cycles(f, admitted)
    passing, periods = 0, Counter[int]()
    for selected in product(parts, repeat=4):
        # Independently rotating each initial cell along its f-cycle commutes
        # with every port step. Both predicates are invariant; restore multiplicity.
        cells = tuple(c[0] for c in selected)
        weight = prod(map(len, selected))
        for h in range(2):
            passing += weight * short_ball(maps, h, cells)
            periods[native_period(maps, h, cells, word)] += weight
    total = 2 * len(admitted) ** 4
    need(sum(periods.values()) == total, "omitted root")
    return Result(
        len(admitted),
        sum(len(op) == 3 for op in circuit),
        tuple(sorted(map(len, parts))),
        tuple(sorted({f[x] ^ inv[x] for x in admitted})),
        passing,
        total,
        word,
        dict(sorted(periods.items())),
    )


def partitions(n: int, minimum: int = 4) -> Iterator[Word]:
    if n == 0:
        yield ()
    for first in range(minimum, n + 1):
        for rest in partitions(n - first, first):
            yield (first, *rest)


def main() -> None:
    for width, cmp in ((2, C4), (3, C8)):
        f, inv = evaluate(cmp, width)
        q = 1 << width
        need(
            all(f[x] == (x + 1) % q and inv[x] == (x - 1) % q for x in range(q)),
            "binary ring reference",
        )

    ab = (0, 1)
    q4 = inspect(C4, 2, tuple(range(4)), ab)
    q8 = inspect(C8, 3, tuple(range(8)), ab)
    six = inspect(TRIANGLE_BIT, 3, tuple(range(2, 8)), ab)
    padded = inspect(TRIANGLE_BIT, 3, tuple(range(8)), ab)
    full = inspect(TRIANGLE_C4, 4, tuple(range(16)), ab * 2)
    rows = (q4, q8, six, padded, full)
    need([r.scalar_nonlinear_gates for r in rows] == [0, 1, 2, 2, 2], "gate costs")
    need(
        [r.cycle_lengths for r in rows] == [(4,), (8,), (6,), (2, 6), (4, 12)],
        "orbit structures",
    )
    need(
        len(q4.cell_role_xor_values) == 1 and len(q8.cell_role_xor_values) == 2,
        "affine and one-AND sharp examples",
    )
    for r in (q4, q8, six, full):
        need(r.short_ball_passing_roots == r.total_roots, "all-admitted echo law")
    need(padded.short_ball_passing_roots < padded.total_roots, "bad-code control")
    padded_maps = evaluate(TRIANGLE_BIT, 3)
    need(
        endpoint(padded_maps, 0, (0, 0, 0, 0), ab * 2) == (0, 0, 0, 0, 0),
        "raw four-tick false echo",
    )
    need(six.native_period_counts == {6: six.total_roots}, "admission-limited period")
    need(
        full.native_period_counts
        == {2: full.total_roots // 16, 6: 15 * full.total_roots // 16},
        "active versus inactive translated cells",
    )

    # Supplement the encoding-independent argument with *all* 3-bit six-cycle
    # encodings, counting labelled origins and directions, not isomorphism types.
    diversity = Counter(
        len({e[i - 1] ^ e[(i + 1) % 6] for i in range(6)})
        for e in permutations(range(8), 6)
    )
    need(sum(diversity.values()) == 20160 and min(diversity) >= 3, "six-cycle XORs")
    small = {1 << k: tuple(partitions(1 << k)) for k in range(4)}
    need(small == {1: (), 2: (), 4: ((4,),), 8: ((4, 4), (8,))}, "small partitions")
    need(
        not any(lcm(*part) % 3 == 0 for ps in small.values() for part in ps),
        "raw width lower bound",
    )
    print(
        json.dumps(
            {
                "binary_cell_fixtures": dict(
                    zip(
                        (
                            "affine_c4",
                            "one_and_c8",
                            "admitted_c6",
                            "raw_c2_c6",
                            "raw_c4_c12",
                        ),
                        (asdict(r) for r in rows),
                        strict=True,
                    )
                ),
                "six_cycle_encodings_by_xor_diversity": dict(sorted(diversity.items())),
                "all_minimum_four_partitions_below_four_bits": small,
                "one_and_necessary_allowed_cycle_lengths_not_sufficient_for_general_gate": (
                    1,
                    2,
                    4,
                    8,
                ),
                "scope": "finite separated-wire shuttle; no detector, phase prior or spatial dimension derived",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
