"""Exact controls for relational charge in a supplied four-label gate network.

Unequal inputs are replaced by their two-label complement. In Klein-four
coordinates the XOR of all four labels is zero, so each update preserves
pair XOR. Relabeling by x -> L(x) XOR t sends an n-site charge q to
L(q) XOR ((n mod 2) t): names change, but equality at fixed n does not.

Orbit tests use only single adjacent applications of the gate on an open
chain. The directed bond-density tests are a different question: they ask
about additive real sums of one translation-invariant nearest-neighbor
density, not arbitrary functions of words or higher-range densities.
The gradient part of a density cancels on a ring but leaves an endpoint
difference in the raw open sum.
No preparation, postselection, yield, or physical dynamics are inferred.
"""

from collections import Counter
from collections.abc import Iterable
from fractions import Fraction
from functools import reduce
from itertools import pairwise, permutations, product
from operator import xor
from typing import TYPE_CHECKING

if TYPE_CHECKING or __package__:
    from .probe_reference_fanout import Gate, check, swap, transparent_roots
else:
    from probe_reference_fanout import Gate, check, swap, transparent_roots

Word = tuple[int, ...]
Row = tuple[int, ...]
LABELS = tuple(range(4))
PAIRS = tuple(product(LABELS, LABELS))
WINDOWS = tuple(product(LABELS, repeat=4))


def faithful_gates() -> list[Gate]:
    roots = list(transparent_roots(LABELS))
    check(len(roots) == 120, "unexpected root enumeration size")
    gates = [
        gate for gate in roots if all(x == y or y not in gate[x, y] for x, y in PAIRS)
    ]
    check(
        len({tuple(gate[pair] for pair in PAIRS) for gate in gates}) == 8 == len(gates),
        "expected eight distinct globally faithful roots",
    )
    for gate in gates:
        for x, y in PAIRS:
            a, b = gate[x, y]
            # On each unequal edge the four iterates are the two orders of
            # the input pair and its complement, for every faithful root.
            check(gate[a, b] == (y, x), "gate square is not swap")
            check(
                (a, b) == (x, x) if x == y else {a, b} == set(LABELS) - {x, y},
                "gate is not transparent/complementary",
            )
            check(a ^ b == x ^ y, "pair XOR changed")
    return gates


def charge(word: Iterable[int]) -> int:
    return reduce(xor, word, 0)


def parity(mask: int, letter: int) -> int:
    return (mask & letter).bit_count() % 2


def relabeling_and_parity_controls(gates: list[Gate]) -> None:
    for relabel in permutations(LABELS):
        linear = tuple(x ^ relabel[0] for x in relabel)
        check(
            all(linear[x ^ y] == linear[x] ^ linear[y] for x, y in PAIRS),
            "four-label permutation is not affine",
        )

    masks = LABELS[1:]
    partitions = {
        frozenset(
            frozenset(x for x in LABELS if parity(mask, x) == bit) for bit in (0, 1)
        )
        for mask in masks
    }
    balanced_partitions = {
        frozenset((frozenset((0, x)), frozenset(set(LABELS) - {0, x}))) for x in masks
    }
    check(partitions == balanced_partitions, "missing a balanced pair partition")
    for gate in gates:
        for mask in masks:
            pair_sums = {pair: sum(parity(mask, x) for x in pair) for pair in PAIRS}
            check(
                all(pair_sums[pair] % 2 == pair_sums[gate[pair]] % 2 for pair in PAIRS),
                "a balanced parity test changed modulo two",
            )
            check(
                any(pair_sums[pair] != pair_sums[gate[pair]] for pair in PAIRS),
                "an integer bit sum unexpectedly survived",
            )


def update(word: Word, edge: int, gate: Gate) -> Word:
    return word[:edge] + gate[word[edge], word[edge + 1]] + word[edge + 2 :]


def orbit_sizes(size: int, gate: Gate) -> tuple[int, tuple[int, ...]]:
    """Remove whole actual gate orbits and check their complete partition."""
    remaining: set[Word] = set(product(LABELS, repeat=size))
    uniform = {(x,) * size for x in LABELS}
    fixed: set[Word] = set()
    nonuniform: dict[int, int] = {}
    while remaining:
        start = remaining.pop()
        pending = [start]
        sector = charge(start)
        count = 1
        # Every local update is invertible by three repetitions, so forward
        # traversal suffices; swap/complement are not separate edges here.
        while pending:
            word = pending.pop()
            check(charge(word) == sector, "an orbit crossed XOR sectors")
            for edge in range(size - 1):
                neighbor = update(word, edge, gate)
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    pending.append(neighbor)
                    count += 1
        if start in uniform:
            check(count == 1, "a uniform word was not a singleton")
            fixed.add(start)
        else:
            check(sector not in nonuniform, "a nonuniform XOR sector split")
            nonuniform[sector] = count

    # For each charge the first size-1 letters are free and the last is forced.
    uniform_counts = Counter(map(charge, uniform))
    expected = {
        q: 4 ** (size - 1) - uniform_counts[q]
        for q in LABELS
        if 4 ** (size - 1) > uniform_counts[q]
    }
    check(fixed == uniform and nonuniform == expected, "unexpected orbit partition")
    return len(fixed) + len(nonuniform), tuple(nonuniform.get(q, 0) for q in LABELS)


def bond_delta(before: Word, after: Word) -> Row:
    old, new = Counter(pairwise(before)), Counter(pairwise(after))
    return tuple(new[pair] - old[pair] for pair in PAIRS)


def exact_rank(rows: Iterable[Row]) -> int:
    """Eliminate over the rationals; integer matrices have the same real rank."""
    pivots: dict[int, list[Fraction]] = {}
    for row in set(rows):
        current = list(map(Fraction, row))
        for index in range(len(current)):
            coefficient = current[index]
            if not coefficient:
                continue
            if index not in pivots:
                pivots[index] = [value / coefficient for value in current]
                break
            current = [
                value - coefficient * pivot
                for value, pivot in zip(current, pivots[index], strict=True)
            ]
    return len(pivots)


def preserves(rows: Iterable[Row], density: Row) -> bool:
    return all(
        sum(a * b for a, b in zip(row, density, strict=True)) == 0 for row in rows
    )


def interior_rows(gate: Gate) -> set[Row]:
    # The same three directed bonds change in every periodic chain of length
    # >= 4. All four-letter windows occur even at length four; the closing
    # bond (v,u) does not change when the middle edge is updated.
    return {bond_delta(word, update(word, 1, gate)) for word in WINDOWS}


def real_density_controls(gates: list[Gate]) -> None:
    constant = (1,) * len(PAIRS)
    gauge_basis = [
        tuple(int(x == label) - int(y == label) for x, y in PAIRS)
        for label in LABELS[1:]
    ]
    basis = [constant, *gauge_basis]
    check(exact_rank(basis) == 4, "constant and gauge directions are dependent")
    for gate in gates:
        periodic = interior_rows(gate)
        opened = {
            bond_delta(word, update(word, edge, gate))
            for word in WINDOWS
            for edge in range(3)
        }
        isolated = {bond_delta(pair, gate[pair]) for pair in PAIRS}
        check(exact_rank(periodic) == 12, "wrong periodic bond rank")
        check(
            all(preserves(periodic, density) for density in basis),
            "constant plus telescoping densities should span the periodic kernel",
        )
        check(
            exact_rank(opened) == 15 and preserves(opened, constant),
            "raw open chain should have only constants in the kernel",
        )
        check(exact_rank(isolated) == 9, "wrong isolated pair rank")

    swap_rows = interior_rows({pair: swap(pair) for pair in PAIRS})
    count_density = tuple(int(x == 0) + int(y == 0) for x, y in PAIRS)
    check(
        preserves(swap_rows, count_density)
        and exact_rank([*basis, count_density]) == 5,
        "swap-only control should conserve a nonconstant site count",
    )


def main() -> None:
    gates = faithful_gates()
    relabeling_and_parity_controls(gates)
    print(
        "Eight globally faithful roots: pair XOR and all three balanced parities conserved."
    )
    print("Integer bit sums fail; all 24 relabelings are affine.")
    print("Open length | orbits | nonuniform sizes by XOR 0,1,2,3")
    representative = min(gates, key=lambda gate: tuple(gate[pair] for pair in PAIRS))
    for size, expected in enumerate((4, 7, 8, 8, 8, 8), start=1):
        count, counts_by_charge = orbit_sizes(size, representative)
        check(count == expected, "wrong open-chain orbit count")
        if size <= 4:
            check(
                all(
                    orbit_sizes(size, gate) == (count, counts_by_charge)
                    for gate in gates
                ),
                "faithful roots disagree on open-chain orbits",
            )
        print(f"{size} | {count} | {counts_by_charge}")
    check(
        charge((0, 0, 0, 0)) == charge((0, 0, 1, 1)) == 0,
        "uniform/nonuniform shared-charge control failed",
    )
    print("Uniform words remain separate singleton orbits: 0000 and 0011 share XOR 0.")
    real_density_controls(gates)
    print("Directed real bond rank/16: periodic n>=4 12; open n=4 15; isolated pair 9.")
    print("Periodic kernel: constant + g(x)-g(y); raw open kernel: constants only.")
    print("Swap-only control retains a nonconstant site count.")


if __name__ == "__main__":
    main()
