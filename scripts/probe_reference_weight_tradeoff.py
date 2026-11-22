"""Finite census of real additive weights versus reference branching.

Only four-label transparent square roots of swap are considered. A reference
is faithful here if neither output on (x, b) equals b for any x != b. This
test supplies b and does not require an all-reference gate, exact copying,
or preparation of a reference. The conserved weights are model labels, not
physical energy, and the census does not derive quantum mechanics.
"""

import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_reference_fanout import (
    Gate,
    GateSignature,
    Pair,
    check,
    swap,
    transparent_roots,
)

Chain = tuple[int, ...]
Reaction = frozenset[frozenset[int]]
STATES = tuple(range(4))
PAIRS: tuple[Pair, ...] = tuple((x, y) for x in STATES for y in STATES)


def weight_system(gate: Gate) -> tuple[list[list[Fraction]], list[int]]:
    """Return an exact reduced system and pivots; its rank is also real rank."""
    rows = [
        [Fraction(pair.count(s) - gate[pair].count(s)) for s in STATES]
        for pair in PAIRS
    ]
    pivots: list[int] = []
    for column in STATES:
        rank = len(pivots)
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][column]
        rows[rank] = [value / scale for value in rows[rank]]
        for i, row in enumerate(rows):
            if i != rank and (factor := row[column]):
                rows[i] = [v - factor * w for v, w in zip(row, rows[rank], strict=True)]
        pivots.append(column)
    return rows, pivots


def normalized_weights(
    rows: list[list[Fraction]], pivots: list[int]
) -> tuple[int, ...]:
    """Choose a nonconstant null vector and normalize its first two levels."""
    free = [s for s in STATES if s not in pivots]
    check(len(free) == 2, "expected a constant and one independent conserved weight")
    weights = [Fraction(0) for _ in STATES]
    # A constant vector has equal free coordinates. Taking (1, 0) cannot be
    # constant; the pivot equations determine its other two coordinates.
    weights[free[0]] = Fraction(1)
    for i, pivot in enumerate(pivots):
        weights[pivot] = -rows[i][free[0]]
    levels = sorted(set(weights))
    check(len(levels) == 3, "expected precisely three distinct weight levels")
    origin, step = levels[0], levels[1] - levels[0]
    normalized = tuple((value - origin) / step for value in weights)
    check(sorted(normalized) == [0, 1, 1, 2], "unexpected normalized weights")
    return tuple(int(value) for value in normalized)


def reaction(inputs: Pair, outputs: Pair) -> Reaction:
    return frozenset((frozenset(inputs), frozenset(outputs)))


def chain_partition(gate: Gate, size: int) -> set[frozenset[Chain]]:
    """Enumerate actual open-chain orbits under adjacent applications of T."""
    remaining = set(product(STATES, repeat=size))
    orbits: set[frozenset[Chain]] = set()
    while remaining:
        seed = remaining.pop()
        pending = [seed]
        orbit = {seed}
        while pending:
            state = pending.pop()
            for i in range(size - 1):
                updated = state[:i] + gate[state[i], state[i + 1]] + state[i + 2 :]
                # T^4 is the identity, so forward moves also give inverses.
                if updated in remaining:
                    remaining.remove(updated)
                    orbit.add(updated)
                    pending.append(updated)
        orbits.add(frozenset(orbit))
    return orbits


def check_chain_partition(gate: Gate, weights: tuple[int, ...], size: int) -> int:
    expected: defaultdict[tuple[str, int], set[Chain]] = defaultdict(set)
    for chain in product(STATES, repeat=size):
        if len(set(chain)) == 1 and weights[chain[0]] == 1:
            key = ("frozen middle", chain[0])
        else:
            key = ("total", sum(weights[s] for s in chain))
        expected[key].add(chain)
    actual = chain_partition(gate, size)
    check(
        actual == {frozenset(group) for group in expected.values()}
        and len(actual) == 2 * size + 3,
        f"unexpected orbit partition for open chain of length {size}",
    )
    return len(actual)


def main() -> None:
    signatures: set[GateSignature] = set()
    census: Counter[tuple[int, int]] = Counter()
    example: tuple[Gate, tuple[int, ...], dict[int, tuple[int, Pair]]] | None = None
    for gate in transparent_roots(STATES):
        check(gate.keys() == set(PAIRS), "incomplete gate table")
        signature = tuple(gate[pair] for pair in PAIRS)
        check(signature not in signatures, "duplicate gate table")
        signatures.add(signature)
        check(all(gate[gate[p]] == swap(p) for p in PAIRS), "T squared is not swap")
        check(all(gate[s, s] == (s, s) for s in STATES), "nontransparent gate")

        leaks: dict[int, tuple[int, Pair]] = {}
        for x, b in PAIRS:
            outputs = gate[x, b]
            if x != b and b in outputs:
                leaks.setdefault(b, (x, outputs))
        faithful = set(STATES) - leaks.keys()
        rows, pivots = weight_system(gate)
        dimension = len(STATES) - len(pivots)
        census[dimension, len(faithful)] += 1

        if dimension == 2:
            weights = normalized_weights(rows, pivots)
            low, x, y, high = sorted(STATES, key=weights.__getitem__)
            check(
                all(
                    weights[a] + weights[b] == sum(weights[s] for s in gate[a, b])
                    for a, b in PAIRS
                ),
                "normalized weights do not conserve every closed pair",
            )
            check(faithful == {x, y}, "faithful references are not the middle labels")
            check(leaks.keys() == {low, high}, "missing extreme-reference leak")
            expected_reactions = {
                reaction((low, x), (low, y)),
                reaction((high, x), (high, y)),
                reaction((low, high), (x, y)),
            }
            observed_reactions = {reaction(p, gate[p]) for p in PAIRS if p[0] < p[1]}
            check(observed_reactions == expected_reactions, "unexpected reactions")
            if example is None:
                example = gate, weights, leaks

    check(len(signatures) == 120, "expected 120 transparent gate tables")
    check(census == {(1, 1): 64, (2, 2): 48, (1, 4): 8}, f"wrong census: {census}")
    print("120 transparent four-label square roots of swap.")
    print("(dimension of real conserved weight space, faithful references): gates")
    for (dimension, count), gates in sorted(census.items()):
        print(f"  ({dimension}, {count}): {gates}")
    print("Dimension includes the constant weight; a faithful reference is supplied.")
    print("All 48 dimension-two tables conserve a normalized weight (0,1,1,2)")
    print("up to label order and reversal. Only the two middle labels are faithful.")
    print("Their unordered reactions are LX <-> LY, HX <-> HY, LH <-> XY.")

    if example is None:
        raise ValueError("no gate conserved a nonconstant weight")
    gate, weights, leaks = example
    low, x, y, high = sorted(STATES, key=weights.__getitem__)
    print(f"Example: (L,X,Y,H)={(low, x, y, high)}; ordered T outputs on i<j:")
    print("  " + ", ".join(f"{p}->{gate[p]}" for p in PAIRS if p[0] < p[1]))
    for b in (low, high):
        label, outputs = leaks[b]
        print(f"  Extreme reference {b} leaks: T{(label, b)}={outputs}.")
    inputs = (low, x)
    outputs = gate[inputs]
    check(inputs.count(y) == 0 and outputs.count(y) == 1, "missing readout change")
    print(f"  q = number of Y labels changes 0 -> 1 on {inputs}->{outputs},")
    print("  at unchanged total weight 1.")

    sizes = range(2, 6)
    counts = {size: check_chain_partition(gate, weights, size) for size in sizes}
    print(f"Example open-chain orbit counts by length: {counts}.")
    print("At these lengths, total weight labels each orbit except for the separate")
    print("frozen all-X and all-Y states, which share weight n with a mixed orbit.")
    print(f"  At n=2, {(x, x)}, {(y, y)}, and {(low, high)} all have weight 2.")
    print("Finite model weights are not physical energy; this does not derive QM.")


if __name__ == "__main__":
    main()
