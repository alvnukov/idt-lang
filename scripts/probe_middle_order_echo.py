"""Exact finite order echo on two middle labels with supplied references.

Words are chronological: A applies T to sites 0,1 and B to sites 1,2.
The analyzer uses one further T after the echo, with a supplied middle
reference. The readout rates are only for the specified preparations and
detectors. No preparation rule, physical detector, or QM result is inferred.
"""

import sys
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_reference_fanout import (
    Gate,
    GateSignature,
    check,
    swap,
    transparent_roots,
)
from scripts.probe_reference_weight_tradeoff import (
    PAIRS,
    STATES,
    normalized_weights,
    weight_system,
)

Triple = tuple[int, int, int]
L, X, Y, H = STATES
WEIGHTS = (0, 1, 1, 2)
MIDDLE = (X, Y)
EXTREMES = (L, H)
ENCODED = tuple((r, m, r) for r, m in product(EXTREMES, MIDDLE))
U, V = "AB", "ABBA"
UV, VU = U + V, V + U
SWAPS = {p: swap(p) for p in PAIRS}
TAGS: Triple = (0, 1, 2)


def conserved_gates() -> list[Gate]:
    """Reuse the rational census and express every gate in L,X,Y,H labels."""
    raw_signatures: set[GateSignature] = set()
    semantic_signatures: Counter[GateSignature] = Counter()
    gates: list[Gate] = []
    for gate in transparent_roots(STATES):
        signature = tuple(gate[p] for p in PAIRS)
        check(signature not in raw_signatures, "duplicate raw gate")
        raw_signatures.add(signature)
        rows, pivots = weight_system(gate)
        if len(STATES) - len(pivots) != 2:
            continue
        weights = normalized_weights(rows, pivots)
        labels = sorted(STATES, key=weights.__getitem__)
        rename = {label: role for role, label in enumerate(labels)}
        named: Gate = {
            (rename[a], rename[b]): (rename[c], rename[d])
            for (a, b), (c, d) in gate.items()
        }
        check(all(named[s, s] == (s, s) for s in STATES), "not transparent")
        for a, b in PAIRS:
            c, d = named[a, b]
            check(named[c, d] == (b, a), "not a square root of swap")
            check(
                WEIGHTS[a] + WEIGHTS[b] == WEIGHTS[c] + WEIGHTS[d],
                "not a conserved normalized weight",
            )
        semantic_signatures[tuple(named[p] for p in PAIRS)] += 1
        gates.append(named)
    check(len(raw_signatures) == 120 and len(gates) == 48, "wrong gate census")
    check(sorted(semantic_signatures.values()) == [6] * 8, "wrong relabeled census")
    return gates


def run(gate: Gate, word: str, state: Triple) -> Triple:
    a, b, c = state
    for move in word:
        if move == "A":
            a, b = gate[a, b]
        elif move == "B":
            b, c = gate[b, c]
        else:
            raise ValueError(f"unknown forward move: {move}")
    return a, b, c


def check_echo(gates: list[Gate]) -> None:
    check(Counter(UV) == Counter(VU) == {"A": 3, "B": 3}, "different move counts")
    check(run(SWAPS, UV, TAGS) == run(SWAPS, VU, TAGS) == (1, 2, 0), "routing differs")
    for gate in gates:
        for state in ENCODED:
            r, m, _ = state
            other = Y if m == X else X
            check(run(gate, UV, state) == (r, other, r), "UV did not echo and flip")
            check(run(gate, VU, state) == state, "VU did not echo and retain")
            check(run(gate, U, state) not in ENCODED, "U did not leave the encoding")
        for a, b, c in product(STATES, repeat=3):
            check(run(gate, VU, (a, b, c)) == (c, b, a), "VU is not outer swap")


def encoded_map(gates: list[Gate], word: str) -> tuple[int, ...] | None:
    outputs: list[int] = []
    for gate in gates:
        for state in ENCODED:
            left, middle, right = run(gate, word, state)
            if left != state[0] or right != state[2] or middle not in MIDDLE:
                return None
            outputs.append(middle)
    return tuple(outputs)


def check_bounded_search(gates: list[Gate]) -> list[int]:
    """Exhaust ordered nonempty forward-word pairs, with no inverse alphabet."""
    counts: list[int] = []
    for size in range(2, 7):
        words = ("".join(letters) for letters in product("AB", repeat=size))
        maps = {
            word: (run(SWAPS, word, TAGS), encoded_map(gates, word)) for word in words
        }
        hits: set[tuple[str, str]] = set()
        for word, (route, first_map) in maps.items():
            if first_map is None:
                continue
            for cut in range(1, size):
                left, right = word[:cut], word[cut:]
                other_route, second_map = maps[right + left]
                if (
                    route == other_route
                    and second_map is not None
                    and first_map != second_map
                ):
                    check(
                        all(a != b for a, b in zip(first_map, second_map, strict=True)),
                        "a hit separated only on part of the encoded domain",
                    )
                    hits.add((left, right))
        counts.append(len(hits))
        if size == len(UV):
            check((U, V) in hits and (V, U) in hits, "named echo missing from search")
    check(counts == [0, 0, 0, 0, 8], f"unexpected bounded search counts: {counts}")
    return counts


def analyze(gate: Gate, state: Triple, word: str, reference: int) -> bool:
    middle = run(gate, word, state)[1]
    return WEIGHTS[gate[middle, reference][0]] != 1


def check_analyzer(gates: list[Gate]) -> None:
    for gate in gates:
        for middle, reference in product(MIDDLE, repeat=2):
            check(
                all(
                    (WEIGHTS[s] != 1) == (middle != reference)
                    for s in gate[middle, reference]
                ),
                "analyzer is not a middle mismatch detector on both ports",
            )
        for r in EXTREMES:
            for word, expected in ((UV, 1), (VU, 0)):
                shared = Fraction(
                    sum(analyze(gate, (r, m, r), word, m) for m in MIDDLE), 2
                )
                check(shared == expected, "shared fair reference did not separate")
                for m in MIDDLE:
                    independent = Fraction(
                        sum(analyze(gate, (r, m, r), word, s) for s in MIDDLE), 2
                    )
                    check(
                        independent == Fraction(1, 2),
                        "independent fair reference separated",
                    )


def check_ancillas(gates: list[Gate]) -> None:
    rho = (H, Y, X, L)
    ancillas = tuple(product(MIDDLE, repeat=2))
    census: Counter[tuple[bool, tuple[int, ...]]] = Counter()
    for gate in gates:
        invariant = all(
            gate[rho[a], rho[b]] == (rho[c], rho[d]) for (a, b), (c, d) in gate.items()
        )
        counts = tuple(
            sum(WEIGHTS[run(gate, "BA", (m, r1, r2))[0]] == 1 for r1, r2 in ancillas)
            for m in MIDDLE
        )
        census[invariant, counts] += 1
        for m in MIDDLE:
            shared = sum(WEIGHTS[run(gate, "BA", (m, r, r))[0]] == 1 for r in MIDDLE)
            check(shared == 1, "shared fair BA ancillas did not give 1/2")
    check(
        census == {(True, (2, 2)): 24, (False, (1, 3)): 12, (False, (3, 1)): 12},
        f"unexpected BA ancilla census: {census}",
    )


def main() -> None:
    gates = conserved_gates()
    check_echo(gates)
    counts = check_bounded_search(gates)
    check_analyzer(gates)
    check_ancillas(gates)
    print(
        "48 weight-conserving gates (8 L,X,Y,H tables); U=AB and V=ABBA, chronological."
    )
    print("Both orders use 3 A and 3 B moves and have identical literal-swap routing.")
    print(
        "For both extreme references r: UV flips the middle, VU retains it; sides return exactly."
    )
    print("U alone leaves the encoding; VU is exactly outer swap on every triple.")
    print(f"Ordered forward-word hits at total lengths 2..6: {counts}.")
    print("Same post-echo analyzer T and detector E=[output weight != 1]:")
    print("  Matched s=m, even from a shared fair source: (UV,VU) = (1,0).")
    print("  Independent fair s: (UV,VU) = (1/2,1/2).")
    print("BA, M=[first weight == 1], independent fair middle ancillas, rates for X,Y:")
    print("  (1/2,1/2): 24, exactly the rho-invariant gates (rho=(L H)(X Y)).")
    print(
        "  (1/4,3/4): 12; (3/4,1/4): 12. Shared fair ancillas give (1/2,1/2) on all 48."
    )
    print(
        "Finite model with supplied preparations and fixed schedules; no QM derivation."
    )


if __name__ == "__main__":
    main()
