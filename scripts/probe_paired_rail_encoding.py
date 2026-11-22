"""A finite native paired-port encoding; no fitted phases or physical mixing claim.

Each physical port has signed integer real/imaginary counts. One addressed
two-port mixer is T=((1+i,1-i),(1-i,1+i))/2. Each layer uses 2T and doubles
idle counts: the common amplitude denominator doubles, the ticket gain is 4.
Addressability, simultaneous disjoint wiring, a coherent two-outcome port
shutter/herald and grouped port readout are supplied operations. The herald
does NOT identify which surviving port; a which-port record destroys the code.

On a single injected basis port the sum of normalized amplitudes and norm
squared are both 1. If in three ports (z,-z,w) is the pre-shutter state,
the sum forces w=1 and the norm forces z=0. The same argument excludes two
bare ports outright (their sum would vanish). This wall is for a single
basis injection, T-only preparation and a final port mask, not all protocols.
Four ports suffice; the remaining two here are for a three-logical-port word.

We enumerate all ranked tickets of the preparation, then propagate the full
circuit's signed counts exactly, without enumerating its exponential ticket
tree. We compare to a separate three-dimensional complex-matrix oracle.
This is a conditional finite orientation witness, not CP violation in nature,
a measurement derivation, or a neutrino/quark mass or mixing prediction.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from functools import cache
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_ranked_event_routing import RankedGate

Pair = tuple[int, int]
Layer = tuple[Pair, ...]
Word = tuple[Layer, ...]
Counts = tuple[int, ...]
IntMatrix = tuple[tuple[int, ...], ...]
Matrix = tuple[tuple[complex, ...], ...]

PORTS = 6
PAIRS: tuple[Pair, ...] = ((0, 3), (1, 4), (2, 5))
PREP: Word = (((0, 1),), ((0, 2), (1, 3)))
BLOCK = ((1, -1, 1, 1), (1, 1, -1, 1), (1, 1, 1, -1), (-1, 1, 1, 1))


def need(test: bool, reason: str) -> None:
    if not test:
        raise AssertionError(reason)


@cache
def raw(layer: Layer) -> IntMatrix:
    """Real integer lift of the common-denominator layer, with bypass gain."""
    used = [p for pair in layer for p in pair]
    need(len(set(used)) == len(used) and all(0 <= p < PORTS for p in used), "wiring")
    n = 2 * PORTS
    mat = [[2 * int(j == k) for k in range(n)] for j in range(n)]
    for pair in layer:
        ix = [2 * p + axis for p in pair for axis in range(2)]
        for j, src in enumerate(ix):
            for k, dst in enumerate(ix):
                mat[src][dst] = BLOCK[j][k]
    need(
        all(
            sum(row[j] * row[k] for row in mat) == 4 * int(j == k)
            for j, k in product(range(n), repeat=2)
        ),
        "integer columns must be orthogonal with equal gain",
    )
    return tuple(map(tuple, mat))


def physical(q: Counts, word: Word) -> Counts:
    for layer in word:
        q = tuple(sum(a * b for a, b in zip(row, q, strict=True)) for row in raw(layer))
    return q


def amplitude(q: Counts, port: int, denom: int) -> complex:
    return complex(q[2 * port], q[2 * port + 1]) / denom


def weights(q: Counts, denom: int) -> tuple[Fraction, ...]:
    return tuple(
        Fraction(sum(q[2 * p + k] ** 2 for p in pair for k in range(2)), denom**2)
        for pair in PAIRS
    )


def prepare() -> tuple[Counts, int]:
    q = (1,) + (0,) * (2 * PORTS - 1)
    events = {(0, 0, 0)}
    for layer in PREP:
        gate = RankedGate(q, raw(layer), reverse_matching=False)
        out = set()
        for ev, seed in product(events, range(gate.gain)):
            result = gate.route(ev, seed)
            need(gate.unroute(result) == (ev, seed), "ranked inverse")
            out.add(result)
        q = physical(q, (layer,))
        need(gate.q_out == q and len(out) == 4 * len(events), "ranked expansion")
        events = out
    need(
        tuple(amplitude(q, p, 4) for p in range(PORTS))
        == (0.5j, 0.5, 0.5, -0.5j, 0, 0),
        "four-port preparation",
    )
    counts = tuple(sum(ev[0] // 2 == p for ev in events) for p in range(PORTS))
    need(counts == (4, 4, 4, 4, 0, 0), "ranked source table")
    kept = tuple(x if k // 2 in PAIRS[0] else 0 for k, x in enumerate(q))
    need(weights(kept, 4) == (Fraction(1, 2), Fraction(0), Fraction(0)), "source yield")
    return kept, 4


def cross(j: int, k: int) -> Layer:
    return tuple(zip(PAIRS[j], PAIRS[k], strict=True))


V: Word = (cross(0, 1), cross(1, 2), cross(0, 1))
DELAY: Word = ((PAIRS[1], PAIRS[2]), (PAIRS[2],))


def inverse(word: Word) -> Word:
    # The single two-port mixer has order four; disjoint gates commute.
    return tuple(layer for layer in reversed(word) for _ in range(3))


def conjugate(word: Word) -> Word:
    # Conjugate each symmetric native mixer without reversing the word.
    return tuple(layer for layer in word for _ in range(3))


def code_basis(k: int) -> Counts:
    plus, minus = PAIRS[k]
    return tuple(int(i == 2 * plus) - int(i == 2 * minus) for i in range(2 * PORTS))


def decoded(q: Counts, denom: int) -> tuple[complex, ...]:
    values = tuple(amplitude(q, a, denom) for a, _ in PAIRS)
    need(
        all(
            amplitude(q, b, denom) == -z
            for (_, b), z in zip(PAIRS, values, strict=True)
        ),
        "leakage out of paired code",
    )
    return values


def logical(word: Word) -> Matrix:
    cols = [decoded(physical(code_basis(k), word), 2 ** len(word)) for k in range(3)]
    return tuple(zip(*cols, strict=True))


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum(a[r][s] * b[s][c] for s in range(3)) for c in range(3))
        for r in range(3)
    )


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(z.conjugate() for z in row) for row in zip(*a, strict=True))


def square(z: complex) -> Fraction:
    # The bounded oracle uses only exactly representable binary dyadics.
    return Fraction(z.real) ** 2 + Fraction(z.imag) ** 2


def main() -> None:
    source, denominator = prepare()
    a, b = (1 + 1j) / 2, (1 - 1j) / 2
    t01: Matrix = ((a, b, 0), (b, a, 0), (0, 0, 1))
    t12: Matrix = ((1, 0, 0), (0, a, b), (0, b, a))
    identity: Matrix = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    delay: Matrix = ((1, 0, 0), (0, 1j, 0), (0, 0, -1))
    v = mul(mul(t01, t12), t01)
    vc = tuple(tuple(z.conjugate() for z in row) for row in v)
    need(logical((cross(0, 1),) * 2) == ((0, 1, 0), (1, 0, 0), (0, 0, 1)), "swap")
    need(logical(V) == v and logical(conjugate(V)) == vc, "mixing columns")
    need(
        logical(inverse(V)) == adjoint(v) and mul(v, adjoint(v)) == identity, "inverse"
    )
    need(logical(DELAY) == delay, "native delay")
    for row, bar in zip(v, vc, strict=True):
        need(
            all(square(x) == square(y) for x, y in zip(row, bar, strict=True)), "moduli"
        )
    j = Fraction((v[0][0] * v[1][1] * v[0][1].conjugate() * v[1][0].conjugate()).imag)
    need(j == -Fraction(1, 16), "quartet orientation")

    def table(
        word: Word, phases: Word, mixing: Matrix, d: Matrix
    ) -> tuple[Fraction, ...]:
        sequence = inverse(word) + phases + word
        q = physical(source, sequence)
        divisor = denominator * 2 ** len(sequence)
        observed = weights(q, divisor)
        reference = mul(mul(mixing, d), adjoint(mixing))
        column = tuple(row[0] for row in reference)
        need(
            decoded(q, divisor) == tuple(z * 0.5j for z in column), "oracle amplitudes"
        )
        need(observed == tuple(square(z) / 2 for z in column), "oracle counts")
        need(sum(observed) + Fraction(1, 2) == 1, "including all source failures")
        return observed

    conjugated = conjugate(V)
    forward = table(V, DELAY, v, delay)
    reverse = table(conjugated, DELAY, vc, delay)
    need(
        forward == (Fraction(13, 64), Fraction(17, 64), Fraction(1, 32)), "forward raw"
    )
    need(reverse == (Fraction(13, 64), Fraction(1, 64), Fraction(9, 32)), "reverse raw")
    # Conjugating all phases also conjugates the source up to global sign.
    need(
        table(conjugated, conjugate(DELAY), vc, adjoint(delay)) == forward,
        "global conjugation",
    )
    need(
        table(V, (), v, identity) == table(conjugated, (), vc, identity),
        "constant delay",
    )
    two_equal: Matrix = ((1, 0, 0), (0, 1j, 0), (0, 0, 1j))
    first_delay = DELAY[:1]
    need(
        table(V, first_delay, v, two_equal)
        == table(conjugated, first_delay, vc, two_equal),
        "two-fold degenerate delay",
    )
    print("Ranked source: physical ports 0..5 = (4,4,4,4,0,0) / 16 source tickets;")
    print("  one coherent keep outcome {0,3}: 8/16; rejected {1,2}: 8/16.")
    print(f"Paired V: same entry weights as conjugate(V), J = {j}.")
    for label, result in (("V", forward), ("conjugate(V)", reverse)):
        print(f"{label}, fixed delay:")
        print("  per herald =", ", ".join(str(2 * p) for p in result))
        print("  per injection =", ", ".join(map(str, result)), "; rejected = 1/2")
    print(
        "Global conjugation unchanged; both (1,1,1) and (1,i,i) erase the table difference."
    )
    print("Full six-port word: compressed integer counts, not ticket enumeration.")


if __name__ == "__main__":
    main()
