"""Conditional two-copy discriminator using an exact Mermin-Peres square.

SUPPLIED: a real four-dimensional tensor carrier per party, two shared Bell
pairs, Pauli-product observables, sharp joint-projector measurement and the
trace probability rule. CNOT and scaled Hadamard circuits below verify the
joint readouts but do not derive these operations from the raw opposition
primitive. Local Pauli axis orientations need no continuously tunable angle.

This is not an experiment or a quantum derivation. The exact classical cap
requires fresh independent uniform questions conditional on the complete
past and pre-question shared/local hidden state, with no within-trial communication.
Invalid/absent outputs count as failures. Arbitrary between-trial memory is
allowed under that conditional question contract. A realized finite-sample
score can exceed its expectation; no significance calculation is made here.

Existing theory_experiments/native_bell_bridge.py and bell_trial_test.py
cover different, explicitly supplied CHSH bridges. This standalone probe
does not modify their candidate statuses, tests, or experimental records.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod

Matrix = tuple[tuple[F, ...], ...]
Output = tuple[int, ...] | None
Strategy = tuple[Output, ...]
SIGNS = (-1, 1)
COL_PARITY = (1, 1, -1)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def mat(rows: tuple[tuple[int, ...], ...]) -> Matrix:
    return tuple(tuple(F(x) for x in row) for row in rows)


def identity(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def scale(a: Matrix, n: F | int) -> Matrix:
    return tuple(tuple(n * x for x in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(r, s, strict=True))
        for r, s in zip(a, b, strict=True)
    )


def transpose(a: Matrix) -> Matrix:
    return tuple(tuple(a[j][i] for j in range(len(a))) for i in range(len(a)))


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((a[i][k] * b[k][j] for k in range(len(a))), F(0)) for j in range(len(a))
        )
        for i in range(len(a))
    )


def trace(a: Matrix) -> F:
    return sum((a[i][i] for i in range(len(a))), F(0))


def kron(a: Matrix, b: Matrix) -> Matrix:
    n, m = len(a), len(b)
    return tuple(
        tuple(a[i // m][j // m] * b[i % m][j % m] for j in range(n * m))
        for i in range(n * m)
    )


I = identity(2)
X = mat(((0, 1), (1, 0)))
Z = mat(((1, 0), (0, -1)))
H = mat(((1, 1), (1, -1)))  # Unnormalized, squared norm gain 2.
YY = mat(((0, 0, 0, -1), (0, 0, 1, 0), (0, 1, 0, 0), (-1, 0, 0, 0)))
I4 = identity(4)
SQUARE = (
    (kron(X, I), kron(I, X), kron(X, X)),
    (kron(I, Z), kron(Z, I), kron(Z, Z)),
    (kron(X, Z), kron(Z, X), YY),
)
COLUMNS = tuple(tuple(SQUARE[r][c] for r in range(3)) for c in range(3))
CNOT = tuple(
    tuple(F(i == (j ^ (1 if j & 2 else 0))) for j in range(4)) for i in range(4)
)


def outputs(parity: int) -> tuple[tuple[int, ...], ...]:
    return tuple((a, b, parity * a * b) for a, b in product(SIGNS, repeat=2))


def valid(output: Output, parity: int) -> bool:
    return (
        output is not None
        and len(output) == 3
        and all(type(x) is int and x in SIGNS for x in output)
        and prod(output) == parity
    )


def win(a: Output, b: Output, row: int, col: int) -> bool:
    return (
        a is not None
        and b is not None
        and valid(a, 1)
        and valid(b, COL_PARITY[col])
        and a[col] == b[row]
    )


def projector(context: tuple[Matrix, ...], output: tuple[int, ...]) -> Matrix:
    return scale(
        mm(
            add(I4, scale(context[0], output[0])), add(I4, scale(context[1], output[1]))
        ),
        F(1, 4),
    )


def contexts() -> tuple[tuple[tuple[Matrix, ...], int], ...]:
    return tuple((row, 1) for row in SQUARE) + tuple(
        zip(COLUMNS, COL_PARITY, strict=True)
    )


def operator_controls() -> None:
    for context, parity in contexts():
        for a, b in product(context, repeat=2):
            need(mm(a, b) == mm(b, a), "context observables must commute")
            need(mm(a, a) == I4 and transpose(a) == a, "real involutory observable")
        need(
            mm(mm(context[0], context[1]), context[2]) == scale(I4, parity),
            "context product parity",
        )
        projectors = tuple(projector(context, a) for a in outputs(parity))
        total = scale(I4, 0)
        for i, p in enumerate(projectors):
            need(
                mm(p, p) == p and transpose(p) == p and trace(p) == 1,
                "rank-one orthogonal projector",
            )
            for j, q in enumerate(projectors):
                if i != j:
                    need(mm(p, q) == scale(I4, 0), "outcome orthogonality")
            for value, observable in zip(outputs(parity)[i], context, strict=True):
                need(mm(observable, p) == scale(p, value), "joint eigenvalues")
            total = add(total, p)
        need(total == I4, "complete local measurement")


def joint_probability(p: Matrix, q: Matrix) -> F:
    # On |Phi4> = sum_i |i,i>/2, i.e. two Bell pairs regrouped by party:
    # <Phi4|P tensor Q|Phi4> = Tr(P^T Q)/4.
    direct = sum((p[i][j] * q[i][j] for i, j in product(range(4), repeat=2)), F(0)) / 4
    need(direct == trace(mm(transpose(p), q)) / 4, "Bell-pair contraction")
    return direct


def distribution_controls() -> dict[tuple[int, int], tuple[F, ...]]:
    distributions: dict[tuple[int, int], tuple[F, ...]] = {}
    alice_marginals: dict[int, tuple[F, ...]] = {}
    bob_marginals: dict[int, tuple[F, ...]] = {}
    for r, c in product(range(3), repeat=2):
        alice, bob = outputs(1), outputs(COL_PARITY[c])
        probabilities = tuple(
            joint_probability(projector(SQUARE[r], a), projector(COLUMNS[c], b))
            for a, b in product(alice, bob)
        )
        need(
            sum(probabilities) == 1 and min(probabilities) >= 0,
            "normalized joint probability",
        )
        need(
            Counter(probabilities) == {F(0): 8, F(1, 8): 8}, "full sixteen-outcome law"
        )
        for (a, b), p in zip(product(alice, bob), probabilities, strict=True):
            need(
                p == (F(1, 8) if win(a, b, r, c) else F(0)), "perfect intersection law"
            )
        am = tuple(sum(probabilities[4 * i : 4 * i + 4], F(0)) for i in range(4))
        bm = tuple(sum(probabilities[i::4], F(0)) for i in range(4))
        need(am == bm == (F(1, 4),) * 4, "uniform no-signalling marginals")
        need(
            alice_marginals.setdefault(r, am) == am
            and bob_marginals.setdefault(c, bm) == bm,
            "remote context affected marginal",
        )
        distributions[r, c] = probabilities
    need(len(distributions) == 9, "missing setting")
    return distributions


def partial_trace(p: Matrix) -> Matrix:
    return tuple(
        tuple(sum((p[2 * i + k][2 * j + k] for k in range(2)), F(0)) for j in range(2))
        for i in range(2)
    )


def circuit_controls() -> tuple[str, ...]:
    # U acts on the state BEFORE computational Z readout. No irrational
    # entries: U^T U = gain*I, with gain divided out exactly in conjugation.
    bell = mm(kron(H, I), CNOT)
    row3 = mm(bell, kron(I, H))
    targets = ((bell, 2, COLUMNS[2]), (row3, 4, SQUARE[2]))
    for u, gain, context in targets:
        need(mm(transpose(u), u) == scale(I4, gain), "scaled circuit isometry")
        for observable, target in zip(
            (kron(Z, I), kron(I, Z)), context[:2], strict=True
        ):
            need(
                scale(mm(mm(transpose(u), observable), u), F(1, gain)) == target,
                "CNOT/H joint analyzer",
            )
    entangled: list[str] = []
    names = ("row1", "row2", "row3", "column1", "column2", "column3")
    for name, (context, parity) in zip(names, contexts(), strict=True):
        purities = {
            trace(
                mm(
                    partial_trace(projector(context, a)),
                    partial_trace(projector(context, a)),
                )
            )
            for a in outputs(parity)
        }
        if name in ("row3", "column3"):
            need(
                purities == {F(1, 2)},
                "joint context must have entangled eigenprojectors",
            )
            entangled.append(name)
        else:
            need(purities == {F(1)}, "product context purity")
    # A product local analyzer produces product rank-one projectors with
    # pure reduced states. It cannot equal either entangled PVM above.
    need(entangled == ["row3", "column3"], "entangled-context classification")
    return tuple(entangled)


def score(a: Strategy, b: Strategy) -> int:
    return sum(win(a[r], b[c], r, c) for r, c in product(range(3), repeat=2))


def classical_controls() -> tuple[int, int, list[tuple[Strategy, Strategy]]]:
    alice = tuple(product(outputs(1), repeat=3))
    bob = tuple(product(*(outputs(p) for p in COL_PARITY)))
    scores: Counter[int] = Counter()
    by_cell: list[tuple[Strategy, Strategy]] = []
    tables = tuple(product(alice, bob))
    for a, b in tables:
        scores[score(a, b)] += 1
    need(len(tables) == 4**3 * 4**3 == 4096, "classical response-table coverage")
    need(max(scores) == 8 and scores[8] > 0, "tight uniform classical cap")
    for r, c in product(range(3), repeat=2):
        by_cell.append(next((a, b) for a, b in tables if win(a[r], b[c], r, c)))
    # Choosing any table, or a stochastic mixture, as a function of prior
    # history leaves its conditional fresh-uniform score <=8/9. This is a
    # convexity consequence of exhaustive table coverage, not an IID claim.
    for past in range(10):
        a, b = tables[(379 * past + 23) % len(tables)]
        need(F(score(a, b), 9) <= F(8, 9), "history-selected table cap")
    # Negative control: aggregate-uniform but predictable settings, or a
    # hidden variable correlated with the present setting, permit 9/9.
    need(
        all(
            win(a[r], b[c], r, c)
            for (r, c), (a, b) in zip(product(range(3), repeat=2), by_cell, strict=True)
        ),
        "predictable-question escape",
    )
    return max(scores), scores[8], by_cell


def loss_controls() -> tuple[F, F, F]:
    alice = tuple(product((*outputs(1), None), repeat=3))
    bob = tuple(product(*((*outputs(p), None) for p in COL_PARITY)))
    maximum_unconditional, maximum_perfect_detected = 0, 0
    for a, b in product(alice, bob):
        wins = score(a, b)
        detected = sum(
            a[r] is not None and b[c] is not None
            for r, c in product(range(3), repeat=2)
        )
        maximum_unconditional = max(maximum_unconditional, wins)
        if wins == detected:
            maximum_perfect_detected = max(maximum_perfect_detected, detected)
        # Filling absent outputs with valid local answers cannot remove a
        # prior win. Any wrong-parity or malformed answer is equally losing
        # on all its cells and may first be replaced with an abort.
        filled_a = tuple(v if v is not None else outputs(1)[0] for v in a)
        filled_b = tuple(
            v if v is not None else outputs(COL_PARITY[c])[0] for c, v in enumerate(b)
        )
        need(wins <= score(filled_a, filled_b) <= 8, "loss completion domination")
    need(len(alice) * len(bob) == 15625, "abort-table coverage")
    need(
        maximum_unconditional == 8 and maximum_perfect_detected == 6,
        "untrusted-loss bounds",
    )
    abort_alice: Strategy = ((1, 1, 1), (1, 1, 1), None)
    abort_bob: Strategy = ((1, 1, 1), (1, 1, 1), (1, 1, -1))
    need(score(abort_alice, abort_bob) == 6, "simple local abort witness")
    for invalid in (None, (), (1, 1), (0, 1, 1), (-1, 1, 1), (True, 1, 1)):
        need(not win(invalid, (1, 1, 1), 0, 0), "invalid output not counted as failure")
    return F(maximum_unconditional, 9), F(6, 9), F(6, 6)


def main() -> None:
    operator_controls()
    distributions = distribution_controls()
    entangled = circuit_controls()
    best, attaining, _ = classical_controls()
    unconditional, efficiency, selected = loss_controls()
    print("PASS exact conditional magic-square probe; all checks survive -O.")
    print(
        f"Full law: {len(distributions)} settings, each 16 outcome pairs: eight 1/8 wins and eight zero losses; marginals 1/4."
    )
    print(
        f"Classical exhaustive 4096 valid tables: maximum {best}/9, attained by {attaining} tables."
    )
    print(
        f"Exhaustive 15625 local-abort tables: unconditional cap {unconditional}; perfect selected score {selected} at joint detection {efficiency}."
    )
    print(
        "Abort witness: Alice suppresses third row; Bob answers +++,+++,++-. Retained score 1, unconditional score 2/3."
    )
    print(
        f"Entangled local PVMs: {entangled}; scaled H/CNOT circuits checked exactly. Product Pauli analyzers alone do not implement them."
    )
    print(
        "Memory is allowed with conditionally fresh uniform questions; aggregate uniformity without freshness permits classical 9/9."
    )
    print(
        "SUPPLIED tensor/Bell-pair preparation, joint projectors, CNOT, and probability rule; no raw-primitive derivation or empirical significance."
    )


if __name__ == "__main__":
    main()
