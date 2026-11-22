"""Finite exchange-sign relators on a SUPPLIED hard-core occupation carrier.

Encoded one-particle controls supply native T and single-mode phase i
(see gaussian_dyadic_words.py). The finite word

    C = diag(-i,1) T diag(1,i) = [[1,1],[1,-1]]/(1+i)

satisfies C X C^dagger=Z, with X=T^2 the mode swap and Z=diag(1,-1).
No infinitesimal commutator is used. Hard-core capacity (0/1 per complete
mode), coherent number-preserving lifts, unchanged outside occupations,
and a phase gate counting the addressed occupancy are SUPPLIED.

CRUCIAL additional test: the one-particle identity must lift to the SAME
word identity up to one scalar on the WHOLE fixed-number sector. Its
one-particle validity alone does not imply that test. On pair-empty and
pair-full one-dimensional sectors C contributes only cancelling phases.
The tested identity therefore forces X_full/X_empty=-1. Four modes with
total number two compare |12> and |34> in the same sector, so a common
projective scalar cancels. Comparing different total numbers instead
would leave independent projective phases uncalibrated. A spectator- or
occupancy-dependent extra phase in Z defeats the inference; the exact
unsigned control below passes only after violating the counting-phase
calibration. The test leaves both +/-i choices for the full-sector T phase.

LOCAL IS NOT AUTOMATICALLY GLOBALLY SPECTATOR-BLIND. Assigning the same
two-bit FSWAP to EVERY pair passes the local CXC^dagger test, but fails
s_13=s_12 s_23 s_12. The one-particle-identity loop has phase -1 on |12>
and +1 on |14>. A fixed-number coherent C preparation of these alternatives
and its inverse read the relative sign as distinct occupation outputs.
An incoherent mixture cannot. The exterior/Jordan-Wigner comparator gives
the missing occupied-between sign on nonadjacent single-occupation swaps
and passes this loop; it is supplied as a consistent comparator, not
uniquely derived from the two finite relations. Adjacent FSWAPs agree with
it. A physical direct path may instead be a different braid/path or retain
memory; then equality of one-particle matrices need not mean that the
many-body control words are physically identical.

BOSONIC COUNTERCONTROL: Sym^2(C) also obeys the finite word relation, while
the one-in-each-mode symmetric state has swap eigenvalue +1. Its pair
number-two sector also contains |20>,|02>; C mixes those with |11>.
Thus the scalar-sector cancellation step fails when hard-core capacity is
removed. The word identity does not derive capacity or fermionic physics.

The older probe_signed_slot_transfers.py imposed the full transfer
commutator [E_ij,E_jl]=E_il. Here two explicit finite word comparisons have
less coverage; they do not establish that Lie algebra or a full group
representation. Its adjacent-sector countercontrol also remains: identical
number-preserving transfers can coexist with different creation phases and
failed CAR. We replay that existing control rather than duplicate it.

All tensor/amplitude/number/readout and encoded-control assumptions remain
explicit. No cross-number phase reference, particle identification, CAR,
spin-statistics, universal exchange law, or QM closure is established.
Finite exact checks below are not a Lean universal proof.

Run: python3 -B -O -m scripts.probe_exchange_sign_relator
"""

import sys
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    CROSS,
    DIAG,
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    eye,
    g,
    run,
    unitary,
)
from scripts.probe_signed_slot_transfers import adjacent_sector_countermodel

Vector = tuple[Gaussian, ...]
T: Matrix = ((DIAG, CROSS), (CROSS, DIAG))
X: Matrix = ((ZERO, ONE), (ONE, ZERO))
Z: Matrix = ((ONE, ZERO), (ZERO, g(-1)))
C_WORD: tuple[Move, ...] = (
    ("i", 1, 1),
    ("T", 0, 1),
    ("i", 0, 0),
    ("i", 0, 0),
    ("i", 0, 0),
)


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(value.star() for value in col) for col in zip(*a, strict=True))


def scaled(value: Gaussian, a: Matrix) -> Matrix:
    return tuple(tuple(value * entry for entry in row) for row in a)


def apply(a: Matrix, vector: Vector) -> Vector:
    return tuple(
        sum((x * y for x, y in zip(row, vector, strict=True)), ZERO) for row in a
    )


def determinant(a: Matrix) -> Gaussian:
    total = ZERO
    for order in permutations(range(len(a))):
        inversions = sum(order[i] > order[j] for i, j in combinations(range(len(a)), 2))
        term = g((-1) ** inversions)
        for row, col in enumerate(order):
            term = term * a[row][col]
        total = total + term
    return total


def masks(n: int, k: int) -> tuple[int, ...]:
    return tuple(mask for mask in range(1 << n) if mask.bit_count() == k)


def phase_count(n: int, k: int, slot: int, phase: Gaussian) -> Matrix:
    states = masks(n, k)
    return tuple(
        tuple(
            (phase if state & (1 << slot) else ONE) if i == j else ZERO
            for j in range(len(states))
        )
        for i, state in enumerate(states)
    )


def local_hardcore(
    u: Matrix,
    n: int,
    k: int,
    pair: tuple[int, int],
    *,
    full: Gaussian,
    empty: Gaussian = ONE,
    between_sign: bool = False,
) -> Matrix:
    """Preserve outside occupations; optional JW sign is a comparator."""
    states = masks(n, k)
    index = {state: i for i, state in enumerate(states)}
    result = [[ZERO for _ in states] for _ in states]
    a, b = pair
    need(a < b, "ordered address pair")
    pair_mask = (1 << a) | (1 << b)
    for col, state in enumerate(states):
        count = (state & pair_mask).bit_count()
        if count != 1:
            result[col][col] = empty if count == 0 else full
            continue
        incoming = 0 if state & (1 << a) else 1
        source_slot = pair[incoming]
        for outgoing, target_slot in enumerate(pair):
            target = (state ^ (1 << source_slot)) | (1 << target_slot)
            parity = sum(bool(state & (1 << s)) for s in range(a + 1, b))
            sign = -1 if between_sign and incoming != outgoing and parity % 2 else 1
            result[index[target]][col] = g(sign) * u[outgoing][incoming]
    return tuple(tuple(row) for row in result)


def one_particle_embed(u: Matrix, n: int, pair: tuple[int, int]) -> Matrix:
    position = {slot: index for index, slot in enumerate(pair)}
    return tuple(
        tuple(
            u[position[i]][position[j]]
            if i in position and j in position
            else ONE
            if i == j
            else ZERO
            for j in range(n)
        )
        for i in range(n)
    )


def exterior_lift(u: Matrix, k: int) -> Matrix:
    states = masks(len(u), k)
    occupied = [tuple(i for i in range(len(u)) if state & (1 << i)) for state in states]
    return tuple(
        tuple(
            determinant(tuple(tuple(u[i][j] for j in source) for i in target))
            for source in occupied
        )
        for target in occupied
    )


def native_identity() -> Matrix:
    c = run(eye(2), C_WORD)
    need(c == ((CROSS, CROSS), (CROSS, g(-1) * CROSS)), "encoded native C word")
    need(unitary(c) and mul(T, T) == X, "native unitary and swap square")
    need(mul(c, mul(X, adjoint(c))) == Z, "one-particle exact finite relator")
    inverse_word = tuple(move for move in reversed(C_WORD) for _ in range(3))
    need(run(eye(2), inverse_word) == adjoint(c), "inverse uses native cubes")
    return c


def local_relator_controls() -> None:
    n, k, pair = 4, 2, (0, 1)
    states = masks(n, k)
    full_index, empty_index = states.index(0b0011), states.index(0b1100)
    z = phase_count(n, k, 1, g(-1))
    left, right = phase_count(n, k, 0, g(0, -1)), phase_count(n, k, 1, I)
    accepted = []
    for full in (ONE, I, g(-1), g(0, -1)):
        t = local_hardcore(T, n, k, pair, full=full)
        c = mul(left, mul(t, right))
        x = mul(t, t)
        need(unitary(t) and unitary(c), "unitary hard-core candidates")
        conjugated = mul(c, mul(x, adjoint(c)))
        if conjugated == z:
            accepted.append(full)
            need(
                x[full_index][full_index] == g(-1) * x[empty_index][empty_index],
                "relative full/empty swap sign",
            )
            for projective in (ONE, I, g(-1), g(0, -1)):
                chosen_x = scaled(projective, x)
                need(
                    mul(c, mul(chosen_x, adjoint(c))) == scaled(projective, z),
                    "one common projective representative phase",
                )
                need(
                    chosen_x[full_index][full_index]
                    == g(-1) * chosen_x[empty_index][empty_index],
                    "projective scalar cancels within fixed total number",
                )
        if full == ONE:
            need(
                conjugated != z,
                "one-particle identity alone does not constrain unsigned lift",
            )
            repaired_z = tuple(
                tuple(
                    g(-1) * value if row == full_index else value for value in entries
                )
                for row, entries in enumerate(z)
            )
            need(
                conjugated == repaired_z,
                "extra occupancy/spectator phase can counterfeit the relator",
            )
            need(
                repaired_z[full_index][full_index]
                == repaired_z[empty_index][empty_index]
                == ONE,
                "counterfeit violates occupancy-counting calibration",
            )
    need(
        accepted == [I, g(0, -1)], "finite relator leaves both full-sector square roots"
    )


def exterior_controls(c: Matrix) -> None:
    for k in range(5):
        for pair in combinations(range(4), 2):
            for u in (T, X, Z, c):
                explicit = local_hardcore(
                    u, 4, k, pair, full=determinant(u), between_sign=True
                )
                exterior = exterior_lift(one_particle_embed(u, 4, pair), k)
                need(
                    explicit == exterior and unitary(exterior),
                    "proper exterior/JW comparator",
                )
                if pair[1] == pair[0] + 1:
                    naive = local_hardcore(u, 4, k, pair, full=determinant(u))
                    need(naive == exterior, "adjacent local lift agrees with exterior")


def permutation_loop_readout(c: Matrix) -> None:
    n, k = 4, 2
    pairs = ((0, 1), (1, 2), (0, 2))
    one = [one_particle_embed(X, n, pair) for pair in pairs]
    need(
        one[2] == mul(one[0], mul(one[1], one[0])), "one-particle permutation relation"
    )
    naive = [local_hardcore(X, n, k, pair, full=g(-1)) for pair in pairs]
    exterior = [exterior_lift(one_particle_embed(X, n, pair), k) for pair in pairs]
    for pair, swap in zip(pairs, naive, strict=True):
        t = local_hardcore(T, n, k, pair, full=I)
        c_local = mul(
            phase_count(n, k, pair[0], g(0, -1)),
            mul(t, phase_count(n, k, pair[1], I)),
        )
        need(mul(t, t) == swap, "each naive swap is its native lift square")
        need(
            mul(c_local, mul(swap, adjoint(c_local)))
            == phase_count(n, k, pair[1], g(-1)),
            "all tested naive pairs pass the local relator",
        )
    bad_loop = mul(naive[2], mul(naive[0], mul(naive[1], naive[0])))
    good_loop = mul(exterior[2], mul(exterior[0], mul(exterior[1], exterior[0])))
    states = masks(n, k)
    first, other = states.index(0b0011), states.index(0b1001)
    need(good_loop == eye(len(states)), "exterior identity loop")
    need(
        bad_loop[first][first] == g(-1) and bad_loop[other][other] == ONE,
        "spectator-blind loop has a physical relative sign",
    )
    prep = exterior_lift(one_particle_embed(c, n, (1, 3)), k)
    blind_prep = local_hardcore(c, n, k, (1, 3), full=determinant(c))
    source = tuple(ONE if j == first else ZERO for j in range(len(states)))
    prepared = apply(prep, source)
    need(
        prepared == apply(blind_prep, source),
        "same native preparation in both controls on this source",
    )
    need(
        prepared
        == tuple(CROSS if j in (first, other) else ZERO for j in range(len(states))),
        "fixed-number coherent alternatives",
    )
    outputs = []
    for loop in (good_loop, bad_loop):
        out = apply(adjoint(prep), apply(loop, prepared))
        need(
            out == apply(adjoint(blind_prep), apply(loop, prepared)),
            "same inverse preparation on the tested coherent subspace",
        )
        need(sum((value.norm2() for value in out), F(0)) == 1, "full-emission readout")
        outputs.append((out[first].norm2(), out[other].norm2()))
        incoherent = []
        for selected in (first, other):
            branch = tuple(
                prepared[j] if j == selected else ZERO for j in range(len(states))
            )
            incoherent.append(apply(adjoint(prep), apply(loop, branch)))
        need(
            tuple(
                sum((branch[j].norm2() for branch in incoherent), F(0))
                for j in (first, other)
            )
            == (F(1, 2), F(1, 2)),
            "which-alternative record hides the loop sign",
        )
    need(
        outputs == [(F(1), F(0)), (F(0), F(1))],
        "inverse preparation reads relative phase at fixed number",
    )


def tensor_square(a: Matrix) -> Matrix:
    return tuple(
        tuple(a[i][j] * a[k][ell] for j, ell in product(range(2), repeat=2))
        for i, k in product(range(2), repeat=2)
    )


def bosonic_control(c: Matrix) -> None:
    c2, x2, z2 = (tensor_square(u) for u in (c, X, Z))
    particle_swap = tuple(eye(4)[i] for i in (0, 2, 1, 3))
    for lifted in (c2, x2, z2):
        need(
            mul(lifted, particle_swap) == mul(particle_swap, lifted),
            "the symmetric two-copy subspace is invariant",
        )
    need(
        unitary(c2) and mul(c2, mul(x2, adjoint(c2))) == z2,
        "positive symmetric-square lift retains the relator",
    )
    one_each = (ZERO, ONE, ONE, ZERO)
    need(apply(x2, one_each) == one_each, "bosonic one-each state has swap phase plus")
    mixed = apply(c2, one_each)
    need(
        mixed == (g(0, -1), ZERO, ZERO, I),
        "C accesses |20> and |02> instead of acting as scalar",
    )
    need(
        sum((value.norm2() for value in mixed), F(0)) == 2,
        "positive bosonic norm preserved",
    )


def main() -> None:
    c = native_identity()
    local_relator_controls()
    exterior_controls(c)
    permutation_loop_readout(c)
    bosonic_control(c)
    adjacent_sector_countermodel()
    print(
        "Native finite CXC^dagger=Z: calibrated fixed-number projective relator forces full/empty swap ratio -1; both T full phases +/-i remain."
    )
    print(
        "Unsigned hard-core control fails unless Z gains an uncalibrated many-body phase. One-particle agreement alone is insufficient."
    )
    print(
        "All-pair spectator-blind FSWAP fails the identity loop: coherent fixed-number inverse-preparation returns 0 vs exterior 1; incoherent controls both give 1/2."
    )
    print(
        "Bosonic Sym^2 passes the word relation with swap +1 by accessing double occupancies. Hard-core capacity, coherent lifts and counting phase were supplied."
    )
    print(
        "No full transfer algebra, unique lift, creation law, CAR, spin-statistics or physical Pauli derivation is claimed."
    )


if __name__ == "__main__":
    main()
