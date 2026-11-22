"""Six packet bits do not by themselves derive a fermionic 16-state carrier.

Use the six tetrahedral edges, ordered in complementary pairs as in
probe_six_packet_sectors.py. Their real permutation representation E has
an invariant uniform vector u and W=u-perp of dimension five, split 3+2.
This probe distinguishes unsigned bit labels from a SUPPLIED coherent
exterior algebra. No statistics, spacetime chirality, quantum readout,
gauge fields, or particle identifications are derived.

CHARACTER WALL. Even six-bit masks modulo global complement give 16
unsigned basis labels, with S4 orbits 1,3,12. On vertex cycle classes
(identity, transposition, double transposition, 3-cycle, 4-cycle), their
characters are (16,4,4,1,2), whereas Lambda^even(W) has (16,0,0,1,0).
These representations are not isomorphic. Relabeling or rephasing the
basis cannot change a character. S4 matching is not established by a
state count or by the common value on a 3-cycle.

SIGNED HODGE HALVES. Every S4 permutation of the six edges has determinant
+1. The complex-LINEAR Euclidean Hodge star on Lambda^even(E) therefore
commutes with S4, squares to one, and has two 16-dimensional eigenspaces.
Both have the desired S4 character. However the native raw gate
U=T_(0,1) T_(2,3)^(-1) is unitary, determinant one and fixes u, yet does
not preserve either Hodge half. In a real orthonormal pair frame its
phases are i,-i,1,1,1,1. For alpha=(e0-e1) wedge (e4-e5)/2,
Gamma(U) alpha=i alpha and Gamma(U)(star alpha)=-i star alpha, so the
entire plus vector alpha+star alpha is sent into the minus space.
The Hermitian star is anti-linear and commutes with this SU(6) gate, but
its fixed set is a real form, NOT a complex 16-dimensional subspace:
star_H(i psi)=-i star_H(psi). This does not repair the complex quotient.

UNIFORM VACUUM. On the SUPPLIED fermionic six-mode Fock space, the even
projector P0=I-a(u)^dagger a(u) has rank 16, with grade ranks 1,10,5,0.
Its image is Lambda^even(W). It commutes with every number-preserving
exterior lift of a unitary fixing u. This is a genuine invariant carrier,
not a proof that the delocalized uniform-vacuum constraint is physically
prepared. Its raw occupation-basis projector has 1/6 coefficients and is
not a bitwise complement identification or a Gaussian-dyadic matrix.
The invariant projector and an implementable selective preparation are
different obligations. Euclidean star interchanges P0 and I-P0.

NATURAL ALTERNATIVE. Vacuum plus raw two-particle states, Lambda^0(E)
plus Lambda^2(E), also has dimension 16 and the same S4 character. It is
invariant under EVERY exterior U(6) lift, including the gate above. On
fixed-uniform SU(5), however, it is 1+Lambda^2(W)+W rather than the desired
1+Lambda^2(W)+W*. Thus finite symmetry, gate stability and dimension still
do not select the desired carrier. With the supplied slot weights
(-2,-2,-2,3,3), the desired even charge counts are
    0:1, -4:3, 1:6, 6:1, 2:3, -3:2.
The alternative replaces the last five states by -2:3, 3:2. Its cubic
charge trace is 60 rather than zero. Calling this an anomaly would require
the additional left-Weyl field interpretation; here it is only a trace.

ODD CONJUGATE BOUNDARY. For determinant-one action on W, the odd exterior
carrier is conjugate to the even carrier and its charges are negated.
For general fixed-uniform U(5), the relation has a determinant twist:
Lambda^odd(W) = det(W) tensor conjugate(Lambda^even(W)). A single native
within-pair T has det(W)=i and explicitly fails the untwisted statement.
Continuous block charges/groups remain supplied comparison structure.

BIT-ONLY ESCAPE, WITH ITS PRICE. Signed exchange can be encoded on ordinary
coherent occupation qubits using the inversion parity
(-1)^sum_{i<j, p(i)>p(j)} n_i*n_j, or Jordan-Wigner prefix signs. The code
checks the cocycle and CAR exactly. This adds occupation-dependent phase
operations; it is not a harmless basis rephasing and is not forced by
unsigned occupancy. Classical bit labels alone do not observe those phases.
Signless hard-core lowering operators give a concrete
CAR counterexample. Such an encoding establishes finite algebraic capacity,
not a physical derivation of fermionic exchange or the choice of carrier.

All checks are finite and exact, active under -O; no fit or numerical
optimizer is used. The general arguments above are not Lean proofs.
Run: python3 -B -O -m scripts.probe_six_packet_matter
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
from typing import Literal

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    apply,
    eye,
    g,
    unitary,
)
from scripts.probe_six_packet_sectors import PACKETS

Vector = dict[int, Gaussian]
Permutation = tuple[int, ...]
Cycle = tuple[int, ...]
EVEN = tuple(mask for mask in range(64) if mask.bit_count() % 2 == 0)
LOW = tuple(mask for mask in EVEN if mask.bit_count() <= 2)
CLASSES = ((1, 1, 1, 1), (2, 1, 1), (2, 2), (3, 1), (4,))
SIZES = (1, 6, 3, 8, 6)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def basis(mask: int) -> Vector:
    return {mask: ONE}


def plus(v: Vector, w: Vector) -> Vector:
    out = dict(v)
    for mask, coefficient in w.items():
        out[mask] = out.get(mask, ZERO) + coefficient
    return {mask: z for mask, z in out.items() if z != ZERO}


def scaled(z: Gaussian, v: Vector) -> Vector:
    return {
        mask: z * coefficient
        for mask, coefficient in v.items()
        if z * coefficient != ZERO
    }


def inner(v: Vector, w: Vector) -> Gaussian:
    return sum((z.star() * w.get(mask, ZERO) for mask, z in v.items()), ZERO)


def canonical(mask: int) -> int:
    need(mask in EVEN, "even mask required")
    return mask if mask.bit_count() <= 2 else mask ^ 63


def cycles(permutation: Permutation) -> Cycle:
    seen: set[int] = set()
    lengths: list[int] = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        size, current = 0, start
        while current not in seen:
            seen.add(current)
            size += 1
            current = permutation[current]
        lengths.append(size)
    return tuple(sorted(lengths, reverse=True))


def signed_permutation(mask: int, permutation: Permutation) -> tuple[int, int]:
    occupied = [permutation[i] for i in range(6) if mask >> i & 1]
    parity = sum(a > b for j, a in enumerate(occupied) for b in occupied[j + 1 :])
    return sum(1 << j for j in occupied), (-1) ** parity


def permute(v: Vector, permutation: Permutation) -> Vector:
    out: Vector = {}
    for mask, coefficient in v.items():
        target, sign = signed_permutation(mask, permutation)
        out[target] = g(sign) * coefficient
    return out


def hodge(v: Vector, *, anti: bool = False) -> Vector:
    out: Vector = {}
    for mask, coefficient in v.items():
        k = mask.bit_count()
        parity = sum(i for i in range(6) if mask >> i & 1) - k * (k - 1) // 2
        out[mask ^ 63] = g((-1) ** parity) * (
            coefficient.star() if anti else coefficient
        )
    return out


def mode_step(mask: int, slot: int, create: bool) -> tuple[int, int] | None:
    occupied = bool(mask >> slot & 1)
    if occupied == create:
        return None
    sign = (-1) ** (mask & ((1 << slot) - 1)).bit_count()
    return mask ^ (1 << slot), sign


def uniform_step(v: Vector, *, create: bool) -> Vector:
    out: Vector = {}
    for mask, coefficient in v.items():
        for slot in range(6):
            target = mode_step(mask, slot, create)
            if target is not None:
                index, sign = target
                out[index] = out.get(index, ZERO) + g(sign) * coefficient
    return {mask: z for mask, z in out.items() if z != ZERO}


def uniform_vacuum(v: Vector) -> Vector:
    number = scaled(
        g(F(1, 6)), uniform_step(uniform_step(v, create=False), create=True)
    )
    return plus(v, scaled(g(-1), number))


def exterior_column(u: Matrix, mask: int) -> Vector:
    out = basis(0)
    # Left creation in reversed input order gives Ue_i1 wedge ... wedge Ue_ik.
    for column in reversed([i for i in range(6) if mask >> i & 1]):
        following: Vector = {}
        for occupied, coefficient in out.items():
            for row in range(6):
                if u[row][column] == ZERO:
                    continue
                target = mode_step(occupied, row, True)
                if target is not None:
                    index, sign = target
                    value = g(sign) * u[row][column] * coefficient
                    following[index] = following.get(index, ZERO) + value
        out = {index: z for index, z in following.items() if z != ZERO}
    return out


def act(columns: dict[int, Vector], v: Vector) -> Vector:
    out: Vector = {}
    for mask, coefficient in v.items():
        out = plus(out, scaled(coefficient, columns[mask]))
    return out


def exterior_w_character(edge_permutation: Permutation) -> int:
    polynomial = [1]
    for length in cycles(edge_permutation):
        updated = [0] * (len(polynomial) + length)
        for degree, coefficient in enumerate(polynomial):
            updated[degree] += coefficient
            updated[degree + length] += (-1) ** (length + 1) * coefficient
        polynomial = updated
    # Remove the invariant uniform eigenvalue: det(I+tE)=(1+t)det(I+tW).
    quotient: list[int] = []
    for degree in range(6):
        quotient.append(polynomial[degree] - (quotient[-1] if quotient else 0))
    need(polynomial[6] == quotient[5], "uniform factor division")
    return sum(quotient[degree] for degree in (0, 2, 4))


def representation_controls() -> tuple[Permutation, ...]:
    need(len(EVEN) == 32 and len(LOW) == 16, "mask dimensions")
    need({canonical(mask) for mask in EVEN} == set(LOW), "complement classes")
    rows: dict[Cycle, set[tuple[int, int, int]]] = {}
    sizes: Counter[Cycle] = Counter()
    moves: list[Permutation] = []
    for vertex_permutation in permutations(range(4)):
        edge = tuple(
            PACKETS.index(tuple(sorted((vertex_permutation[i], vertex_permutation[j]))))
            for i, j in PACKETS
        )
        moves.append(edge)
        kind = cycles(vertex_permutation)
        sizes[kind] += 1
        need(
            signed_permutation(63, edge) == (63, 1),
            "S4 edge action reversed orientation",
        )
        unsigned = sum(
            canonical(signed_permutation(mask, edge)[0]) == mask for mask in LOW
        )
        exterior = exterior_w_character(edge)
        low_trace = sum(
            sign
            for mask in LOW
            for target, sign in (signed_permutation(mask, edge),)
            if target == mask
        )
        projected_trace = ZERO
        for mask in EVEN:
            v = basis(mask)
            projected_trace += uniform_vacuum(permute(v, edge)).get(mask, ZERO)
            need(
                uniform_vacuum(permute(v, edge)) == permute(uniform_vacuum(v), edge),
                "uniform projector S4 invariance",
            )
            need(
                hodge(permute(v, edge)) == permute(hodge(v), edge),
                "oriented Hodge equivariance",
            )
        need(
            projected_trace == g(exterior) and low_trace == exterior,
            "independent exterior characters",
        )
        for eigenvalue in (-1, 1):
            hodge_trace = 0
            for mask in LOW:
                v = plus(basis(mask), scaled(g(eigenvalue), hodge(basis(mask))))
                target, sign = signed_permutation(mask, edge)
                image_basis = plus(
                    basis(target), scaled(g(eigenvalue), hodge(basis(target)))
                )
                need(
                    permute(v, edge) == scaled(g(sign), image_basis),
                    "Hodge half representation",
                )
                if target == mask:
                    hodge_trace += sign
            need(hodge_trace == exterior, "Hodge character")
        rows.setdefault(kind, set()).add((unsigned, exterior, low_trace))
    need(tuple(sizes[kind] for kind in CLASSES) == SIZES, "S4 class sizes")
    unsigned_character = (16, 4, 4, 1, 2)
    exterior_character = (16, 0, 0, 1, 0)
    for kind, u, e in zip(CLASSES, unsigned_character, exterior_character, strict=True):
        need(rows[kind] == {(u, e, e)}, "character mismatch")
    unassigned = set(LOW)
    orbit_sizes: list[int] = []
    while unassigned:
        mask = min(unassigned)
        orbit = {canonical(signed_permutation(mask, edge)[0]) for edge in moves}
        unassigned -= orbit
        orbit_sizes.append(len(orbit))
    need(sorted(orbit_sizes) == [1, 3, 12], "unsigned orbits")
    irreducibles = (
        (1, 1, 1, 1, 1),
        (1, -1, 1, 1, -1),
        (3, 1, -1, 0, -1),
        (3, -1, -1, 0, 1),
        (2, 0, 2, -1, 0),
    )
    for character, expected in (
        (unsigned_character, (3, 0, 2, 1, 2)),
        (exterior_character, (1, 1, 2, 2, 1)),
    ):
        multiplicities = tuple(
            F(
                sum(
                    size * x * y
                    for size, x, y in zip(SIZES, character, irrep, strict=True)
                ),
                24,
            )
            for irrep in irreducibles
        )
        need(
            multiplicities == tuple(F(x) for x in expected), "irreducible decomposition"
        )
    return tuple(moves)


def projector_and_gate_controls() -> None:
    ranks: dict[int, F] = {k: F(0) for k in (0, 2, 4, 6)}
    projection = {mask: uniform_vacuum(basis(mask)) for mask in EVEN}
    non_dyadic = False
    for mask in EVEN:
        v = basis(mask)
        p = projection[mask]
        need(uniform_vacuum(p) == p, "uniform-vacuum idempotence")
        need(hodge(hodge(v)) == v, "even-grade Hodge square")
        need(
            hodge(uniform_vacuum(hodge(v))) == plus(v, scaled(g(-1), p)),
            "Hodge swaps uniform occupancy",
        )
        diagonal = p.get(mask, ZERO)
        need(diagonal.im == 0, "real projector diagonal")
        ranks[mask.bit_count()] += diagonal.re
        non_dyadic |= any(not coefficient.dyadic() for coefficient in p.values())
    need(
        ranks == {0: 1, 2: 10, 4: 5, 6: 0} and sum(ranks.values()) == 16,
        "uniform-vacuum grade ranks",
    )
    need(non_dyadic, "uniform projection was silently made dyadic")
    for left, right in product(EVEN, repeat=2):
        need(
            projection[right].get(left, ZERO)
            == projection[left].get(right, ZERO).star(),
            "uniform-vacuum Hermiticity",
        )
    u = apply(eye(6), ("T", 0, 1))
    for _ in range(3):
        u = apply(u, ("T", 2, 3))
    need(
        unitary(u) and all(sum(row, ZERO) == ONE for row in u),
        "native fixed-uniform gate",
    )
    eigenphases = (I, g(0, -1), ONE, ONE, ONE, ONE)
    frame = tuple(
        tuple(g(int(j == 2 * pair) + sign * int(j == 2 * pair + 1)) for j in range(6))
        for sign in (-1, 1)
        for pair in range(3)
    )
    for i, j in product(range(6), repeat=2):
        need(
            sum((x.star() * y for x, y in zip(frame[i], frame[j], strict=True)), ZERO)
            == g(2 if i == j else 0),
            "complete real pair eigenframe",
        )
    for vector, phase in zip(frame, eigenphases, strict=True):
        image = tuple(
            sum((z * x for z, x in zip(row, vector, strict=True)), ZERO) for row in u
        )
        need(image == tuple(phase * x for x in vector), "native eigenphase control")
    determinant = ONE
    for phase in eigenphases:
        determinant = determinant * phase
    need(determinant == ONE, "native determinant-one countercontrol")
    columns = {mask: exterior_column(u, mask) for mask in EVEN}
    for mask in EVEN:
        need(
            all(target.bit_count() == mask.bit_count() for target in columns[mask]),
            "exterior number conservation",
        )
        need(
            uniform_vacuum(columns[mask]) == act(columns, uniform_vacuum(basis(mask))),
            "native uniform-vacuum invariance",
        )
        need(
            hodge(columns[mask], anti=True)
            == act(columns, hodge(basis(mask), anti=True)),
            "Hermitian anti-star covariance",
        )
        if mask in LOW:
            need(set(columns[mask]) <= set(LOW), "lower-grade alternative invariance")
    for left, right in product(EVEN, repeat=2):
        need(
            inner(columns[left], columns[right]) == (ONE if left == right else ZERO),
            "exterior lift unitarity",
        )
    alpha = {
        (1 << 0) | (1 << 4): g(F(1, 2)),
        (1 << 0) | (1 << 5): g(F(-1, 2)),
        (1 << 1) | (1 << 4): g(F(-1, 2)),
        (1 << 1) | (1 << 5): g(F(1, 2)),
    }
    dual = hodge(alpha)
    need(inner(alpha, alpha) == inner(dual, dual) == ONE, "unit two/four-form")
    need(
        act(columns, alpha) == scaled(I, alpha)
        and act(columns, dual) == scaled(g(0, -1), dual),
        "unequal complementary phases",
    )
    positive = plus(alpha, dual)
    negative = plus(alpha, scaled(g(-1), dual))
    need(
        hodge(positive) == positive and hodge(negative) == scaled(g(-1), negative),
        "Hodge eigenspaces",
    )
    exterior_image = act(columns, positive)
    need(exterior_image == scaled(I, negative), "complete Hodge-half leakage")
    need(
        scaled(g(F(1, 2)), plus(exterior_image, scaled(g(-1), hodge(exterior_image))))
        == exterior_image,
        "minus-half leakage projection",
    )
    need(hodge(positive, anti=True) == positive, "Hermitian-star real form")
    need(
        hodge(scaled(I, positive), anti=True) == scaled(g(0, -1), positive),
        "anti-linearity boundary",
    )
    # A genuine native determinant-i word, not only an abstract slot spectrum.
    single = apply(eye(6), ("T", 0, 1))
    native_traces: list[Gaussian] = []
    for parity in (0, 1):
        masks = tuple(mask for mask in range(64) if mask.bit_count() % 2 == parity)
        projected_trace = sum(
            (
                uniform_vacuum(exterior_column(single, mask)).get(mask, ZERO)
                for mask in masks
            ),
            ZERO,
        )
        rank = sum(
            (uniform_vacuum(basis(mask)).get(mask, ZERO) for mask in masks), ZERO
        )
        need(rank == g(16), "even/odd uniform-vacuum dimensions")
        native_traces.append(projected_trace)
    need(native_traces == [g(8, 8), g(8, 8)], "native determinant twist")


def two_steps(
    mask: int, inner_slot: int, inner_create: bool, outer_slot: int, outer_create: bool
) -> dict[int, int]:
    first = mode_step(mask, inner_slot, inner_create)
    if first is None:
        return {}
    second = mode_step(first[0], outer_slot, outer_create)
    return {} if second is None else {second[0]: first[1] * second[1]}


def add_integer_terms(a: dict[int, int], b: dict[int, int]) -> dict[int, int]:
    out = dict(a)
    for mask, coefficient in b.items():
        out[mask] = out.get(mask, 0) + coefficient
    return {mask: x for mask, x in out.items() if x}


def bit_encoding_controls(moves: tuple[Permutation, ...]) -> None:
    for left, right in product(moves, repeat=2):
        combined = tuple(left[right[j]] for j in range(6))
        for mask in EVEN:
            middle, right_sign = signed_permutation(mask, right)
            final, left_sign = signed_permutation(middle, left)
            need(
                signed_permutation(mask, combined) == (final, left_sign * right_sign),
                "signed exchange cocycle",
            )
    for mask, i, j in product(range(64), range(6), range(6)):
        mixed = add_integer_terms(
            two_steps(mask, j, True, i, False), two_steps(mask, i, False, j, True)
        )
        need(mixed == ({mask: 1} if i == j else {}), "CAR mixed anticommutator")
        annihilators = add_integer_terms(
            two_steps(mask, j, False, i, False), two_steps(mask, i, False, j, False)
        )
        need(annihilators == {}, "CAR annihilator anticommutator")
    # Unsigned hard-core bit lowering commutes on different occupied slots:
    # both paths from mask 0b11 lead to the vacuum with +1, not cancellation.
    unsigned_paths: Counter[int] = Counter()
    for first, second in ((0, 1), (1, 0)):
        state = 3
        for slot in (first, second):
            need(bool(state >> slot & 1), "hard-core lowering on empty bit")
            state ^= 1 << slot
        unsigned_paths[state] += 1
    need(unsigned_paths == {0: 2}, "unsigned hard-core CAR countercontrol")


def phase_character(
    eigenvalues: tuple[Gaussian, ...], parity: Literal[0, 1]
) -> Gaussian:
    value = ZERO
    for mask in range(1 << len(eigenvalues)):
        if mask.bit_count() % 2 != parity:
            continue
        coefficient = ONE
        for j, eigenvalue in enumerate(eigenvalues):
            if mask >> j & 1:
                coefficient = coefficient * eigenvalue
        value = value + coefficient
    return value


def charge_controls() -> tuple[Counter[int], Counter[int]]:
    weights = (-2, -2, -2, 3, 3)
    even = Counter(
        sum(weights[j] for j in occupied)
        for k in (0, 2, 4)
        for occupied in combinations(range(5), k)
    )
    odd = Counter(
        sum(weights[j] for j in occupied)
        for k in (1, 3, 5)
        for occupied in combinations(range(5), k)
    )
    need(even == {0: 1, -4: 3, 1: 6, 6: 1, 2: 3, -3: 2}, "conditional even charges")
    need(
        odd
        == Counter({-charge: multiplicity for charge, multiplicity in even.items()}),
        "odd conjugate charges",
    )
    raw_weights = (0, *weights)
    lower = Counter(
        sum(raw_weights[j] for j in occupied)
        for k in (0, 2)
        for occupied in combinations(range(6), k)
    )
    need(lower == {0: 1, -4: 3, 1: 6, 6: 1, -2: 3, 3: 2}, "alternative sixteen charges")
    need(sum(even.values()) == sum(lower.values()) == 16, "carrier dimensions")
    need(
        sum(charge * multiplicity for charge, multiplicity in even.items())
        == sum(charge * multiplicity for charge, multiplicity in lower.items())
        == 0,
        "linear traces",
    )
    need(
        sum(charge**3 * multiplicity for charge, multiplicity in even.items()) == 0,
        "even cubic trace",
    )
    need(
        sum(charge**3 * multiplicity for charge, multiplicity in lower.items()) == 60,
        "alternative cubic trace",
    )
    one_phase = (I, ONE, ONE, ONE, ONE)
    even_trace, odd_trace = phase_character(one_phase, 0), phase_character(one_phase, 1)
    need(even_trace == odd_trace == g(8, 8), "native determinant-coset trace")
    need(
        odd_trace != even_trace.star() and odd_trace == I * even_trace.star(),
        "required determinant twist",
    )
    # Abstract determinant-one eigenvalue controls; these 256 spectra are
    # not a claim that all five centered modes are natively addressable.
    for phases in product((ONE, I, g(-1), g(0, -1)), repeat=4):
        determinant = ONE
        for phase in phases:
            determinant = determinant * phase
        eigenvalues = (*phases, determinant.star())
        need(
            phase_character(eigenvalues, 1) == phase_character(eigenvalues, 0).star(),
            "determinant-one complement pairing",
        )
    return even, lower


def main() -> None:
    moves = representation_controls()
    projector_and_gate_controls()
    bit_encoding_controls(moves)
    even, lower = charge_controls()
    print(
        "S4 classes: identity, transposition, double transposition, 3-cycle, 4-cycle."
    )
    print(
        "Unsigned complement quotient: character (16,4,4,1,2), orbits (1,3,12). Exterior W5: (16,0,0,1,0)."
    )
    print(
        "Signed Hodge halves match S4, but the exact native determinant-one gate sends one whole plus vector to minus."
    )
    print(
        "Uniform-vacuum even projector: rank 16, grades (1,10,5,0), invariant under the fixed-uniform exterior lift."
    )
    print(f"Conditional desired charges: {dict(sorted(even.items()))}.")
    print(
        f"Stable raw grades 0+2 alternative: {dict(sorted(lower.items()))}; cubic charge trace 60, not 0."
    )
    print(
        "Odd conjugacy requires determinant one; coherent bit encodings require supplied exchange phases."
    )
    print(
        "No fermion statistics, carrier selection, preparation primitive, spacetime chirality or particle family was derived."
    )


if __name__ == "__main__":
    main()
