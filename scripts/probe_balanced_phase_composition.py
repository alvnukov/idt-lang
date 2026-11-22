"""Exact integer/rational controls for a SUPPLIED phase-composition choice.

Let L=Z^2, J(e)=f, J(f)=-e. J makes L a Z[i]-module without requiring
noninteger coordinates. On L tensor_Z L put A=J tensor I, B=I tensor J,
K=AB. K is a symmetric involution. Ordinary real composition retains both
P+ and P-=(I +/- K)/2. Balanced composition imposes A=B, hence K=-I;
the other sector instead has A=-B, a conjugate-balanced composition.

INTEGER DISTINCTION. In basis a=e.e,b=e.f,c=f.e,d=f.f, the full balanced
quotient has primitive relations c-b and a+d, hence is free Z^2. Its
quotient map is q(a,b,c,d)=(a-d,b+c). The selected minus-sector lattice has
basis u=a-d,v=b+c, but q(u),q(v) are twice the primitive quotient basis.
The index is FOUR overall, not two; there is a factor two per generator.
P-L=(1/2)L-. The plus/minus integral lattices together have index four in
Z^4. No torsion arises in the full balanced quotient. Torsion Z2 x Z2 does
arise when opposite balancing is imposed inside an already selected sector.
An isometric real-space identification additionally rescales by sqrt(2),
or equivalently rescales the restricted squared metric by two. Algebraic
quotient, chosen integral sublattice, and normalized physical tensor differ.

ORIENTATION. Edge signs eps_uv mean J_u=eps_uv J_v. They are compatible
exactly when every cycle has sign product +1. Tree signs can be removed by
local frame choices. A frustrated loop forces J=-J: its real common sector
is zero, while after balancing a spanning tree the integer quotient becomes
Z[i]/(2), namely Z2 x Z2. A bookkeeping frame change is not a physical random
orientation register. Independent random signs do not impose a common sector.

NORMALIZATION/RESOURCE. A normalized real product has P- weight 1/2, since
v^T J v=0. Declaring balanced composition is not performing that filter and
discarding the other outcome. Omega=(I-K)/4 is a rational, normalized positive
shared orientation reference. Every real-separable state, including arbitrary
shared-classical-lambda mixtures of real product states, has K expectation
zero; Omega has expectation -1. Thus the shared reference is NOT supplied by
an iid sign or a shared classical sign. The same argument holds across two
source factors with a skew J on each source's incoming phase register.

Two independent sources distributing Omega_AB1 and Omega_B2C give both middle
P+/- outcomes weight 1/2. Conditional outer references are Omega+ and Omega-;
retaining both gives I/4. The reference aligned across all four phase registers
requires the selected branch or a non-real-separable shared resource relative
to ordinary real tensor composition. A balanced tensor category instead builds
the scalar identification into composition; it is not that real-QM model.

Renou et al., https://arxiv.org/abs/2101.10873, postulate (iv) and Eq. (decomp),
target ordinary Hilbert tensor composition and real source states conditional
on shared classical lambda. Their model already allows that classical lambda.
This probe does not recompute their universal bound or claim an experimental
network violation. Signed lattice, J, state/effect interpretation, normalization
and composition remain distinct supplied contracts; no QM closure follows.
"""

from __future__ import annotations

import argparse
import json
import unittest
from collections.abc import Sequence
from fractions import Fraction as F
from itertools import combinations, permutations, product

Matrix = tuple[tuple[F, ...], ...]
Edge = tuple[int, int, int]


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def matrix(rows: Sequence[Sequence[int | F]]) -> Matrix:
    if not rows or not rows[0] or any(len(row) != len(rows[0]) for row in rows):
        raise ValueError("nonempty rectangular matrix required")
    return tuple(tuple(F(entry) for entry in row) for row in rows)


def identity(n: int) -> Matrix:
    return matrix(tuple(tuple(int(i == j) for j in range(n)) for i in range(n)))


def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a, strict=True))


def scale(value: int | F, a: Matrix) -> Matrix:
    return tuple(tuple(value * entry for entry in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    if len(a) != len(b) or len(a[0]) != len(b[0]):
        raise ValueError("matching matrix shapes required")
    return tuple(
        tuple(x + y for x, y in zip(ar, br, strict=True))
        for ar, br in zip(a, b, strict=True)
    )


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if len(a[0]) != len(b):
        raise ValueError("incompatible matrix product")
    columns = transpose(b)
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True) if x and y), F(0))
            for col in columns
        )
        for row in a
    )


def tensor(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x * y for x in ar for y in br) for ar in a for br in b)


def trace(a: Matrix) -> F:
    if len(a) != len(a[0]):
        raise ValueError("square matrix required")
    return sum((a[i][i] for i in range(len(a))), F(0))


def determinant(a: Matrix) -> F:
    if len(a) != len(a[0]) or len(a) > 4:
        raise ValueError("this independent determinant oracle is bounded to order four")
    result = F(0)
    for order in permutations(range(len(a))):
        term = F(
            (-1) ** sum(order[i] > order[j] for i, j in combinations(range(len(a)), 2))
        )
        for i, j in enumerate(order):
            term *= a[i][j]
        result += term
    return result


I2 = identity(2)
J = matrix(((0, -1), (1, 0)))
A = tensor(J, I2)
B = tensor(I2, J)
K = tensor(J, J)
P_MINUS = scale(F(1, 2), add(identity(4), scale(-1, K)))
P_PLUS = scale(F(1, 2), add(identity(4), K))
OMEGA_MINUS = scale(F(1, 2), P_MINUS)
OMEGA_PLUS = scale(F(1, 2), P_PLUS)


def phase_operator(n: int, positions: tuple[int, ...]) -> Matrix:
    result = matrix(((1,),))
    for i in range(n):
        result = tensor(result, J if i in positions else I2)
    return result


def lattice_controls() -> dict[str, object]:
    minus = matrix(((1, 0), (0, 1), (0, 1), (-1, 0)))
    plus = matrix(((1, 0), (0, -1), (0, 1), (1, 0)))
    section = matrix(((1, 0), (0, 1), (0, 0), (0, 0)))
    quotient = matrix(((1, 0, 0, -1), (0, 1, 1, 0)))
    difference = add(A, scale(-1, B))
    relation_coefficients = matrix(((0, 1, -1, 0), (1, 0, 0, 1)))
    require(multiply(difference, minus) == scale(0, minus), "balanced sector")
    require(
        multiply(difference, identity(4)) == multiply(plus, relation_coefficients),
        "full relation image",
    )
    # The two plus generators are precisely columns b and a of the difference.
    require(
        tuple(row[1] for row in difference) == tuple(row[0] for row in plus),
        "first image generator",
    )
    require(
        tuple(row[0] for row in difference) == tuple(row[1] for row in plus),
        "second image generator",
    )
    split_basis = matrix(tuple(tuple(section[i]) + tuple(plus[i]) for i in range(4)))
    sector_basis = matrix(tuple(tuple(minus[i]) + tuple(plus[i]) for i in range(4)))
    require(abs(determinant(split_basis)) == 1, "saturated relation lattice")
    require(multiply(quotient, plus) == scale(0, identity(2)), "relations killed")
    require(multiply(quotient, section) == identity(2), "integral quotient section")
    require(
        multiply(quotient, minus) == scale(2, identity(2)),
        "index four selected-lattice image",
    )
    require(abs(determinant(sector_basis)) == 4, "sector sum index four")
    require(
        multiply(P_MINUS, section) == scale(F(1, 2), minus),
        "half-integral projector image",
    )
    require(
        multiply(transpose(quotient), quotient) == scale(2, P_MINUS),
        "squared metric rescaling",
    )
    require(
        multiply(difference, plus) == scale(2, multiply(plus, J)),
        "wrong-sector relation is twice J",
    )
    require(
        multiply(add(A, B), minus) == scale(2, multiply(minus, J)),
        "opposite balancing on selected minus",
    )
    require(
        abs(determinant(scale(2, J))) == 4,
        "two independent order-two torsion generators",
    )
    unit_product = matrix(((1,), (0,), (0,), (0,)))
    weight = multiply(transpose(unit_product), multiply(P_MINUS, unit_product))[0][0]
    require(weight == F(1, 2), "real product projection has half weight")
    for entries in product(range(-2, 3), repeat=4):
        v, w = matrix((entries[:2],)), matrix((entries[2:],))
        raw = transpose(tensor(v, w))
        image = multiply(quotient, raw)
        expected = sum(x * x for x in entries[:2]) * sum(x * x for x in entries[2:])
        require(
            multiply(transpose(image), image)[0][0] == expected,
            "complex multiplication norm identity",
        )
    return {
        "full_integer_balanced_quotient": "free Z^2; no torsion",
        "selected_minus_lattice_image_index": 4,
        "sector_sum_index": 4,
        "projector_image": "one half of the primitive minus-sector lattice",
        "wrong_sector_quotient": "Z2 x Z2",
        "normalized_real_product_minus_weight": str(weight),
    }


def frames(n: int, edges: Sequence[Edge]) -> tuple[int, ...] | None:
    if n < 1 or any(
        not (0 <= u < v < n) or sign not in (-1, 1) for u, v, sign in edges
    ):
        raise ValueError("ordered distinct vertices and +/-1 edge signs required")
    signs = [0] * n
    for root in range(n):
        if signs[root]:
            continue
        signs[root] = 1
        pending = [root]
        while pending:
            u = pending.pop()
            for left, right, relation in edges:
                if u not in (left, right):
                    continue
                v = right if u == left else left
                required = relation * signs[u]
                if signs[v] and signs[v] != required:
                    return None
                if not signs[v]:
                    signs[v] = required
                    pending.append(v)
    return tuple(signs)


def gluing_projector(n: int, edges: Sequence[Edge]) -> Matrix:
    result = identity(1 << n)
    for u, v, sign in edges:
        local = scale(
            F(1, 2), add(identity(1 << n), scale(-sign, phase_operator(n, (u, v))))
        )
        result = multiply(result, local)
    return result


def orientation_controls() -> dict[str, object]:
    pairs = tuple(combinations(range(4), 2))
    cases = 0
    for labels in product((-1, 0, 1), repeat=len(pairs)):
        edges = tuple(
            (u, v, sign) for (u, v), sign in zip(pairs, labels, strict=True) if sign
        )
        found = frames(4, edges)
        brute = any(
            all(s[u] == relation * s[v] for u, v, relation in edges)
            for s in product((-1, 1), repeat=4)
        )
        require((found is not None) == brute, "independent frame-assignment oracle")
        cases += 1
    for signs in product((-1, 1), repeat=3):
        edges = tuple(
            (u, v, sign)
            for (u, v), sign in zip(((0, 1), (1, 2), (0, 2)), signs, strict=True)
        )
        projector = gluing_projector(3, edges)
        require(
            multiply(projector, projector) == projector, "commuting gluing projectors"
        )
        require(
            trace(projector) == (2 if signs[0] * signs[1] * signs[2] == 1 else 0),
            "loop holonomy sector",
        )
    require(
        frames(3, ((0, 1, 1), (1, 2, 1), (0, 2, -1))) is None, "frustrated triangle"
    )
    # After the first two balances, the remaining opposite relation is 2J
    # on the primitive Z[i] quotient; reducing its columns modulo two gives zero.
    require(
        scale(2, J) == matrix(((0, -2), (2, 0))), "integer frustrated-loop relation"
    )
    return {
        "signed_graph_cases": cases,
        "triangle_sector_cases": 8,
        "tree_orientation_signs": "removable by a consistent local frame choice",
        "negative_loop_holonomy": "zero real common sector; Z2 x Z2 after integer quotient",
        "frame_choice_is_not": "an iid sign, postselection, or a shared classical source",
    }


def outer_marginal(state: Matrix) -> Matrix:
    if len(state) != 16 or len(state[0]) != 16:
        raise ValueError("four two-dimensional phase registers required")

    def index(a: int, b: int, c: int, d: int) -> int:
        return 8 * a + 4 * b + 2 * c + d

    return tuple(
        tuple(
            sum(
                (
                    state[index(a, b, c, d)][index(aa, b, c, dd)]
                    for b, c in product(range(2), repeat=2)
                ),
                F(0),
            )
            for aa, dd in product(range(2), repeat=2)
        )
        for a, d in product(range(2), repeat=2)
    )


def reference_controls() -> dict[str, object]:
    require(transpose(J) == scale(-1, J), "J skew symmetry")
    require(
        multiply(K, K) == identity(4) and transpose(K) == K, "K symmetric involution"
    )
    for projector in (P_MINUS, P_PLUS):
        require(
            multiply(projector, projector) == projector and trace(projector) == 2,
            "rank-two positive projector",
        )
    require(
        trace(OMEGA_MINUS) == 1 and trace(multiply(OMEGA_MINUS, K)) == -1,
        "shared-reference witness",
    )
    symmetric_basis = (
        matrix(((1, 0), (0, 0))),
        matrix(((0, 0), (0, 1))),
        matrix(((0, 1), (1, 0))),
    )
    require(
        all(trace(multiply(rho, J)) == 0 for rho in symmetric_basis),
        "all real symmetric local matrices",
    )
    for rho, sigma in product(symmetric_basis, repeat=2):
        require(
            trace(multiply(tensor(rho, sigma), K)) == 0, "real product span witness"
        )
    # A genuinely shared classical sign can correlate two real basis states,
    # but still cannot give the reference's nonzero K expectation.
    classical = scale(
        F(1, 2),
        add(
            tensor(symmetric_basis[0], symmetric_basis[0]),
            tensor(symmetric_basis[1], symmetric_basis[1]),
        ),
    )
    require(trace(multiply(classical, K)) == 0, "classical lambda is not the reference")
    independent = tensor(OMEGA_MINUS, OMEGA_MINUS)
    middle_k = phase_operator(4, (1, 2))
    source_basis = tuple(
        matrix(
            tuple(
                tuple(int((r, c) in ((i, j), (j, i))) for c in range(4))
                for r in range(4)
            )
        )
        for i in range(4)
        for j in range(i, 4)
    )
    require(
        middle_k == tensor(tensor(I2, J), tensor(J, I2)),
        "middle witness factors into skew operators on the two sources",
    )
    for left, right in product(source_basis, repeat=2):
        require(
            trace(multiply(tensor(left, right), middle_k)) == 0,
            "all real-symmetric source product span, hence every classical-lambda mixture",
        )
    require(
        trace(independent) == 1 and trace(multiply(independent, middle_k)) == 0,
        "independent sources",
    )
    require(
        outer_marginal(independent) == scale(F(1, 4), identity(4)),
        "unconditional outer product",
    )
    branches: list[dict[str, object]] = []
    retained = scale(0, independent)
    for eigenvalue, target in ((-1, OMEGA_MINUS), (1, OMEGA_PLUS)):
        effect = scale(F(1, 2), add(identity(16), scale(eigenvalue, middle_k)))
        branch = multiply(effect, multiply(independent, effect))
        probability = trace(branch)
        require(probability == F(1, 2), "both middle sectors retained at half weight")
        conditional = scale(1 / probability, branch)
        require(outer_marginal(conditional) == target, "conditional outer reference")
        require(
            trace(multiply(conditional, middle_k)) == eigenvalue,
            "selected global reference",
        )
        retained = add(retained, branch)
        branches.append(
            {
                "middle_K": eigenvalue,
                "probability": str(probability),
                "conditional_outer_K": str(trace(multiply(target, K))),
            }
        )
    require(
        outer_marginal(retained) == scale(F(1, 4), identity(4)),
        "no postselected unconditional upgrade",
    )
    return {
        "shared_reference": "Omega=(I-J tensor J)/4",
        "reference_K_expectation": "-1",
        "every_real_separable_lambda_mixture_K_expectation": "0",
        "every_real_source_product_lambda_mixture_middle_K": "0",
        "two_independent_source_branches": branches,
        "retaining_both_outer_marginal": "I4/4",
        "boundary": "rational state/effect comparator; not Renou bound recomputation or native Born derivation",
    }


def audit() -> dict[str, object]:
    return {
        "ok": True,
        "lattice": lattice_controls(),
        "orientation": orientation_controls(),
        "reference": reference_controls(),
        "boundary": "integer coordinates do not select ordinary real tensor quantum theory; composition and resource assumptions remain explicit",
    }


class CompositionTests(unittest.TestCase):
    def test_integer_quotient_projection_and_metric(self) -> None:
        self.assertEqual(lattice_controls()["selected_minus_lattice_image_index"], 4)

    def test_orientation_graphs_and_loop(self) -> None:
        self.assertEqual(orientation_controls()["signed_graph_cases"], 729)

    def test_shared_reference_and_all_branches(self) -> None:
        self.assertEqual(reference_controls()["reference_K_expectation"], "-1")

    def test_frame_change_preserves_cycle_consistency(self) -> None:
        for edges in (
            ((0, 1, -1), (1, 2, -1), (0, 2, 1)),
            ((0, 1, -1), (1, 2, 1), (0, 2, 1)),
        ):
            for signs in product((-1, 1), repeat=3):
                changed = tuple(
                    (u, v, sign * signs[u] * signs[v]) for u, v, sign in edges
                )
                self.assertEqual(frames(3, edges) is None, frames(3, changed) is None)

    def test_integer_basis_counterexample(self) -> None:
        a, b, c, d = tuple(
            matrix(tuple((int(i == j),) for i in range(4))) for j in range(4)
        )
        quotient = matrix(((1, 0, 0, -1), (0, 1, 1, 0)))
        self.assertEqual(multiply(quotient, b), multiply(quotient, c))
        self.assertEqual(multiply(quotient, d), scale(-1, multiply(quotient, a)))
        self.assertEqual(multiply(transpose(b), c), matrix(((0,),)))

    def test_projector_sign_and_invalid_shapes(self) -> None:
        self.assertEqual(add(P_PLUS, P_MINUS), identity(4))
        self.assertEqual(multiply(P_PLUS, P_MINUS), scale(0, identity(4)))
        with self.assertRaises(ValueError):
            frames(2, ((0, 1, 0),))
        with self.assertRaises(ValueError):
            multiply(identity(2), identity(3))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: saturated integer quotient, index-four sector lattices, and half-weight projector."
        )
        print(
            "PASS: 729 signed graphs, all triangle sectors, and frustrated-loop control."
        )
        print(
            "PASS: shared-reference real-separability witness and both independent-source branches."
        )
        print(
            "A shared classical sign is not the reference; no rejected branch is discarded."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
