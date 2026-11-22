"""Exact two-particle audit of the ORIGINAL four-port junction, not a six-port lift.

SUPPLIED CONTRACTS. Four coherent one-particle modes, linear same-event action
G=J/2-I, rewiring R, the usual symmetric/antisymmetric two-particle functor,
and squared-norm projective readout are inputs here. This does not derive
bosonic/fermionic statistics, a coincidence detector, a bound moving pair, or
physical particles from unsigned stocks. Sources are the exact G/R convention
in probe_routed_diamond_cones.py and the edge/complement convention in
probe_six_packet_sectors.py. No fit, floating point, or external package.

RESULT. Write a bosonic state as a symmetric matrix A, with norm squared
Tr(A* A), transported by U A U^T. Off-diagonal matrices describe distinct
ports; diagonal matrices describe doubled occupations. Opposite-even edge
amplitudes (dimension three) are fixed by G. Opposite-odd amplitudes m_i are
swapped with centered diagonal b_i=G m_i G. Thus distinct-port postselection
has effect P_even, NOT a scalar success probability: weights 1 and 0 for
opposite-even/odd superpositions, although both have the same one-body state.
A single edge has weight 1/2, concealing this distinction. An unread coherent
second junction returns the state; an intervening which-sector record does
not. A hard-core restriction is consequently different dynamics, not this
bosonic linear gate. Calling doubled occupations background is not a detector
that makes them absent without changing the supplied measurement model.

The six four-cycles generate exactly phi(S4), order 24, where
phi(p)=G^(parity(p)) P_p. All fix the raw uniform vector u and have determinant
one. Independently adjoining G gives order 48; even-length words give A4.
The two-boson representation is 2*1 + 2 + 3 + 3', whereas the two-fermion
representation is 2*3'. Euclidean Hodge +/- give its two canonical triplets.
There is no projective invariant fermion line or 1+3+2 reslicing. Global phase
changes do not change invariant subspaces. Trivial external tensor labels
only multiply the triplets; nontrivial labels or direct-sum spectators are
additional resources. The two equivalent triplets admit noncanonical mixing;
the Hodge split is canonical, not the only invariant three-dimensional split.

A REAL RESCUE, WITH A SELECTION COST. Sym^2(u^perp) is an actual raw two-boson
sector of dimension six and S4 type 1+2+3. It uses coherent doubled-port
amplitudes: it is not the six distinct-pair basis. Its canonical basis consists
of P=I-J/4, the centered opposite-even plane, and m_i+b_i. Filtering A to PAP
has weights 1/4, 1, 1/2 on the edge singlet, plane, and triplet respectively.
The restriction is invertible but nonisometric. An abstract isometry can
rescale these three blocks, but no raw one-particle U(4) maps the entire
distinct-pair space to a common-mode-vacuum sector: the sum of squared
annihilation norms on all six pairs is 3*||v||^2 for every candidate mode v.
Preparing the invariant sector, postselection, or interactions is new input.

Under the full finite group the graph m_i+c*b_i is invariant iff c=+/-1.
The two signs give inequivalent BOSONIC triplets; the minus graph is not an
antisymmetric two-particle state. Together with the unique doublet
and any line in the two-dimensional trivial multiplicity space they give
the 1+2+3 or 1+2+3' carriers. These exhaust invariant six-dimensional carriers
containing a singlet and doublet, over C as well as R. The other possible
six-dimensional isotypic choice is 3+3'. The smaller even-word A4 subgroup
has additional mixing freedom; the full-S4 statement must not be applied to it.

NON-GAUGE RIVAL. In the orthonormal Walsh three-frame the rescue is ordinary
symmetric rank-two tensors: trace + traceless diagonal (2) + off-diagonal (3),
the cubic quadrupole split. Native routings are signed permutations and
preserve it. A continuous SO(3) rotation with cos=3/5, sin=4/5 mixes the two
blocks exactly. The traceless block label (-2 on 3, +3 on 2) commutes with
the finite point group, not arbitrary rotations. The finite 3+2 pattern and
its labels are therefore not a derivation of dynamical gauge charge. More
general fixed-u complex gates preserve Sym^2(u^perp), not its finite split.
A port-dependent real propagation phase already leaks out of the rescue;
one-vertex invariance is not a global lattice transport or binding result.

These are exact finite executable controls plus the stated elementary
representation arguments, not Lean proofs or a physical identification.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_balanced_phase_composition import (
    Matrix,
    add,
    determinant,
    identity,
    matrix,
    multiply,
    scale,
    trace,
    transpose,
)
from scripts.probe_routed_diamond_cones import I4, WALSH, G, rotations
from scripts.probe_six_packet_sectors import PACKETS

Basis = tuple[Matrix, ...]
CLASS_ORDER = ((1, 1, 1, 1), (1, 1, 2), (2, 2), (1, 3), (4,))
CLASS_SIZES = (1, 6, 3, 8, 6)
IRREPS = {
    "1": (1, 1, 1, 1, 1),
    "sign": (1, -1, 1, 1, -1),
    "2": (2, 0, 2, -1, 0),
    "3": (3, 1, -1, 0, -1),
    "3_prime": (3, -1, -1, 0, 1),
}


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def sub(a: Matrix, b: Matrix) -> Matrix:
    return add(a, scale(-1, b))


def inner(a: Matrix, b: Matrix) -> F:
    return sum(
        (
            x * y
            for ar, br in zip(a, b, strict=True)
            for x, y in zip(ar, br, strict=True)
        ),
        F(0),
    )


def norm2(a: Matrix) -> F:
    return inner(a, a)


def action(u: Matrix, a: Matrix) -> Matrix:
    return multiply(multiply(u, a), transpose(u))


def sum_matrices(items: Basis) -> Matrix:
    need(bool(items), "nonempty matrix sum")
    result = scale(0, items[0])
    for item in items:
        result = add(result, item)
    return result


def orthogonal(basis: Basis) -> None:
    need(all(norm2(b) > 0 for b in basis), "zero basis vector")
    need(
        all(inner(a, b) == 0 for a, b in combinations(basis, 2)), "nonorthogonal basis"
    )


def project(basis: Basis, a: Matrix) -> Matrix:
    return sum_matrices(tuple(scale(inner(b, a) / norm2(b), b) for b in basis))


def restricted_trace(u: Matrix, basis: Basis) -> F:
    images = tuple(action(u, a) for a in basis)
    need(all(project(basis, a) == a for a in images), "not an invariant subspace")
    return sum(
        (inner(a, b) / norm2(a) for a, b in zip(basis, images, strict=True)), F(0)
    )


def pair(i: int, j: int, sign: int = 1) -> Matrix:
    need(0 <= i < j < 4 and sign in (-1, 1), "pair convention")
    return matrix(
        tuple(
            tuple(
                int((r, c) == (i, j)) + sign * int((r, c) == (j, i)) for c in range(4)
            )
            for r in range(4)
        )
    )


DISTINCT = tuple(pair(i, j) for i, j in PACKETS)
EVEN = tuple(add(DISTINCT[i], DISTINCT[i + 1]) for i in (0, 2, 4))
ODD = tuple(sub(DISTINCT[i], DISTINCT[i + 1]) for i in (0, 2, 4))
BUNCHED = tuple(action(G, a) for a in ODD)
PLANE = (sub(EVEN[0], EVEN[1]), sub(add(EVEN[0], EVEN[1]), scale(2, EVEN[2])))
PLUS = tuple(add(a, b) for a, b in zip(ODD, BUNCHED, strict=True))
MINUS = tuple(sub(a, b) for a, b in zip(ODD, BUNCHED, strict=True))
EDGE_SINGLET = sum_matrices(EVEN)
P = sub(I4, scale(F(1, 4), add(EDGE_SINGLET, I4)))
RESCUE = (P, *PLANE, *PLUS)
FULL_BOSON = (I4, EDGE_SINGLET, *PLANE, *PLUS, *MINUS)
FERMION = tuple(pair(i, j, -1) for i, j in combinations(range(4), 2))


def star(a: Matrix) -> Matrix:
    """Euclidean orientation 0123, on antisymmetric two-forms only."""
    need(transpose(a) == scale(-1, a), "two-form required")
    terms = []
    for i, j in combinations(range(4), 2):
        k, l = (v for v in range(4) if v not in (i, j))
        order = (i, j, k, l)
        sign = (-1) ** sum(order[r] > order[s] for r, s in combinations(range(4), 2))
        terms.append(scale(sign * a[i][j], pair(k, l, -1)))
    return sum_matrices(tuple(terms))


HODGE_PLUS = tuple(add(a, star(a)) for a in FERMION[:3])
HODGE_MINUS = tuple(sub(a, star(a)) for a in FERMION[:3])


def closure(generators: Basis, cap: int) -> set[Matrix]:
    found, pending = {I4}, [I4]
    while pending:
        x = pending.pop()
        for generator in generators:
            y = multiply(generator, x)
            if y not in found:
                found.add(y)
                pending.append(y)
                need(len(found) <= cap, "group exceeded declared finite cap")
    return found


def cycle_type(p: tuple[int, ...]) -> tuple[int, ...]:
    remaining = set(range(4))
    lengths = []
    while remaining:
        v, length = min(remaining), 0
        while v in remaining:
            remaining.remove(v)
            length += 1
            v = p[v]
        lengths.append(length)
    return tuple(sorted(lengths))


def native_group() -> tuple[tuple[tuple[int, ...], Matrix], ...]:
    rows = []
    for p in permutations(range(4)):
        raw = tuple(I4[i] for i in p)
        u = raw if determinant(raw) == 1 else multiply(G, raw)
        need(multiply(u, transpose(u)) == I4 and determinant(u) == 1, "SO(4) gate")
        need(all(sum(row, F(0)) == 1 for row in u), "uniform mode changed")
        rows.append((p, u))
    generators = tuple(multiply(G, r) for r in rotations())
    need(len(generators) == 6, "six four-cycles")
    expected = {u for _, u in rows}
    need(
        len(expected) == 24 and closure(generators, 24) == expected, "twisted S4 group"
    )
    need(
        len(closure((*generators, G), 48)) == 48, "independent G changes control group"
    )
    even_words = tuple(multiply(a, b) for a in generators for b in generators)
    need(len(closure(even_words, 12)) == 12, "even words give A4")
    need(
        Counter(cycle_type(p) for p, _ in rows)
        == dict(zip(CLASS_ORDER, CLASS_SIZES, strict=True)),
        "conjugacy classes",
    )
    return tuple(rows)


def decomposition(chars: tuple[F, ...]) -> dict[str, int]:
    result = {}
    for name, irreducible in IRREPS.items():
        multiplicity = (
            sum(
                (
                    n * x * y
                    for n, x, y in zip(CLASS_SIZES, chars, irreducible, strict=True)
                ),
                F(0),
            )
            / 24
        )
        need(
            multiplicity.denominator == 1 and multiplicity >= 0, "character integrality"
        )
        result[name] = int(multiplicity)
    return result


def representation_controls(
    group: tuple[tuple[tuple[int, ...], Matrix], ...],
) -> dict[str, object]:
    bases = {
        "boson": FULL_BOSON,
        "rescue": RESCUE,
        "opposite_rescue": (P, *PLANE, *MINUS),
        "fermion": FERMION,
        "hodge_plus": HODGE_PLUS,
        "hodge_minus": HODGE_MINUS,
        "plane": PLANE,
        "plus_graph": PLUS,
        "minus_graph": MINUS,
    }
    expected = {
        "boson": (10, 2, 2, 1, 2),
        "rescue": (6, 2, 2, 0, 0),
        "opposite_rescue": (6, 0, 2, 0, 2),
        "fermion": (6, -2, -2, 0, 2),
        "hodge_plus": (3, -1, -1, 0, 1),
        "hodge_minus": (3, -1, -1, 0, 1),
        "plane": (2, 0, 2, -1, 0),
        "plus_graph": (3, 1, -1, 0, -1),
        "minus_graph": (3, -1, -1, 0, 1),
    }
    # Orthogonality and squared dimensions certify the complete S4 table;
    # the nontrivial entries are also realized by the explicit sectors below.
    for name, row in IRREPS.items():
        for other, column in IRREPS.items():
            need(
                sum(n * x * y for n, x, y in zip(CLASS_SIZES, row, column, strict=True))
                == 24 * int(name == other),
                "irreducible character table",
            )
    need(
        sum(row[0] ** 2 for row in IRREPS.values()) == 24,
        "complete finite character table",
    )
    for basis in bases.values():
        orthogonal(basis)
    seen: dict[str, dict[tuple[int, ...], F]] = {name: {} for name in bases}
    raw_fermion: dict[tuple[int, ...], F] = {}
    for p, u in group:
        kind = cycle_type(p)
        raw = tuple(I4[i] for i in p)
        raw_value = restricted_trace(raw, FERMION)
        need(
            raw_value == raw_fermion.setdefault(kind, raw_value),
            "raw permutation class",
        )
        for name, basis in bases.items():
            value = restricted_trace(u, basis)
            need(value == seen[name].setdefault(kind, value), "class character")
        tr_square = trace(multiply(u, u))
        need(
            seen["boson"][kind] == (trace(u) ** 2 + tr_square) / 2,
            "symmetric trace formula",
        )
        need(
            seen["fermion"][kind] == (trace(u) ** 2 - tr_square) / 2,
            "exterior trace formula",
        )
        for a in FERMION:
            need(star(action(u, a)) == action(u, star(a)), "native Hodge covariance")
    result: dict[str, object] = {}
    for name, values in seen.items():
        chars = tuple(values[kind] for kind in CLASS_ORDER)
        need(
            chars == tuple(F(x) for x in expected[name]), "wrong finite-group character"
        )
        result[name] = {
            "characters": [int(x) for x in chars],
            "multiplicities": decomposition(chars),
        }
    raw_chars = tuple(raw_fermion[kind] for kind in CLASS_ORDER)
    need(
        raw_chars == tuple(map(F, (6, 0, -2, 0, 0))),
        "raw permutation exterior character",
    )
    result["raw_permutation_fermion"] = {
        "characters": [int(x) for x in raw_chars],
        "multiplicities": decomposition(raw_chars),
    }
    need(
        decomposition(tuple(F(x) for x in expected["fermion"]))
        == {"1": 0, "sign": 0, "2": 0, "3": 0, "3_prime": 2},
        "no projective line or doublet",
    )
    # A raw orientation reversal swaps Hodge halves; G and a four-cycle
    # each do so, although their native product does not.
    for u in (G, rotations()[0]):
        for a in HODGE_PLUS:
            need(
                star(action(u, a)) == scale(-1, action(u, a)),
                "orientation reversal control",
            )
    return result


def boson_controls(
    group: tuple[tuple[tuple[int, ...], Matrix], ...],
) -> dict[str, object]:
    need(multiply(G, G) == I4 and multiply(P, P) == P, "raw involution/projector")
    expected_diagonals = ((-1, -1, 1, 1), (-1, 1, -1, 1), (-1, 1, 1, -1))
    for b, values in zip(BUNCHED, expected_diagonals, strict=True):
        need(
            b
            == matrix(
                tuple(
                    tuple(values[i] if i == j else 0 for j in range(4))
                    for i in range(4)
                )
            ),
            "bunched signs",
        )
    for w, m, b in zip(EVEN, ODD, BUNCHED, strict=True):
        need(action(G, w) == w and action(G, b) == m, "swap and fixed sectors")
        need(project(DISTINCT, action(G, m)) == scale(0, m), "complete bunching")
        need(
            scale(1 / norm2(w), multiply(w, transpose(w))) == scale(F(1, 4), I4),
            "even one-body density",
        )
        need(
            scale(1 / norm2(m), multiply(m, transpose(m))) == scale(F(1, 4), I4),
            "odd same one-body density",
        )
    for _, u in group:
        for a in FULL_BOSON:
            need(norm2(action(u, a)) == norm2(a), "two-particle norm")
    for r in rotations():
        u = multiply(G, r)
        for a in DISTINCT:
            need(
                project(DISTINCT, action(u, a)) == action(r, project(EVEN, a)),
                "compression equals routing times even projector",
            )
            need(
                norm2(project(DISTINCT, action(u, a))) / norm2(a) == F(1, 2),
                "single edge half survival",
            )
    # All 36 two-junction words return the distinct-port space coherently.
    for r in rotations():
        for s in rotations():
            two = multiply(multiply(G, s), multiply(G, r))
            need(two == multiply(s, r), "coherent two-tick cancellation")
            for a in DISTINCT:
                need(project(DISTINCT, action(two, a)) == action(two, a), "pair return")
    a = DISTINCT[0]
    first = action(G, a)
    distinct_record = project(DISTINCT, first)
    records = (distinct_record, sub(first, distinct_record))
    returned = tuple(action(G, x) for x in records)
    need(sum_matrices(returned) == a, "coherent amplitude return")
    measured_return = sum((inner(a, x) ** 2 / norm2(a) ** 2 for x in returned), F(0))
    need(measured_return == F(1, 2), "which-sector measurement dephases return")
    need(
        project(DISTINCT, action(G, ODD[0])) == scale(0, ODD[0]),
        "hard-core compression has kernel",
    )
    return {
        "distinct_survival_even_odd_single_edge": ["1", "0", "1/2"],
        "one_body_density_both": "I4/4",
        "coherent_return": "1",
        "recorded_sector_return": str(measured_return),
    }


def rescue_controls(
    group: tuple[tuple[tuple[int, ...], Matrix], ...],
) -> dict[str, object]:
    weights = []
    for a, expected in ((EDGE_SINGLET, F(1, 4)), (PLANE[0], F(1)), (ODD[0], F(1, 2))):
        image = action(P, a)
        weight = norm2(image) / norm2(a)
        need(
            weight == expected and project(RESCUE, image) == image,
            "nonneutral common-mode filter",
        )
        weights.append(str(weight))
    need(action(P, EDGE_SINGLET) == scale(-1, P), "singlet image")
    for m, b in zip(ODD, BUNCHED, strict=True):
        need(action(P, m) == scale(F(1, 2), add(m, b)), "triplet filter")
    for a in RESCUE:
        need(
            action(P, a) == a and all(sum(row, F(0)) == 0 for row in a),
            "common-mode vacuum",
        )
    # Graph stability: G(m+c*b)=b+c*m; the residual after subtracting
    # c*(m+c*b) is (1-c^2)*b. Thus +/-1 are the only complex roots too.
    for c in (F(-2), F(-1), F(0), F(1, 2), F(1), F(2)):
        for m, b in zip(ODD, BUNCHED, strict=True):
            graph = add(m, scale(c, b))
            need(
                sub(action(G, graph), scale(c, graph)) == scale(1 - c * c, b),
                "graph residual polynomial",
            )
    for _, u in group:
        need(
            action(u, I4) == I4 and action(u, EDGE_SINGLET) == EDGE_SINGLET,
            "two trivial multiplicities",
        )
    # Coefficientwise certificate of sum_{i<j} ||a(v)|ij>||^2 = 3||v||^2.
    annihilator_gram = matrix(
        tuple(
            tuple(
                sum(int(r in edge) for edge in PACKETS) if r == c else 0
                for c in range(4)
            )
            for r in range(4)
        )
    )
    need(annihilator_gram == scale(3, I4), "no common empty mode on all distinct pairs")
    phase = matrix(((-1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)))
    moved = action(phase, P)
    survival = norm2(action(P, moved)) / norm2(P)
    need(survival == F(11, 16), "real port phase leaks from rescue")
    return {
        "filter_singlet_plane_triplet": weights,
        "graph_roots": [-1, 1],
        "raw_unitary_encoding_obstruction": "annihilator Gram = 3 I4",
        "port_phase_rescue_survival": str(survival),
    }


def cubic_controls(
    group: tuple[tuple[tuple[int, ...], Matrix], ...],
) -> dict[str, object]:
    need(multiply(transpose(WALSH), WALSH) == I4, "orthonormal raw-to-cubic frame")
    v = tuple(tuple(row[j] for j in range(1, 4)) for row in WALSH)
    need(multiply(v, transpose(v)) == P, "three-frame complement")
    d = matrix(((1, 0, 0), (0, -1, 0), (0, 0, 0)))
    xy = matrix(((0, 1, 0), (1, 0, 0), (0, 0, 0)))
    rotation = matrix(((F(3, 5), F(-4, 5), 0), (F(4, 5), F(3, 5), 0), (0, 0, 1)))
    need(
        determinant(rotation) == 1
        and multiply(rotation, transpose(rotation)) == identity(3),
        "rational SO3 rotation",
    )
    image = action(rotation, d)
    need(
        image == add(scale(F(-7, 25), d), scale(F(24, 25), xy)),
        "continuous diagonal/offdiagonal mixing",
    )
    for _, u in group:
        small = multiply(multiply(transpose(v), u), v)
        need(determinant(small) == 1, "oriented cubic frame")
        need(
            all(
                sum(x != 0 for x in row) == 1 and all(x in (-1, 0, 1) for x in row)
                for row in small
            ),
            "native signed permutation",
        )
        need(
            all(
                action(small, d)[i][j] == 0
                for i in range(3)
                for j in range(3)
                if i != j
            ),
            "cubic diagonal invariance",
        )
    for a in PLANE:
        small = multiply(multiply(transpose(v), a), v)
        need(
            trace(small) == 0
            and all(small[i][j] == 0 for i in range(3) for j in range(3) if i != j),
            "packet plane is cubic diagonal plane",
        )
    for a in PLUS:
        small = multiply(multiply(transpose(v), a), v)
        need(
            all(small[i][i] == 0 for i in range(3)),
            "packet rescue triplet is cubic offdiagonal",
        )
    # Q has weights +3 on the diagonal plane, -2 on off-diagonal tensors.
    q_image = add(scale(F(-21, 25), d), scale(F(-48, 25), xy))
    commutator = sub(q_image, scale(3, image))
    need(commutator == scale(F(-24, 5), xy), "finite block label is not an SO3 charge")
    raw_rotation = add(sub(I4, P), multiply(multiply(v, rotation), transpose(v)))
    need(
        multiply(raw_rotation, transpose(raw_rotation)) == I4,
        "raw fixed-uniform rotation",
    )
    for a in RESCUE:
        need(
            project(RESCUE, action(raw_rotation, a)) == action(raw_rotation, a),
            "whole rescue survives continuous rotation",
        )
    return {
        "rotation_cos_sin": ["3/5", "4/5"],
        "diagonal_to_diagonal_xy": ["-7/25", "24/25"],
        "block_label_commutator_xy": "-24/5",
        "interpretation": "finite cubic quadrupoles, not a gauge-charge derivation",
    }


def main() -> None:
    group = native_group()
    result = {
        "status": "exact finite controls; supplied two-particle/readout contracts",
        "native_group_order": len(group),
        "independent_G_group_order": 48,
        "even_word_group_order": 12,
        "classes": [list(kind) for kind in CLASS_ORDER],
        "representations": representation_controls(group),
        "distinct_pair_transport": boson_controls(group),
        "coherent_bunched_rescue": rescue_controls(group),
        "cubic_countercontrol": cubic_controls(group),
        "boundary": "no statistics origin, physical particles, binding, gauge dynamics, masses, or SM identification",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
