"""Exact D5 lattice obstruction and explicit even unimodular completions.

The five-coordinate even demihypercube supplies one set of sixteen
half-integer spinor weights. Its shortest differences generate D5 in
the supplied Euclidean form. In that form there is no proper even
overlattice of D5 in the same rank: each added class would lie in
D5*/D5 and must have zero norm modulo 2. Only the origin does.

The small-rank bound here need not invoke the general multiple-of-eight
theorem. An even Gram matrix with odd determinant is alternating and
nondegenerate modulo 2, so its rank is even. Over Z/4, choose an odd
off-diagonal entry as a pivot, making an invertible 2x2 block with even
diagonal and determinant -1. Congruence clears its couplings, preserves
evenness and changes determinant by a unit square. Iteration gives
det(G)=(-1)^(rank/2) mod 4. Positive unimodularity therefore also
excludes rank six, and the explicit rank-eight completion is minimal
among positive-definite even unimodular ambient ranks containing D5.

The E8 construction is the one written by Viazovska in arXiv:1603.04246
§1. Rank-16 lattice controls are mathematical comparison with the
Gross--Harvey--Martinec--Rohm heterotic construction (1985,
doi:10.1103/PhysRevLett.54.502 and doi:10.1016/0550-3213(85)90394-3),
not physical predictions. No worldsheet, compactification, gauge-boson
observations, fermion generations, or choice of a D5 embedding is inferred.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product

Vector = tuple[int, ...]  # coordinates are doubled to retain exact halves
Basis = tuple[Vector, ...]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def dot4(u: Vector, v: Vector) -> int:
    return sum(a*b for a, b in zip(u, v, strict=True))


def dot(u: Vector, v: Vector) -> Fraction:
    return Fraction(dot4(u, v), 4)


def det(rows) -> Fraction:
    work = [list(map(Fraction, row)) for row in rows]
    value = Fraction(1)
    for i in range(len(work)):
        pivot = next((j for j in range(i, len(work)) if work[j][i]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != i:
            work[i], work[pivot] = work[pivot], work[i]
            value = -value
        a = work[i][i]
        value *= a
        for j in range(i+1, len(work)):
            factor = work[j][i]/a
            for k in range(i+1, len(work)):
                work[j][k] -= factor * work[i][k]
            work[j][i] = Fraction(0)
    return value


def vector_norm2_roots(n: int) -> set[Vector]:
    return {tuple(a if k == i else b if k == j else 0 for k in range(n))
            for i, j in combinations(range(n), 2) for a, b in product((-2, 2), repeat=2)}


def dn_basis(n: int) -> Basis:
    differences = tuple(tuple(2 if i == j else -2 if i == j+1 else 0 for i in range(n))
                        for j in range(n-1))
    return (*differences, (0,)*(n-2) + (2, 2))


def half_weights(n: int, parity: int) -> set[Vector]:
    return {v for v in product((-1, 1), repeat=n) if v.count(-1) % 2 == parity}


def in_dn(v: Vector) -> bool:
    return all(x % 2 == 0 for x in v) and sum(v) % 4 == 0


def in_plus(v: Vector) -> bool:
    return in_dn(v) or (all(x % 2 == 1 for x in v) and sum(x-1 for x in v) % 4 == 0)


def in_dual_dn(v: Vector) -> bool:
    # This input encodes half-integral candidates. Integral evaluation
    # on e_i-e_j forces common fractional part and on e_i+e_j
    # forces that common part to be 0 or 1/2, so there are no others.
    return all(x % 2 == v[0] % 2 for x in v)


def odd_dn_coset(v: Vector) -> int:
    need(len(v) % 2 == 1 and in_dual_dn(v), "coset labels need odd D_n dual")
    if v[0] % 2 == 0:
        return 0 if in_dn(v) else 2
    return 1 if in_plus(v) else 3


def determinant_and_form(basis: Basis) -> tuple[Fraction, Fraction]:
    covol = abs(det(tuple(tuple(Fraction(v, 2) for v in u) for u in basis)))
    gram = tuple(tuple(dot(u, v) for v in basis) for u in basis)
    discriminant = det(gram)
    need(discriminant == covol*covol > 0, "wrong Gram/covolume normalization")
    need(all(v.denominator == 1 for row in gram for v in row)
         and all(gram[i][i] % 2 == 0 for i in range(len(basis))), "basis form not even and integral")
    return covol, discriminant


def audit_demihypercube() -> dict[str, object]:
    spinor = half_weights(5, 0)
    other = half_weights(5, 1)
    differences = {tuple(a-b for a, b in zip(x, y, strict=True))
                   for x, y in product(spinor, repeat=2) if x != y}
    shortest = {v for v in differences if dot4(v, v) == 8}
    basis = dn_basis(5)
    need(len(spinor) == len(other) == 16 and all(odd_dn_coset(v) == 1 for v in spinor)
         and all(odd_dn_coset(v) == 3 for v in other), "wrong D5 half-weight cosets")
    need(len(shortest) == 40 and shortest == vector_norm2_roots(5) and set(basis) <= shortest
         and all(in_dn(v) for v in differences), "shortest differences do not generate D5")
    covol, disc = determinant_and_form(basis)
    need(covol == 2 and disc == 4, "D5 determinant")
    reps = tuple((k,)*5 for k in range(4))
    norms = tuple(dot(v, v) % 2 for v in reps)
    need(tuple(odd_dn_coset(v) for v in reps) == (0, 1, 2, 3)
         and norms == (0, Fraction(5, 4), 1, Fraction(5, 4)), "D5 discriminant quadratic form")
    for i, x in enumerate(reps):
        need(all(dot(x, b).denominator == 1 for b in basis), "representative not in dual")
        for j, y in enumerate(reps):
            need(odd_dn_coset(tuple(a+b for a, b in zip(x, y, strict=True))) == (i+j) % 4,
                 "coset addition is not Z4")
    unit = (2, 0, 0, 0, 0)
    need(odd_dn_coset(unit) == 2 and dot(unit, unit) == 1, "integral but odd extension control")
    return {"coordinate_rank": 5, "spinor_weights_in_one_chirality": len(spinor),
            "shortest_differences": len(shortest), "covolume": int(covol), "gram_determinant": int(disc),
            "discriminant_group": "Z/4 generated by h=(1/2)^5", "norm_mod2_by_coset": list(map(str, norms)),
            "nonzero_isotropic_cosets": 0, "same_rank_proper_even_overlattice_possible": False,
            "odd_same_rank_control": "D5 plus the class of e1 gives the odd unimodular Z^5"}


def plus_basis(n: int) -> Basis:
    need(n in (8, 16), "this probe only constructs rank-eight and rank-sixteen plus lattices")
    basis = dn_basis(n)
    h = (1,)*n
    lifted = (h, *basis[1:])
    # Twice the coefficients of h in the D_n simple-root basis.
    twice = (*range(1, n-1), (n-2)//2, n//2)
    need(twice[0] == 1 and tuple(sum(k*v[i] for k, v in zip(twice, basis, strict=True)) for i in range(n))
         == (2,)*n, "h cannot replace the first basis vector")
    need(determinant_and_form(lifted) == (1, 1), "plus overlattice not unimodular")
    return lifted


def roots_plus(n: int) -> set[Vector]:
    # For integer coordinates, norm two requires exactly two ±1.
    # All-half-integer coordinates have norm >= n/4, with equality
    # exactly at minimal absolute values on every coordinate.
    integral = vector_norm2_roots(n)
    half = half_weights(n, 0) if n == 8 else set()
    roots = integral | half
    need(all(in_plus(v) and dot4(v, v) == 8 for v in roots), "incorrect norm-two root")
    if n == 8:
        brute_integer = {v for v in product((-2, 0, 2), repeat=8) if dot4(v, v) == 8 and in_plus(v)}
        brute_half = {v for v in product((-1, 1), repeat=8) if dot4(v, v) == 8 and in_plus(v)}
        need(roots == brute_integer | brute_half, "independent rank-eight enumeration mismatch")
    return roots


def projection(roots: set[Vector], n: int) -> dict[str, object]:
    left_zero, right_zero = (0,)*5, (0,)*(n-5)
    bins: dict[str, Counter] = {key: Counter() for key in
                              ("D5_roots", "zero_on_D5", "vector_weights", "spinor_even", "spinor_odd")}
    for v in roots:
        left, right = v[:5], v[5:]
        if left == left_zero:
            kind = "zero_on_D5"
        elif right == right_zero:
            kind = "D5_roots"
        elif left[0] % 2:
            kind = "spinor_odd" if left.count(-1) % 2 else "spinor_even"
        else:
            kind = "vector_weights"
        bins[kind][left] += 1
    need(set(bins["D5_roots"]) == vector_norm2_roots(5) and set(bins["zero_on_D5"]) == {left_zero}
         and all(dot4(v, v) == 4 for v in bins["vector_weights"]), "projection class mismatch")
    for parity, kind in ((0, "spinor_even"), (1, "spinor_odd")):
        if bins[kind]:
            need(set(bins[kind]) == half_weights(5, parity), "incorrect projected chirality inventory")
    return {k: {"counted_roots": sum(h.values()), "distinct_projected_weights": len(h),
                "multiplicity_per_projected_weight": sorted(set(h.values()))} for k, h in bins.items()}


def glue_and_conjugate_embedding(roots: set[Vector]) -> dict[str, object]:
    h = (1,)*8
    glue = tuple((odd_dn_coset((k,)*5), odd_dn_coset((k,)*3)) for k in range(4))
    need(glue == ((0, 0), (1, 1), (2, 2), (3, 3)), "diagonal gluing")
    for parity in (0, 1):
        for a, b in product(half_weights(5, parity), half_weights(3, parity)):
            need(a+b in roots and in_plus(a+b), "glued chirality not an E8 root")
    geometric = {(x, y) for x in range(4) for y in range(4)
                 if in_plus((x,)*5 + (y,)*3)}
    need(geometric == set(glue), "coset gluing includes off-diagonal classes")
    coordinate = {r for r in roots if r[5:] == (0,)*3}

    def reflect(v: Vector) -> Vector:
        c = dot(v, h)
        need(c.denominator == 1, "nonintegral root reflection")
        return tuple(x-int(c)*y for x, y in zip(v, h, strict=True))

    reflected = {reflect(v) for v in coordinate}
    need({reflect(v) for v in roots} == roots and {reflect(v) for v in reflected} == coordinate
         and len(reflected) == len(coordinate) == 40 and reflected != coordinate
         and any(v[0] % 2 for v in reflected), "non-coordinate conjugate embedding")
    return {"D5_and_D3_both_saturated_coordinate_sublattices": True,
            "glue_in_Z4_cross_Z4": glue, "glue_index_over_D5_plus_D3": len(glue),
            "half_spinor_gluing": "same parity on the 5 and 3 sides; four right weights per left weight",
            "reflected_noncoordinate_D5_roots": len(reflected),
            "embedding_scope": "one coordinate embedding and an isometric conjugate, not a classification"}


def root_components(roots: set[Vector]) -> list[int]:
    unseen = set(roots)
    sizes = []
    while unseen:
        root = unseen.pop()
        count, pending = 1, deque([root])
        while pending:
            v = pending.popleft()
            linked = {u for u in unseen if dot4(u, v)}
            pending.extend(linked)
            unseen.difference_update(linked)
            count += len(linked)
        sizes.append(count)
    return sorted(sizes)


def probe() -> dict[str, object]:
    d5 = audit_demihypercube()
    basis8, basis16 = plus_basis(8), plus_basis(16)
    roots8, roots16 = roots_plus(8), roots_plus(16)
    p8, p16 = projection(roots8, 8), projection(roots16, 16)
    need([p8[k]["counted_roots"] for k in p8] == [40, 12, 60, 64, 64]
         and p8["spinor_even"]["multiplicity_per_projected_weight"] == [4]
         and p8["spinor_odd"]["multiplicity_per_projected_weight"] == [4]
         and p8["vector_weights"]["multiplicity_per_projected_weight"] == [6], "E8 projection census")
    e8e8 = {v+(0,)*8 for v in roots8} | {(0,)*8+v for v in roots8}
    doubled_e8_basis = tuple(v+(0,)*8 for v in basis8) + tuple((0,)*8+v for v in basis8)
    need(determinant_and_form(doubled_e8_basis) == determinant_and_form(basis16) == (1, 1),
         "rank 16 comparison forms")
    p88 = projection(e8e8, 16)
    c88, c16 = root_components(e8e8), root_components(roots16)
    need(len(e8e8) == len(roots16) == 480 and p16["spinor_even"]["counted_roots"] == 0
         and p16["spinor_odd"]["counted_roots"] == 0 and c88 == [240, 240] and c16 == [480],
         "rank 16 alternatives are not distinguished by root components")
    return {
        "scope": "exact Euclidean lattice counts under stated embeddings; not a physical or generation count",
        "demihypercube_D5": d5,
        "smallest_even_positive_unimodular_ambient_rank_containing_D5": 8,
        "E8": {"rank": 8, "covolume": 1, "gram_determinant": 1, "norm_two_roots": len(roots8),
               "purely_integer_roots": 112, "half_integer_roots": 128, "projection": p8,
               "opposite_root_pairs": len(roots8)//2, "cartan_directions_if_used_as_a_root_system": 8,
               "coordinate_gluing_and_noncoordinate_control": glue_and_conjugate_embedding(roots8)},
        "rank_16_comparators": {
            "E8_plus_E8": {"norm_two_roots": len(e8e8), "root_component_sizes": c88, "projection": p88},
            "D16_plus": {"norm_two_roots": len(roots16), "root_component_sizes": c16, "projection": p16,
                         "minimum_squared_norm_of_half_integer_coset": 4},
        },
        "not_selected_or_identified": [
            "a five-coordinate or rank-sixteen physical lattice law",
            "sixteen spinor weights are not sixteen lattice dimensions",
            "root counts omit Cartan directions and are not observed particle counts",
            "weight multiplicity after projection is not a generation count",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
