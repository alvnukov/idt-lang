"""Exact contextuality-algebra controls for two binary lifts of folded five.

Base: the five toggles are g1,...,g4 the coordinate basis of F2^4 and
g5=g1+...+g4. Binary lift: every pair anticommutes up to central z, with
z^2=1. The invariant quadratic refinement squares every g_i to +1.
Its only five nonzero +1-square directions are those toggles, so there
is no compatible pair of such distinct directions, let alone a square.

For the supplied nonneighbour mark t=g1+g2, Q'=Q+B(t,.) is a different
microscopic lift. Sign rephasing within the binary lift cannot change
any square. Allowing scalar i instead enlarges the center and is a
separate resource. The plus refinement admits a real Mermin square;
this fact does not supply physical outcome instruments or compatibility.

Paper comparators, not carrier observations: Kirchmair et al.,
doi:10.1038/nature08172 (ions); Amselem et al.,
doi:10.1103/PhysRevLett.103.160405 (single photons). Neither paper
implements the finite carrier or selects its lift.
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from functools import reduce
from itertools import combinations, permutations, product
from operator import xor

V = tuple(range(16))
BASIS = (1, 2, 4, 8)
PORTS = (*BASIS, 15)
MARK = BASIS[0] ^ BASIS[1]
Elt = tuple[int, int]  # direction x, central sign exponent a
Perm = tuple[int, ...]  # i-th column is signed row position, one-based
Dense = tuple[tuple[int, ...], ...]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


@dataclass(frozen=True)
class Lift:
    diagonal: int

    def cocycle(self, x: int, y: int) -> int:
        lower = sum((y & (i-1)).bit_count() for i in BASIS if x & i)
        return (lower + (x & y & self.diagonal).bit_count()) % 2

    def square(self, x: int) -> int:
        return self.cocycle(x, x)

    def mul(self, left: Elt, right: Elt) -> Elt:
        x, a = left
        y, b = right
        return x ^ y, a ^ b ^ self.cocycle(x, y)

    def fold(self, seq) -> Elt:
        return reduce(self.mul, seq, (0, 0))


ORIGINAL = Lift(0)


def polar(x: int, y: int) -> int:
    return ORIGINAL.cocycle(x, y) ^ ORIGINAL.cocycle(y, x)


REFINED = Lift(sum(i for i in BASIS if polar(MARK, i)))


def element_set(lift: Lift) -> dict[str, object]:
    need(all(lift.cocycle(x, y) ^ lift.cocycle(x ^ y, w)
             == lift.cocycle(y, w) ^ lift.cocycle(x, y ^ w)
             for x, y, w in product(V, repeat=3)), "not an associative lift")
    need(all(lift.mul((x, s), (x, s ^ lift.square(x))) == (0, 0)
             for x, s in product(V, (0, 1))), "missing inverse")
    involutions = tuple(v for v in V if v and not lift.square(v))
    commuting_pairs = [pair for pair in combinations(involutions, 2) if not polar(*pair)]
    triples = []
    for trial in combinations(involutions, 3):
        if all(not polar(*pair) for pair in combinations(trial, 2)):
            x, sign = lift.fold((v, 0) for v in trial)
            need(x == 0, "commuting triple failed central product test")
            triples.append((trial, sign))
    return {"involutions": involutions, "commuting_pairs": commuting_pairs, "triples": triples,
            "port_square_bits": [lift.square(x) for x in PORTS], "group_order": 32}


def check_refinement() -> dict[str, object]:
    need(all(polar(x, y) == 1 for x, y in combinations(PORTS, 2)), "port commutator changed")
    need([x for x in V if not any(polar(x, y) for y in V)] == [0], "polar rank changed")
    need(reduce(xor, PORTS) == 0, "base toggles do not close")
    need([k for k in V if len({Lift(k).square(v) for v in PORTS}) == 1] == [0],
         "more than one constant-port-square refinement")
    refinements: Counter = Counter()
    for t in V:
        diag = sum(i for i in BASIS if polar(t, i))
        lift = Lift(diag)
        need(all(lift.square(x) == ORIGINAL.square(x) ^ polar(t, x) for x in V), "incorrect refinement")
        refinements[sum(not lift.square(x) for x in V if x)] += 1
    need(refinements == {5: 6, 9: 10}, "shift family departure")
    # Within Z2 central extensions, a normalized section rephasing
    # contributes f(x)+f(y)+f(x+y), which is zero for y=x. In Z4 this
    # phase map works, but uses actual i phases for the marked ports.
    def phase4(element: Elt):
        x, s = element
        return x, (2*s + (x & REFINED.diagonal).bit_count()) % 4

    for a, b in product(product(V, (0, 1)), repeat=2):
        x, s = phase4(a)
        y, t = phase4(b)
        need(phase4(REFINED.mul(a, b)) == (x ^ y, (s+t+2*ORIGINAL.cocycle(x, y)) % 4),
             "enlarged four-phase embedding")
    return {"refinement_counts_by_nontrivial_involution_count": dict(refinements),
            "binary_section_rephasing_changes_squares": False,
            "enlarged_center_z4_embeds_refined_lift": True,
            "new_phase_needed_on_port_masks": [v for v in PORTS if polar(MARK, v)]}


def check_original_s5() -> dict[str, object]:
    elements = tuple(product(V, (0, 1)))
    literal_port_symmetries = 0
    root_order = {v: i for i, v in enumerate(PORTS)}
    for p in permutations(PORTS):
        inversions = sum(root_order[a] > root_order[b] for a, b in combinations(p, 2))
        odd = inversions % 2

        def transfer(e: Elt, phase: int = odd, images: tuple[int, ...] = p[:4]) -> Elt:
            x, s = e
            return ORIGINAL.fold([(0, s), *((y, phase) for i, y in zip(BASIS, images, strict=True) if i & x)])

        # Odd permutations need central signs on lifts. Giving all
        # five generator lifts that same parity is enough, preserving
        # the chosen closing product of all five words.
        mapping = {e: transfer(e) for e in elements}
        need(len(set(mapping.values())) == 32 and all(mapping[v, 0] == (w, odd)
             for v, w in zip(PORTS, p, strict=True)), "S5 lift action on ports")
        need(all(mapping[ORIGINAL.mul(a, b)] == ORIGINAL.mul(mapping[a], mapping[b])
                 for a, b in product(elements, repeat=2)), "S5 lift action not multiplicative")
        pure_product = ORIGINAL.fold((g, 0) for g in p)
        need(pure_product == (0, odd), "literal reordering failed closing-word control")
        literal_port_symmetries += int(not pure_product[1])
    need(literal_port_symmetries == 60, "wrong literal lift symmetry count")
    return {"lift_class_port_symmetries": 120, "literal_sign_free_port_symmetries": literal_port_symmetries,
            "odd_port_permutation_needs_central_phase": True}


def sign_of_product(lift: Lift, triple: tuple[int, ...]) -> int:
    direction, sign = lift.fold((x, 0) for x in triple)
    need(not direction, "not a central triple")
    return sign


def grid_contexts(grid: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    return grid + tuple(zip(*grid, strict=True))


def grid_census(refined: dict[str, object]) -> dict[str, object]:
    triples = tuple(t for t, _ in refined["triples"])
    lines = tuple(map(frozenset, triples))
    directions = refined["involutions"]
    grids = set()
    for rowids in combinations(range(len(lines)), 3):
        colids = tuple(i for i in range(len(lines)) if i not in rowids)
        if len(frozenset().union(*(lines[i] for i in rowids))) != 9:
            continue
        if len(colids) != 3 or len(frozenset().union(*(lines[i] for i in colids))) != 9:
            continue
        if not all(len(lines[i] & lines[j]) == 1 for i, j in product(rowids, colids)):
            continue
        for rows, cols in product(permutations(rowids), permutations(colids)):
            grids.add(tuple(tuple(next(iter(lines[i] & lines[j])) for j in cols) for i in rows))
    need(len(grids) == 72, "labelled grid count")
    patterns_by_grid = []
    for grid in sorted(grids):
        contexts = grid_contexts(grid)
        products = tuple(sign_of_product(REFINED, line) for line in contexts)
        masks = tuple(sum(1 << directions.index(v) for v in line) for line in contexts)
        counts: Counter = Counter()
        failures: Counter = Counter()
        for chosen_signs in range(1 << len(directions)):
            alternative = tuple(s ^ ((mask & chosen_signs).bit_count() % 2)
                                for s, mask in zip(products, masks, strict=True))
            counts[alternative] += 1
            failures[sum(alternative)] += 1
        # The same exhaustive signs are also all possible global
        # hidden-value assignments against the measured products.
        need(len(counts) == 32 and set(counts.values()) == {16}
             and failures == {1: 96, 3: 320, 5: 96}, "grid gauge signs or contrast counts")
        patterns_by_grid.append(len(counts))
    return {"labelled_grids": len(grids), "signings_per_grid": 512, "sign_patterns_per_grid": min(patterns_by_grid),
            "every_pattern_has_odd_negative_parity": True,
            "global_assignments_by_number_failed_contexts": {1: 96, 3: 320, 5: 96},
            "noncontextual_contrast_max": 4, "ideal_context_contrast": 6}


def p_mul(a: Perm, b: Perm) -> Perm:
    return tuple((1 if j > 0 else -1)*a[abs(j)-1] for j in b)


def p_sign(a: Perm, s: int) -> Perm:
    return tuple(-j if s else j for j in a)


def regular_signed(lift: Lift, element: Elt) -> Perm:
    x, s = element
    return tuple((-1)**(s ^ lift.cocycle(x, y))*((x ^ y)+1) for y in V)


def check_maps(lift: Lift, mapping: dict[Elt, Perm]) -> None:
    need(len(mapping) == len(set(mapping.values())) == 32, "representation not faithful")
    need(all(p_mul(a, b) == mapping[lift.mul(x, y)] for (x, a), (y, b) in product(mapping.items(), repeat=2)),
         "representation not multiplicative")


PAULIS = (
    (2, 1, 4, 3),  # X on bit 0
    (1, -2, 3, -4),  # Z on bit 0
    (3, 4, 1, 2),  # X on bit 1
    (1, 2, -3, -4),  # Z on bit 1
)
I4 = (1, 2, 3, 4)


def word(x: int, generators: tuple[Perm, ...]) -> Perm:
    return reduce(p_mul, (a for i, a in zip(BASIS, generators, strict=True) if x & i), I4)


def real_mapping() -> tuple[dict[Elt, Perm], tuple[int, ...]]:
    target = {x: word(x, PAULIS) for x in V}
    sources = []
    for i in BASIS:
        sources.append(tuple(x for x in V if x and p_mul(target[x], target[x]) == p_sign(I4, REFINED.square(i))))
    pattern = None
    for cand in product(*sources):
        matrices = tuple(target[x] for x in cand)
        if all(p_mul(a, b) == p_sign(p_mul(b, a), 1) for a, b in combinations(matrices, 2)):
            pattern = cand
            break
    need(pattern is not None, "no real two-bit representation")
    generators = tuple(target[x] for x in pattern)
    mapping = {(x, sign): p_sign(word(x, generators), sign) for x, sign in product(V, (0, 1))}
    check_maps(REFINED, mapping)
    return mapping, pattern


def dense(p: Perm) -> Dense:
    return tuple(tuple((1 if j > 0 else -1) if abs(j) == i+1 else 0 for j in p) for i in range(len(p)))


def combine(*terms) -> Dense:
    return tuple(tuple(sum(s*a[i][j] for s, a in terms) for j in range(4)) for i in range(4))


def dense_mul(a: Dense, b: Dense) -> Dense:
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)) for i in range(4))


def canonical_contexts(mapping: dict[Elt, Perm]) -> dict[str, object]:
    inverse = {v: x for x, v in mapping.items()}
    x1, z1, x2, z2 = PAULIS
    xa, xb = p_mul(x1, z2), p_mul(z1, x2)
    grid = ((x1, x2, p_mul(x1, x2)), (z2, z1, p_mul(z1, z2)), (xa, xb, p_mul(xa, xb)))
    contexts = grid_contexts(grid)
    identity = dense(I4)
    expected = [1, 1, 1, 1, 1, -1]
    for (a, b, c), target in zip(contexts, expected, strict=True):
        need(all(p_mul(x, y) == p_mul(y, x) for x, y in combinations((a, b, c), 2)), "real context not commuting")
        need(REFINED.fold(inverse[p] for p in (a, b, c)) == (0, int(target == -1)), "canonical sign")
        # Numerators of rank-one joint projectors; actual projectors
        # are these matrices divided by 4.
        projectors = []
        for s, t in product((-1, 1), repeat=2):
            p = combine((1, identity), (s, dense(a)), (t, dense(b)), (s*t, dense(p_mul(a, b))))
            need(p == tuple(zip(*p, strict=True)) and dense_mul(p, p) == combine((4, p))
                 and sum(p[i][i] for i in range(4)) == 4, "not a real rank-one orthogonal projector")
            need(dense_mul(dense(c), p) == combine((target*s*t, p)), "context outcome product relation")
            projectors.append(p)
        need(combine(*((1, p) for p in projectors)) == combine((4, identity))
             and all(dense_mul(p, q) == combine((0, identity)) for p, q in combinations(projectors, 2)),
             "joint projectors not an orthogonal complete readout")
    # Context-indexed random assignments can reach the algebraic value
    # without a single assignment. Their overlaps even have fair marginals.
    local = []
    for sign in expected:
        draws = [(a, b, sign*a*b) for a, b in product((-1, 1), repeat=2)]
        need(all(sum(row[j] for row in draws) == 0 for j in range(3))
             and all(row[0]*row[1]*row[2] == sign for row in draws), "context-dependent escape")
        local.append(draws)
    need(len(local) == 6, "not six local context laws")
    return {"grid_of_direction_and_sign_bit": tuple(tuple(inverse[v] for v in row) for row in grid),
            "context_products": expected, "joint_projectors_per_context": 4,
            "joint_projectors_all_rank_one": True,
            "context_dependent_escape": "four equally likely product-satisfying outcomes per context; fair overlaps",
            "compatible_repeatable_instrument": "ideal projective model requires supplied outcome/update rules"}


def two_copy_control() -> dict[str, object]:
    identity = (0, 0)
    one, two = (1, 0), (2, 0)
    z = (0, 1)

    def mul(a, b):
        return ORIGINAL.mul(a[0], b[0]), ORIGINAL.mul(a[1], b[1])

    def compose_center(a):
        return a[0][0], a[1][0], a[0][1] ^ a[1][1]

    def value(a):
        return (-1)**compose_center(a)[2]

    original_involutions = tuple((x, s) for x, s in product(V, (0, 1)) if not ORIGINAL.square(x))
    raw_involutions = tuple(product(original_involutions, repeat=2))
    need(len(raw_involutions) == 144, "new raw direct-product involution")
    # Globally assign the product of the two displayed sign bits. In
    # each factor a compatible pair of involution directions repeats
    # its direction or uses zero, so the section cocycle vanishes.
    # The assignment therefore extends multiplicatively to all literal
    # commuting involution contexts; not just the displayed grid fails.
    for a, b in product(raw_involutions, repeat=2):
        ab = mul(a, b)
        if ab == mul(b, a):
            need(value(ab) == value(a)*value(b), "raw product should admit global context values")
    x1, z1, x2, z2 = (one, identity), (two, identity), (identity, one), (identity, two)
    xa, xb = mul(x1, z2), mul(z1, x2)
    delta = (z, z)
    bottom = mul(xa, xb)
    need(mul(bottom, bottom) == delta and mul(xa, xb) == mul(delta, mul(xb, xa))
         and compose_center(delta) == (0, 0, 0), "independent central signs did not block square")
    grid = ((x1, x2, mul(x1, x2)), (z2, z1, mul(z1, z2)), (xa, xb, bottom))
    products = []
    for line in grid_contexts(grid):
        need(all(compose_center(mul(a, b)) == compose_center(mul(b, a)) for a, b in combinations(line, 2))
             and all(compose_center(mul(a, a)) == (0, 0, 0) for a in line),
             "composed square not commuting/involutive")
        outcome = compose_center(reduce(mul, line, (identity, identity)))
        need(outcome[:2] == (0, 0), "cross-copy noncentral context product")
        products.append((-1)**outcome[2])
    need(products == [1, 1, 1, 1, 1, -1], "composed center product signs")
    full = {(x, y, a ^ b) for x, y, a, b in product(V, V, (0, 1), (0, 1))}
    sub = {(x, y, a ^ b) for x, y, a, b in product(range(4), range(4), (0, 1), (0, 1))}
    need(len(full) == 512 and len(sub) == 32, "composed group orders")
    return {"raw_direct_product_completes_square": False,
            "raw_blocker": "bottom-right square and row-3 commutator are z1*z2",
            "raw_involutions_including_centers": len(raw_involutions),
            "raw_global_assignment": "product of the two central sign bits on all compatible involutions",
            "compose_central_parity": "identify z1*z2=1; tensor realizations with scalar minus implement this",
            "full_composed_order": len(full), "two_toggles_per_copy_composed_order": len(sub),
            "composed_context_products": products}


def probe() -> dict[str, object]:
    original, refined = element_set(ORIGINAL), element_set(REFINED)
    need(original["involutions"] == PORTS and not original["commuting_pairs"]
         and not original["triples"], "original lift did not exclude the square")
    need(len(refined["involutions"]) == 9 and len(refined["commuting_pairs"]) == 18
         and len(refined["triples"]) == 6, "refined context incidence")
    original_reps = {e: regular_signed(ORIGINAL, e) for e in product(V, (0, 1))}
    check_maps(ORIGINAL, original_reps)
    refined_reps, images = real_mapping()
    return {"scope": "finite algebra and specified ideal measurement model; no experimental carrier claim",
            "original": original, "marked_refined": refined, "refinement_checks": check_refinement(),
            "original_port_symmetries": check_original_s5(),
            "grid_census": grid_census(refined), "explicit_real_square": canonical_contexts(refined_reps),
            "real_signed_permutation_dimensions": {"original_regular": 16, "marked_refined": 4},
            "marked_real_generator_image_masks_x1_z1_x2_z2": images,
            "two_copy_control": two_copy_control(),
            "experimental_comparators_not_carrier_evidence": {
                "ions": {
                    "doi": "10.1038/nature08172",
                    "ten_state_square_scores": "5.23(5) to 5.46(4); Fig. 3 error bars 1 sigma",
                    "trials_per_square_score": 6600,
                    "limit": "imperfect compatibility; separate disturbance inequality not the full square",
                },
                "photons": {
                    "doi": "10.1103/PhysRevLett.103.160405",
                    "source_table_i_average": "5.4550 +/- 0.0006",
                    "distinct_source_main_text_value": "5.4521",
                    "limit": "single photon path/polarization; mixed-state data combined from pure data",
                },
            }}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
