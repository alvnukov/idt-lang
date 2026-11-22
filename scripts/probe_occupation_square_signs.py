"""Finite Z2 carried signs on five SUPPLIED hard-core occupation slots.

Each directed letter inserts or removes at one addressed slot, subject to
its occupancy. Reverse directions share an edge sign. A mutable frame for the
carried bit at each configuration changes edge signs, not square parities.
Here "exchange of orders" means exchanging two distinct toggle instructions,
not transporting two already identified particles around one another.

Compute the whole square-curvature space over F2, then classify invariance of
CURVATURE (not literal edge signs) under all slot permutations or a 3+2 split.
Check these dimensions independently from constraints on the actual edges.
Build explicit positive permutation controls on (occupation, carried bit).
An all-odd choice agrees with the Jordan--Wigner signs and makes the signed
formal toggle operators anticommute. This imposes the square signs; the cube
and its symmetries alone do not select them.

For curvature-preserving slot permutations, integrate the edge-sign change
from the vacuum to get a unique normalized vertex correction. For a
transposition, the corrected sign ratio on two individually fixed
configurations with the same particle count is its vacuum-square sign. This
gives a conditional interface to probe_exchange_sign_relator.py, without
identifying the corrected permutation with a physical swap implementation.

Run: python3 -B -O -m scripts.probe_occupation_square_signs
"""

from __future__ import annotations

import json
from collections.abc import Iterable
from itertools import combinations, permutations, product

SLOTS = tuple(range(5))
C_SLOTS = SLOTS[:3]
W_SLOTS = SLOTS[3:]
VERTICES = tuple(range(1 << len(SLOTS)))
PAIRS = tuple((i, j) for i, j in combinations(SLOTS, 2))
TRIPLES = tuple((i, j, k) for i, j, k in combinations(SLOTS, 3))
LABELS = ("C1", "C2", "C3", "W1", "W2")
C_MASK = sum(1 << i for i in C_SLOTS)
W_MASK = sum(1 << i for i in W_SLOTS)

Face = tuple[int, int, int]  # base with both active slots empty, then slot pair
Permutation = tuple[int, ...]  # image of each slot
Profile = tuple[int, int, int]  # active C count, occupied C and W spectators
Basis = dict[int, tuple[int, int]]
SignedState = tuple[int, int]  # configuration and a separate classical bit
Word = tuple[int, ...]  # + or - (zero-based slot + 1), insertion or removal

EDGES = tuple((x, i) for x in VERTICES for i in SLOTS if not (x & (1 << i)))
FACES = tuple(
    (x, i, j) for x in VERTICES for i, j in PAIRS if not (x & ((1 << i) | (1 << j)))
)
EDGE_IDS = {edge: index for index, edge in enumerate(EDGES)}
FACE_IDS = {face: index for index, face in enumerate(FACES)}
ALL_PERMS: tuple[Permutation, ...] = tuple(permutations(SLOTS))
SPLIT_PERMS = tuple(p for p in ALL_PERMS if set(p[: len(C_SLOTS)]) == set(C_SLOTS))


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def parity(mask: int) -> int:
    return mask.bit_count() % 2


def edge_tag(texture: int, x: int, i: int) -> int:
    return (texture >> EDGE_IDS[x & ~(1 << i), i]) & 1


def step(texture: int, state: SignedState, letter: int) -> SignedState:
    x, tag = state
    i = abs(letter) - 1
    need(i in SLOTS, "invalid directed slot letter")
    need(bool(x & (1 << i)) == (letter < 0), "insertion/removal fails occupancy guard")
    return x ^ (1 << i), tag ^ edge_tag(texture, x, i)


def walk(texture: int, state: SignedState, word: Word) -> SignedState:
    for letter in word:
        state = step(texture, state, letter)
    return state


def enabled_letter(x: int, i: int) -> int:
    return -(i + 1) if x & (1 << i) else i + 1


def direct_square(texture: int, face: Face) -> int:
    x, i, j = face
    a, b = i + 1, j + 1
    end, loop = walk(texture, (x, 0), (a, b, -a, -b))
    need(end == x, "square does not close")
    y, ab = walk(texture, (x, 0), (a, b))
    z, ba = walk(texture, (x, 0), (b, a))
    need(z == y and (ab ^ ba) == loop, "two routes disagree")
    return loop


def boundary_mask(face: Face) -> int:
    x, i, j = face
    edges = (x, i), (x | (1 << j), i), (x, j), (x | (1 << i), j)
    return sum(1 << EDGE_IDS[e] for e in edges)


def cube_face_rows() -> tuple[tuple[int, ...], ...]:
    rows = []
    for x in VERTICES:
        for i, j, k in TRIPLES:
            if x & ((1 << i) | (1 << j) | (1 << k)):
                continue
            faces = tuple(
                (base, a, b)
                for a, b, c in ((i, j, k), (i, k, j), (j, k, i))
                for base in (x, x | (1 << c))
            )
            rows.append(tuple(FACE_IDS[f] for f in faces))
    return tuple(rows)


def xor_indices(indices: Iterable[int]) -> int:
    mask = 0
    for index in indices:
        mask ^= 1 << index
    return mask


def eliminate(equations: Iterable[tuple[int, int]]) -> Basis:
    basis: Basis = {}
    for mask, rhs in equations:
        while mask:
            pivot = (mask & -mask).bit_length() - 1
            if pivot not in basis:
                basis[pivot] = mask, rhs
                break
            row, value = basis[pivot]
            mask, rhs = mask ^ row, rhs ^ value
        else:
            need(rhs == 0, "inconsistent GF(2) equations")
    return basis


def rank(rows: Iterable[int]) -> int:
    return len(eliminate((row, 0) for row in rows))


def solve(basis: Basis, seed: int = 0) -> int:
    need(all(not (seed & (1 << pivot)) for pivot in basis), "seed sets a pivot")
    for pivot in sorted(basis, reverse=True):
        row, rhs = basis[pivot]
        if parity(seed & row) != rhs:
            seed ^= 1 << pivot
    return seed


def solutions(basis: Basis, columns: int) -> Iterable[int]:
    free = tuple(i for i in range(columns) if i not in basis)
    for bits in product(range(2), repeat=len(free)):
        yield solve(
            basis, xor_indices(i for i, bit in zip(free, bits, strict=True) if bit)
        )


def permute(x: int, p: Permutation) -> int:
    return sum(1 << target for i, target in enumerate(p) if x & (1 << i))


def transform_face(face: Face, p: Permutation) -> Face:
    x, i, j = face
    a, b = sorted((p[i], p[j]))
    return permute(x, p), a, b


def split_profile(face: Face) -> Profile:
    x, i, j = face
    return (
        int(i in C_SLOTS) + int(j in C_SLOTS),
        (x & C_MASK).bit_count(),
        (x & W_MASK).bit_count(),
    )


def orbit_indices(
    group: tuple[Permutation, ...],
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    minima = tuple(
        min(FACE_IDS[transform_face(face, p)] for p in group) for face in FACES
    )
    reps = tuple(sorted(set(minima)))
    index = {r: i for i, r in enumerate(reps)}
    return reps, tuple(index[r] for r in minima)


def split_texture(cc: int, ww: int, mixed: dict[tuple[int, int], int]) -> int:
    """Explicit edge lift for any 1 CC + 1 WW + 6 mixed square bits.

    Within-block prefix parity gives a constant square bit in that block.
    At W, sum mixed bits across smaller C counts, so a C toggle differentiates
    that sum to the required entry. Both W slots use the same rule; its two
    derivatives on a WW square cancel.
    """
    texture = 0
    for e, (x, i) in enumerate(EDGES):
        if i in C_SLOTS:
            bit = cc * parity(x & ((1 << i) - 1))
        else:
            bit = ww * parity(x & W_MASK & ((1 << i) - 1))
            bit ^= (
                sum(
                    mixed[k, (x & W_MASK).bit_count()]
                    for k in range((x & C_MASK).bit_count())
                )
                % 2
            )
        texture |= bit << e
    return texture


def gauge_texture(frames: int) -> int:
    return sum(
        parity(frames & ((1 << x) | (1 << (x ^ (1 << i))))) << e
        for e, (x, i) in enumerate(EDGES)
    )


def classify() -> tuple[dict[str, dict[str, int]], int, int, int]:
    # Analytically, in S5 a cube relates f_m and f_(m+1) three times, hence
    # they are equal. In a mixed cube under S3xS2 the two mixed-face
    # differences cancel. This forces the same-block CC and WW square bits
    # constant (also use the all-C cube); the six mixed bits are independent.
    identity = (tuple(SLOTS),)
    boundaries = tuple(map(boundary_mask, FACES))
    cubes = cube_face_rows()
    gauge_rows = tuple(gauge_texture(1 << x) for x in VERTICES)
    face_rank = rank(boundaries)
    gauge_rank = rank(gauge_rows)
    cube_rank = rank(xor_indices(row) for row in cubes)
    need(
        (len(VERTICES), len(EDGES), len(FACES), len(cubes)) == (32, 80, 80, 40),
        "cube counts",
    )
    need((gauge_rank, face_rank, cube_rank) == (31, 49, 31), "boundary ranks")
    need(
        all(parity(g & b) == 0 for g in gauge_rows for b in boundaries),
        "gauge changes curvature",
    )
    for row in cubes:
        total = 0
        for f in row:
            total ^= boundaries[f]
        need(total == 0, "cube Bianchi row is not an edge identity")
    need(gauge_rank + face_rank == len(EDGES), "gauge is not the full flat kernel")
    need(
        cube_rank + face_rank == len(FACES),
        "Bianchi is not the full curvature condition",
    )

    vac = tuple(i for i, (x, _, _) in enumerate(FACES) if x == 0)
    report: dict[str, dict[str, int]] = {}
    groups = (("none", identity), ("S5", ALL_PERMS), ("S3xS2", SPLIT_PERMS))
    for name, group in groups:
        reps, orbit = orbit_indices(group)
        orbit_bianchi = tuple(xor_indices(orbit[f] for f in row) for row in cubes)
        orbit_basis = eliminate((row, 0) for row in orbit_bianchi)
        symmetry_edge_rows = tuple(
            b ^ boundaries[reps[orbit[i]]] for i, b in enumerate(boundaries)
        )
        edge_rank = rank(symmetry_edge_rows)
        vac_basis = eliminate(
            [(row, 0) for row in orbit_bianchi] + [(1 << orbit[f], 1) for f in vac]
        )
        vac_edge_rank = rank((*symmetry_edge_rows, *(boundaries[f] for f in vac)))
        freedoms = len(reps) - len(orbit_basis)
        vac_freedoms = len(reps) - len(vac_basis)
        need(
            freedoms == face_rank - edge_rank,
            "independent edge symmetry rank disagrees",
        )
        need(
            vac_freedoms == face_rank - vac_edge_rank,
            "independent vacuum edge rank disagrees",
        )
        report[name] = {
            "slot_permutations": len(group),
            "face_orbits": len(reps),
            "projected_bianchi_rank": len(orbit_basis),
            "edge_symmetry_rank": edge_rank,
            "curvature_bits": freedoms,
            "edge_symmetry_and_vacuum_rank": vac_edge_rank,
            "bits_after_all_vacuum_squares_odd": vac_freedoms,
            "vacuum_odd_completions_modulo_vertex_frames": 1 << vac_freedoms,
        }
        if name == "none":
            continue  # Unrestricted space is certified by rank, not 2^49 enumeration.
        if name == "S5":
            full_profile = tuple(FACES[f][0].bit_count() for f in reps)
            need(
                len(set(full_profile)) == 4
                and all(
                    FACES[f][0].bit_count() == full_profile[orbit[f]]
                    for f in range(len(FACES))
                ),
                "S5 orbit is not exactly total spectator count",
            )
        if name == "S3xS2":
            split = tuple(split_profile(FACES[f]) for f in reps)
            need(
                len(set(split)) == 16
                and all(
                    split_profile(face) == split[orbit[f]]
                    for f, face in enumerate(FACES)
                ),
                "split orbit is not exactly pair type and two spectator counts",
            )

        counted_vac = 0
        for assignment in solutions(orbit_basis, len(reps)):
            values = tuple((assignment >> o) & 1 for o in orbit)
            counted_vac += all(values[f] for f in vac)
            if name == "S3xS2":
                profile = {
                    split_profile(f): value
                    for f, value in zip(FACES, values, strict=True)
                }
                mixed = {(c, w): profile[1, c, w] for c in range(3) for w in range(2)}
                texture = split_texture(profile[2, 0, 0], profile[0, 0, 0], mixed)
            else:
                texture = solve(eliminate(zip(boundaries, values, strict=True)))
            need(
                all(
                    direct_square(texture, face) == bit
                    for face, bit in zip(FACES, values, strict=True)
                ),
                "edge lift mismatch",
            )
        need(counted_vac == 1 << vac_freedoms, "direct vacuum compatibility count")
    need(
        [row["curvature_bits"] for row in report.values()] == [49, 1, 8],
        "curvature dimensions",
    )
    need(
        [row["bits_after_all_vacuum_squares_odd"] for row in report.values()]
        == [39, 0, 5],
        "vacuum-conditioned dimensions",
    )
    return report, face_rank, cube_rank, gauge_rank


def jordan_wigner() -> int:
    return sum(parity(x & ((1 << i) - 1)) << e for e, (x, i) in enumerate(EDGES))


def toggle_checks(texture: int) -> int:
    """Count anticommuting (start, pair) tests, including every orientation.

    On the signed formal states ``(-1)^tag [x]``, a tag flip is multiplication
    by -1. The underlying graph on two classical tag values is positive: its
    relation is a tag flip, not negation of a transition probability.
    """
    signed = 0
    for x in VERTICES:
        for i in SLOTS:
            a = enabled_letter(x, i)
            for tag in (0, 1):
                need(
                    walk(texture, (x, tag), (a, -a)) == (x, tag),
                    "reverse is not inverse",
                )
        for i, j in PAIRS:
            a, b = enabled_letter(x, i), enabled_letter(x, j)
            y, ab = walk(texture, (x, 0), (a, b))
            z, ba = walk(texture, (x, 0), (b, a))
            need(y == z, "orders do not reach the same configuration")
            base = x & ~((1 << i) | (1 << j))
            need(
                (ab ^ ba) == direct_square(texture, (base, i, j)),
                "rooted order relation",
            )
            signed += ab ^ ba
    return signed


def gauge_lift(texture: int, p: Permutation) -> tuple[int, ...] | None:
    """Integrate a(e) xor a(p(e)) from the vacuum. Test every non-tree edge."""
    px = tuple(permute(x, p) for x in VERTICES)
    frame = [0] * len(VERTICES)
    for x in VERTICES[1:]:
        bit = x & -x
        i = bit.bit_length() - 1
        prec = x ^ bit
        frame[x] = (
            frame[prec] ^ edge_tag(texture, prec, i) ^ edge_tag(texture, px[prec], p[i])
        )
    if any(
        frame[x] ^ frame[x ^ (1 << i)]
        != edge_tag(texture, x, i) ^ edge_tag(texture, px[x], p[i])
        for x, i in EDGES
    ):
        return None
    return tuple(frame)


def check_lifts(
    texture: int, group: tuple[Permutation, ...], gauge: int
) -> dict[str, object]:
    bits = tuple(direct_square(texture, f) for f in FACES)
    actual = tuple(
        p
        for p in ALL_PERMS
        if all(
            bits[f] == bits[FACE_IDS[transform_face(face, p)]]
            for f, face in enumerate(FACES)
        )
    )
    need(actual == group, "unexpected curvature stabilizer")
    lifts: dict[Permutation, tuple[int, ...]] = {}
    for p in ALL_PERMS:
        g = gauge_lift(texture, p)
        if g is None:
            need(p not in group, "invariant curvature did not lift")
            continue
        need(p in group and g[0] == 0, "unexpected unnormalized lift")
        lifts[p] = g
        px = tuple(permute(x, p) for x in VERTICES)
        shifted = tuple(
            g[x] ^ (((gauge >> x) ^ (gauge >> px[x])) & 1) for x in VERTICES
        )
        need(
            gauge_lift(texture ^ gauge_texture(gauge), p) == shifted, "gauge covariance"
        )
        for x in VERTICES:
            for i in SLOTS:
                a = enabled_letter(x, i)
                ap = enabled_letter(px[x], p[i])
                need((a > 0) == (ap > 0), "permutation changed insertion/removal")
                y, tag = step(texture, (x, 0), a)
                need(
                    step(texture, (px[x], g[x]), ap) == (px[y], tag ^ g[y]),
                    "lift does not intertwine directed toggles",
                )
    ordered_states = {p: tuple(permute(x, p) for x in VERTICES) for p in lifts}
    for q, gq in lifts.items():
        qx = ordered_states[q]
        for p, gp in lifts.items():
            pq = tuple(p[i] for i in q)
            need(
                lifts[pq] == tuple(gq[x] ^ gp[qx[x]] for x in VERTICES),
                "lifts do not compose",
            )

    ratios: list[int] = []
    for i, j in PAIRS:
        p = tuple(j if k == i else i if k == j else k for k in SLOTS)
        if p not in lifts:
            continue
        g = lifts[p]
        ij = (1 << i) | (1 << j)
        for k, ell in PAIRS:
            kl = (1 << k) | (1 << ell)
            if kl & ij:
                continue
            need(
                permute(ij, p) == ij and permute(kl, p) == kl,
                "not two fixed configurations",
            )
            need(g[kl] == 0, "fixed-slot path from vacuum did not cancel")
            sign_ratio = g[ij] ^ g[kl]
            need(
                sign_ratio == direct_square(texture, (0, i, j)),
                "fixed-number ratio is not vacuum flux",
            )
            ratios.append(-1 if sign_ratio else 1)
    need(
        len(ratios) == (30 if group == ALL_PERMS else 12),
        "transposition ratio test coverage",
    )
    return {
        "normalized_permutation_lifts": len(lifts),
        "same_number_sector_transposition_ratios_checked": len(ratios),
        "distinct_ratios": sorted(set(ratios)),
    }


def report() -> dict[str, object]:
    classification, face_rank, cube_rank, gauge_rank = classify()
    flat, jw = 0, jordan_wigner()
    mixed = {(c, w): 1 ^ (c % 2) for c in range(3) for w in range(2)}
    rival = split_texture(1, 1, mixed)
    need(
        jw == split_texture(1, 1, dict.fromkeys(mixed, 1)),
        "equivalent all-odd edge formulas",
    )
    for e, (x, i) in enumerate(EDGES):
        n = (x & C_MASK).bit_count()
        correction = ((n * (n - 1) // 2) % 2) if i in W_SLOTS else 0
        need(((rival ^ jw) >> e) & 1 == correction, "explicit spectator competitor")

    parity_frame = sum(parity(x) << x for x in VERTICES)
    parity_tag = (1 << len(EDGES)) - 1
    need(
        parity_tag == gauge_texture(parity_frame),
        "constant tag-flip texture is not pure gauge",
    )
    for x in VERTICES:
        for i in SLOTS:
            for tag in (0, 1):
                y, result = step(parity_tag, (x, tag), enabled_letter(x, i))
                need(
                    result == tag ^ parity(x) ^ parity(y), "positive parity-tag control"
                )
    counts = {
        name: toggle_checks(a)
        for name, a in (
            ("flat", flat),
            ("flat_with_parity_tag", parity_tag),
            ("Jordan_Wigner", jw),
            ("split_spectator_rival", rival),
        )
    }
    need(counts["flat"] == counts["flat_with_parity_tag"] == 0, "flat must commute")
    need(
        counts["Jordan_Wigner"] == len(VERTICES) * len(PAIRS), "all-odd toggle algebra"
    )
    need(
        0 < counts["split_spectator_rival"] < counts["Jordan_Wigner"],
        "mixed-curvature toy",
    )
    arbitrary_frame = sum(
        (1 << x) for x in VERTICES if x.bit_count() in (1, 3) and x & 0b00101
    )
    need(
        all(
            direct_square(jw, f)
            == direct_square(jw ^ gauge_texture(arbitrary_frame), f)
            for f in FACES
        ),
        "direct gauge invariance of all-odd representative",
    )

    words = []
    for x, i, j in ((0, 0, 1), (0, 3, 4), (0, 0, 3), (1 << 1, 0, 3), (1 << 4, 0, 3)):
        a, b = i + 1, j + 1
        word = (a, b, -a, -b)
        words.append(
            {
                "spectators": [LABELS[k] for k in SLOTS if x & (1 << k)],
                "word": [f"{'+' if l > 0 else '-'}{LABELS[abs(l) - 1]}" for l in word],
                "loop_signs_flat_parity_tag_JW_rival": [
                    (-1 if walk(g, (x, 0), word)[1] else 1)
                    for g in (flat, parity_tag, jw, rival)
                ],
            }
        )
    need(
        all(direct_square(rival, f) == 1 for f in FACES if f[0] == 0),
        "rival vacuum agreement",
    )
    need(
        direct_square(rival, (1 << 1, 0, 3)) == 0,
        "C spectator did not expose the rival",
    )

    lifts = {
        name: check_lifts(g, group, arbitrary_frame)
        for name, g, group in (
            ("flat", flat, ALL_PERMS),
            ("Jordan_Wigner", jw, ALL_PERMS),
            ("split_spectator_rival", rival, SPLIT_PERMS),
        )
    }
    need(
        lifts["flat"]["distinct_ratios"] == [1]
        and lifts["Jordan_Wigner"]["distinct_ratios"]
        == lifts["split_spectator_rival"]["distinct_ratios"]
        == [-1],
        "coherent relator's conditional selectivity",
    )
    return {
        "occupation_configurations": len(VERTICES),
        "reciprocal_edges": len(EDGES),
        "directed_transitions_before_tag": 2 * len(EDGES),
        "square_faces": len(FACES),
        "three_cubes": len(cube_face_rows()),
        "edge_to_curvature_rank": face_rank,
        "vertex_frame_rank": gauge_rank,
        "cube_bianchi_rank": cube_rank,
        "curvature_classification": classification,
        "split_independent_bits": {"CC": 1, "WW": 1, "CW": 6},
        "tested_words": words,
        "anticommuting_formal_toggle_tests_out_of_320_each": counts,
        "corrected_slot_lifts": lifts,
        "boundary": [
            "Hard-core addressable slots and reciprocal signs are inputs. No physical Pauli law.",
            "The tag can be stored classically; the signed formal operators are not amplitudes.",
            "A passive relabeling, normalized signed lift and implemented coherent swap differ.",
            "Applying the calibrated odd swap relator to the corrected toggle lift would select S5 all-odd; the identity of the physical controls is unproved.",
            "The split within-block swap tests leave mixed squares unconstrained.",
            "Interpreting the tag as a measurable relative phase requires an order-sensitive coherent/reunion instrument and compatible superselection handling; cross-block visibility is not automatic.",
            "No physical fermions, transport exchange, spin-statistics, Born rule or QM closure.",
        ],
    }


def main() -> None:
    print(json.dumps(report(), indent=2))


if __name__ == "__main__":
    main()
