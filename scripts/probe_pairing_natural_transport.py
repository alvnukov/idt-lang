"""Readout-free natural routing between supplied matchings of six persistent labels.

EXTRA STRUCTURE. One tetrahedron supplies one packet complement. Its S4 edge
relabelings preserve that complement; fifteen independently varying matchings
are not supplied by relabeling the same tetrahedron. This probe tests that
additional structure without projections, polar rebalancing, random outcomes,
or a quantum measurement postulate. Every deterministic link is a permutation
of the six actual data addresses, hence reversible for arbitrary label data.

CLASSIFICATION. For disjoint matching involutions M,N their product R=NM has
order three. U=R^2=MN satisfies UM=NU and U(N,M)=U(M,N)^(-1). There is exactly
ONE other S6-equivariant permutation prescription on this ordered orbit:
V=UM=MNM=NMN, an odd involution, also reversible. Indeed <M,N> acts regularly
as S3 on the six labels. Its centralizer is the common stabilizer H of M,N,
also regular S3. Equivariance forces a selected permutation into C(H)=<M,N>;
exactly two elements there conjugate M to N. This classifies all six-label
permutations, so in particular all pair-local ones, without assuming a word
ansatz. The program exhausts all 720 permutations and verifies orbit coverage.

For identical charts the equivariant choices are I and M; requiring no change
selects I. For a single common pair, H has order eight, is V4 x C2, and is
self-centralizing. It contains M,N, so every H-fixed permutation commutes
with M and cannot conjugate it to distinct N. No equivariant deterministic
intertwiner extends across this orbit, even if arbitrary six-label routing
is permitted. Breaking symmetry, supplying more local structure, or recording
an additional choice can evade this exact finite obstruction.

LOOPS. On the 15-vertex, 60-edge disjoint-matching graph, U holonomies give
exactly C_S6(M0) intersect A6, order24: the original tetrahedral S4 edge action.
Odd coordinates are signed permutations with even total pair-flip parity;
even coordinates are pair permutations. On the centered even plane this gives
S3. Odd-3 and centered-even-2 determinants agree, but can both be -1: these
are not automatically orientation-preserving block rotations. V multiplies
each odd-coordinate link by -I3 and leaves even links unchanged. Its full
loop group has order48, the matching stabilizer S4 x C2. The central complement
acts as (-I3,+I2). An odd-length U loop already has identity holonomy, giving
that independent central element under V. Both groups are FINITE; no continuous
gauge group or arbitrary independent block orientation follows.

STOCHASTIC CONTROL. With one common pair there are two single transpositions
intertwining M,N. Their equal mixture is equivariant and reversal-symmetric.
Each realized permutation preserves all data, and retaining its choice permits
exact inversion. Forgetting the choice is not a reversible channel on the six
labels: its average has rank4 and kills an explicit contrast. Uniform mixing
over all48 intertwiners keeps only the total population. Randomness and a
choice register are additional resources, not a deterministic resolution.

CHARTS ARE NOT CURVATURE. These loop permutations describe the actively
specified routing rule. Arbitrarily selecting one frame at each matching gives
flat links g_N g_M^(-1), including shared-pair links, but introduces a common
frame choice and is not S6-equivariant. A mere passive change of description
does not perform a physical loop permutation or establish a dynamical gauge
field. No metric/readout is used to enact U,V; the small Gram matrix below only
checks coordinates of the centered pair-count plane.

Sources: MATCHES and loop_generators from probe_matching_transport.py; packet
order from probe_six_packet_sectors.py. Exact bounded finite controls and the
stated group arguments, not Lean proofs or a physical gauge identification.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, deque
from fractions import Fraction as F
from itertools import pairwise, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import probe_balanced_phase_composition as b
from scripts.probe_matching_transport import MATCHES, Match, loop_generators
from scripts.probe_six_packet_sectors import PACKETS

Perm = tuple[int, ...]
Edges = dict[tuple[int, int], Perm]
IDENTITY = tuple(range(6))
S6 = tuple(permutations(range(6)))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def mul(a: Perm, c: Perm) -> Perm:
    return tuple(a[c[i]] for i in range(6))


def inverse(a: Perm) -> Perm:
    return tuple(a.index(i) for i in range(6))


def conjugate(a: Perm, c: Perm) -> Perm:
    return mul(mul(a, c), inverse(a))


def parity(a: Perm) -> int:
    inversions = sum(a[i] > a[j] for i in range(6) for j in range(i + 1, 6))
    return -1 if inversions % 2 else 1


def involution(m: Match) -> Perm:
    return tuple(
        next(c if a == i else a for a, c in m if i in (a, c)) for i in range(6)
    )


INVOLUTIONS = tuple(involution(m) for m in MATCHES)


def common(i: int, j: int) -> int:
    return len(set(MATCHES[i]) & set(MATCHES[j]))


def rotate(m: Perm, n: Perm) -> Perm:
    r = mul(n, m)
    return mul(r, r)


def reflect(m: Perm, n: Perm) -> Perm:
    return mul(rotate(m, n), m)


def stabilizer(m: Perm, n: Perm) -> tuple[Perm, ...]:
    return tuple(p for p in S6 if mul(p, m) == mul(m, p) and mul(p, n) == mul(n, p))


def intertwiners(m: Perm, n: Perm) -> tuple[Perm, ...]:
    return tuple(p for p in S6 if mul(p, m) == mul(n, p))


def closure(generators: tuple[Perm, ...], cap: int) -> set[Perm]:
    found, pending = {IDENTITY}, [IDENTITY]
    while pending:
        x = pending.pop()
        for g in generators:
            y = mul(g, x)
            if y not in found:
                found.add(y)
                pending.append(y)
                need(len(found) <= cap, "finite permutation-group bound")
    return found


def permutation_matrix(p: Perm) -> b.Matrix:
    return b.matrix(tuple(tuple(int(i == p[j]) for j in range(6)) for i in range(6)))


def block(p: Perm, source: Match, target: Match, sign: int) -> b.Matrix:
    """Destination rows/source columns in the sorted, oriented pair frames."""
    rows = [[0] * 3 for _ in range(3)]
    for col, (a, c) in enumerate(source):
        image = (p[a], p[c])
        destination = tuple(sorted(image))
        row = target.index((destination[0], destination[1]))
        rows[row][col] = 1 if sign == 1 or image == destination else -1
    return b.matrix(rows)


def centered(a: b.Matrix) -> b.Matrix:
    # Coordinates (x,y,-x-y); the induced Gram is [[2,1],[1,2]].
    basis = b.matrix(((1, 0), (0, 1), (-1, -1)))
    image = b.multiply(a, basis)
    reduced = image[:2]
    need(b.multiply(basis, reduced) == image, "centered plane invariance")
    gram = b.matrix(((2, 1), (1, 2)))
    need(
        b.multiply(b.transpose(reduced), b.multiply(gram, reduced)) == gram,
        "centered coordinate metric",
    )
    return reduced


def classification() -> dict[str, object]:
    out: dict[str, object] = {}
    need(len(MATCHES) == 15 and len(S6) == 720, "finite domains")
    for shared, expected_h, expected_choices, orbit_size in (
        (3, 48, 2, 15),
        (0, 6, 2, 120),
        (1, 8, 0, 90),
    ):
        j = next(i for i in range(15) if common(0, i) == shared)
        m, n = INVOLUTIONS[0], INVOLUTIONS[j]
        h = stabilizer(m, n)
        centralizer = tuple(p for p in S6 if all(mul(p, q) == mul(q, p) for q in h))
        choices = tuple(p for p in centralizer if mul(p, m) == mul(n, p))
        need(
            len(h) == expected_h and len(choices) == expected_choices,
            "natural transport classification",
        )
        orbit = {(conjugate(p, m), conjugate(p, n)) for p in S6}
        expected = {
            (INVOLUTIONS[a], INVOLUTIONS[c])
            for a, c in product(range(15), repeat=2)
            if common(a, c) == shared
        }
        need(
            orbit == expected and len(orbit) == orbit_size,
            "all ordered configurations covered",
        )
        if shared == 0:
            need(
                len(centralizer) == 6 and {p[0] for p in centralizer} == set(range(6)),
                "regular six-label action",
            )
            need(
                set(centralizer) == closure((m, n), 6), "regular S3 double centralizer"
            )
            need(
                set(choices) == {rotate(m, n), reflect(m, n)},
                "only rotation and reflection",
            )
            for p in S6:
                pm, pn = conjugate(p, m), conjugate(p, n)
                need(
                    rotate(pm, pn) == conjugate(p, rotate(m, n)),
                    "rotation equivariance",
                )
                need(
                    reflect(pm, pn) == conjugate(p, reflect(m, n)),
                    "reflection equivariance",
                )
        elif shared == 1:
            need(
                set(centralizer) == set(h) and m in h and n in h,
                "shared-pair stabilizer obstruction",
            )
            need(
                all(mul(a, c) == mul(c, a) for a in h for c in h),
                "abelian V4 x C2 stabilizer",
            )
            need(
                all(mul(a, a) == IDENTITY for a in h),
                "elementary abelian shared-pair stabilizer",
            )
        else:
            need(set(choices) == {IDENTITY, m}, "identical-chart options")
        out[str(shared)] = {
            "ordered_configurations": orbit_size,
            "common_stabilizer_order": len(h),
            "equivariant_permutation_choices": len(choices),
        }
    return out


def make_edges(flip: bool) -> Edges:
    edges = {}
    for i, j in permutations(range(15), 2):
        if common(i, j):
            continue
        m, n = INVOLUTIONS[i], INVOLUTIONS[j]
        r = mul(n, m)
        need(
            mul(mul(r, r), r) == IDENTITY and r != IDENTITY,
            "disjoint product order three",
        )
        u = reflect(m, n) if flip else rotate(m, n)
        need(mul(u, m) == mul(n, u), "pairing intertwiner")
        reverse = reflect(n, m) if flip else rotate(n, m)
        need(reverse == inverse(u), "exact reversal")
        need(parity(u) == (-1 if flip else 1), "link parity")
        if flip:
            need(mul(u, u) == IDENTITY, "reflection involution")
            need(u == mul(mul(m, n), m) == mul(mul(n, m), n), "reflection word")
        else:
            need(u == mul(m, n), "rotation word")
        edges[i, j] = u
    need(len(edges) == 120, "disjoint graph links")
    return edges


def raw_loops(
    edges: Edges,
) -> tuple[dict[int, Perm], tuple[tuple[tuple[int, ...], Perm], ...]]:
    frames = {0: IDENTITY}
    paths: dict[int, tuple[int, ...]] = {0: (0,)}
    queue = deque((0,))
    loops = []
    while queue:
        i = queue.popleft()
        for j in range(15):
            if (i, j) not in edges:
                continue
            t = mul(edges[i, j], frames[i])
            if j not in frames:
                frames[j], paths[j] = t, (*paths[i], j)
                queue.append(j)
            else:
                loop = mul(inverse(frames[j]), t)
                path = (*paths[i], j, *reversed(paths[j][:-1]))
                direct = IDENTITY
                for a, c in pairwise(path):
                    direct = mul(edges[a, c], direct)
                need(loop == direct, "loop reversal/composition convention")
                loops.append((path, loop))
    need(len(frames) == 15, "connected matching graph")
    return frames, tuple(loops)


def tetrahedral_group() -> set[Perm]:
    return {
        tuple(PACKETS.index(tuple(sorted((p[i], p[j])))) for i, j in PACKETS)
        for p in permutations(range(4))
    }


def loop_controls() -> dict[str, object]:
    m = INVOLUTIONS[0]
    full = set(stabilizer(m, m))
    tetra = tetrahedral_group()
    need(
        len(tetra) == 24 and tetra == {p for p in full if parity(p) == 1},
        "tetrahedral S4 preserves only the base complement",
    )
    data: dict[str, object] = {}
    edge_sets = (make_edges(False), make_edges(True))
    for (i, j), rotation in edge_sets[0].items():
        reflection = edge_sets[1][i, j]
        need(
            block(reflection, MATCHES[i], MATCHES[j], -1)
            == b.scale(-1, block(rotation, MATCHES[i], MATCHES[j], -1)),
            "reflection adds the odd sign on every link",
        )
        need(
            block(reflection, MATCHES[i], MATCHES[j], 1)
            == block(rotation, MATCHES[i], MATCHES[j], 1),
            "reflection leaves every even link unchanged",
        )
    raw_records = []
    for flip, edges in enumerate(edge_sets):
        frames, loops = raw_loops(edges)
        raw_records.append(loops)
        minus_edges = {
            (i, j): block(p, MATCHES[i], MATCHES[j], -1) for (i, j), p in edges.items()
        }
        plus_edges = {
            (i, j): block(p, MATCHES[i], MATCHES[j], 1) for (i, j), p in edges.items()
        }
        for sign, coordinates in ((-1, minus_edges), (1, plus_edges)):
            actual = loop_generators(coordinates)
            expected = tuple(
                (path, block(p, MATCHES[0], MATCHES[0], sign)) for path, p in loops
            )
            need(actual == expected, "independent coordinate loop composition")
        group = closure(tuple(p for _, p in loops), 48)
        need(group == (full if flip else tetra), "joint finite holonomy group")
        plus_image, minus_image, joint_image = set(), set(), set()
        orientations: Counter[tuple[int, int]] = Counter()
        for p in group:
            odd = block(p, MATCHES[0], MATCHES[0], -1)
            even = centered(block(p, MATCHES[0], MATCHES[0], 1))
            need(
                b.multiply(b.transpose(odd), odd) == b.identity(3),
                "odd signed permutation",
            )
            d_odd, d_even = int(b.determinant(odd)), int(b.determinant(even))
            need(d_odd * d_even == parity(p), "raw parity versus block orientations")
            orientations[d_odd, d_even] += 1
            plus_image.add(even)
            minus_image.add(odd)
            joint_image.add((odd, even))
        need(
            len(plus_image) == 6 and len(minus_image) == len(joint_image) == len(group),
            "faithful odd and joint actions",
        )
        # A selected global frame makes every link flat; this is an extra
        # common choice, not the natural rule on each ordered pair.
        flat = {
            (i, j): mul(frames[j], inverse(frames[i]))
            for i, j in product(range(15), repeat=2)
        }
        for i, j, k in product(range(15), repeat=3):
            need(mul(flat[j, k], flat[i, j]) == flat[i, k], "flat chosen frames")
        i, j = next((i, j) for i, j in edges if edges[i, j] != flat[i, j])
        need(
            edges[i, j] != flat[i, j], "natural rule is not merely selected flat charts"
        )
        data["reflection" if flip else "rotation"] = {
            "joint_group_order": len(group),
            "odd_image_order": len(minus_image),
            "centered_even_image_order": len(plus_image),
            "orientation_counts": {
                str(key): value for key, value in sorted(orientations.items())
            },
            "nontrivial_loop": list(next(path for path, p in loops if p != IDENTITY)),
        }
    rotation_loops, reflection_loops = raw_records
    for (path, p), (other, q) in zip(rotation_loops, reflection_loops, strict=True):
        need(path == other, "same loop frames")
        need(
            q == (mul(m, p) if (len(path) - 1) % 2 else p),
            "length parity adds central complement",
        )
    odd_identity = next(
        path for path, p in rotation_loops if (len(path) - 1) % 2 and p == IDENTITY
    )
    need(
        block(m, MATCHES[0], MATCHES[0], -1) == b.scale(-1, b.identity(3)),
        "central odd sign",
    )
    need(
        centered(block(m, MATCHES[0], MATCHES[0], 1)) == b.identity(2),
        "central even identity",
    )
    data["odd_length_identity_rotation_loop"] = list(odd_identity)
    data["graph_cycle_rank"] = 60 - 15 + 1
    return data


def stochastic_control() -> dict[str, object]:
    m, n = INVOLUTIONS[0], INVOLUTIONS[1]
    need(common(0, 1) == 1, "shared-pair example")
    candidates = intertwiners(m, n)
    swaps = tuple(p for p in candidates if sum(p[i] != i for i in range(6)) == 2)
    need(
        len(candidates) == 48 and len(swaps) == 2, "canonical two-transposition mixture"
    )
    for h in stabilizer(m, n):
        need({conjugate(h, p) for p in swaps} == set(swaps), "stochastic equivariance")
    need(all(inverse(p) == p for p in swaps), "stochastic reversal")
    average = b.scale(F(1, 2), b.add(*(permutation_matrix(p) for p in swaps)))
    need(
        b.multiply(average, average) == average and b.trace(average) == 4,
        "forgotten choice rank-four projection",
    )
    lost = b.matrix(((0,), (0,), (0,), (1,), (-1,), (0,)))
    need(b.multiply(average, lost) == b.scale(0, lost), "explicit lost contrast")
    for p in swaps:
        need(
            b.multiply(
                permutation_matrix(inverse(p)), b.multiply(permutation_matrix(p), lost)
            )
            == lost,
            "choice-retained reversible data",
        )
    uniform = b.scale(0, b.identity(6))
    for p in candidates:
        uniform = b.add(uniform, b.scale(F(1, 48), permutation_matrix(p)))
    need(
        uniform == b.matrix(((F(1, 6),) * 6,) * 6),
        "uniform intertwiner mixture retains only total",
    )
    return {
        "two_swaps": [list(p) for p in swaps],
        "forgotten_choice_rank": 4,
        "lost_contrast": [0, 0, 0, 1, -1, 0],
        "uniform_all_intertwiners_rank": 1,
        "retained_choice": "each permutation exactly reversible; extra choice register",
    }


def main() -> None:
    result = {
        "status": "exact finite routing controls; independently varying matching is supplied",
        "classification_by_shared_pairs": classification(),
        "holonomy": loop_controls(),
        "stochastic_shared_pair_control": stochastic_control(),
        "boundary": "finite active permutations are not a derived gauge field or physical curvature",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
