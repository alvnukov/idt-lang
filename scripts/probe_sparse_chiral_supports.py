"""Punctures of the supplied five-slot symmetric pencil (standalone research probe).

Keep every undeleted entry nonzero. The two tests below certify *exactly*
rank ten with specified unit channel coefficients regardless of phases and
magnitudes over C. A negative test is not a theorem of rank-ten avoidance.
Edge indices are the adapter's lexicographic unordered even-mask pairs.

For k=1,...,12 deletions we count the survivors of the 85 support tests;
eligibility conditions are reported separately. The first all-channel
survivors (k=5) and first all-vertex/all-channel survivors (k=12) each
admit at least one weighting avoiding rank ten for ALL complex coefficients.
See vertex_control and split_control. We do not classify arbitrary weights
on those supports or promote the adapter's unsupported-zero status.
The forest control needs four channels to reveal its forced rank ten.

All addresses, symmetric supports, freely selectable coefficients and the
rank holdout are supplied here; no observable, particle or physical law is
reconstructed. These finite arguments are not Lean proof artifacts.

Run: python3 -B -O -m scripts.probe_sparse_chiral_supports
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Iterable, Iterator, Sequence
from functools import cache
from itertools import combinations
from math import comb

from scripts.probe_chiral_pencil_signs import (
    EDGES as REFERENCE_EDGES,
)
from scripts.probe_chiral_pencil_signs import (
    car_certificate,
    exterior_witness,
    need,
    rank_q,
    step,
)
from theory_experiments.chiral_pencil import CHANNELS, EDGES, MASKS

FULL = (1 << len(EDGES)) - 1


def bits(items: Iterable[int]) -> int:
    return sum(1 << j for j in items)


def singles(mask: int) -> Iterator[int]:
    while mask:
        b = mask & -mask
        yield b
        mask ^= b


VERTEX = {m: bits(j for j, e in enumerate(EDGES) if m in e) for m in MASKS}
AXIS = tuple(bits(j for j, c in enumerate(CHANNELS) if c == i) for i in range(10))
SLOTS = tuple(AXIS[i] | AXIS[i + 1] for i in range(0, 10, 2))


@cache
def triples() -> tuple[tuple[tuple[int, ...], int, int, int, int], ...]:
    tests = []
    for ks in combinations(range(10), 3):
        if len({k // 2 for k in ks}) != 3:
            continue
        sub = sum(AXIS[k] for k in ks)
        incident = [sub & v for v in VERTEX.values()]
        stars = [v for v in incident if v.bit_count() == 3]
        need(len(stars) == 2 and not stars[0] & stars[1], "two distinct star centers")
        need(
            all(
                ((VERTEX[a] & sub).bit_count(), (VERTEX[b] & sub).bit_count())
                in ((1, 3), (3, 1))
                for j, (a, b) in enumerate(EDGES)
                if (stars[0] | stars[1]) >> j & 1
            ),
            "each star edge is pendant",
        )
        cycle = sub ^ stars[0] ^ stars[1]
        need(cycle.bit_count() == 6, "six remaining edges")
        matchings = []
        for edges in combinations((x.bit_length() - 1 for x in singles(cycle)), 3):
            if len({v for j in edges for v in EDGES[j]}) == 6:
                matchings.append(bits(edges))
        need(
            len(matchings) == 2
            and sum(matchings) == cycle
            and not matchings[0] & matchings[1],
            "complementary hexagon matchings",
        )
        tests.append((ks, *matchings, *stars))
    need(len(tests) == 80, "all distinct-slot triples")
    return tuple(tests)


def repair(d: int) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """None: screened but unresolved; otherwise a necessary disjunction to extend D.

    A reciprocal pair has disjoint edges. Five surviving edges have rank ten.
    Any extension avoiding this witness must delete at least one more of them.
    A broken hexagon with exactly one surviving matching has a nonzero
    determinant monomial in its 3x3 biadjacency matrix (hence symmetric rank 6).
    Each nonempty star has rank 2. To escape their rank-ten sum, a superset
    of D must delete one edge of the surviving matching OR kill a whole star.
    """
    for i, m in enumerate(SLOTS):
        if (d & m).bit_count() == 3:
            return (2 * i, 2 * i + 1), tuple(singles(m & ~d))
    for ks, a, b, s, t in triples():
        if bool(d & a) != bool(d & b) and d & s != s and d & t != t:
            intact = a if not d & a else b
            return ks, (*singles(intact), s & ~d, t & ~d)
    return None


def search(limit: int) -> set[int]:
    """Complete among supersets of distinguished edge 0, by the repair disjunction.

    Stop only at the cardinality bound; deduplicate masks, not witnesses.
    Any non-pruned target D is reached inductively via a child contained in D.
    """
    seen, keep = set(), set()

    def visit(d: int) -> None:
        if d in seen or d.bit_count() > limit:
            return
        seen.add(d)
        constraint = repair(d)
        if constraint is None:
            keep.add(d)
        if d.bit_count() != limit:
            children = singles(FULL & ~d) if constraint is None else constraint[1]
            for delta in children:
                visit(d | delta)

    visit(1)
    return keep


def reference_weights() -> tuple[int, ...]:
    s = exterior_witness()
    weights = {
        (a, b): 1 - 2 * ((s >> j) & 1) for j, (a, b, _) in enumerate(REFERENCE_EDGES)
    }
    need(set(weights) == set(EDGES), "identical reference edge ordering after lookup")
    return tuple(weights[e] for e in EDGES)


def direct_rank(d: int, weights: Sequence[int], coeffs: Sequence[int]) -> int:
    matrix = [[0] * 16 for _ in MASKS]
    for j, ((a, b), k) in enumerate(zip(EDGES, CHANNELS, strict=True)):
        if not (d >> j & 1):
            x, y = MASKS.index(a), MASKS.index(b)
            matrix[x][y] = matrix[y][x] = weights[j] * coeffs[k]
    return rank_q(matrix)


def unit(ks: Iterable[int]) -> tuple[int, ...]:
    active = set(ks)
    return tuple(int(k in active) for k in range(10))


def support_controls() -> None:
    # Reciprocal pairs really are disjoint eight-edge matchings. Any generic
    # complex field subtlety is irrelevant: five nonzero disjoint edges rank 10.
    need(
        all(all((m & v).bit_count() == 1 for v in VERTEX.values()) for m in SLOTS),
        "five perfect reciprocal matchings",
    )
    w = tuple((-1) ** j * (j + 2) for j in range(40))
    for d in (
        1,
        bits((0, 1)),
        bits(x.bit_length() - 1 for x in tuple(singles(SLOTS[0]))[:3]),
    ):
        result = repair(d)
        need(result is not None, "specified nonzero test")
        need(direct_rank(d, w, unit(result[0])) == 10, "exact rational Gaussian rank")
    # Signed nonuniform integer weights above; rational rank computed over Q.
    # Independent brute force at the first nonempty anchored layer. This
    # checks the branching argument against screening every anchored subset.
    brute = {
        1 | bits(js)
        for n in range(4)
        for js in combinations(range(1, 40), n)
        if repair(1 | bits(js)) is None
    }
    need(brute == search(4), "branch vs unpruned subsets through k=4")


def vertex_control(weights: tuple[int, ...]) -> None:
    """One vertex hole is P B P. Its rank differs from rank B by at most 2
    (delete a row, then a column). Since the reference has only ranks 0,8,16
    over C, a rank of 10 is impossible. Two vertex holes also suffice (loss
    at most four). These are existence witnesses, not universal over weights.
    """
    car_certificate()
    d = VERTEX[0]
    need(d.bit_count() == 5 and all(m & ~d for m in AXIS), "all channels still present")
    for u in (unit(()), unit((0,)), unit((0, 1)), (1, 3, 1, -3, 1, 0, 0, 0, 0, 0)):
        before, after = direct_rank(0, weights, u), direct_rank(d, weights, u)
        need(
            before in (0, 8, 16) and before - 2 <= after <= before,
            "principal compression",
        )


def parity_hole(pair: int, side: int) -> int:
    inside = {m for m in MASKS if (m & pair).bit_count() % 2 == side}
    return bits(j for j, (a, b) in enumerate(EDGES) if a in inside and b in inside)


def split_control(weights: tuple[int, ...]) -> None:
    """Split the exterior witness into the first two slots A and last three B.

    Delete the induced edges on the A-even vertices. The signed complement
    pairing J preserves A-parity. Remove J for rank purposes and order the
    inputs as even-even, odd-odd, outputs as odd-even, even-odd. The new
    operator is [[E⊗I4, -I2⊗T], [0, F⊗I4]]. T acts from B-odd to B-even.

         E = [[x0,-y1],[x1,y0]],     F = [[y0,y1],[-x1,x0]] = adj E.

    Their determinant is qA=x0*y0+x1*y1. For qA!=0, rank=16. If qA=0
    and the four A coefficients are not all zero, E and F have rank one,
    FE=0 and im E=ker F. The off-diagonal carries ker(F⊗I4) into im(E⊗I4).
    A triangular block map with this property has rank rank(E⊗I4)+rank(F⊗I4)
    (project its image to the second output); hence rank 8. If E=0 then
    F=0 and only the off-diagonal remains, giving rank at most 8. No generic
    rank assumption, bounded coefficient grid, or reality restriction is used.
    An even translation toggling a chosen A bit and an outside bit interchanges
    the two sides; slot permutations carry the pair to any other pair. Transport
    the weighting with the address/channel permutation to get all 20 examples.
    """
    d = parity_hole(3, 0)
    ueven, uodd = (0, 3), (1, 2)
    # Check the full 16x16 coefficient matrix for *each* basis channel against
    # the block expression, including all zeros and the one fixed row sign
    # per output of J. Linearity extends these identities to every coefficient.
    positions = {e: j for j, e in enumerate(EDGES)}
    jsigns: dict[int, int] = {}
    for k in range(10):
        x, y, u, v = unit((k,))[:4]
        e = ((x, -v), (u, y))
        f = ((y, v), (-u, x))
        for i in MASKS:
            a, b = i & 3, i >> 2
            for row in MASKS:
                out = row ^ 31
                a2, b2 = out & 3, out >> 2
                expected = 0
                if a in ueven and a2 in uodd and b == b2:
                    expected = e[uodd.index(a2)][ueven.index(a)]
                elif a in uodd and a2 in ueven and b == b2:
                    expected = f[ueven.index(a2)][uodd.index(a)]
                elif a == a2 and a in uodd and k >= 4:
                    dest = step(b, (k // 2 - 2, k % 2 == 0))
                    if dest is not None and dest[0] == b2:
                        expected = -dest[1]
                j = positions.get(tuple(sorted((i, row))))
                actual = (
                    weights[j]
                    if j is not None and CHANNELS[j] == k and not d >> j & 1
                    else 0
                )
                if expected:
                    sign = jsigns.setdefault(row, actual * expected)
                    need(
                        abs(sign) == 1 and actual == sign * expected,
                        "fixed pairing sign",
                    )
                else:
                    need(actual == 0, "zero of block expression")
    need(set(jsigns) == set(MASKS), "pairing verified on every output")
    for coeffs, expected_rank in (
        (unit(()), 0),
        (unit((4,)), 4),
        (unit((4, 5)), 8),
        (unit((0,)), 8),
        ((1, 3, 1, -3, 3, -2, 1, 1, 1, 2), 8),
        (unit((0, 1)), 16),
    ):
        need(direct_rank(d, weights, coeffs) == expected_rank, "rational block control")


def leaf_rank(d: int, ks: tuple[int, ...]) -> int | None:
    """Eliminate a leaf and its neighbor: their invertible 2x2 pivot adds 2.
    Others touch only the neighbor, whose inverse-pivot diagonal is zero; the
    remaining matrix is unchanged. Unresolved cyclic cores return None.
    """
    active = ~d & sum(AXIS[k] for k in ks)
    r = 0
    while active:
        for v in VERTEX.values():
            incident = v & active
            if incident.bit_count() == 1:
                a, b = EDGES[incident.bit_length() - 1]
                active &= ~(VERTEX[a] | VERTEX[b])
                r += 2
                break
        else:
            return None
    return r


def four_channel_control() -> None:
    kept = bits((1, 3, 9, 11, 13, 14, 15, 20, 25, 30, 31, 32, 38, 39))
    d = FULL ^ kept
    need(all(v & kept for v in (*VERTEX.values(), *AXIS)), "no empty vertex or channel")
    need(repair(d) is None, "two initial screens miss this forest")
    hist = Counter(
        leaf_rank(d, ks) for n in (1, 2, 3) for ks in combinations(range(10), n)
    )
    need(hist == {2: 7, 4: 32, 6: 88, 8: 48}, "all 175 small supports; no rank ten")
    axes = (0, 1, 2, 3)
    need(leaf_rank(d, axes) == 10, "four-channel leaf certificate")
    w = tuple((j + 3) * (-1) ** j for j in range(40))
    need(direct_rank(d, w, unit(axes)) == 10, "independent four-channel exact rank")


def main() -> None:
    limit = 12
    support_controls()
    keep = search(limit)
    freq = Counter(d.bit_count() for d in keep)
    eligible = Counter(d.bit_count() for d in keep if all(m & ~d for m in AXIS))
    both = {d for d in keep if all(m & ~d for m in (*AXIS, *VERTEX.values()))}
    addressed = Counter(d.bit_count() for d in both)
    expected = (
        (0, 0, 0),
        (0, 0, 0),
        (0, 0, 0),
        (10, 0, 0),
        (16, 16, 0),
        (0, 0, 0),
        (0, 0, 0),
        (125, 0, 0),
        (120, 40, 0),
        (200, 200, 0),
        (160, 0, 0),
        (1140, 20, 20),
    )
    print(
        "k total survivors channel_active_survivors vertex_and_channel_active_survivors"
    )
    for k in range(1, limit + 1):
        # The even-XOR translations take an endpoint to zero, and permutations
        # of five slots take the distance-four displacement to any other.
        # Both permute the named channels and our support tests. Thus oriented
        # incidences (D,e in D) double-count as 40*anchored_count = k*count.
        totals = tuple(40 * c[k] for c in (freq, eligible, addressed))
        need(all(n % k == 0 for n in totals), "integral incidence count")
        row = tuple(n // k for n in totals)
        need(row == expected[k - 1], "reproduced support census")
        print(k, comb(40, k), *row)
    need(
        {d for d in keep if d.bit_count() == 5}
        == {v for v in VERTEX.values() if v & 1},
        "first all-channel survivors are precisely the vertex holes",
    )
    holes = {
        parity_hole(bits(pair), side)
        for pair in combinations(range(5), 2)
        for side in (0, 1)
    }
    need(
        len(holes) == 20 and all(h.bit_count() == 12 for h in holes),
        "distinct parity holes",
    )
    need(
        both == {h for h in holes if h & 1}, "all doubly active survivors through k=12"
    )
    weights = reference_weights()
    vertex_control(weights)
    split_control(weights)
    four_channel_control()
    print(
        "k=5: 16 vertex holes; k=12: 20 parity holes with all vertices and channels active."
    )
    print(
        "Each admits an all-complex-coefficient no-rank-ten weighting, not arbitrary weights."
    )
    print(
        "A 14-edge forest evades every <=3-channel test but has forced rank ten on axes 0,1,2,3."
    )
    print(
        "Supplied pencil and selection hypothesis; no physical rank law or status upgrade."
    )


if __name__ == "__main__":
    main()
