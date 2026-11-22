"""When can a reversible deterministic packet rule close on one-slot counts?

One trial is a binary occupancy vector. A batch has N trials; retain only N
and the sum m of those vectors. Closure means *every* two batches with the
same N,m have the same output m. This is not testing one prepared histogram.
Equivalently the output mean is affine on the convex hull of allowed inputs:
any rational affine relation splits after clearing denominators into two such
batches. The kernel of the augmented integer vertex matrix (columns (1,x))
has a rational basis, so output rows annihilating those relations factor
through (1,x) over the reals. Conversely an affine map respects all batches.

For two-of-n packets, vertices are edges of K_n. A two-run vector sum has a
different decomposition into two edges exactly when its endpoints are four
DISTINCT slots: the three pairings give the same sum. Repeated/intersecting
edges have a unique decomposition. Thus a bijection passing these elementary
comparisons sends disjoint edge pairs to disjoint edge pairs (the alternative
outputs remain distinct); finiteness makes this an equivalence. It preserves
the adjacency of the line graph of K_n, the Johnson graph J(n,2).

For n>=5, its maximal cliques of size >=4 are precisely the incident stars:
if ab,ac share a vertex, an edge meeting both without a must be bc; no fourth
distinct edge meets all three sides of that triangle. Stars have size n-1,
so a graph automorphism permutes stars; intersecting two stars identifies
their unique edge. Thus ONLY wire permutations survive, for all n>=5.
For n=4 the three pairs of opposite edges form a matching. Its automorphisms
number 3! * 2^3 = 48: the 24 wires and their distinct complements. These
families do close on every distribution, so the two-run comparisons suffice;
every other reversible edge table fails on two explicit equal-marginal inputs.
This is standard Johnson graph geometry, not a new automorphism theorem;
see A. Ganesan, https://arxiv.org/abs/1412.5055 for the complement symmetry.

On the FULL binary cube a mass-preserving bijection fixes zero and permutes
the one-hot inputs. Affinity then fixes every subset as the sum of those wire
images. This conclusion requires closure ACROSS mixtures of occupancies,
not just separate tests on fixed-number preparations. Conditional operations
can be valid reversible controls and yet fail to close on first moments.
Nothing here forbids storing pair correlations, auxiliary controls, stochastic
channels, non-affine interactions or amplitudes. No dynamical or QM claim.
Run: python3 -B -m scripts.probe_packet_marginal_automorphisms (also with -O).
"""

from itertools import combinations, permutations
from math import factorial


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


def pairs(n):
    return tuple((1 << i) | (1 << j) for i, j in combinations(range(n), 2))


def marginals(batch, n):
    return tuple(sum((x >> i) & 1 for x in batch) for i in range(n))


def relations(n):
    for quad in combinations((1 << j for j in range(n)), 4):
        a, b, c, d = quad
        yield ((a | b, c | d), (a | c, b | d), (a | d, b | c))


def sum_code(x, y):
    """Exactly the slots with one and with two occurrences, respectively."""
    return x ^ y, x & y


def witness(table, comparisons):
    for base, *alts in comparisons:
        lhs = sum_code(*(table[x] for x in base))
        for other in alts:
            if sum_code(*(table[x] for x in other)) != lhs:
                return base, other
    return None


def wire(mask, permutation):
    return sum(1 << dst for src, dst in enumerate(permutation) if mask & (1 << src))


def recover_wires(table, n):
    """Reconstruct from images of entire incident stars, not one fitted input."""
    stars = [frozenset(x for x in table if x & (1 << i)) for i in range(n)]
    by_star = {s: i for i, s in enumerate(stars)}
    dest = tuple(by_star.get(frozenset(table[x] for x in star)) for star in stars)
    if None in dest or len(set(dest)) != n:
        return None
    return dest if all(wire(x, dest) == y for x, y in table.items()) else None


def four_slots():
    edges, groups = pairs(4), tuple(relations(4))
    survivors = set()
    rejected = 0
    for image in permutations(edges):
        table = dict(zip(edges, image))
        bad = witness(table, groups)
        if bad is None:
            survivors.add(image)
            continue
        left, right = bad
        need(
            marginals(left, 4) == marginals(right, 4)
            and marginals(tuple(map(table.get, left)), 4)
            != marginals(tuple(map(table.get, right)), 4),
            "not a paired witness",
        )
        rejected += 1
    wires = {tuple(wire(x, p) for x in edges) for p in permutations(range(4))}
    complemented = {tuple(x ^ 15 for x in image) for image in wires}
    need(
        not wires & complemented
        and survivors == wires | complemented
        and len(wires) == len(complemented) == 24
        and rejected == 672,
        "four-slot census",
    )
    # For any histogram, summing the pointwise indicator identity gives
    # m'[p(i)] = N - m[i], hence minus a wire permutation about N/2.
    for p in permutations(range(4)):
        for x in edges:
            out = 15 ^ wire(x, p)
            need(
                all(((out >> p[i]) & 1) == 1 - ((x >> i) & 1) for i in range(4)),
                "complement marginal identity",
            )


def larger_slots():
    # Finite cross-checks of the general star argument; not a 10! enumeration.
    for n in (5, 6):
        edges, groups = pairs(n), tuple(relations(n))
        for p in permutations(range(n)):
            table = {x: wire(x, p) for x in edges}
            need(
                recover_wires(table, n) == p and witness(table, groups) is None,
                "star reconstruction",
            )
        for e, f in combinations(edges, 2):
            table = {x: f if x == e else e if x == f else x for x in edges}
            need(
                recover_wires(table, n) is None and witness(table, groups) is not None,
                "unresolved non-wire transposition",
            )


def cube_witness(table, n):
    # x + 0 = (x minus i) + e_i. Induction from 0 and the singleton
    # images proves sufficiency of this finite family on the entire cube.
    for x in range(1 << n):
        for i in range(n):
            e = 1 << i
            if x & e and sum_code(table[x], table[0]) != sum_code(
                table[x ^ e], table[e]
            ):
                return (0, x), (x ^ e, e)
    return None


def isolated(mask, block):
    return mask ^ block if (mask & block).bit_count() == 2 else mask


def cube_and_overlap():
    # All mass-preserving permutations of the three-cube; 0 and 7 fixed.
    singles, doubles = (1, 2, 4), (3, 5, 6)
    hits = set()
    for one in permutations(singles):
        for two in permutations(doubles):
            table = {0: 0, 7: 7, **dict(zip(singles, one)), **dict(zip(doubles, two))}
            if cube_witness(table, 3) is None:
                hits.add(tuple(table[x] for x in range(8)))
    need(
        len(hits) == factorial(3)
        and hits
        == {tuple(wire(x, p) for x in range(8)) for p in permutations(range(3))},
        "full-cube affine closure",
    )
    full = {x: isolated(x, 15) for x in range(16)}
    need(
        all(full[y] == x and x.bit_count() == y.bit_count() for x, y in full.items())
        and cube_witness(full, 4) is not None,
        "isolated completion is nonlinear",
    )
    # These two batches already have exactly two marks per run across FIVE
    # slots. A block rule that complements only two-of-four within its block
    # and is otherwise idle is a perfectly reversible, nonclosed completion.
    left, right = (3, 20), (5, 18)  # 01+24 versus 02+14
    expected = ((0, 0, 2, 1, 1), (0, 2, 0, 1, 1))
    need(marginals(left, 5) == marginals(right, 5) == (1, 1, 1, 0, 1), "input control")
    for blocks, pred in (((15,), expected), ((15, 30), expected[::-1])):

        def act(x, schedule=blocks):
            for block in schedule:
                x = isolated(x, block)
            return x

        table = {x: act(x) for x in range(32)}
        need(
            len(set(table.values())) == 32
            and all(x.bit_count() == y.bit_count() for x, y in table.items()),
            "overlap lost information or mass",
        )
        out = tuple(
            marginals(tuple(table[x] for x in batch), 5) for batch in (left, right)
        )
        need(out == pred, "five-slot equal-input countercontrol")


def main():
    four_slots()
    larger_slots()
    cube_and_overlap()
    print(
        "Two-of-four: 48 of 720 tables close on all batch marginals:"
        " 24 wire permutations and 24 complements. Each of the other 672 has a two-run witness."
    )
    print(
        "Two-of-n, n>=5: intersecting stars recover only wire permutations."
        " All wire maps checked on n=5,6; the all-n statement uses the star argument."
    )
    print(
        "Five-slot batches 01+24 and 02+14 have the same marginals."
        " One conditional four-block complement gives (0,0,2,1,1) versus (0,2,0,1,1)."
    )
    print(
        "Full binary cube: reversible mass conservation and affine first-moment closure"
        " allow only wires. Reversible controls with correlation-dependent outputs are not excluded."
    )


if __name__ == "__main__":
    main()
