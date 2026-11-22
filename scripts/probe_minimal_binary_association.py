"""The lowest comparison order for a universally marginal-null binary tally.

Assume an instrument sees only four joint binary count cells (a,b,c,d).
Its response is a polynomial of degree at most two in those counts; this
includes sums over one or two comparisons and sampling distinct pairs via
falling factorials. Demand zero on EVERY factorized count array, not just
our chosen 16 states, balanced arrays, or a fitted reference distribution.

Substitute (ru,rv,su,sv) for the four cells. Distinct monomials of degree
<=2 then have distinct exponent signatures in (r,s,u,v), except ad and
bc. A polynomial which vanishes for all nonnegative integer quadruples
has zero coefficients (apply the one-variable finite-root property
successively). Consequently no first-order nonzero tally works, and the
second-order kernel is precisely multiples of ad-bc. A primitive signed
integer unit selects one of its two signs. This is a result *in a specified
instrument class*, not a derivation that any physical detector should
measure association, ignore its marginals, or use at most two comparisons.

For a marked subset T of N root directions and a queried bit subset W,
the same tally is N|T intersect W|-|T||W|. Disjoint-union additivity,
zero on a constant and oddness under complement now follow without
putting those conditions into the charge dictionary. On the marked
five-direction graph |T|=2, so elementary contributions are +3 or -2.
Some singleton subsets are not even-sheet states: the elementary
contribution is a combinatorial decomposition, not five observed particles.
Higher-degree or normalized readouts survive the same independence test.
"""

from collections import Counter, defaultdict
from itertools import combinations_with_replacement, product

from scripts.probe_anonymous_folded_carrier import forced_completion
from scripts.probe_two_turn_germ_ballots import record, votes


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def substitution(n):
    monomials = [w for k in range(n+1) for w in combinations_with_replacement(range(4), k)]
    groups = defaultdict(list)
    for m in monomials:
        counts = Counter(m)
        a, b, c, d = (counts[j] for j in range(4))
        groups[a+b, c+d, a+c, b+d].append(m)
    return groups


def det(cells):
    a, b, c, d = cells
    return a*d-b*c


def relation(t, w):
    return 5*(t & w).bit_count()-t.bit_count()*w.bit_count()


def trial(cells, draws):
    # Distinct trials vs independently resampling the same *index*:
    # algebra on a finite repeated-sample space, not a sampling hypothesis.
    outcomes = tuple(i for i, count in enumerate(cells) for _ in range(count))
    total = 0
    for sample in product(outcomes, repeat=draws):
        counts = Counter(sample)
        total += det([counts[i] for i in range(4)])
    need(total == draws*(draws-1)*det(cells)*len(outcomes)**(draws-2),
         "expected signed tally of iid draws")


def probe():
    kernels = []
    for n in range(5):
        groups = substitution(n)
        kernels.append(sum(len(g)-1 for g in groups.values()))
    collisions = [set(g) for g in substitution(2).values() if len(g) > 1]
    need(kernels == [0, 0, 1, 5, 15] and collisions == [{(0, 3), (1, 2)}],
         "lowest-degree marginal-null kernel")
    # The linear agreement score fails on biased independent marginals.
    independent = (6, 3, 2, 1)
    a, b, c, d = independent
    need(det(independent) == 0 and a-b-c+d == 2, "independent baseline countercontrol")
    for tables in (independent, (2, 1, 0, 2), (1, 0, 0, 1)):
        trial(tables, 3)
    g = forced_completion()
    checked = 0
    for root in range(len(g)):
        readings = record(g, root)
        ports = tuple(readings)
        masks = {v: sum(readings[p][v] << i for i, p in enumerate(ports)) for v in range(len(g))}
        need(set(masks.values()) == {w for w in range(32) if not w.bit_count() % 2},
             "covered endpoint chart")
        for t in range(len(g)):
            if t == root or t in g[root]:
                continue
            marked = masks[t]
            need(marked.bit_count() == 2, "marked bit subset")
            coefficients = [relation(marked, 1 << i) for i in range(5)]
            need(Counter(coefficients) == {-2: 3, 3: 2} and sum(coefficients) == 0,
                 "primitive integer increments")
            for v, w in masks.items():
                need(votes(readings, t, v)[0] == relation(marked, w), "two instruments disagree")
                checked += 1
            for w in range(32):
                need(relation(marked, 31 ^ w) == -relation(marked, w), "complement")
                for z in range(32):
                    if not w & z:
                        need(relation(marked, w | z) == relation(marked, w)+relation(marked, z),
                             "disjoint additivity")
    # Nonlinear fully marginal-null alternative: multiply determinant by
    # a positive function of the marginal imbalance. Its agreement with
    # independence/constant nulls does not entail the same additive charge.
    t = 3
    def alternate(w):
        return relation(t, w) * (1+(5-2*w.bit_count())**2)
    need(all(alternate(w) == -alternate(31 ^ w) for w in range(32))
         and alternate(3) != alternate(1)+alternate(2), "nonunique higher-order readout")
    need(checked == 2560, "missing frame")
    return kernels, checked


if __name__ == "__main__":
    ranks, frames = probe()
    print(f"Marginal-null polynomial dimensions at degrees <=0..4: {ranks}; "
          f"the sole quadratic generator is the integer determinant. {frames} endpoint checks.")
    print("Disjoint additivity and complement reversal follow for this tally. "
          "Higher-order readouts are not excluded, and a normalized probability law is not derived.")
