"""A six-level relative index from binary readouts of local port transport.

Inputs to the operational kernel: adjacency with identifiable reunions, a
root, a chosen first *port germ* at the root, and a traversed edge. Across
an edge parallel to the germ transport it back along that edge. Otherwise
transport by the opposite side of the unique square. Apply a reversible
two-state recorder update depending only on whether these ports coincide.
There are exactly four such update laws (two independent permutations of
two states). Demand that the recorded bit at a vertex not depend on which
path reached it. On the folded graph only the trivial recorder and the one
flipping on different directions qualify. This is a flatness/test contract,
not an assertion that every detector in nature has a two-state flat memory.

Choose the second mark by one nonbacktracking two-step path. At that mark
and at a queried vertex, read the bits for each of five distinct root germs.
For each unordered pair of germs abstain if either location does not
distinguish the two. Otherwise vote +1 if the distinguished orders agree,
-1 if reversed. The difference of the two raw counts is a 2x2 contingency
determinant, with no real-valued amplitude, additive site weight, optimized
energy, sampling law or fitted normalization. The lookup-free index happens
to equal the earlier oriented, primitive-integer field for every two-step
frame. It is not conserved by ordinary carrier motion.

Supplied: access to a rooted experiment, stable port comparison and traversal
of an observed square, path control, a still distinguishable pair of marked
endpoints, reusable preparations or copies, a sign convention for the ballot,
and a tally over all distinct germ pairs. A vote can be zero. A single
unselected click does not return the integer index. Classical finite memory
implements all updates; no quantum incompatibility or measured charge follows.
"""

from collections import Counter, defaultdict, deque
from itertools import combinations, product

from scripts.probe_anonymous_folded_carrier import cube, forced_completion


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def cross(g, u, v, germ, bit, policy):
    if v not in g[u] or germ not in g[u]:
        raise ValueError("cursor or germ not local")
    same = v == germ
    if same:
        next_germ = u
    else:
        fourth = (g[v] & g[germ])-{u}
        if len(fourth) != 1:
            raise ValueError("square reunion missing or ambiguous")
        next_germ, = fourth
    return v, next_germ, bit ^ policy[0 if same else 1]


def closure(g, r, germ, policy):
    first = r, germ, 0
    reached, work = {first: 0}, deque([first])
    while work:
        state = work.popleft()
        u, p, b = state
        for v in g[u]:
            out = cross(g, u, v, p, b, policy)
            need(cross(g, v, u, *out[1:], policy) == state, "non-reciprocal germ update")
            if out not in reached:
                reached[out] = reached[state]+1
                work.append(out)
    groups, signs = defaultdict(set), defaultdict(set)
    for u, p, b in reached:
        groups[u].add(p)
        signs[u].add(b)
    need(len(groups) == len(g) and all(len(a) == 1 for a in groups.values()),
         "direction transport itself depended on route")
    return signs, reached.get((r, germ, 1))


def record(g, root):
    reads = {}
    for p in g[root]:
        for policy in product(range(2), repeat=2):
            signs, wall = closure(g, root, p, policy)
            if not policy[0]:
                need(wall is None and all(len(vals) == 1 for vals in signs.values()),
                     "flat policy inconsistent on a closed route")
                values = {v: next(iter(vals)) for v, vals in signs.items()}
                if policy[1]:
                    reads[p] = values
                else:
                    need(set(values.values()) == {0}, "trivial recorder changed")
            else:
                need(wall == 5 and all(len(vals) == 2 for vals in signs.values()),
                     "five different directions must expose the path-sensitive recorder")
    return reads


def votes(reads, t, v, allowed=None):
    ports = tuple(reads if allowed is None else allowed)
    ballots = Counter()
    cells = Counter((reads[p][t], reads[p][v]) for p in ports)
    for a, b in combinations(ports, 2):
        x = reads[a][t]-reads[b][t]
        y = reads[a][v]-reads[b][v]
        ballots[x*y] += 1
    signed = ballots[1]-ballots[-1]
    need(signed == cells[0, 0]*cells[1, 1]-cells[0, 1]*cells[1, 0],
         "native pair ballots differ from independent table determinant")
    return signed, cells


def probe():
    from scripts.probe_rooted_parity_walk import additive_reference

    g = forced_completion()
    matches = Counter()
    for root in range(len(g)):
        reads = record(g, root)
        for t in range(len(g)):
            if t == root:
                need(all(votes(reads, t, v)[0] == 0 for v in range(len(g))),
                     "omitting the second mark should leave zero")
                continue
            if t in g[root]:
                need(votes(reads, t, t)[0] == 4, "neighbor chose a one/four split")
                matches["adjacent"] += 1
                continue
            need(sorted(Counter(reads[p][t] for p in reads).values()) == [2, 3],
                 "turn did not separate two and three")
            observed = tuple(votes(reads, t, v)[0] for v in range(len(g)))
            # Independent comparison AFTER all elementary readouts are finished.
            need(observed == additive_reference(g, root, t), "integer contrast mismatch")
            need(all(votes(reads, t, t, set(reads)-{p})[0] != observed[t]
                     for p in reads), "dropping one direction went unnoticed")
            need(observed[t] == 6 and observed[root] == 0, "endpoint checks")
            # A recorder using no germ sees only 'an edge'. Constant flip is
            # path-dependent on the odd return, while never flip is trivial.
            need(any(z < 0 for z in observed) and any(z > 0 for z in observed),
                 "signed tally is not the probability of an elementary click")
            matches["two_step"] += 1
    # Negative control: removing the odd quotient restores two more flat
    # laws; the same-only update no longer fails the path-independence test.
    unwrapped = cube(5)
    n_flat = sum(closure(unwrapped, 0, min(unwrapped[0]), policy)[1] is None
                 for policy in product(range(2), repeat=2))
    need(n_flat == 4 and matches == {"two_step": 160, "adjacent": 80}, "control counts")
    return matches, n_flat


if __name__ == "__main__":
    counts, flat = probe()
    print(f"{counts['two_step']} two-step frames, 10 pair ballots per vertex, all 2560 indices match. "
          f"{counts['adjacent']} one-step marks yield the 1+4 control.")
    print(f"Exactly one nonconstant flat reversible two-state germ law on the folded carrier; "
          f"{flat} total flat laws on the unwrapped cube. A common tally is extra apparatus.")
