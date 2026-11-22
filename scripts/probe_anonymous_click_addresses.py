"""Can the graph's destructive readout name the *original* survivors?

Use the frozen unsigned device, not a generic bipartite counterexample.
Give the selector every intermediate rail-labelled graph, the registered
settings and output ports, and the parent projection at every split. Siblings
are NOT individually marked "retained" versus "exchanged". Such a mark is
an additional address. Fix ordered factors and both projections at products.
All settings, stages and rails are distinguished; no spatial symmetry assumed.

A deterministic equivariant subset must be a union of stabilizer orbits.
Failed subset sums therefore rule out selecting actual majority occurrences,
even with the genealogy above; they do not rule out cardinalities, quotient
tokens, stochastic matching, or apparatus with extra records. They neither
derive a physical detector nor construct trajectories of single photons.
This is an executable finite probe, not Lean evidence or a claim-status change.

Run: python3 -B -O -m scripts.probe_anonymous_click_addresses
"""

from collections import Counter
from dataclasses import dataclass
from itertools import permutations, product

from scripts.probe_bipartite_triangle_origin import (
    D, Packet, independent, need, path_parity, reflection, seed, split, stock,
)


@dataclass(frozen=True)
class Stage:
    g: Packet
    gens: tuple  # permutations of final vertices induced by history symmetries


def identity(n):
    return tuple(range(n))


def auto(g, p):
    return (len(p) == len(g.tags) and set(p) == set(range(len(p))) and
            all(g.tags[u] == g.tags[v] and {p[w] for w in g.adj[u]} == g.adj[v]
                for u, v in enumerate(p)))


def initial(k):
    # The seed has two DIFFERENT rail labels, so its history stabilizer is trivial.
    return Stage(seed(k), ())


def flips(n, parents):
    return tuple((u + n) % (2*n) if u % n in parents else u
                 for u in range(2*n))


def lift(p):
    return p + tuple(u + len(p) for u in p)


def branches(s, exchange):
    n = len(s.g.tags)
    fixed = [u for u, tag in enumerate(s.g.tags) if exchange(tag) == tag]
    for port, h in enumerate(split(s.g, exchange)):
        # Every old symmetry lifts diagonally. Any other lift differs by
        # flips of siblings over the identity on parents. For the positive
        # device each fiber is a pair of false twins, and a flip is legal
        # iff its two rail labels match. For the negative device each old
        # edge has parallel (not crossed) lifts, so the flip bit must be
        # the same at both ends: connectedness forces a single global bit.
        kernel = ([flips(n, {u}) for u in fixed] if port == 0
                  else [flips(n, set(range(n)))] if len(fixed) == n else [])
        gens = tuple(lift(p) for p in s.gens) + tuple(kernel)
        need(all(auto(h, p) for p in gens), "invalid history generator")
        for p in gens:
            parent = tuple(v % n for v in p[:n])
            need(parent in (identity(n), *s.gens) and
                 all(p[u] % n == parent[u % n] for u in range(2*n)),
                 "generator does not commute with parent projection")
        yield Stage(h, gens)


def both(s, t):
    n, m = len(s.g.tags), len(t.g.tags)
    h = independent(s.g, t.g)
    # For two REGISTERED ordered factor projections these lifts generate
    # the product stabilizer. In a bare product graph there may be more.
    gens = tuple(tuple(p[i]*m+j for i,j in product(range(n),range(m))) for p in s.gens)
    gens += tuple(tuple(i*m+p[j] for i,j in product(range(n),range(m))) for p in t.gens)
    need(all(auto(h, p) for p in gens), "invalid product generator")
    return Stage(h, gens)


def orbits(points, gens):
    todo = set(points)
    parts = []
    while todo:
        orbit = {next(iter(todo))}
        stack = list(orbit)
        while stack:
            u = stack.pop()
            for p in gens:
                v = p[u]
                if v not in orbit:
                    orbit.add(v)
                    stack.append(v)
        need(orbit <= todo, "purported symmetry did not preserve domain")
        todo -= orbit
        parts.append(frozenset(orbit))
    return parts


def sides(g, rail):
    parity = path_parity(g, 0)
    return tuple(frozenset(u for u,t in enumerate(g.tags) if t == rail and parity[u] == b)
                 for b in (0, 1))


def same_action(source, target, gens):
    """Isomorphism of two transitive sets under the SAME generators."""
    if len(source) != len(target):
        return False
    origin = next(iter(source))
    for image in target:
        mapping = {origin:image}
        stack = [origin]
        valid = True
        while stack and valid:
            u = stack.pop()
            for p in gens:
                v, w = p[u], p[mapping[u]]
                if v not in mapping:
                    mapping[v] = w
                    stack.append(v)
                elif mapping[v] != w:
                    valid = False
                    break
        if valid:
            need(set(mapping)==source and set(mapping.values())==target, "bad orbit map")
            return True
    return False


def injection(source, target, gens):
    # Image of an orbit under an equivariant injection is a whole isomorphic
    # orbit. Greedy matching by isomorphism CLASS is exact. This is stronger
    # than finding a union of the desired size or only counting fixed points.
    available = orbits(target,gens)
    for part in orbits(source,gens):
        for j,candidate in enumerate(available):
            if same_action(part,candidate,gens):
                available.pop(j)
                break
        else:
            return False
    return True


def address_test(s):
    """Prove an address obstruction, or report no obstruction for THIS task."""
    case = Counter(states=1)
    for rail in set(s.g.tags):
        a,b = sides(s.g,rail)
        case["rails"] += 1
        majority, minority = sorted((a,b), key=len, reverse=True)
        if not minority:
            continue
        # A side-exchanging symmetry needs an unoriented involution test,
        # not this injection criterion. None occur on the searched domain.
        need(all(p[next(iter(majority))] in majority for p in s.gens),
             "side-exchanging generator: matching classification not implemented")
        has_matching = injection(minority,majority,s.gens)
        if len(a) == len(b):
            if not has_matching:
                case["balanced_matching_wall"] += 1
            continue
        case["mixed_unequal"] += 1
        target = len(majority)-len(minority)
        sizes = 1  # bit i says some union of whole majority orbits has size i
        for orbit in orbits(majority,s.gens):
            sizes |= sizes << len(orbit)
        has_subset = bool(sizes & (1 << target))
        need(not has_matching or has_subset, "injection did not leave invariant survivors")
        case["subset_available" if has_subset else "survivor_wall"] += 1
        if has_subset and not has_matching:
            case["subset_without_matching"] += 1
    return case


def generated_group(gens,n):
    # Independent small exhaustive check only, never used for larger graphs.
    group = {identity(n)}
    todo = list(group)
    while todo:
        p = todo.pop()
        for q in gens:
            r = tuple(q[u] for u in p)
            if r not in group:
                group.add(r)
                todo.append(r)
    return group


def enumerate_lifts(old,h):
    n = len(old.g.tags)
    need(n <= 4, "unbounded exhaustive check")
    found = set()
    for p in generated_group(old.gens,n):
        pp = lift(p)
        for bits in product((0,1),repeat=n):
            f = flips(n,{u for u,b in enumerate(bits) if b})
            q = tuple(pp[v] for v in f)
            if auto(h,q):
                found.add(q)
    return found


def single_scan():
    tally = Counter()
    verified = 0
    layer = [initial(k) for k in D]
    for depth in range(4):
        for s in layer:
            tally += address_test(s)
        if depth == 3:
            break
        nxt = []
        for s,k in product(layer,D):
            for t in branches(s,lambda x: reflection(k,x)):
                if depth < 2:
                    need(generated_group(t.gens,len(t.g.tags)) == enumerate_lifts(s,t.g),
                         "fiber enumeration disagrees with history group")
                    verified += 1
                nxt.append(t)
        layer = nxt
    need(tally["states"] == 777 and verified == 126, "single scan coverage")
    return tally, verified


def product_scan():
    tally, joint = Counter(), Counter()
    # All one-split factor preps (not just the six named preparations).
    prep = [h for a,k in product(D,repeat=2)
            for h in branches(initial(a),lambda x: reflection(k,x))]
    for s,t in product(prep,repeat=2):
        tally += address_test(both(s,t))
    # The native swap-herald experiment, both local setting orders and ports.
    for a,b in product(D,repeat=2):
        g = both(initial(a),initial(b))
        for flag,herald in enumerate(branches(g,lambda t: (t[1],t[0]))):
            for k,l in product(D,repeat=2):
                left = lambda t: (reflection(k,t[0]),t[1])
                right = lambda t: (t[0],reflection(l,t[1]))
                for first,second in ((left,right),(right,left)):
                    for h in branches(herald,first):
                        for end in branches(h,second):
                            result = address_test(end)
                            joint += result
                            if result["survivor_wall"]:
                                need(a != b and flag == 0 and k != l,
                                     "new joint survivor wall outside known sector")
                            if flag == 1 and a != b and sum(stock(end.g).values()):
                                joint["live_antisymmetric_balanced_matching_walls"] += (
                                    result["balanced_matching_wall"])
                                joint["antisymmetric_subset_without_matching"] += (
                                    result["subset_without_matching"])
    need(tally["states"] == 324 and joint["states"] == 1296, "product coverage")
    return tally,joint


def witness():
    s = initial(0)
    middle = next(branches(s,lambda x: reflection(1,x)))
    end = next(branches(middle,lambda x: reflection(0,x)))
    a,b = sides(end.g,1)
    need((a,b) == (frozenset((0,2)),frozenset((5,))), "named reachable witness")
    p = lift((2,1,0,3))
    need(p in end.gens and p[0]==2 and p[2]==0 and p[5]==5, "ancestry swap")
    histories = {u:(s.g.tags[u%2],middle.g.tags[u%4],end.g.tags[u]) for u in a|b}
    need(histories[0] == histories[2] == (1,1,1) and histories[5] == (2,2,1),
         "witness traces")
    # A root frame at EITHER seed endpoint is already fixed by this automorphism.
    # With the added ordered sibling bit, the word (seed tag, sheet1, sheet2)
    # names vertices uniquely, and an arbitrary address ordering can break ties.
    addr = {u:(s.g.tags[u%2],(u//2)%2,u//4) for u in range(8)}
    need(len(set(addr.values())) == 8 and {min(a,key=addr.get),max(a,key=addr.get)} == a,
         "extra sheet-bit address")
    # Uniform choice of a matching is covariant IN LAW; neither single
    # realization is fixed by p. Here there are exactly two equiprobable
    # survivor/matching choices (one bit), each yielding one diagonal click.
    matches = {tuple(zip(sorted(b),targets)) for targets in permutations(a,len(b))}
    images = {tuple((p[i],p[j]) for i,j in matching) for matching in matches}
    need(len(matches)==2 and images==matches and
         all(tuple((p[i],p[j]) for i,j in m) != m for m in matches), "invariant law")
    need(stock(end.g)[1] == 1 and sum((sum(histories[u]==h for u in a) -
         sum(histories[v]==h for v in b))**2 for h in set(histories.values())) == 5,
         "forbidding cross-history cancellation changes the observable")
    # Directly enumerate all injections on these tiny sides as an oracle for
    # the group-action classifier, including its successful cases.
    for s0 in (s,middle,end):
        for rail in set(s0.g.tags):
            big,small = sorted(sides(s0.g,rail),key=len,reverse=True)
            origins = tuple(small)
            direct = False
            for dest in permutations(big,len(small)):
                image = dict(zip(origins,dest))
                if all(image[p[i]] == p[image[i]] for p in s0.gens for i in origins):
                    direct = True
                    break
            need(direct == injection(small,big,s0.gens), "direct matching disagreement")
    # Append positive splits fixing rail 1. Repeated doubling does not
    # resolve this tie. All majority vertices stay in one genealogy orbit.
    for q in range(5):
        a,b = sides(end.g,1)
        need((len(a),len(b)) == (2 << q,1 << q) and orbits(a,end.gens)==[a],
             "amplified history wall")
        if q < 4:
            end = next(branches(end,lambda x: reflection(1,x)))

    # Anti-heralded state, different settings, live branch. This is
    # a MATCHING wall on a dark rail, not a survivor wall on that rail.
    paired = both(initial(0),initial(1))
    _,anti = branches(paired,lambda t: (t[1],t[0]))
    _,left = branches(anti,lambda t: (reflection(0,t[0]),t[1]))
    read = next(branches(left,lambda t: (t[0],reflection(1,t[1]))))
    a,b = sides(read.g,(0,1))
    need((a,b) == (frozenset((5,21)),frozenset((13,29))) and
         any(p[5]==21 and p[21]==5 and all(p[i]==i for i in b) for p in read.gens)
         and not injection(a,b,read.gens) and sum(stock(read.g).values())==12,
         "live antisymmetric matching control")
    # On another LIVE antisymmetric rail invariant survivor subsets exist,
    # yet no choice can be realized by a deterministic equivariant matching.
    left = next(branches(anti,lambda t: (reflection(0,t[0]),t[1])))
    read = next(branches(left,lambda t: (t[0],reflection(2,t[1]))))
    big,small = sorted(sides(read.g,(1,2)),key=len,reverse=True)
    need(big == {0,14,16,30} and small == {10,26} and
         {frozenset((0,16)),frozenset((14,30))} == set(orbits(big,read.gens)) and
         any(p[10] == 26 and all(p[i]==i for i in big) for p in read.gens) and
         not injection(small,big,read.gens) and stock(read.g)[1,2] == 4 and
         sum(stock(read.g).values())==36, "nonzero antisymmetric matching control")


def main():
    witness()
    single, verified = single_scan()
    preps, joint = product_scan()
    columns = ("mixed_unequal","survivor_wall","subset_without_matching","balanced_matching_wall")
    need(tuple(single[c] for c in columns) == (744,120,192,234) and
         tuple(preps[c] for c in columns) == (0,0,0,0) and
         tuple(joint[c] for c in columns) == (2496,96,480,1236) and
         joint["live_antisymmetric_balanced_matching_walls"] == 84 and
         joint["antisymmetric_subset_without_matching"] == 192, "classification drift")
    for name,tally in (("single through depth 3",single),("paired preps",preps),
                       ("native final joint branches, both orders",joint)):
        print(f"{name}: {dict(sorted(tally.items()))}")
    print(f"Exact independent fiber-lift agreement on {verified} split outputs through depth 2.")
    print("seed(0), positive fix 1, positive fix 0: rail 1 has 2 against 1;"
          " a history automorphism swaps the two possible diagonal click addresses."
          " Two uniform matchings agree in law; keeping path labels as separate detection"
          " sectors gives stock 5 instead of 1. Four further doublings retain the wall.")
    print("Live antisymmetric branch of stock 36, rail (1,2): 4 against 2."
          " Two invariant survivor subsets exist, but swapping only the minority"
          " twins rules out every equivariant injection. This is not a no-go"
          " for the abstract stock of four ordered pairs.")


if __name__ == "__main__":
    main()
