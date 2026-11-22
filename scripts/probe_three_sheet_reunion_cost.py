"""Sharp local reunion cost of an ordinary connected three-sheet cover of folded five.

Every base port lifts bijectively; reverse edge transport is its inverse.
No deck transitivity, global sheet labels or commutative voltages assumed.
The five recovered direction matchings lift to involutions. If ALL squares
close on all sheets these involutions commute. Their orbit has at most
2^5=32 vertices; it is the whole lift if connected. Since the base has
16 vertices, a connected flat cover can have only one or two sheets.

Each base square lies in three embedded ordinary cubes. Within any such
cube, five trivial face holonomies force the sixth for ANY permutation
group: replace ab by ccab, cacb, cabc, cbac, cbca, ccba, ba using five
other square swaps and two immediate backtracks. For a given square,
the five other faces of those three cubes are disjoint as FACE SETS.
Thus one broken square forces at least three others. A nonidentity
permutation of three sheets moves at least two; at least 8 of 120
face/sheet tests fail. Each yields eight oriented nonbacktracking two-hop
tests (4 starts, 2 orders, conjugate or inverse holonomy): 64/960.
These are uniform incidence counts, not a per-origin detection probability.

Sharp ordinary example: use tau=(01) on every edge (flat but an odd base
loop acts by tau), then COMPOSE one oriented edge with sigma=(12) and
use its inverse on the reverse. Four broken squares exchange two sheets.
An odd loop avoiding the seam and a seam square generate transitive S3.
Merely replacing tau by sigma instead produces a three-cycle defect.
If a connected REGULAR three-cover is required, its monodromy is regular
of order three: a deck transformation fixing a lifted vertex fixes all
reachable lifts; root holonomy commutes with the three deck permutations,
so lies in their centralizer C3, and transitivity gives equality.
Hence a broken face moves all three and the sharp cost becomes 12/120.

Additional equality check: of all four-face supports, only edge stars and
parallel four-packs avoid a cube with a single defect. If only the ab faces
are broken, the other three lifted matchings c,d,e commute with everything;
w=abcde preserves each fiber and w^2=(ab)^2. Hence every square permutation
there is a square in S3, never a transposition. The 8-cost optimizer's
support must be an edge star (no claim that its entire connection is unique).

The premise is THREE states over EVERY base vertex in one connected ordinary
cover, with both routes compared on the physical sheet. Three disconnected
copies and observers seeing only the base evade the bound for distinct
reasons. This is not a generation count, gauge dynamics, or a measurement.
"""

import json
from collections import Counter, deque
from itertools import combinations, pairwise, permutations

from scripts.probe_anonymous_folded_carrier import forced_completion, square_directions


def need(test, why):
    if not test:
        raise AssertionError(why)


def edge(x,y):
    return min(x,y),max(x,y)


def compose(p,q):
    return tuple(p[i] for i in q)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def directions(base):
    _,groups = square_directions(base)
    ops = []
    for group in groups:
        m = {i:j for x,y in group for i,j in ((x,y),(y,x))}
        ops.append(tuple(m[v] for v in range(len(base))))
    return sorted(ops,key=lambda f:f[0])


def faces(base):
    polys = {}
    for a,c in combinations(range(len(base)),2):
        if c not in base[a]:
            b,d = sorted(base[a]&base[c])
            path = a,b,c,d
            polys[frozenset(path)] = path
    return sorted(polys, key=sorted), polys


def induced_cube(base,vs):
    n = {v:base[v]&vs for v in vs}
    if any(len(row)!=3 for row in n.values()):
        return False
    r = min(vs)
    first = n[r]
    second = []
    for a,b in combinations(first,2):
        common = (n[a]&n[b])-{r}
        if len(common)!=1:
            return False
        second.extend(common)
    far = vs-{r}-first-set(second)
    return len(far)==1 and n[next(iter(far))] == set(second) and len(set(second))==3


def geometry(base,ops,fs):
    n = len(base)
    generated = {}
    for axes in combinations(range(5),3):
        for root in range(n):
            vs = {root}
            for j in axes:
                vs |= {ops[j][x] for x in vs}
            need(len(vs)==8, "quotient identified two vertices inside one cube")
            generated[frozenset(vs)] = axes
    # Independent enumeration: identify Q3 via adjacency, NOT via port labels.
    found = {frozenset(s) for s in combinations(range(n),8) if induced_cube(base,frozenset(s))}
    need(found == set(generated) and len(found)==20, "embedded cube census")
    memberships = [{i for i, f in enumerate(fs) if f <= vs} for vs in generated]
    need(all(len(s)==6 for s in memberships), "cube does not have six base squares")
    for j in range(len(fs)):
        triplet = [s-{j} for s in memberships if j in s]
        need(len(triplet)==3 and len(set.union(*triplet))==15, "other face sets overlap")
    swaps = 0
    for vs,axes in generated.items():
        for a,b in combinations(axes,2):
            c, = set(axes)-{a,b}
            for r in vs:
                words = [(c,c,a,b), (c,a,c,b), (c,a,b,c), (c,b,a,c), (c,b,c,a), (c,c,b,a)]
                used = set()
                for before,after in pairwise(words):
                    i = next(i for i in range(4) if before[i]!=after[i])
                    x = r
                    for j in before[:i]:
                        x=ops[j][x]
                    j,k = before[i:i+2]
                    need(after == before[:i]+(k,j)+before[i+2:], "not an elementary square swap")
                    used.add(frozenset((x,ops[j][x],ops[k][x],ops[k][ops[j][x]])))
                target = frozenset((r,ops[a][r],ops[b][r],ops[b][ops[a][r]]))
                need(used == {f for f in fs if f <= vs and f!=target}, "cube cancellation certificate")
                swaps += 1
    return memberships,swaps


def four_supports(base,ops,fs,memberships):
    masks = [sum(1<<i for i in s) for s in memberships]
    stars = {sum(1<<i for i,f in enumerate(fs) if u in f and v in f)
             for u,neighbors in enumerate(base) for v in neighbors if u<v}
    parallel = {sum(1<<i for i,f in enumerate(fs) if all(ops[j][v] in f and ops[k][v] in f for v in f))
                for j,k in combinations(range(5),2)}
    allowed = set()
    checked = 0
    for ids in combinations(range(len(fs)),4):
        mask = sum(1<<i for i in ids)
        checked += 1
        if all((mask&m).bit_count()!=1 for m in masks):
            allowed.add(mask)
    need(len(stars)==40 and len(parallel)==10 and not stars&parallel and
         allowed==stars|parallel and checked==91390, "four-face geometric support census")
    return checked,len(stars),len(parallel)


ID = (0,1,2)
TAU = (1,0,2)
SIGMA = (0,2,1)
CYCLE = (1,2,0)


def connection(base,ops,kind,seam):
    trans = {}
    for u,row in enumerate(base):
        for v in row:
            if u>=v:
                continue
            e = (u,v)
            if kind == "parallel_cyclic":
                p = TAU if v==ops[0][u] else SIGMA if v==ops[1][u] else ID
            elif kind in ("flat_odd","sharp","literal_replace"):
                p = TAU
                if e==seam and kind=="sharp":
                    p = compose(SIGMA,TAU)
                if e==seam and kind=="literal_replace":
                    p = SIGMA
            else:
                p = CYCLE if kind=="cyclic_seam" and e==seam else ID
            trans[e],trans[v,u] = p,inverse(p)
    return trans


def transport(trans,path):
    p = ID
    for x,y in pairwise(path):
        p = compose(trans[x,y],p)
    return p


def monodromy(base,trans):
    # Tree transports give labels at a common root for ALL fundamental loops.
    tree,queue = {0:ID},[0]
    for u in queue:
        for v in base[u]:
            if v not in tree:
                tree[v] = compose(trans[u,v],tree[u])
                queue.append(v)
    gens = {compose(inverse(tree[v]),compose(p,tree[u])) for (u,v),p in trans.items()}
    group, seen = [ID],{ID}
    for p in group:
        for q in gens:
            h=compose(q,p)
            if h not in seen:
                seen.add(h)
                group.append(h)
    return seen


def lifted_analysis(base,ops,polys,trans):
    lifted = [tuple(3*op[v]+trans[v,op[v]][s] for v in range(16) for s in range(3)) for op in ops]
    need(all(compose(f,f)==tuple(range(48)) for f in lifted) and
         all({f[x]//3 for f in lifted}==base[x//3] for x in range(48)), "not an ordinary port-bijective cover")
    unseen, sizes = set(range(48)),[]
    while unseen:
        q=[unseen.pop()]
        for x in q:
            for f in lifted:
                if f[x] in unseen:
                    unseen.remove(f[x])
                    q.append(f[x])
        sizes.append(len(q))
    defects = {}
    for face,p in polys.items():
        h=transport(trans,p+p[:1])
        defects[face]=sum(x!=y for x,y in enumerate(h))
    paths = Counter()
    for x in range(48):
        for i,j in permutations(range(5),2):
            a,b = lifted[j][lifted[i][x]],lifted[i][lifted[j][x]]
            need(a//3==b//3,"projection changed base reunion")
            face=frozenset((x//3,lifted[i][x]//3,lifted[j][x]//3,a//3))
            paths[face] += a!=b
    need(all(paths[f]==8*k for f,k in defects.items()), "direct path census/holonomy mismatch")
    mono=monodromy(base,trans)
    sizes.sort()
    need(sorted({len({p[s] for p in mono})*16 for s in range(3)})==sorted(set(sizes)), "monodromy orbits")
    return {"component_sizes":sizes,"monodromy_order":len(mono),
            "squares_by_number_of_moved_sheets":dict(sorted(Counter(defects.values()).items())),
            "failed_face_sheet_tests":sum(defects.values()),"failed_directed_two_hop_tests":sum(paths.values()),
            "base_projected_two_hop_failures":0},defects


def odd_away_from(base,seam):
    root = seam[0]
    q = deque([(root,0,(root,))])
    seen = {(root,0)}
    while q:
        v,parity,path = q.popleft()
        for w in base[v]:
            key=w,parity^1
            if edge(v,w)==seam or key in seen:
                continue
            seen.add(key)
            if key==(root,1):
                return (*path,w)
            q.append((w,parity^1,(*path,w)))
    raise AssertionError("missing odd loop away from seam")


def probe():
    base=forced_completion()
    ops=directions(base)
    fs,polys=faces(base)
    memberships,certificates=geometry(base,ops,fs)
    census,stars,parallel=four_supports(base,ops,fs,memberships)
    need({sum(i!=j for i,j in enumerate(compose(p,p))) for p in permutations(range(3))} == {0,3},
         "square of a within-fiber permutation cannot be a transposition")
    seam=(0,min(base[0]))
    outputs={}
    for kind,components,mono,failed in (
        ("flat_copies",[16,16,16],1,0), ("flat_odd",[16,32],2,0), ("sharp",[48],6,8),
        ("cyclic_seam",[48],3,12), ("literal_replace",[48],6,12), ("parallel_cyclic",[48],3,12),
    ):
        trans=connection(base,ops,kind,seam)
        out,defects=lifted_analysis(base,ops,polys,trans)
        need((out["component_sizes"],out["monodromy_order"],out["failed_face_sheet_tests"]) ==
             (components,mono,failed),"unexpected cover result")
        outputs[kind]=out
        if kind=="sharp":
            odd=transport(trans,odd_away_from(base,seam))
            around=next(p for f,p in polys.items() if set(seam)<=f)
            ix=around.index(seam[0])
            around=around[ix:]+around[:ix]
            second=transport(trans,around+around[:1])
            need(odd==TAU and sum(x!=y for x,y in enumerate(second))==2 and second!=odd,
                 "two explicit generators did not give transitive monodromy")
            # Independent per-vertex change of sheet names; declared failures
            # are physical reunion tests, not artifacts of chosen fiber labels.
            ps=tuple(permutations(range(3)))
            chart=[ps[(7*v+v//2+2)%6] for v in range(16)]
            changed={(u,v):compose(chart[v],compose(p,inverse(chart[u]))) for (u,v),p in trans.items()}
            need(lifted_analysis(base,ops,polys,changed)==(out,defects),"fiber relabel changed reunion")
    return {"scope":"ordinary connected degree-three graph cover; full sheet-sensitive square reunion",
            "square_count":len(fs),"induced_cube_count":len(memberships),"five_face_path_certificates":certificates,
            "four_face_support_census":{"checked":census,"edge_stars":stars,"parallel_packs":parallel},
            "number_of_face_sheet_tests":120,"number_of_directed_nonbacktracking_tests":960,
            "sharp_ordinary_failure_fraction":"1/15","sharp_regular_cyclic_failure_fraction":"1/10",
            "examples":outputs}


if __name__ == "__main__":
    print(json.dumps(probe(),separators=(",",":")))
