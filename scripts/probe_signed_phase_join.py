"""A retrospective signed-history join for the six raw F5 contact phases.

Replay: python3 -B -O -m scripts.probe_signed_phase_join

The gate, orbit, four skip histories and old window are existing inputs.
New inputs: divide the histories into two equal-net integer clouds, exchange
a signed zero-net pair between them, count ordered pairs only within each
cloud, and twirl by one common uniform phase. This is a proposed source
rule, NOT the evolution of two triples under the F5 gate. It was found by
factoring a known target. No target probabilities are read by its generator.
We test its other allowed joins rather than treating that fit as prediction.

The orientations give the aligned convention; complementing Bob gives the
anti-source. The event router is checked on the specified binary windows.
Its seed is positive and setting-independent; its matching is JOINT, even
though every individual signed leaf uses only a local terminal response.
Signed leaf/atom masses are not frequencies. No Born law, laboratory data,
machine proof, or change of public scientific status is claimed.
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product

from scripts.probe_affine_contact_fringe import Six, cycle, detector, need


Z = range(6)
PAIRS = tuple(product(Z, repeat=2))
SIGNS = (-1, 1)


def plus(x, y):
    return tuple(a+b for a, b in zip(x, y, strict=True))


def minus(x, y):
    return tuple(a-b for a, b in zip(x, y, strict=True))


def atom(t):
    return tuple(int(r == t % 6) for r in Z)


def scale(k, x):
    return tuple(k*n for n in x)


def contrast(x, f):
    return tuple(sum(x[t]*f[(t+i) % 6] for t in Z) for i in Z)


def split(e, m, z):
    return plus(e, z), minus(m, z)


def branches(clouds):
    """Address-distinct signed events: translate both leaves by the same r."""
    out = []
    for cloud in clouds:
        leaves = [(t, 1 if n > 0 else -1) for t, n in enumerate(cloud) for _ in range(abs(n))]
        for r, (p, s), (q, t) in product(Z, leaves, leaves):
            out.append(((p+r) % 6, (q+r) % 6, s*t))
    return out


def relative_num(clouds):
    return tuple(sum(x[t]*x[(t+d) % 6] for x in clouds for t in Z) for d in Z)


def relative_row(w, c):
    return tuple(sum(w[k]*c[(d+k) % 6] for k in Z) for d in Z)


def raw_cell(leaves, f, i, j):
    cell = Counter()
    for t, u, s in leaves:
        cell[f[(t+i) % 6], f[(u+j) % 6]] += s
    return cell


def check_table(leaves, f, g):
    n = sum(s for _, _, s in leaves)
    for i, j in PAIRS:
        cell = raw_cell(leaves, f, i, j)
        for a, b in product(SIGNS, repeat=2):
            need(F(cell[a,b], n) == (1+a*b*g[(j-i) % 6])/4, "window probability mismatch")
            need(cell[a,b] >= 0, "negative window event")


def native_area_control():
    # Competing primitive: assign a signed weight using only oriented area
    # of the two centered F5 triples. Take two coordinates on the constant
    # sum plane; divide by the one-beat area to cancel any common frame
    # rescaling. No interpretation of a residue as a real number is needed.
    # Every function of this invariant (even sign-changing) treats the two
    # collinear relative phases 0 and 3 alike, contrary to required w0-w3.
    def det(x,y):
        return (x[0]*y[1]-x[1]*y[0]) % 5
    for a,b in product(range(5),repeat=2):
        if a == b:
            continue
        orbit = cycle((b,a,b),Six)
        mean = (2*b+a)*pow(3,-1,5) % 5
        v = [tuple((x-mean)%5 for x in s[:2]) for s in orbit]
        for t in Z:
            need(v[(t+3)%6] == tuple(-x%5 for x in v[t]), "not native half-turn")
            unit = det(v[t],v[(t+1)%6])
            row = tuple(det(v[t],v[(t+d)%6])*pow(unit,-1,5)%5 for d in Z)
            need(row == (0,1,1,0,4,4), "native oriented-area classes")


def sharp_bound(f, c, g, num):
    # Cyclic averaging of any normalized (possibly asymmetric) atom table
    # produces relative weights w summing to one, with no increase of its
    # negative mass by triangle inequality. E[d] is its averaged correlation.
    # The circular second difference of the bare c is a signed atom pair.
    lap = lambda v, d: 2*v[d]-v[(d-1) % 6]-v[(d+1) % 6]
    need(tuple(lap(c,d) for d in Z) == scale(F(4,3), minus(atom(0),atom(3))), "phase inverse")
    diff = tuple(F(3,4)*lap(g,d) for d in Z)
    need(diff == tuple(F(n,8) for n in (6,3,-3,-6,-3,3)), "required antipode differences")
    # E[d]=sum_k w[k]*c[d+k], so the inverse gives w[-d]-w[3-d];
    # this target's inverse happens to be even.
    # These three odd differences, plus normalization, are also sufficient:
    # c is odd under a half-turn, so every even zero-sum change is invisible.
    w = tuple(F(n,8) for n in num)
    need(relative_row(w, c) == g, "attainability of inverse")
    for t in (0,1):
        null = minus(plus(atom(t),atom(t+3)),plus(atom(2),atom(5)))
        need(relative_row(null, c) == (0,)*6 and sum(null) == 0, "even nullspace")
    # Equality in the triangle bound sum |w| >= sum_positive diff = 3/2
    # requires only sign-aligned splits. At net 8 the 2 negative tickets
    # can be placed in the three opposite pairs in all six compositions.
    lifts = set()
    for d0, d1, d5 in product(range(3), repeat=3):
        if d0+d1+d5 == 2:
            v = (6-d0,3-d1,-d5,-d0,-d1,3-d5)
            need(sum(v) == 8 and sum(map(abs,v)) == 12, "nonoptimal lift")
            need(relative_row(scale(F(1,8),v), c) == g, "integer lift")
            lifts.add(v)
    need(len(lifts) == 6 and num in lifts, "optimal integer kernels")
    # An operationally unbiased joint cell of mass 3/8 forces a multiple
    # of 8 as net count for equal signed integer tickets. Without microscopic
    # cyclic symmetry, net 8 already suffices. A sparse certificate found by
    # integer allocation (not a proposed native generator) is checked afresh.
    small = [
        (0,0,2), (0,4,-1), (1,1,1), (2,2,1), (2,3,1), (3,2,1),
        (4,0,-1), (4,4,1), (4,5,1), (5,4,1), (5,5,1),
    ]
    need(sum(s for _,_,s in small) == 8 and sum(abs(s) for _,_,s in small) == 12, "small lift")
    check_table(small,f,g)
    # L=(3/2)*mean_i [E(i,i-1)+E(i,i+1)] is exactly +/-1 on each
    # deterministic raw phase pair. This is a bound for THESE responses,
    # not for arbitrary local deterministic functions.
    scores = {F(3,12)*sum(f[(t+i) % 6]*(f[(u+i-1) % 6]+f[(u+i+1) % 6])
                           for i in Z) for t,u in PAIRS}
    need(scores == {-1,1} and F(3,2)*(g[1]+g[-1]) == F(3,2), "dual witness")
    # With max error eps, 3/2-3 eps <= L <= 1+2 N. Equality throughout
    # 0<=N<=1/4 by interpolation: raw delta0 has no negative support, and
    # these affine rows/numerators have fixed signs throughout the segment.
    for t in (F(0),F(1,3),F(1)):
        mix = plus(scale(1-t,atom(0)),scale(t,w))
        n = -sum(min(x,0) for x in mix)
        eps = max(abs(a-b) for a,b in zip(relative_row(mix,c),g))
        need(n == t/4 and eps == (1-t)/6 and 3*eps+2*n == F(1,2), "sharp noise bound")
    return len(lifts)


def sector_controls(e, m, f, c, g):
    # Center the observed window at phase zero for the classification only.
    fc = tuple(f[(i+1) % 6] for i in Z)
    h = plus(e,m)
    need(contrast(h,fc) == (4,2,-2,-4,-2,2), "centered four-history row")
    controls = {}
    for u,v in PAIRS:
        clouds = split(e,m,minus(atom(u),atom(v)))
        need(plus(*clouds) == h and tuple(map(sum,clouds)) == (2,2), "different solo stock")
        row = relative_row(scale(F(1,8),relative_num(clouds)),c)
        controls[u,v] = row
    hits = {k for k,r in controls.items() if r == g}
    need(hits == {(0,3),(2,1),(4,5)}, "oriented single-dipole hits")
    valid = {k for k,r in controls.items() if k[0]!=k[1] and max(map(abs,r))<=1}
    need(len(valid) == 13, "window-positive oriented dipoles")
    symmetric = {(u,v) for u,v in PAIRS if u != v and -u % 6 == u and -v % 6 == v}
    need(symmetric == {(0,3),(3,0)} and symmetric & valid == {(0,3)}, "single-dipole selection")
    # For integer strength k of the reflection-symmetric (0,3) dipole, E0
    # is quadratic by the autocorrelation formula. Three points identify it.
    for k in (-1,0,1):
        clouds = split(e,m,scale(k,minus(atom(0),atom(3))))
        row = relative_row(scale(F(1,8),relative_num(clouds)),c)
        need(row[0] == F(3*k*k-2*k+2,3), "symmetric dipole quadratic")
    # E0<=1 iff -1/3<=k<=1; only k=0,1 survive among the integers.
    # Another single-dipole hit has indistinguishable windows but different
    # native phase atoms. Its same-mark middle-wire test is an ordinary
    # nonnegative binary table, separately, in both signed proposals.
    other_num = relative_num(split(e,m,minus(atom(2),atom(1))))
    need(other_num == (8,1,-2,2,-2,1) and -sum(min(0,n) for n in other_num)==4,
         "alternate window-blind refinement")
    for num,joint in ((relative_num(split(e,m,minus(atom(0),atom(3)))), F(1,8)),
                      (other_num,F(1,6))):
        p = F(num[0],48)
        need(p == joint and min(p,F(1,6)-p,F(2,3)+p) >= 0, "aligned singleton discriminator")
    # Wider class: ANY integer X,Y with X+Y=h and each of net 2. Since the
    # six f columns are +/-1 and opposite under a half-turn, their contrasts
    # for X are twice (a,b,c,-a,-b,-c). Y's follow by subtraction. The
    # all-dial E_d is their summed autocorrelation divided by 6*8.
    # Cauchy gives |E_d|<=E0, making E0<=1 necessary AND sufficient for
    # positivity (the common twirl makes both margins unbiased).
    #
    # 6 E0 = a²+(2-a)² + b²+(1-b)² + c²+(-1-c)². The pair minima are
    # 2,1,1; a outside 0..2 gives >=10 already, b or c outside the bracket
    # gives >=5 in that pair and >=3 elsewhere. These finite bounds apply
    # to all integer clouds, not just a finite coefficient search.
    classes = defaultdict(list)
    for a,b,k in product(range(3), (0,1), (-1,0)):
        raw = (a,b,k,-a,-b,-k)
        other = minus((2,1,-1,-2,-1,1),raw)
        row = scale(F(1,12),relative_num((raw,other)))
        need(row[0] == F(a*a+(2-a)**2+b*b+(1-b)**2+k*k+(-1-k)**2,6), "energy bound")
        need(max(map(abs,row)) <= 1 and (row == g) == ((0,)*6 in (raw,other)), "dark-channel criterion")
        # Construct X for each allowed signature (not only a necessary list).
        # Difference of consecutive +++ windows recovers X[n]-X[n+3].
        oriented = tuple(raw[(1-n) % 6]-raw[(2-n) % 6] for n in range(3))
        x = (*oriented,0,0,0)
        delta = 2-sum(x)
        need(delta % 2 == 0, "cannot supply net two")
        x = plus(x,scale(delta//2,plus(atom(0),atom(3))))
        clouds = (x,minus(h,x))
        need(contrast(x,fc) == scale(2,raw) and tuple(map(sum,clouds)) == (2,2), "source signature")
        need(relative_row(scale(F(1,8),relative_num(clouds)),c) == row, "unattained class")
        classes[row[:2]].append((a,b,k))
    need(set(classes) == {(1,F(1,2)),(1,F(1,3)),(1,F(-1,6)),
                          (F(2,3),F(1,3)),(F(2,3),F(1,6))}, "cloud classes")
    z = minus(plus(atom(0),atom(3)),plus(atom(2),atom(4)))
    alt = relative_row(scale(F(1,8),relative_num(split(e,m,z))),c)
    need(alt[:2] == (1,F(-1,6)), "symmetric wider perfect countercontrol")
    return classes


def match(leaves, labels):
    """Pair unlike signs within each bin, returning negative involution edges."""
    buckets = defaultdict(lambda: {1: [], -1: []})
    for i,(leaf,label) in enumerate(zip(leaves,labels,strict=True)):
        buckets[label][leaf[2]].append(i)
    edges = {}
    for bucket in buckets.values():
        need(len(bucket[1]) >= len(bucket[-1]), "negative bin: no positive event routing")
        for p,n in zip(bucket[1],bucket[-1]):
            edges[p],edges[n] = n,p
    return edges


def event_router(leaves, f, g):
    # Baseline matching only sees the left raw phase t, so every unmatched
    # baseline leaf is an emission seed prior to any setting. Repeated
    # cancellation/uncancellation preserves Alice's bit and ends at a positive
    # leaf unmatched by the OUTCOME-bin matching. No seed is discarded.
    baseline = match(leaves,[t for t,_,_ in leaves])
    seeds = [i for i in range(len(leaves)) if i not in baseline]
    need(len(seeds) == 48 and all(leaves[i][2] == 1 for i in seeds), "incorrect seeds")
    runs = {}
    for i,j in PAIRS:
        labels = [(f[(t+i) % 6],f[(u+j) % 6]) for t,u,_ in leaves]
        joint = match(leaves,labels)
        outputs = {}
        for seed in seeds:
            end = seed
            visited = set()
            while end in joint:
                need(end not in visited, "cycle reached from a seed")
                visited.add(end)
                end = baseline[joint[end]]
            need(leaves[end][2] == 1 and labels[end][0] == labels[seed][0], "rewrote first bit")
            outputs[seed] = end
        need(set(outputs.values()) == set(range(len(leaves)))-joint.keys(), "lost or duplicated event")
        runs[i,j] = {seed:labels[end] for seed,end in outputs.items()}
        counts = Counter(runs[i,j].values())
        need(counts == raw_cell(leaves,f,i,j), "route not the signed window table")
    aflip = sum(runs[i,j][s][0] != runs[i,0][s][0] for i,j in PAIRS for s in seeds)
    bwit = next(((s,i,j,runs[0,j][s][1],runs[i,j][s][1]) for i,j in PAIRS for s in seeds
                 if runs[i,j][s][1] != runs[0,j][s][1]), None)
    chsh = g[1]+g[0]+g[-1]-g[-2]
    need(aflip == 0 and bwit is not None and chsh == F(5,2), "locality boundary lost")
    return len(seeds), bwit


def run():
    orbit = cycle((0,1,0),Six)
    f = tuple(2*int(detector(s,0))-1 for s in orbit)
    need(f == (1,1,1,-1,-1,-1), "stale raw F5 contact")
    # Shift the origin of the four skip histories by minus one so their
    # doubled midpoint is zero. This relabels source phases, not outcomes.
    groups = [Counter(),Counter()]
    for i,j in product(range(2),repeat=2):
        groups[(i+j)%2][(i+j-1)%6] += 1
    e,m = (tuple(group[t] for t in Z) for group in groups)
    clouds = split(e,m,minus(atom(0),atom(3)))
    num = relative_num(clouds)
    leaves = branches(clouds)
    c = scale(F(1,6),relative_num((f,)))
    g = tuple(F(sum(f[(t+d+1)%6]*n for t,n in enumerate(plus(e,m))),4) for d in Z)
    need(num == (6,2,-1,0,-1,2) and sum(num) == 8, "native branch count")
    need(len(leaves)==120 and Counter(s for _,_,s in leaves)=={1:84,-1:36}, "history multiplicities")
    atoms = Counter()
    for t,u,s in leaves:
        atoms[t,u] += s
    need(all(atoms[t,u] == num[(u-t)%6] for t,u in PAIRS), "twirled phase atoms")
    need(tuple(int(s[1] == 0) for s in orbit) == atom(5), "native middle-wire singleton")
    # Set the old middle-wire reader to shifts +5 (left), +3 (right);
    # their simultaneous equality event selects exactly phase pair (0,2).
    atom_event = sum(s for t,u,s in leaves if orbit[(t+5)%6][1] == orbit[(u+3)%6][1] == 0)
    need(atom_event == atoms[0,2] == -1, "negative native singleton joint")
    check_table(leaves,f,g)
    native_area_control()
    count = sharp_bound(f,c,g,num)
    classes = sector_controls(e,m,f,c,g)
    n, witness = event_router(leaves,f,g)
    print("signed same-cloud join; source split and pairing are supplied, not F5 laws")
    print(f"relative signed counts {num}/8; window E={tuple(map(str,g))}; CHSH=5/2")
    print("minimum negative atom mass 1/4; raw positive uniform error at least 1/6 (sharp)")
    print(f"{count} optimal net-eight relative integer lifts; untwirled net eight is feasible")
    print("13/30 oriented dipoles window-positive; 3 match; only z=delta0-delta3")
    print("in the nonzero reflection-symmetric single-dipole class survives")
    print("all integer equal-net two-cloud joins: five positive (E0,E1) rows:",
          sorted(tuple(map(str,p)) for p in classes))
    print(f"{n} positive seeds, all 36 windows; no Alice flips; Bob witness (seed,i,j,B0j,Bij)={witness}")
    print("raw middle-wire joint at (phase 0,phase 2) = -1/48: signed source is not a probability")
    print("area-only join excluded; aligned raw-singleton coincidence: 1/8 vs alternate 1/6")


if __name__ == "__main__":
    run()
