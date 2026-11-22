"""What repeat and dark-branch tests can select on a neutral triangle.

Conditional all-lattice argument; the executable checks below are finite.
Input: L={(a,b,c) in Z^3: a+b+c=0}. Each setting supplies one transposition P
and two nonzero additive endomorphisms A,B of L. This assumes descent from raw
packets, additive pooling, a fixed zero, and a common linear lift when currents
are known only up to sign. None follows from a finite frequency table.

1. Assume AB=BA=0, neither repeat A²,B² is zero, and each raw kernel is
   invariant under P. Over Q both maps have rank one: the nonzero image of
   each lies in the other's proper kernel. Those lines are distinct or both
   squares vanish. P has only its two eigenlines as invariant lines here.
   Thus after exchanging outputs, A kills the minus line and maps into the
   plus line; B does the reverse. For P fixing the first label take lattice
   coordinates (a,b), c=-a-b. Then (I+P)v=a(2,-1), (I-P)v=(a+2b)(0,1).
   Both functionals hit Z and both output vectors are primitive. Consequently
   A=s(I+P), B=t(I-P), with nonzero *integers* s,t. The same holds by
   relabeling at any port. Only primitive image on each line would give unit
   scale by this argument alone. Faithful zero detection on both cross words
   for spanning inputs suffices for raw AB=BA=0; repetition frequencies with
   blind states need not. Raw equality A²=A is not the repeat assumption.

2. Jointly constrain the contact and its *unknown* stock. Assume a nonzero
   even nonnegative W on all L, W(0)=0, and W(Av)+W(Bv)=g_P W(v) for every
   v and each of the three settings, with g_P>0 independent of v. Evenness
   is appropriate to an unoriented packet; raw signed measurements need not
   be even. Each setting's identity implies W(Pv)=W(v) by step 1 and
   evenness. Thus W is label-symmetric. Pick just one setting; conjugation
   gives its equation with the SAME |s|,|t|,g at each port for this argument.
   The actual contacts need not have equal scales or gains across settings.

   Let E(n)=W(0,n,-n), M(n)=W(2n,-n,-n), F(n)=E(t n), H(n)=M(s n).
   For v=(a,b,-a-b), g W(v)=H(a)+F(a+2b). Comparing the splits of an edge
   gives H(n)=F(2n)-F(n). Comparing the first and second ports then gives
       F(2a+b)-F(a+2b)=H(a)-H(b).
   Take forward differences in both a and b. D=delta_1 delta_2 F obeys
   D(2a+b)=D(a+2b). Every integer pair x,y with x+y=0 mod 3 is of that
   form, so D has period 3. The two-sided recurrence delta_3 delta_1
   delta_2 F=0 has characteristic polynomial (X-1)^3(X+1)(X²+X+1).
   Its six independent solutions span the quadratics, the alternating
   sequence and the two zero-mean three-periodic sequences. Evenness and
   F(0)=0 therefore give F(n)=u n²+h [2 does not divide n]+d [3 does not
   divide n]. H(n)=3u n²-h [2 does not divide n]. The alternating residue
   cancels in H(a)+F(a+2b). With Q=sum(v_i²)/2 and T the indicator that
   the three currents are not all congruent modulo 3, W=C Q+K T, where
   g C=4u and g K=d. This is an output of the equations, not an input.

   Compare F(n)=C t² n²+K [3 does not divide t n] and H(n)=3C s² n²
   to the preceding expressions. Hence u=C t²=C s², h=0 and
   d=K [3 does not divide t]. If any median is lit then C>0, |s|=|t|,
   g=4s² and K=0. Repeat for each actual setting. Each common multiplier
   is invisible to normalized quadratic readings; an independently measured
   absolute total gain of four selects unit scale AT THAT SETTING. Otherwise
   C=0 gives W=K T (K>0), g=1, t coprime to 3, and s is unconstrained:
   the entire median output is blind. These cases also satisfy the equations.

3. Optional signed-stock refinement (NOT a graph orientation rule). Without
   evenness, split W into its even and odd parts. The nonnegative even part
   obeys step 2 and is nonzero wherever either sign is lit. In the bright
   case the odd part V is forced to vanish as follows. Each setting writes V
   as H(k)+F(l) with odd H,F, k=a, l=a+2b at the first port (absorb gain in
   H,F). The other port writes V as a sum of functions of b and 2a+b.
   Hence the product of differences along (a,b) shifts (1,0), (-1,2)
   annihilates V. In k,l this gives delta_1 delta_-1 H(k) =
   -delta_1 delta_3 F(l) for all k,l of the same parity. At k and -k the
   left sides must agree, but are opposites by oddness and the symmetric
   shifts. Both sides vanish. Thus H has constant first difference, and
   F has constant third-step increment, giving at most linear growth.
   But on each pure output line, iterating
   V(2s v)=4s² V(v) or V(2t v)=4t² V(v) excludes linear growth unless V=0.
   The sum law then kills V everywhere. In the dark case nonnegativity of W
   makes all medians dark since the even part vanishes there. The first two
   settings then write W as functions solely of l=a+2b and 2a+b respectively.
   These arguments range over all pairs whose sum is divisible by 3; hence W
   depends only on r=(a-b) mod 3. The minus output acts by r -> -t r for
   every port. Unequal nonnegative stocks on residues 1 and 2 are possible
   precisely when every signed minus multiplier t equals -1 modulo 3.

No statement that physical contacts are additive, all currents preparable,
stock actually obeys an all-scale law, or signs jointly align when packets
are fused. This selects no unique graph wiring or coincidence/readout rule.
Run: python3 -B -O -m scripts.probe_repeatable_triangle_contact
"""

from fractions import Fraction
from itertools import product

from scripts import probe_bipartite_triangle_origin as graphs


def need(condition, why):
    if not condition:
        raise AssertionError(why)


# Row-major integer matrices act on (a,b); the third current is -a-b.
I, O = (1, 0, 0, 1), (0, 0, 0, 0)
EXCHANGES = ((1, 0, -1, -1), (-1, -1, 0, 1), (0, 1, 1, 0))


def act(m, v):
    return m[0]*v[0]+m[1]*v[1], m[2]*v[0]+m[3]*v[1]


def mul(m, n):
    x, y = act(m, n[::2]), act(m, n[1::2])
    return x[0], y[0], x[1], y[1]


def times(k, m):
    return tuple(k*x for x in m)


def split_matrices(p):
    return tuple(tuple(x+k*y for x,y in zip(I,p)) for k in (1,-1))


def census(bound):
    census_rows = []
    # Rank-two candidates cannot annihilate a nonzero opposite image. Start
    # with all nonzero singular matrices in the box, not a projector ansatz.
    matrices = [m for m in product(range(-bound,bound+1), repeat=4)
                if m != O and m[0]*m[3] == m[1]*m[2]]
    for p in EXCHANGES:
        allowed = []
        for m in matrices:
            row = m[:2] if any(m[:2]) else m[2:]
            kernel = -row[1], row[0]
            if act(m, act(p, kernel)) == (0,0) and mul(m,m) != O:
                allowed.append(m)
        pairs = {(a,b) for a,b in product(allowed, repeat=2)
                 if mul(a,b) == mul(b,a) == O}
        plus, minus = split_matrices(p)
        def candidates(m):
            return [times(k,m) for k in range(-bound,bound+1)
                    if k and max(map(abs,times(k,m))) <= bound]
        forward = set(product(candidates(plus), candidates(minus)))
        need(pairs == forward | {(b,a) for a,b in forward}, "raw census")
        census_rows.append(len(pairs))
    # Remove non-nilpotent repeats: both maps can have the SAME invariant
    # kernel/range. Remove P-invariant darkness: coordinate projections work.
    nil = (0,0,1,0)
    need(mul(nil,nil) == O and act(nil,act(EXCHANGES[0],(0,1))) == (0,0),
         "coincident dark lines")
    a,b = (1,0,0,0),(0,0,0,1)
    need(mul(a,b) == mul(b,a) == O and mul(a,a) == a and mul(b,b) == b
         and act(b,act(EXCHANGES[0],(1,0))) != (0,0), "external basis")
    return census_rows


def adjoin_row(pivots, row):
    for j in range(len(row)):
        x = row[j]
        if not x:
            continue
        if j not in pivots:
            pivots[j] = [Fraction(y,x) for y in row]
            return
        row = [u-x*y for u,y in zip(row,pivots[j])]


def ridge_nullity(n):
    """Independent exact elimination on the even values F(1)..F(n)."""
    pivots = {}
    modes = [[fn(k) for k in range(1,n+1)] for fn in
             (lambda k:k*k, lambda k:k%2, lambda k:int(k%3 != 0))]
    for a,b in product(range(-n,n+1), repeat=2):
        args = 2*a+b, a+2*b, 2*a, a, 2*b, b
        if max(map(abs,args)) > n:
            continue
        row = [0]*n
        for k,sign in zip(args, (1,-1,-1,1,1,-1)):
            if k:
                row[abs(k)-1] += sign
        need(all(sum(x*y for x,y in zip(row,mode)) == 0 for mode in modes),
             "ridge solution")
        adjoin_row(pivots,row)
    return n-len(pivots)


def odd_ridge_check(n, s, t):
    """Free odd H,F, no growth ansatz. Fit mixed differences then pure gains."""
    pivots = {}
    def equation(terms):
        row = [0]*(2*n)
        for offset,k,coef in terms:
            if k:
                row[offset+abs(k)-1] += coef*(1 if k>0 else -1)
        adjoin_row(pivots,row)
    for k in range(-n+1,n):
        for l in range(-n,n-3):
            if (k-l)%2 == 0:
                equation(((0,k,2),(0,k+1,-1),(0,k-1,-1),
                          (n,l+4,1),(n,l+1,-1),(n,l+3,-1),(n,l,1)))
    need(2*n-len(pivots) == 3, "free odd ridge terms before dilation")
    for offset,mult in ((0,s),(n,t)):
        # On pure rays the nonzero coordinate is even.
        for k in range(2,n+1,2):
            if abs(2*mult*k) <= n:
                equation(((offset,2*mult*k,1),(offset,k,-4*mult*mult)))
    need(2*n == len(pivots), "odd ridge terms killed by pure repeats")


def q(v):
    a,b = v
    return a*a+a*b+b*b


def dark_stock(v):
    return int((v[0]-v[1]) % 3 != 0)


def stock_controls():
    bounded = list(product(range(-6,7), repeat=2))
    for p in EXCHANGES:
        plus,minus = split_matrices(p)
        for s,t in ((1,1),(-2,2),(3,-3),(2,1),(1,-2),(1,3)):
            a,b = times(s,plus),times(t,minus)
            for v in bounded:
                xs = act(a,v),act(b,v)
                if abs(s) == abs(t):
                    need(sum(map(q,xs)) == 4*s*s*q(v), "quadratic total")
                need(sum(map(dark_stock,xs)) == (t%3 != 0)*dark_stock(v),
                     "blind stock ignores median and scale")
            if abs(s) != abs(t):
                gains = {Fraction(q(act(a,v))+q(act(b,v)),q(v))
                         for v in bounded if v != (0,0)}
                need({4*s*s,4*t*t} <= gains, "unequal Q gains on eigenlines")
    need(ridge_nullity(18) == 3, "bounded free-value ridge rank")
    for s,t in ((1,1),(-1,1),(2,-2),(-2,-2)):
        odd_ridge_check(24,s,t)


def blind_repeat():
    # Perturb the range of each raw rank-one map by 101 times the other
    # eigenvector. Raw kernels are exactly the old invariant lines, but now
    # neither cross word vanishes. A finite-residue detector cannot tell.
    modulus = 101
    a = (2,0,modulus-1,0)
    b = (2*modulus,4*modulus,1-modulus,2*(1-modulus))
    plus,minus = split_matrices(EXCHANGES[0])
    need(mul(a,b) != O and mul(b,a) != O, "raw cross leakage")
    def w(v):
        return sum(((k+modulus//2)%modulus-modulus//2)**2
                   for k in (*v,-sum(v)))
    for v in product(range(modulus), repeat=2):
        need(w(act(mul(a,b),v)) == w(act(mul(b,a),v)) == 0,
             "both forbidden repeats appear dark")
    # The two-step raw and normalized readings match the standard contact
    # exactly for these bounded preparations, not just their dark flags.
    for v in product(range(-3,4), repeat=2):
        current = [(v,v)]
        for _ in range(2):
            current = [(act(m,x),act(n,y)) for x,y in current
                       for m,n in ((a,plus),(b,minus))]
            need(all(w(x) == 2*q(y) for x,y in current), "finite read match")


def remaining_controls():
    # P-dependent gauges at distinct OUTLETS cannot be aligned just by
    # separate squared stocks. Wiring a reference distinguishes the signs.
    x,y = (1,0),(0,1)
    need(q(y) == q(times(-1,y)) and q((x[0]+y[0],x[1]+y[1])) == 3
         and q((x[0]-y[0],x[1]-y[1])) == 1, "coherent reference sign")
    # A nonlinear (but quotient-compatible) gain can agree on a bounded
    # table, preserve all same-setting dark repeats, and keep any normalized
    # single contact fractions. Its total gain is not state-independent.
    plus,minus = split_matrices(EXCHANGES[0])
    def nonlinear(m,v):
        return times(1 if q(v)<=9 else 2, act(m,v))
    u = (2,0)
    need(nonlinear(plus,times(2,u)) != times(2,nonlinear(plus,u)),
         "unchecked additivity")
    for v in product(range(-4,5), repeat=2):
        a,b = nonlinear(plus,v),nonlinear(minus,v)
        need(nonlinear(minus,a) == nonlinear(plus,b) == (0,0) and
             q(a)*q(act(minus,v)) == q(b)*q(act(plus,v)), "nonlinear readings")
    # Signed dark laws on the lift can distinguish residues that the
    # unoriented device cannot. A nonpositive setting gain also breaks the
    # argument for automatic label symmetry (not an allowed hypothesis).
    def signed(v):
        return (0,2,7)[(v[0]-v[1])%3]
    def inactive(v):
        return int((v[0]-v[1])%5 != 0)
    for i,p in enumerate(EXCHANGES):
        plus,minus = split_matrices(p)
        for v in product(range(-5,6), repeat=2):
            need(signed(act(plus,v))+signed(act(times(-1,minus),v)) == signed(v),
                 "raw signed dark law")
            scale = 1 if i == 2 else 5
            need(inactive(act(times(scale,plus),v))+inactive(act(times(scale,minus),v))
                 == (i==2)*inactive(v), "zero-gain boundary")
    need(inactive((2,-1)) > 0 and inactive((1,1)) == 0,
         "one bright median with inactive settings")


def graph_multiplier():
    # All edges are unsigned. An extra identical sheet attached across
    # neighbors scales every relative current by two, without reading colors.
    def extra_sheet(g):
        return graphs.attach(g, lambda k:k,
                             ((u,v) for u,ns in enumerate(g.adj) for v in ns))
    prepared = graphs.single_probe()
    for g in prepared.values():
        for i in graphs.D:
            first = graphs.split(g,lambda k:graphs.reflection(i,k))
            other = tuple(map(extra_sheet,first))
            old = tuple(map(graphs.mass,first))
            new = tuple(map(graphs.mass,other))
            need(new == times(4,old) and sum(new) == 16*graphs.mass(g)
                 and all(len(h.tags) == 2*len(f.tags) for f,h in zip(first,other)),
                 "different graph, same normalized outcomes")


def main():
    counts = census(4)
    need(counts == [32,32,128], "ordered pairs by setting in this basis")
    stock_controls()
    blind_repeat()
    remaining_controls()
    graph_multiplier()
    print("Raw [-4,4] four-entry census: ordered pairs by setting", counts)
    print("Unknown-stock ridge census: 18 even unknowns, exact nullity 3. "
          "Lit median + all-current stock law: Q up to scale, g_P=4 s_P².")
    print("Extra sheets: same normalized data; absolute gain 16 vs 4. "
          "Blind modulus-101 detector: both cross words read zero despite raw leakage.")


if __name__ == "__main__":
    main()
