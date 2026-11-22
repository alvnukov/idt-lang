"""Conditional native coherent analyzers attain/approach the hidden-tag optimum.

Three visible contrast LETTER transpositions T_i are simultaneous physical
rail relabelings of each packet, not swaps of factor slots. For K=sum k_i T_i,
K²=sum(k_i²) I+sum(i<j,k_i*k_j)(C+C^-1) on the FULL raw four-cubed rails.
If sum k_i=d and sum k_i²=d², K²=d²I. Supplied coherent branches dI+/-K
therefore have column Gram 4d²I and can use the existing universal integer
event router. This assumes signed coherent copies, cancellation, complete
ordered-pair stock and uniform seeds; it does not derive an apparatus.
In particular the collective signed-copy/wiring device is supplied: its
integer-router realization is NOT a graph-origin proof or a demonstration
that one calibrated two-sheet contact automatically compiles this schedule.

For the fixed orthogonal visible-word/product-pure-hidden-tag contract,
the visible plus-population gap is k.dot(w)/d. The circle sum c=sum c²=1
maximizes this at (s+2sqrt(q))/3, the arbitrary-visible-POVM trace distance.
Rational points c=(-mn,m(m+n),n(m+n))/(m²+mn+n²) are dense on that circle.
This is a conditional mathematical supremum, not finite exact access to
irrational coefficients, efficient compilation, unlimited physical paths,
or an experimental optimum. Earlier single-letter lower bounds are not
upper bounds once coherent sums of letter controls are permitted.

Full64 Gram and one actual unsigned-source routed population are checked;
partial-hidden-tag probabilities use compact exact reduced moments, not a
huge full hidden-tag router. No empirical data, Lean proof or status upgrade.
"""

from fractions import Fraction as F
from itertools import product
from math import isqrt

from scripts.gaussian_dyadic_words import ONE, ZERO, g
from scripts.probe_cancellation_event_router import pairs, route_block
from scripts.probe_partial_hidden_exchange import GROUP, INDEX, audit, mul
from scripts.probe_three_packet_exchange_sector import CONTRASTS, unsigned_source


def need(ok,why):
    if not ok:
        raise AssertionError(why)


POINTS=tuple(product(range(4),repeat=3))
POS={p:i for i,p in enumerate(POINTS)}
RAIL_SWAPS=((0,2,1,3),(0,3,2,1),(0,1,3,2))
LETTER_SWAPS=((1,0,2),(2,1,0),(0,2,1))


def coefficients(m,n):
    d=m*m+m*n+n*n
    need(d>0,"zero rational parameter")
    k=(-m*n,m*(m+n),n*(m+n))
    need(sum(k)==d and sum(x*x for x in k)==d*d,"rational circle")
    return k,d


def raw_gate(k,d):
    for p,t in zip(RAIL_SWAPS,LETTER_SWAPS):
        need(all(tuple(CONTRASTS[i][a] for a in p)==CONTRASTS[t[i]] for i in range(3)),
             "physical rail-to-letter transposition")
    maps=tuple(tuple(POS[tuple(p[a] for a in point)] for point in POINTS) for p in RAIL_SWAPS)
    n=len(POINTS)
    matrix=tuple(tuple(sum(c*int(mp[i]==j) for c,mp in zip(k,maps)) for j in range(n)) for i in range(n))
    need(all(sum(matrix[i][a]*matrix[a][j] for a in range(n))==(d*d if i==j else 0)
             for i,j in product(range(n),repeat=2)),"K² on full raw64")
    gate=tuple(tuple(d*int(i==j)+sgn*matrix[i][j] for j in range(n))
               for sgn in (1,-1) for i in range(n))
    need(all(sum(row[i]*row[j] for row in gate)==(4*d*d if i==j else 0)
             for i,j in product(range(n),repeat=2)),"full64 column Gram")
    return gate


def gap_from_moments(rp,rm,k,d):
    probabilities=[]
    for r in (rp,rm):
        expected=ZERO
        for c,t in zip(k,LETTER_SWAPS):
            expected=expected+g(c)*sum((r[i][INDEX[mul(p,t)]] for i,p in enumerate(GROUP)),ZERO)
        need(expected.im==0,"real analyzer expectation")
        probabilities.append((1+expected.re/d)/2)
    need(all(0<=p<=1 for p in probabilities),"invalid positive-effect probability")
    return probabilities,probabilities[0]-probabilities[1]


def finite_search(weights,bound=64):
    s=sum(weights)
    q=sum(x*x for x in weights)-sum(weights[i]*weights[j] for i in range(3) for j in range(i+1,3))
    best=None
    for m,n in product(range(-bound,bound+1),repeat=2):
        if not (m or n):
            continue
        k,d=coefficients(m,n)
        value=sum(c*w for c,w in zip(k,weights))/d
        t=(3*value-s)/2
        need(t<=0 or t*t<=q,"candidate exceeds exact optimum")
        if best is None or value>best[0]:
            best=(value,m,n,k,d)
    # An exact rational enclosure, never a floating-point optimum assertion.
    scale=10**9
    root_floor=isqrt(q.numerator*scale*scale//q.denominator)
    lo,hi=F(root_floor,scale),F(root_floor+1,scale)
    need(lo*lo<=q<hi*hi,"sqrt enclosure")
    lower,upper=(s+2*lo)/3,(s+2*hi)/3
    need(best[0]<=upper and upper-best[0]<F(1,100000),"finite near-optimum witness")
    return best,(lower,upper)


def main():
    k,d=(2,2,-1),3
    need(coefficients(2,-1)==(k,d),"special exact analyzer")
    gate=raw_gate(k,d)
    src=unsigned_source()
    cloud,routes,gain,_=route_block(src.cloud,gate)
    counts=tuple(sum(cloud[p[0]][0]//64==b for p in routes.values()) for b in (0,1))
    need(gain==36 and len(routes)==36*len(src.tickets)==2304
         and set(routes.values())==pairs(cloud) and len(set(routes.values()))==len(routes)
         and counts==(1152,1152),"actual native event routing")
    a=(g(F(1,2)),)*4
    b=(ONE,ZERO,ZERO,ZERO); c=(ZERO,ONE,ZERO,ZERO)
    w,optimum,_,rp,rm=audit((a,b,c))
    probs,gap=gap_from_moments(rp,rm,k,d)
    need(w==(F(1,4),F(1,4),0) and gap==optimum==F(1,3)
         and probs==[F(2,3),F(1,3)],"attained physical hidden-tag optimum")
    full=((ONE,ZERO,ZERO),(g(F(3,5)),g(F(4,5)),ZERO),
          (g(F(1,3)),g(F(2,3)),g(F(2,3))))
    w,irrational,_,rp,rm=audit(full)
    need(irrational is None,"nonsquare radical control")
    best,interval=finite_search(w)
    probs,gap=gap_from_moments(rp,rm,best[3],best[4])
    need(gap==best[0],"finite analyzer reduced-moment witness")
    print("k=(2,2,-1), d=3: full64 K²=9I, branch Gram36I; actual64 source tickets ->",counts,"with all2304 descendants.")
    print("Physical weights (1/4,1/4,0): native coherent plus rates2/3 vs1/3; exact optimum gap1/3.")
    print(f"Finite |m|,|n|<=64: m,n={best[1:3]}, k={best[3]}, d={best[4]}, gap={gap}.")
    print(f"Irrational optimum enclosed in [{interval[0]}, {interval[1]}]; gap shortfall <= {interval[1]-gap} < 1/100000.")
    print("Rational circle dense: conditional supremum equals arbitrary-POVM D, but this irrational optimum is not attained by a finite member of this rational analyzer family.")
    print("Large finite witness not routed; no efficient compilation, unlimited physical paths, event-law derivation or empirical claim.")


if __name__=="__main__":
    main()
