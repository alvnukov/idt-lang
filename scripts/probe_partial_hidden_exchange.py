"""Partial hidden tags: exact visible distinguishability of two total characters.

SUPPLIED: three ORTHOGONAL visible letters, normalized pure product hidden
tags with a physical Gram, coherent simultaneous permutation lifts, tensor
composition, hidden trace and quadratic/Born effect readout. Hidden colors
are not quark color. This is a finite mathematical control, not empirical
data, a statistics derivation, detector dynamics or a physical exclusion.

Orthogonal visible permutation words make both unnormalized lift norms six.
The visible density difference has zero same-parity blocks and even/odd
block B/3. Its Latin entries are w_ij=|<h_i,h_j>|^2: no triad phase remains.
BB^T has eigenvalues s^2,q,q, where s=sum(w),
q=sum(w_i^2)-sum_{i<j}w_i*w_j. Thus half the trace norm is
  D=(s+2 sqrt(q))/3.
This is the SUPREMUM of outcome-total-variation over arbitrary visible POVMs,
by the positive/negative spectral projector of the Hermitian difference.
It is not necessarily attainable with the available contact grammar.
A controlled visible LETTER relabel (not a total factor swap) gives gap
w_ij, hence the native lower bound max(w). Its I+/- comparison is essential:
a bare reversible relabel followed by no comparison is not that readout.

Pure product tags and a fixed orthogonal visible input are scope limits.
Triad phase can change each individual reduced density despite equal D.
Nonorthogonal visible words invalidate the constant-six normalization.
"""

from fractions import Fraction as F
from itertools import permutations, product
from math import isqrt

from scripts.gaussian_dyadic_words import ONE, ZERO, g
from scripts.probe_three_packet_exchange_sector import CONTRASTS

GROUP=tuple(permutations(range(3)))
INDEX={p:i for i,p in enumerate(GROUP)}


def need(ok,why):
    if not ok:
        raise AssertionError(why)


def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))


def mul(p,q):
    return tuple(p[q[i]] for i in range(3))


def gram(tags):
    need(len(tags)==3 and len({len(v) for v in tags})==1,"three equally sized tags")
    out=tuple(tuple(sum((a.star()*b for a,b in zip(x,y)),ZERO) for y in tags) for x in tags)
    need(all(out[i][i]==ONE for i in range(3)),"tags must be normalized")
    return out


def reduced(tags):
    h=gram(tags)
    overlap=[]
    for p in GROUP:
        row=[]
        for r in GROUP:
            z=ONE
            for i in range(3):
                z=z*h[r.index(i)][p.index(i)]
            row.append(z)
        overlap.append(row)
    rp=tuple(tuple(z*g(F(1,6)) for z in row) for row in overlap)
    rm=tuple(tuple(z*g(F(sign(p)*sign(r),6)) for r,z in zip(GROUP,row))
             for p,row in zip(GROUP,overlap))
    need(sum((rp[i][i] for i in range(6)),ZERO)==ONE,"plus norm six")
    need(sum((rm[i][i] for i in range(6)),ZERO)==ONE,"minus norm six")
    return h,rp,rm


def matmul(a,b):
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*b)) for row in a)


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def square_root(q):
    a,b=isqrt(q.numerator),isqrt(q.denominator)
    return F(a,b) if a*a==q.numerator and b*b==q.denominator else None


def audit(tags):
    h,rp,rm=reduced(tags)
    need(all(r[i][j]==r[j][i].star() for r in (rp,rm) for i,j in product(range(6),repeat=2)),
         "Hermitian reduced moments")
    weights=tuple(h[i][j].norm2() for i,j in ((0,1),(0,2),(1,2)))
    even=[i for i,p in enumerate(GROUP) if sign(p)==1]
    odd=[i for i,p in enumerate(GROUP) if sign(p)==-1]
    delta=tuple(tuple(rp[i][j]-rm[i][j] for j in range(6)) for i in range(6))
    need(all(delta[i][j]==ZERO for i,j in product(range(6),repeat=2)
             if sign(GROUP[i])==sign(GROUP[j])),"same-parity difference")
    b=tuple(tuple(3*delta[i][j].re for j in odd) for i in even)
    need(all(delta[i][j].im==0 for i in even for j in odd),"triad phase in odd block")
    need(all(sorted(row)==sorted(weights) for row in b)
         and all(sorted(col)==sorted(weights) for col in zip(*b)),"Latin weights")
    s=sum(weights); q=sum(w*w for w in weights)-sum(weights[i]*weights[j] for i in range(3) for j in range(i+1,3))
    m=matmul(b,tuple(zip(*b)))
    need(q>=0 and all(m[i][j]==(q if i==j else 0)+(s*s-q)/3 for i,j in product(range(3),repeat=2)),"BBt exact spectrum")
    need(sum(m[i][i] for i in range(3))==s*s+2*q and det3(m)==s*s*q*q,"spectral multiplicities incl zero")
    root=square_root(q)
    d=(s+2*root)/3 if root is not None else None
    # Visible LETTER transposition acts on the right word label. Both
    # branch populations are computed from the full reduced moments.
    gaps=[]
    for t,w in zip(((1,0,2),(2,1,0),(0,2,1)),weights):
        ex=[]
        for r in (rp,rm):
            value=sum((r[i][INDEX[mul(p,t)]] for i,p in enumerate(GROUP)),ZERO)
            need(value.im==0,"real controlled letter comparison")
            ex.append((1+value.re)/2)
        need(ex==[(1+w)/2,(1-w)/2],"native letter-swap lower bound")
        gaps.append(ex[0]-ex[1])
    need(d is None or max(gaps)<=d<=1,"trace-distance bounds")
    return weights,d,(s,q),rp,rm


def main():
    rail_swap=(0,2,1,3)
    need(tuple(CONTRASTS[0][i] for i in rail_swap)==CONTRASTS[1]
         and tuple(CONTRASTS[1][i] for i in rail_swap)==CONTRASTS[0]
         and tuple(CONTRASTS[2][i] for i in rail_swap)==CONTRASTS[2],
         "native visible-letter transposition via one rail permutation")
    e0,e1,e2=(tuple(g(int(i==j)) for i in range(3)) for j in range(3))
    for name,tags,expected in (("distinct",(e0,e1,e2),F(0)),("identical",(e0,e0,e0),F(1)),
                               ("two identical, third orthogonal",(e0,e0,e1),F(1))):
        w,d,_,_,_=audit(tags); need(d==expected,"endpoint control")
        print(name,"weights",w,"arbitrary-POVM D",d,"native lower",max(w))
    half=g(F(1,2),F(-1,2))
    variants=[]
    for phase in (ONE,g(0,1)):
        tags=((half,half,ZERO),(ZERO,half,half),(half*phase,ZERO,half))
        w,d,_,rp,rm=audit(tags)
        need(w==(F(1,4),)*3 and d==F(1,4),"physical equi-overlap")
        variants.append((rp,rm))
    need(variants[0]!=variants[1],"triad-phase individual density control")
    # Physical normalized four-coordinate hidden tags: overlap squares 1/4,1/4,0.
    a=(g(F(1,2)),)*4
    b=(ONE,ZERO,ZERO,ZERO); c=(ZERO,ONE,ZERO,ZERO)
    w,d,_,_,_=audit((a,b,c))
    need(w==(F(1,4),F(1,4),0) and d==F(1,3) and max(w)==F(1,4),"strict operational gap")
    full=((ONE,ZERO,ZERO),(g(F(3,5)),g(F(4,5)),ZERO),
          (g(F(1,3)),g(F(2,3)),g(F(2,3))))
    w,d,(s,q),_,_=audit(full)
    need(w==(F(9,25),F(1,9),F(121,225)) and square_root(q) is None,
         "full nondegenerate irrational spectrum control")
    print(f"Physical unequal full overlaps: s={s}, q={q}; exact D=({s}+2sqrt({q}))/3.")
    # Collapsing all visible letters makes their word Gram all ones. With
    # identical hidden tags the unnormalized norms become 36 and zero.
    _,rp,rm=reduced((e0,e0,e0))
    need(g(6)*sum((z for row in rp for z in row),ZERO)==g(36)
         and g(6)*sum((z for row in rm for z in row),ZERO)==ZERO,"nonorthogonal visible normalization wall")
    print("Two physical triad phases: same weights/D=1/4, different individual moments.")
    print("Physical weights (1/4,1/4,0): native visible-letter gap1/4 < arbitrary-POVM D1/3.")
    print("Spectrum certificate BBt: s²,q,q; D=(s+2sqrt(q))/3. This is an arbitrary visible POVM supremum, not a contact attainability claim.")
    print("Nonorthogonal visible words change normalization; product pure tags, coherent trace/readout supplied. No empirical exclusion.")


if __name__=="__main__":
    main()
