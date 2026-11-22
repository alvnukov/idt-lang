"""Hidden orthogonal tags defeat a visible-sector physical exclusion.

SUPPLIED: three orthogonal one-packet hidden contrasts on four neutral rails,
distinct input tag word rgb, simultaneous visible/hidden permutation lifts,
coherent integer sums, tensor composition, quadratic normalization and tracing
unread orthogonal tags. These are resources, not derived detector dynamics.
Hidden colors are anonymous tags, NOT quark color or physical space.

L_±(v)=sum_g sign(g)^(0 or 1) U_g v tensor |g rgb> has opposite TOTAL
exchange character, but identical visible reduced moments: the group twirl
of v. Thus ALL visible effects agree between the two lifts. Relative to the
original v only invariant observables necessarily agree. This is a scoped
false-rejection control, not a spin-statistics theorem or observed data.
An uncontrolled total swap changes only a global sign, invisible as a channel;
its coherent identity-versus-swap comparison can read the opposite characters.
Reading diagonal hidden labels alone cannot: each conditional visible column
differs only by a sign. The traced maps have the same Kraus operators up to
individual signs, also with an entangled external reference, subsequent adaptive
visible instruments and any positive-probability visible postselection.

The compact six-word coordinates have an audited orthogonal native Hadamard
realization; no expensive full router is needed. Normalization and hidden
partial trace remain supplied. Repeated hidden tags are not orthogonal word
records: their off-diagonal interference can spoil equality. Two hidden
one-packet colors can suffice for a chosen standard-sector input; they do
not support the full visible carrier's symmetric input in a total alternating
lift, which would need a nonzero third exterior hidden power.
"""

from fractions import Fraction as F
from itertools import permutations, product

from scripts.probe_three_packet_exchange_sector import CONTRASTS


def need(ok, why):
    if not ok:
        raise AssertionError(why)


GROUP = tuple(permutations(range(3)))
INDEX = {p:i for i,p in enumerate(GROUP)}
IDENTITY = (0,1,2)
SWAP = (1,0,2)
CYCLE = (1,2,0)


def mul(p,q):
    return tuple(p[q[i]] for i in range(3))


def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))


def action(p,v):
    out=[0]*6
    for q,x in zip(GROUP,v):
        out[INDEX[mul(p,q)]]=x
    return tuple(out)


def add(*vs):
    return tuple(map(sum,zip(*vs)))


def scaled(n,v):
    return tuple(n*x for x in v)


def moment(columns):
    norm=sum(x*x for col in columns for x in col)
    need(norm>0,"dark lift cannot normalize")
    return tuple(tuple(F(sum(c[i]*c[j] for c in columns),norm) for j in range(6)) for i in range(6))


def lift(v, alternating, colors=(0,1,2)):
    words={}
    for g in GROUP:
        key=tuple(colors[g.index(i)] for i in range(3))
        col=scaled(sign(g) if alternating else 1,action(g,v))
        words[key]=add(words.get(key,(0,)*6),col)
    return words


def total_action(words,p):
    # A hidden word is labelled by its permutation image. On distinct words
    # use left multiplication, the same convention as the visible action.
    out={}
    for g in GROUP:
        key=tuple(g.index(i) for i in range(3))
        dest=mul(p,g)
        out[tuple(dest.index(i) for i in range(3))]=action(p,words[key])
    return out


def expectation(r,p):
    return sum(r[i][INDEX[mul(p,g)]] for i,g in enumerate(GROUP))


def cycle_plus(r):
    # B/3 projects onto C-fixed vectors; B^T B=3B.
    return (1+expectation(r,CYCLE)+expectation(r,mul(CYCLE,CYCLE)))/3


def native_gram():
    need(all(sum(v)==0 for v in CONTRASTS),"neutral hidden tags")
    need([[sum(x*y for x,y in zip(a,b)) for b in CONTRASTS] for a in CONTRASTS]
         == [[4 if i==j else 0 for j in range(3)] for i in range(3)],"hidden tag Gram")
    pts=tuple(product(range(4),repeat=3))
    words=[tuple(CONTRASTS[g[0]][a]*CONTRASTS[g[1]][b]*CONTRASTS[g[2]][c] for a,b,c in pts)
           for g in GROUP]
    need(all(sum(a*b for a,b in zip(v,w))==(64 if i==j else 0)
             for i,v in enumerate(words) for j,w in enumerate(words)),"native permutation-word Gram")


def main():
    native_gram()
    seed=tuple(int(g==IDENTITY) for g in GROUP)
    e=add(seed,action(CYCLE,seed),action(mul(CYCLE,CYCLE),seed))
    x=add(scaled(3,seed),scaled(-1,e))
    symmetric=add(e,action(SWAP,e))
    antisymmetric=add(e,scaled(-1,action(SWAP,e)))
    mix=moment((symmetric,antisymmetric))
    for name,v in (("standard",x),("unsigned even orbit",e),("symmetric",symmetric),("generic",seed)):
        plus,minus=lift(v,False),lift(v,True)
        rp,rm=moment(tuple(plus.values())),moment(tuple(minus.values()))
        twirl=moment(tuple(action(g,v) for g in GROUP))
        need(rp==rm==twirl,"all visible effects need entrywise-equal moments")
        for p in GROUP:
            for words,sgn in ((plus,1),(minus,sign(p))):
                got=total_action(words,p)
                need(all(got[k]==scaled(sgn,words[k]) for k in words),"total exchange character")
        for key in plus:
            need(moment((plus[key],))==moment((minus[key],)),"diagonal tag leaked character")
        for words, expected in ((plus,1),(minus,0)):
            moved=total_action(words,SWAP)
            norm=sum(t*t for col in words.values() for t in col)
            accepted=sum(t*t for key in words for t in add(words[key],moved[key]))
            need(F(accepted,4*norm)==expected,"controlled full-swap comparison")
            need(moment(tuple(moved.values()))==moment(tuple(words.values())),
                 "uncontrolled global sign changed visible state")
        original=moment((v,))
        for p in GROUP:
            # Conjugacy-averaged permutations are invariant effects/diagnostics.
            conjugates=[]
            for g in GROUP:
                inv=tuple(g.index(i) for i in range(3))
                conjugates.append(mul(mul(g,p),inv))
            need(sum(expectation(original,q) for q in conjugates)
                 ==sum(expectation(twirl,q) for q in conjugates),"invariant guard")
        if name=="standard":
            need(cycle_plus(rp)==0,"standard cyclic classifier after trace")
            need(original[0][0]!=rp[0][0],"noninvariant effect must change")
        if name=="unsigned even orbit":
            need(cycle_plus(rp)==cycle_plus(mix)==1,"mixture cycle remains distinct")
        print(f"{name}: opposite total swaps; identical visible moment; cycle plus {cycle_plus(rp)}.")
    # Duplicate tags group coherent columns BEFORE tracing, not after.
    duplicate_plus=moment(tuple(lift(x,False,(0,0,1)).values()))
    duplicate_minus=moment(tuple(lift(x,True,(0,0,1)).values()))
    need(duplicate_plus!=duplicate_minus,"duplicate-color false cancellation")
    # A chosen standard vector with a fixed swap eigenvalue factorizes its
    # irrep/multiplicity coordinates. A different duplicate-color stabilizer
    # then gives equal normalized reduced moments in both total characters.
    diff=add(seed,scaled(-1,action(SWAP,seed)))
    b=add(diff,action(CYCLE,diff),action(mul(CYCLE,CYCLE),diff))
    selected=add(scaled(3,diff),scaled(-1,b))
    found=False
    for colors in ((0,0,1),(0,1,0),(1,0,0)):
        a=tuple(lift(selected,False,colors).values())
        b=tuple(lift(selected,True,colors).values())
        if (sum(t*t for c in a for t in c) and sum(t*t for c in b for t in c)
                and moment(a)==moment(b)):
            found=True
    need(found,"two-color chosen-standard feasibility")
    # With symmetric visible input, total alternating requires an alternating
    # hidden tensor; any word on only two colors repeats an entry and cancels.
    for colors in product(range(2),repeat=3):
        need(not any(z for col in lift(symmetric,True,colors).values() for z in col),
             "two colors unexpectedly realize third exterior power")
    print("Duplicate tags spoil general equality; two colors suffice for a chosen standard input, not full visible support.")
    erased_plus=add(*lift(seed,False).values())
    erased_minus=add(*lift(seed,True).values())
    need(moment((erased_plus,))!=moment((erased_minus,)),"coherent hidden eraser control")
    print("Diagonal hidden labels do not reveal sign; coherent full-swap comparison or hidden erasure can. A bare full swap is only a global sign.")
    print("Invariant readouts survive twirling; a visible noninvariant projector changes. Hidden tags and trace supplied; no physical exclusion or quark-color claim.")


if __name__=="__main__":
    main()
