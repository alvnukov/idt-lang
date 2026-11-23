"""Which signed scalar backgrounds can a four-way junction actually prepare?

For a dyadic unit vector with denominator 2^k, the number of odd numerator
entries is a multiple of four if k>0. Group them in fours. Flip one sign
if necessary so the four sum to 2 mod 4; reflecting each entry about their
mean then makes them all even. A blank spare compensates individual signs
if only paired phase flips are allowed. Repeat to reach a single unit.
Reverse the stored word to prepare the original state. This is a variant
of the four-level denominator reduction in arXiv:2106.01175, not a new
general synthesis theorem.

With calibrated local, sign-insensitive coordinate response f(x) the
important four-input tests (t+2h,t,t,t) need no arbitrarily assigned
unnormalized wave. Complete to a dyadic unit vector with integer spectator
squares, and verify the preparation using actual native gates. For all
dyadic |x|<=1/2 the third-difference tests on each finite central mesh
force a quadratic; f(0)=0, sign symmetry and f(1/2)=1/4 fix it. Splitting
one localized coordinate x over four legs forces f(x)=4f(x/2), covering
the rest. This argument assumes identical local f across preparations and
stable, exhaustive outcomes. It does not reconstruct actualization or give
rates for non-dyadic limiting states without a continuity assumption.
"""

from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import gcd, isqrt

from scripts.probe_anonymous_contact_additive_readout import rank


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def apply(v, instruction):
    kind, *indices = instruction
    w = list(v)
    if kind=="pair":
        for j in indices:
            w[j] = -w[j]
    else:
        need(kind=="contact" and len(indices)==4 and len(set(indices))==4, "bad contact")
        half = F(sum(w[j] for j in indices),2)
        for j in indices:
            w[j] = half-w[j]
    return tuple(w)


def prepare(nums, den):
    need(den>0 and den&(den-1)==0 and sum(x*x for x in nums)==den*den, "not a dyadic unit")
    spare = len(nums)
    x = [*nums,0]
    d,program = den,[]
    while d>1:
        odd = [i for i,n in enumerate(x) if n%2]
        need(len(odd)%4==0, "cannot group odd entries")
        for j in range(0,len(odd),4):
            block = odd[j:j+4]
            if sum(x[i] for i in block)%4 != 2:
                program.append(("pair",block[0],spare))
                x[block[0]] *= -1
            program.append(("contact",*block))
            half = sum(x[i] for i in block)//2
            for i in block:
                x[i] = half-x[i]
        need(all(n%2==0 for n in x), "denominator did not descend")
        x = [n//2 for n in x]
        d //= 2
    need(sum(abs(n) for n in x)==1 and x[spare]==0, "not a single source")
    result = tuple(x)
    for instruction in reversed(program):
        result = apply(result,instruction)
    need(result == tuple(F(a,den) for a in (*nums,0)), "actual unit-source replay disagrees")
    return len(program)


def padding(n):
    pairs = {}
    for i,j in combinations_with_replacement(range(isqrt(n)+1),2):
        if (s:=i*i+j*j) <= n:
            pairs.setdefault(s,(i,j))
    return next((*a,*pairs[n-s]) for s,a in pairs.items() if n-s in pairs)


def calibrated_mesh(den):
    subdivisions = 2*den
    central = range(-den,den+1)
    indices = tuple(sorted(set(central) | set(range(-subdivisions,subdivisions+1,2))))
    rows = []
    preparations = []

    def relation(equation, value=0):
        # Arithmetic checks the target AFTER deriving each conservation
        # equation. Rank, not a fitted or supplied polynomial ansatz,
        # certifies uniqueness among all real tables on these mesh sites.
        row = tuple(equation.get(i,0) for i in indices)
        need(sum(F(i*i,subdivisions**2)*c for i,c in zip(indices,row,strict=True))==value,
             "claimed target does not satisfy the hardware equation")
        rows.append(row)

    def setup(ports):
        remainder = subdivisions**2-sum(v*v for v in ports)
        need(remainder>=0,"cannot normalize local background")
        nums = (*ports,*padding(remainder))
        preparations.append(prepare(nums,subdivisions))

    relation({0:1})
    relation({den:1},F(1,4))  # four equal magnitudes from the single unit
    need(tuple(abs(x) for x in apply((1,0,0,0),("contact",0,1,2,3)))==(F(1,2),)*4,
         "balanced calibration not implemented")
    for i in indices:
        if i>0:
            relation({i:1,-i:-1})
    for k in range(-den,den-2):
        t=k+1
        setup((t+2,t,t,t))
        output = apply((t+2,t,t,t),("contact",0,1,2,3))
        need(output==(t-1,t+1,t+1,t+1),"wrong conservation row")
        relation({k:-1,k+1:3,k+2:-3,k+3:1})
    for n in range(den//2+1,den+1):
        setup((2*n,0,0,0))
        relation({2*n:1,n:-4})
    need(rank(rows)==len(indices),"unconstrained non-square table on tested dyadic grid")
    return {"coarse_denominator":den,"free_table_sites_before_checks":len(indices),"checked_preparations":len(preparations),
            "max_word_length_including_signs":max(preparations),"remaining_homogeneous_directions":0}


def embedding_wall():
    # Different ideals of spectator amplitudes over Z[1/2]. Reversible
    # matrices over this ring preserve the generated ideal in both
    # directions, even with extra blank modes. This does NOT construct
    # a full alternative response or deny locality in the real apparatus.
    a,b=(7,9,9,6,3),(7,13,5,3,2)
    need(sum(x*x for x in a)==sum(x*x for x in b)==16**2 and a[0]==b[0], "not matched at the target")
    for v in (a,b):
        prepare(v,16)
    need((gcd(*a[1:]),gcd(*b[1:]))==(3,1),"odd ideal mismatch")
    return {"same_amplitude":"7/16","complement_numerator_odd_gcd":[3,1],
            "not_implied":"arbitrary complement equivalence by dyadic gates alone"}


def probe():
    return {"meshes":[calibrated_mesh(d) for d in (2,4,8,16)],
            "fixed_hardware":"four active entries, four integer-square padding entries and one sign-compensation blank",
            "spectator_control":embedding_wall(),"empirical_status":"not_tested"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),sort_keys=True))
