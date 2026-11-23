"""Symmetric non-Born transition probabilities on rational four-mode rays.

Not just four specially prepared responses: each allowed ray prepares a state
that passes its own test with certainty. Distinct rays can nevertheless be
operationally equivalent. The first and subsequent complete sharp tests can
use the same reciprocal kernel, resetting to the reported ray. No outcomes
or Born law are inferred from the unsigned carrier.

Take primitive integer directions whose squared length is a square or twice
a square (the two classes of the native frames). Their odd support size k
is 1,2 or 4, and N=k*t² for odd t. Replace each odd coordinate by its sign
modulo 4 (+ for 1, − for 3), and every even one by zero; the overall sign
is immaterial. This sends the rational supply to just 24 signed rays. The
ordinary trace pairing of these small images yields the alternative kernel
[4 Tr(PQ)]_8 / 4, where the bracket reduces odd-denominator rationals mod 8.
It is NOT the ordinary trace pairing of P,Q. Both produce the same transition
numbers between the 24 original rays.

INTEGER REASON. For two even coordinates of a k=2 vector, their residues
are both 0 or both 2 mod4, since their squares sum to 0 mod8. For k=4,
the number of corrections by 4 mod8 to the four signed odd representatives
is even: the norm is 4 mod16, and each corrected square is 9 rather than 1
mod16. These facts reduce squared dot products to the small images in all
six support-size pairings. The program exhausts the necessary congruence
classes, including the denominators 2 and 4 of normalized overlaps, using
integer residues sufficient for the required precision. A real source of
uniform selector bits, a degenerate measurement update, preparation
equivalence for arbitrary ensembles or general physical amplitudes is NOT
established by this model.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import isqrt

from scripts.probe_dense_readout_residue_countermodel import (
    dot,
    junction,
    mv,
    native_frames,
    ray,
)


def need(value, why):
    if not value:
        raise ArithmeticError(why)


def shadow(a):
    # Input may be a rational representative. Remove the COMMON multiplier
    # before reducing, not independently on each coordinate.
    a = ray(a)
    k = sum(x % 2 for x in a)
    n = dot(a,a)
    need(k in (1,2,4) and n % k == 0 and isqrt(n//k)**2 == n//k and isqrt(n//k) % 2,
         "outside the two supplied square classes")
    return ray(tuple(1 if x % 4 == 1 else -1 if x % 4 == 3 else 0 for x in a))


def born(a,b):
    return F(dot(a,b)**2, dot(a,a)*dot(b,b))


def kernel(a,b):
    return born(shadow(a),shadow(b))


def residue_classes(k):
    # Work modulo 8, with sign and coordinate-swap symmetry on the first
    # vector below. Squares of these residues are known modulo 16. Forcing
    # n=k mod 8 (or mod16 for k=4) is necessary and enough for the argument;
    # there is no assumption each enumerated residue has a physical lift.
    return [a for a in product(range(8),repeat=4)
            if sum(x % 2 for x in a) == k and (dot(a,a)-k) % (16 if k == 4 else 8) == 0]


def shadow4(a):
    return tuple(1 if x % 4 == 1 else -1 if x % 4 == 3 else 0 for x in a)


def congruence_census():
    classes = {k:residue_classes(k) for k in (1,2,4)}
    signs = lambda x: min(x,(-x) % 8)
    # Simultaneous signed permutation preserves both pairings. Exhaust the
    # first-vector orbits and all possible residues of the second vector.
    reduced = {k:{tuple(sorted(map(signs,a))) for a in xs} for k,xs in classes.items()}
    count = 0
    for k,t in ((1,1),(1,2),(1,4),(2,2),(2,4),(4,4)):
        for a in reduced[k]:
            sa = shadow4(a)
            for b in classes[t]:
                d = dot(a,b)
                s = dot(sa,shadow4(b))
                value, r = divmod(4*d*d,k*t)
                target, r2 = divmod(4*s*s,k*t)
                # Replacing a coordinate by any integer multiple of 8
                # plus its residue does not affect the quotient mod 8:
                # largest divisor (k*t)/4=4 occurs only if both have four
                # odds, hence d even and (d+8m)^2/4 = d²/4 mod8.
                # The omitted odd t_a² t_b² denominators equal 1 mod8.
                need(not r and not r2 and value % 8 == target and target in (0,1,2,4),
                     "signed shadow not equal to the intrinsic trace residue")
                count += 1
    return {"necessary_classes":{k:len(v) for k,v in classes.items()},
            "first_vector_orbits":{k:len(v) for k,v in reduced.items()}, "comparisons":count}


def instrument():
    bases = native_frames()
    native = set().union(*bases)
    need(len(native) == 24 and all(shadow(a) == a for a in native), "native rays not recovered")
    layers = [set(native)]
    for _ in range(2):
        layers.append({ray(mv(junction(j),a)) for j in range(4) for a in layers[-1]})
    augmented = set().union(*layers)
    # A three-port junction acts as the identity on every finite shadow.
    # For arbitrary primitive v, multiply S*v by 3. Parity is unchanged;
    # on odd entries of the triple, signs mod 4 are reversed iff the sum of
    # triple entries is odd. The spectator gets factor 3. If spectator is
    # odd: for k=2,4 the sum on the triple is odd; for k=1 only the
    # spectator is nonzero in the shadow. Otherwise only the triple matters.
    # Any common odd gcd just changes the overall projective sign.
    need(all(shadow(mv(junction(j),a)) == shadow(a) for a in augmented for j in range(4)), "jump in shadow")
    for b in bases:
        for j in range(4):
            moved = [ray(mv(junction(j),a)) for a in b]
            need(all(sum(kernel(q,a) for a in moved) == 1 for q in augmented), "unnormalized frame")
    # Any orthogonal complete basis of allowed rays has 4 mutually
    # orthogonal shadows by the trace congruence, hence an orthonormal
    # basis in real dimension four after scaling. Reversible rational
    # gates preserve the intrinsic trace, so K is covariant.
    need(all(kernel(a,a) == 1 for a in augmented) and
         all(born(a,b) == kernel(a,b) for a,b in product(native,repeat=2)), "repeatability/calibration")
    selections = Counter()
    for b in bases:
        for a in native:
            counts = tuple(int(4*kernel(a,t)) for t in b)
            need(sum(counts)==4 and all(F(n,4)==kernel(a,t) for n,t in zip(counts,b,strict=True)),
                 "two-bit event table")
            selections[tuple(sorted(counts))] += 1
    # Controlled state update: select one ray according to the table, return
    # its shadow as subsequent state. This simulates any sequence of complete
    # rank-one instruments (or coarse reporting AFTER fine measurement).
    # It is not an implementation of all nondestructive rank-two instruments.
    return {"shadow_states":len(native), "sample_rays":len(augmented),
            "four_slot_profiles":{str(k):v for k,v in sorted(selections.items())}}


def preparation_control():
    a = (1,0,0,0)
    w = ray(mv(junction(3),a))
    need(born(a,w)==F(1,9) and kernel(a,w)==1, "one controlled split")
    # The four native diagonal signs dephase ALL pairs: each nontrivial
    # character of the two-bit coordinate labels occurs equally often.
    family = [tuple(x*(-1 if (i & k).bit_count()%2 else 1) for i,x in enumerate(w)) for k in range(4)]
    n = dot(w,w)
    rho = tuple(tuple(sum(F(x[i]*x[j],4*n) for x in family) for j in range(4)) for i in range(4))
    weights = (F(1,9),F(4,9),F(4,9),F(0))
    need(all(rho[i][j] == (weights[i] if i==j else 0) for i,j in product(range(4),repeat=2)),
         "ensemble density matrices do not agree")
    left = sum(kernel(a,x) for x in family)/4
    right = sum(p*kernel(a,tuple(int(k==i) for k in range(4))) for i,p in enumerate(weights))
    need(left==1 and right==F(1,9), "statistically distinct preparations")
    # These ensemble weights and equivalence are explicit comparator inputs,
    # not inferred from the prep labels; the detector could distinguish them.
    return {"quantum_ensemble_matrices_equal":True, "scrambled_junction_return":str(left),
            "weighted_direct_injections_return":str(right), "empirical_status":"not_tested"}


def probe():
    return {"congruence":congruence_census(), "instruments":instrument(),
            "two_ensemble_control":preparation_control()}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),sort_keys=True))
