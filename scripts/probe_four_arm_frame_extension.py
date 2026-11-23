"""An equal four-arm junction is a new gate, not a new readout basis here.

Old gates: rational orthogonal equal three-arm junctions with one bypass,
and the real signed Pauli operations. Seed measurements are the six native
Peres--Mermin joint frames. Add B = J/2 - I on all four arms. B is its own
inverse. It commutes with each triple junction (each fixes the all-ones
vector), normalizes the signed Pauli group, and permutes the six seed bases.
Every enlarged word thus has the form g or gB, with g an old word. B itself
is not old: old gates have odd denominators. The set of projective bases
obtained from these seeds is UNCHANGED, including the union of their rays.
This does not identify the two operators, their routes, or their action on
a specified preparation. The old permutation-of-four-weights shortcut fails.

Stronger static extension, without continuity or an operator-word bound:
under ANY rational orthogonal four-mode operation, a ray from the 24 seeds
has a primitive integer representative a with N=sum a_i^2 equal to t^2
or 2t^2 for an integer t. Indeed an orthogonal preserves the seed norm
and rescaling is rational; a rational t with t^2 or 2t^2 integral must be
an integer in lowest terms. Conversely a rational Householder maps an axis
or a two-entry seed to a/t of the appropriate length. This characterizes
the rays for the full rational orthogonal group, NOT the native word group.

If N=t^2 with t odd, exactly one entry is odd by reduction modulo four.
If t is even, all four entries must be odd by primitiveness, and t=2u
with odd u by reduction modulo eight. If N=2t^2, t cannot be even: zero
modulo eight would require either all four entries even or four odd, the
latter giving four modulo eight. With t odd precisely two entries are odd.
Consequently N=k*u^2 with u odd and k=#odd in {1,2,4}.

Define p_j(a)=1/k on the odd entries of a and zero elsewhere. For the
rank-one projector P, 4P_jj=4a_j^2/(k*u^2) is odd-denominator rational
and is 4p_j modulo eight. When k=4 there are no even entries. Every full
orthogonal basis of these rays satisfies sum 4p_j=4 modulo eight in each
coordinate. The nonnegative sums total 16 across the four coordinates,
so every sum equals four. On each subset projector Q, the summed 4p_j is
in [0,4] and is singled out by 4Q_jj mod eight, independent of refinement.
This covers mixed orthogonal bases and every subset coarse-graining. No
probability rule for sequential instruments or physical geometry is assumed.
"""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt

from scripts.probe_dense_readout_residue_countermodel import (
    I,
    dot,
    junction,
    mm,
    mv,
    native_frames,
    projection,
    ray,
    residue,
    weights4,
)
from scripts.probe_folded_carrier_parity_contexts import PAULIS, dense, p_sign, word


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def transpose(a):
    return tuple(zip(*a, strict=True))


def atlas_frame(u, frame):
    return tuple(sorted(ray(mv(u,v)) for v in frame))


def gate_extension(b, frames):
    stars = [junction(i) for i in range(4)]
    ps = [dense(p) for p in PAULIS]
    minus_i = tuple(tuple(-v for v in row) for row in I)
    need(mm(mm(ps[0],ps[1]), mm(ps[0],ps[1])) == minus_i, "central minus sign must be an old word")
    pauli_words = {dense(p_sign(word(w,PAULIS),s)): (w,s) for w in range(16) for s in range(2)}
    need(len(pauli_words) == 32 and mm(b,b) == I and b == transpose(b), "four-arm or signed group")
    need(all(mm(b,s) == mm(s,b) for s in stars), "four-arm gate failed to commute with a triple")
    images = [pauli_words[mm(mm(b,p),b)] for p in ps]
    need(images == [(1,0), (6,1), (4,0), (9,1)], "wrong native Pauli conjugation word")
    need(all(F(x).denominator % 2 for op in (*stars,*ps) for row in op for x in row)
         and any(x.denominator == 2 for row in b for x in row), "operator-index obstruction")
    lookup = {tuple(sorted(f)):i for i,f in enumerate(frames)}
    indices = [lookup[atlas_frame(b,f)] for f in frames]
    need(indices == [0,2,1,3,4,5], "native seed bases not permuted")
    # An old e_j had a single nonzero unit weight; B e_j has four quarter
    # weights. A coordinate permutation of that four-vector cannot do this.
    need(all(sorted(weights4(v)) == [0,0,0,4] and weights4(ray(mv(b,v))) == (1,1,1,1) for v in I),
         "the simpler mod-two gate transport should fail")
    return {"four_arm_gate_is_old":False, "index_of_old_operator_group":2,
            "native_projective_basis_orbit_changes":False, "seed_frame_permutation":indices,
            "signed_Pauli_conjugation_word_masks_and_signs":images,
            "coordinate_weight_transport_by_single_permutation_survives":False}


def square_class(v):
    n = dot(v,v)
    t = isqrt(n)
    if t*t == n:
        return 1,t
    t = isqrt(n//2)
    return (2,t) if 2*t*t == n else None


def rational_witness(v, cls):
    # If x and y have equal norm, I-2(x-y)(x-y)^t/||x-y||^2 maps x to y.
    k,t = cls
    x = (1, int(k == 2), 0, 0)
    y = tuple(F(z,t) for z in v)
    d = tuple(a-b for a,b in zip(x,y,strict=True))
    n = dot(d,d)
    h = I if n == 0 else tuple(tuple(I[i][j]-2*d[i]*d[j]/n for j in range(4)) for i in range(4))
    need(mv(h,x) == y and mm(h,transpose(h)) == I, "rational Householder witness")
    return h


def finite_arithmetic_audit():
    counts = Counter()
    for v in product(range(-3,4),repeat=4):
        if gcd(*v) != 1 or next(x for x in v if x) < 0:
            continue
        cls = square_class(v)
        if cls is None:
            continue
        typ,t = cls
        k = sum(x%2 for x in v)
        u = t//2 if k == 4 else t
        need(k in (1,2,4) and u%2 == 1 and dot(v,v) == k*u*u, "integer norm classification")
        q = projection(v)
        need(tuple(residue(4*q[5*j],8) for j in range(4)) == weights4(v), "rank-one residue")
        rational_witness(v,cls)
        counts[typ,k] += 1
    need(set(counts) == {(1,1),(1,4),(2,2)}, "some norm classes not exercised")
    # Rational coordinates of a projective direction do NOT guarantee a
    # normalized rational orthogonal implementation from the native seeds.
    outside = (1,1,2,0)
    q = projection(outside)
    need(square_class(outside) is None and residue(4*q[0],8) == 6 and weights4(outside)[0] == 2,
         "unrestricted rational-direction control did not break diagonal identity")
    return {"primitive_box_coordinate_limit":3,
            "rays_by_square_class_and_number_odd":{f"{t},{k}":v for (t,k),v in sorted(counts.items())},
            "outside_all_rational_orthogonal_seed_orbits":{"ray":outside,"squared_norm":6,
                "first_diagonal_mod_eight":6,"old_formula_four_times_weight":2}}


def mixed_basis_audit(frames, gates):
    transported = {atlas_frame(u,f) for u in gates for f in frames}
    rays = sorted(set().union(*transported))
    neighbors = {v:{w for w in rays if w > v and dot(v,w) == 0} for v in rays}
    bases = {(a,b,c,d) for a in rays for b in neighbors[a] for c in neighbors[a]&neighbors[b]
             for d in neighbors[a]&neighbors[b]&neighbors[c]}
    need(transported < bases, "no additional recombined bases tested")
    z, h = {v:projection(v) for v in rays}, {v:weights4(v) for v in rays}
    seen, counts, repeats = {}, Counter(), Counter()
    for f in bases:
        effects, ws = [(F(0),)*16], [(0,)*4]
        for v in f:
            effects += [tuple(a+b for a,b in zip(q,z[v],strict=True)) for q in effects]
            ws += [tuple(a+b for a,b in zip(w,h[v],strict=True)) for w in ws]
        need(ws[-1] == (4,)*4 and effects[-1] == sum(I,()), "wrong full basis normalization")
        for mask,(q,w) in enumerate(zip(effects,ws,strict=True)):
            rank = mask.bit_count()
            need(all(0 <= i <= 4 for i in w) and tuple(residue(4*q[5*j],8) for j in range(4)) == w,
                 "coarse projector incompatible with summed responses")
            if q in seen:
                repeats[rank] += 1
                need(seen[q] == w, "same shared projector received different weights")
            else:
                counts[rank] += 1
                seen[q] = w
    need(all(repeats[k] for k in range(5)), "missing shared-effect controls")
    return {"test_rays":len(rays),"directly_transported_native_bases":len(transported),
            "all_orthogonal_bases_on_test_rays":len(bases),"distinct_effects_by_rank":dict(counts),
            "repeat_encounters_by_rank":dict(repeats)}


def readout_cases(b, s, r5):
    cases = {}
    for name,u,h,born in (
        ("four_arm_only",b, (F(1,4),)*4, (F(1,4),)*4),
        ("four_arm_and_triple",mm(b,s), (F(1,4),)*4, (F(1,36),F(1,36),F(25,36),F(1,4))),
        ("separate_denominator_five_control",r5,(0,0,1,0),(F(16,25),0,F(9,25),0)),
    ):
        cols = transpose(u)
        got = tuple(F(weights4(ray(x))[2],4) for x in cols)
        reference = tuple(x[2]**2 for x in cols)
        need(got == h and reference == born and sum(got) == sum(reference) == 1, "ordered readout trial")
        cases[name] = {"static_residue":list(map(str,got)), "Born_e3":list(map(str,reference))}
    return cases


def spectral_boundary(s):
    # Executing the three-arm junction is not a sharp measurement of its
    # eigenspaces. If a detector could measure its positive eigenspace and
    # resolve the untouched fourth port, the other positive direction
    # would be genuinely outside the previous rational-orthogonal ray orbit.
    equal, difference, other, bypass = (1,1,1,0), (1,-1,0,0), (1,1,-2,0), I[3]
    vs = (equal,difference,other,bypass)
    need([dot(v,v) for v in vs] == [3,2,6,1] and
         all(dot(v,w) == 0 for i,v in enumerate(vs) for w in vs[:i]), "spectral refinement")
    need([mv(s,v) for v in vs] == [equal,tuple(-x for x in difference),tuple(-x for x in other),bypass],
         "not a triple-junction eigenbasis")
    plus = tuple(F(a+b,2) for row_i,row_s in zip(I,s,strict=True) for a,b in zip(row_i,row_s,strict=True))
    need(tuple(x-y for x,y in zip(plus,projection(bypass),strict=True)) == projection(equal)
         and square_class(equal) is None and square_class(other) is None,
         "new balanced triple projection was not outside the old domain")
    return {"additional_operation_not_assumed":"sharp junction eigenspace readout resolving the bypass",
            "equal_active_ray":equal, "squared_norm":3,
            "possible_full_refinement_squared_norms":[3,2,6,1],
            "status":"outside the static extension domain; does not by itself exclude every extension"}


def probe():
    frames = native_frames()
    b = tuple(tuple(F(1,2)-I[i][j] for j in range(4)) for i in range(4))
    s = junction(3)
    # External comparator, NOT a claimed native gate: a rational planar
    # rotation with denominator five. Native entries lie in Z[1/2,1/3].
    r5 = ((F(3,5),0,F(-4,5),0), (0,1,0,0), (F(4,5),0,F(3,5),0), (0,0,0,1))
    need(mm(r5,transpose(r5)) == I and any(F(x).denominator == 5 for row in r5 for x in row),
         "rational comparator")
    return {"scope":"static accessible projective bases and all subset coarse-grainings; no physical gate claim",
            "gate_extension":gate_extension(b,frames), "arithmetic_control":finite_arithmetic_audit(),
            "mixed_basis_control":mixed_basis_audit(frames,(I,b,s,mm(s,b),r5,mm(b,r5),mm(r5,s))),
            "coordinate_preparation_e3_readout":readout_cases(b,s,r5),
            "genuinely_new_readout_boundary":spectral_boundary(s),
            "boundary":"The old response extends, not uniquely selected. Small angular error alone "
                       "does not calibrate a discontinuous response. No necessity for Born weights inferred."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
