"""A discontinuous, normalized four-mode response on the native dense orbit.

Supply the six real Peres--Mermin joint frames, a spectator-preserving
equal three-port junction S = 2J/3 - I on any triple, and signed Pauli
permutations. Let G consist of finite words. The ring Z_(2) consists of
rationals with odd denominator. Each U in G is orthogonal over this ring
and reduces mod 2 to a permutation: the junction reduces to identity.
Every initial ray has a representative v with k = 1, 2 or 4 entries +/-1
and other entries zero. Thus w=Uv has squared norm k and exactly k odd
entries. Put p_j(ray) = 1/k on the odd positions of w and zero elsewhere.
Clearing its odd denominator and dividing by the common (odd) gcd preserves
the support; sign is immaterial. This is intrinsic to the ray.

All-word shared-effect proof (the finite checks below are cross-controls):
for P=ww^t/k, (4P)_jj belongs to Z_(2) and reduces modulo 8 to 4p_j(P).
Odd squares are 1 mod 8; even squares are 0 mod 4; if k=4 all four entries
are odd. In ANY orthogonal basis of accessible rays, even if assembled from
different gate words, sum P = I. For each j the nonnegative integer sum of
4p_j is therefore 4 mod 8 and hence at least 4. The four such sums total 16
since each ray has total weight one across the four j. Every sum is thus 4.
For any subset Q of a complete basis, its summed 4p_j lies in [0,4] and is
uniquely determined by (4Q)_jj mod 8. Equal projectors have equal weights
at every rank, regardless of refinement. This covers all partitions of an
allowed full basis. It does not give instrument updates, arbitrary POVMs,
an extension to all real projectors, or Born probabilities.

Density does not supply an operational continuity axiom. Separately from
any proof about closure of all of G, the exact two-plane rotation below
has a native orbit approaching a native ray with a different response.
Meyer, quant-ph/9905080, gives a related coloring in three real dimensions
on the rational unit sphere, not this four-dimensional probability model.
The values here are fractional; they do not remove the Peres--Mermin
obstruction to simultaneous deterministic eigenvalue assignments. Nor do
these four preparations and their mixtures supply a certain eigenpreparation
for a two- or four-support ray: the maximum probability is 1/2 or 1/4.
"""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm

from scripts.probe_folded_carrier_parity_contexts import (
    PAULIS,
    dense,
    grid_contexts,
    p_mul,
)


def need(test, message):
    if not test:
        raise ArithmeticError(message)


I = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def dot(x, y):
    return sum(a*b for a, b in zip(x, y, strict=True))


def mv(m, x):
    return tuple(dot(row, x) for row in m)


def mm(m, n):
    cols = tuple(zip(*n, strict=True))
    return tuple(tuple(dot(row, col) for col in cols) for row in m)


def residue(x, modulus):
    x = F(x)
    need(x.denominator % 2 == 1, "even denominator outside residue ring")
    return (x.numerator * pow(x.denominator, -1, modulus)) % modulus


def ray(x):
    scale = lcm(*(F(v).denominator for v in x))
    nums = tuple(int(scale*v) for v in x)
    g = gcd(*nums)
    need(g != 0, "zero ray")
    sign = 1 if next(a for a in nums if a) > 0 else -1
    return tuple(sign*a//g for a in nums)


def projection(x):
    n = dot(x, x)
    return tuple(F(a*b, n) for a in x for b in x)


def weights4(x):
    bits = tuple(a % 2 for a in x)
    k = sum(bits)
    need(k in (1, 2, 4), "ray outside specified family")
    return tuple((4//k)*b for b in bits)


def native_frames():
    x, z, y, w = PAULIS
    a, b = p_mul(x, w), p_mul(z, y)
    grid = ((x, y, p_mul(x, y)), (w, z, p_mul(z, w)), (a, b, p_mul(a, b)))
    candidates = sorted({ray(v) for v in product((-1, 0, 1), repeat=4) if dot(v, v) in (1, 2, 4)})
    frames = []
    for triple in grid_contexts(grid):
        selected = tuple(v for v in candidates if
                         all(mv(dense(op), v) in (v, tuple(-i for i in v)) for op in triple))
        need(len(selected) == 4 and all(dot(l, r) == 0 for l, r in combinations(selected, 2)),
             "canonical native Pauli frame")
        frames.append(selected)
    rays = set().union(*frames)
    need(len(rays) == 24 and len(set(frames)) == 6 and rays == set(candidates),
         "six frames did not yield the native 24 rays")
    # The coordinate axes plus e_i+e_j for each pair already determine any
    # real symmetric trace readout, through its diagonal and cross terms.
    need(set(I) <= rays and all(tuple(a+b for a,b in zip(i,j,strict=True)) in rays
                                for i,j in combinations(I,2)), "tomographic rays missing")
    return tuple(frames)


def junction(spectator):
    return tuple(tuple(F(i == j) if spectator in (i, j) else F(2, 3) - int(i == j)
                       for j in range(4)) for i in range(4))


def permutation_mod2(u):
    a = tuple(tuple(residue(x, 2) for x in row) for row in u)
    need(all(sum(row) == 1 for row in (*a, *zip(*a, strict=True))), "not a permutation modulo two")
    return a


def coarse_audit(frames, gates):
    base_rays = set().union(*frames)
    matrices = (I, *gates, mm(gates[0], gates[1]), mm(gates[4], gates[1]))
    generated, sample_rays = set(), set()
    for u in matrices:
        per = permutation_mod2(u)
        need(mm(u, tuple(zip(*u, strict=True))) == I, "control gate not orthogonal")
        for v in base_rays:
            t = ray(mv(u, v))
            need(weights4(t) == mv(per, weights4(v)), "transport did not permute residue weights")
            sample_rays.add(t)
        generated.update(tuple(sorted(ray(mv(u,v)) for v in f)) for f in frames)

    rays = sorted(sample_rays)
    orth = {v: {w for w in rays if w > v and dot(v,w) == 0} for v in rays}
    bases = {(a,b,c,d) for a in rays for b in orth[a] for c in orth[a] & orth[b]
             for d in orth[a] & orth[b] & orth[c]}
    need(generated < bases, "did not test any additional mixed orthogonal frames")
    p = {v: projection(v) for v in rays}
    h = {v: weights4(v) for v in rays}
    for v in base_rays:
        need(all(4*p[v][5*j] == h[v][j] for j in range(4)), "Born calibration on native base")
        need(max(h[v]) == 4//sum(a != 0 for a in v), "native sharp preparation boundary")

    zero, identity = (F(0),)*16, tuple(map(F, sum(I, ())))
    seen, counts, repeated, native_halves = {}, Counter(), Counter(), set()
    for f in bases:
        # Each of the 16 subsets is included; that covers each block of
        # every 2-, 3- or 4-outcome grouping, not merely the Pauli halves.
        effects, weights = [zero], [(0,)*4]
        for v in f:
            effects += [tuple(a+b for a,b in zip(q,p[v],strict=True)) for q in effects]
            weights += [tuple(a+b for a,b in zip(q,h[v],strict=True)) for q in weights]
        need(effects[-1] == identity and weights[-1] == (4,)*4, "un-normalized full frame")
        for mask, (q, wt) in enumerate(zip(effects, weights, strict=True)):
            rank = mask.bit_count()
            need(all(0 <= z <= 4 for z in wt) and all(residue(4*q[5*j],8) == wt[j] for j in range(4)),
                 "coarsening residue differs from summed ray weights")
            if rank == 2 and f in generated:
                # Here Q is a transported (I +/- A)/2, A a native symmetric
                # Pauli involution. This is a stricter check than mod eight
                # at general rank: only 0, 1/2, 1 occur at these halves.
                need(all(z in (0,2,4) and residue(2*q[5*j],4) == z//2 for j,z in enumerate(wt)),
                     "shared native half-projector residue")
                native_halves.add(q)
            if q in seen:
                repeated[rank] += 1
                need(seen[q] == wt, "identical effect has inconsistent response")
            else:
                seen[q] = wt
                counts[rank] += 1
    need(all(repeated[k] for k in range(5)), "no shared-effect control at some rank")
    return {"sample_gate_words":len(matrices), "sample_rays":len(rays),
            "transported_native_frames":len(generated), "all_sample_orthogonal_bases":len(bases),
            "additional_orthogonal_bases":len(bases-generated), "distinct_native_halves":len(native_halves),
            "distinct_sample_effects_by_rank":dict(counts), "repeat_encounters_by_rank":dict(repeated)}


def discontinuity(frames, s):
    # D is the native diagonal (+,+,-,-). S and DSD are half-turns in
    # the first three coordinates, with axes (1,1,+/-1). Their product
    # rotates span((1,1,0,0), e_3) and fixes the other two directions.
    d = dense(PAULIS[3])
    r = mm(mm(s, d), mm(s, d))
    e, target, axis = I[2], (1,1,0,0), (1,-1,0,0)
    need(d == tuple(tuple((1 if i < 2 else -1)*I[i][j] for j in range(4)) for i in range(4))
         and target in set().union(*frames), "rotation control coordinates")
    need(mv(r, axis) == axis and mv(r,I[3]) == I[3] and permutation_mod2(r) == I,
         "wrong fixed directions or parity")
    # Confirm the actual two-by-two map in a non-normalized orthogonal
    # basis, including determinant +1 rather than just one diagonal entry.
    columns = [(F(dot(target,y),2), dot(e,y)) for y in (mv(r,target),mv(r,e))]
    (a,c), (b,f) = columns
    need(a*f-b*c == 1 and a == f == F(-7,9), "rotation angle or orientation")
    # A root of unity plus its inverse is an algebraic integer; the
    # rational trace 2cos(theta)=-14/9 is not an integer. Thus powers are
    # dense on this circle. They approach the target ray whose p_3 is 0,
    # whereas the entire orbit of e_3 has p_3=1.
    need(weights4(e)[2] == 4 and weights4(target)[2] == 0, "incompatible limiting probabilities")
    v = e
    for n in range(1, 2001):
        v = mv(r,v)
        if dot(v,target)**2/dot(target,target) > F(9999,10000):
            break
    else:
        raise ArithmeticError("no finite near-ray cross-control")
    need(dot(v,v) == 1 and weights4(ray(v))[2] == 4, "finite discontinuity control")
    return {"rotation_cosine":"-7/9", "irrational_angle_in_units_of_pi":True,
            "example_power":n, "squared_overlap_strictly_greater_than":"9999/10000",
            "power_ray_p3":1, "limit_ray_p3":0}


def probe():
    frames = native_frames()
    stars = tuple(junction(j) for j in range(4))
    signed_perms = tuple(dense(p) for p in PAULIS)
    for s in stars:
        need(mm(s,s) == I and permutation_mod2(s) == I, "balanced triple not an involution in the kernel")
    audit = coarse_audit(frames, (*stars, *signed_perms))
    # One exact, prospective experiment, independent of the near-ray
    # search. Use the coordinate preparation e_3, then compare all four
    # outputs after either identity or ONE balanced junction on modes
    # 1,2,3. Residue and Born match every original native frame, not here.
    star = stars[3]
    queries = [mv(star,e) for e in I]
    born = [F(v[2])**2 for v in queries]
    alt = [F(weights4(ray(v))[2],4) for v in queries]
    need(born == [F(4,9),F(4,9),F(1,9),0] and alt == [0,0,1,0], "held-out junction readout")
    # A possible count comparison, not a tolerance in angle. Randomize
    # between identity and this predeclared one-star arm after preparation;
    # retain all attempts including failures. If at most eta of trials in
    # the arm are unconstrained and the rest obey the exact stated law, the
    # residue lower bound is 1-eta, the Born upper bound (1-eta)/9+eta.
    # They are disjoint below the threshold and only touch at equality.
    # Gate-word fidelity, stationarity/randomization, rates of omissions and
    # statistical coverage require independent evidence. Small geometric
    # misalignment is NOT a uniform error bound for a discontinuous law.
    touch = (alt[2]-born[2])/(alt[2]+1-born[2])
    need(touch == F(8,17) and (1-touch)*alt[2] == (1-touch)*born[2]+touch,
         "unconstrained-attempt contamination control")
    return {"scope":"static probabilities on accessible rays, their complete bases and coarse-grainings",
            "native_joint_frames":len(frames), "native_rays":len(set().union(*frames)),
            "coarsening_control":audit, "discontinuity":discontinuity(frames,star),
            "one_star_reference_Born_e3":list(map(str,born)), "one_star_residue_p3":list(map(str,alt)),
            "third_event_population_bounds_disjoint_if_unconstrained_fraction_strictly_below":str(touch),
            "not_supplied":["continuous responses", "sequential instrument", "physical junction calibration",
                            "empirical choice of either law", "general quantum reconstruction"]}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
