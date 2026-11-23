"""Can all accessible contextual tests miss a negative real-state direction?

Use the existing real 4-mode representation of the MARKED central lift, not
the unsigned carrier alone. Even its complete six-context probability tables
and arbitrary finite sequences of the native projectors need not ensure the
reconstructed trace-one quadratic form is positive. Give an explicit robust
counterexample and an additional three-port real scattering operation that
detects it without any fitted parameter.

Closure under rational linear combinations is a representation choice,
not a property proved for an arbitrary experimental readout. Density of
real rotation words uses the ordinary real topology and unbounded word
length. Only a CONTINUOUS quadratic assignment nonnegative on that dense
orbit is thereby nonnegative on the whole sphere. These tests do not
derive Hilbert amplitudes, the Born rule or the probability of a click.
"""

from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_folded_carrier_parity_contexts import (
    I4,
    combine,
    dense,
    dense_mul,
    p_mul,
    real_mapping,
)

I = dense(I4)
ZERO = combine((0, I))


def need(value, why):
    if not value:
        raise ArithmeticError(why)


def tr(a):
    return sum(a[i][i] for i in range(4))


def trans(a):
    return tuple(zip(*a, strict=True))


def scale(k, a):
    return combine((k,a))


def pairing(a, b):
    return sum(a[i][j]*b[j][i] for i in range(4) for j in range(4))


def outer(v):
    return tuple(tuple(a*b for b in v) for a in v)


def rank(rows):
    pivots = {}
    for row in rows:
        v = list(map(F,row))
        for i, a in enumerate(v):
            # list entries change during reduction; enumerate fetches the
            # current entry at the next iteration.
            if a:
                if i not in pivots:
                    pivots[i] = [x/a for x in v]
                    break
                for j, b in enumerate(pivots[i]):
                    v[j] -= a*b
    return len(pivots)


def frames():
    mapping, _ = real_mapping()
    words = {p for (x,s),p in mapping.items() if x and not s and p_mul(p,p) == I4}
    effects = {scale(F(1,2),combine((1,I),(s,dense(w)))) for w in words for s in (-1,1)}
    bases = set()
    for a, b in combinations(words, 2):
        if p_mul(a,b) == p_mul(b,a):
            am, bm, ab = dense(a), dense(b), dense(p_mul(a,b))
            pack = frozenset(scale(F(1,4), combine((1,I),(s,am),(t,bm),(s*t,ab)))
                             for s,t in product((-1,1), repeat=2))
            need(len(pack) == 4 and combine(*((1,p) for p in pack)) == I, "incomplete context")
            bases.add(pack)
    rays = set().union(*bases)
    need((len(words),len(effects),len(bases),len(rays)) == (9,18,6,24), "marked generation")
    need(all(tr(p) == 1 and trans(p) == p and dense_mul(p,p) == p for p in rays), "not rank one")
    need(rank([[p[i][j] for i in range(4) for j in range(i,4)] for p in rays]) == 10,
         "native probabilities fail to identify a real symmetric form")
    return set(map(dense,mapping.values())), effects, bases, rays


def native_closure(ops, effects, rays):
    # In backwards order, a tested branch pulls a terminal effect P through
    # E to EPE, or through a signed gate to U^T P U. Starting I is already a
    # positive sum of native rank-one projectors. The two closure checks
    # imply nonnegative branch weights for ANY finite adaptive word of these
    # ideal instruments, not merely for sequences up to a chosen length.
    scales = set()
    for e,p in product(effects|rays,rays):
        q = dense_mul(e,dense_mul(p,e))
        w = tr(q)
        need(w >= 0 and ((q == ZERO) if not w else scale(1/w,q) in rays), "left finite native cone")
        scales.add(w)
    for u,p in product(ops,rays):
        need(dense_mul(trans(u),dense_mul(p,u)) in rays, "signed operation escaped native cone")
    return sorted(map(str,scales))


def junction(legs):
    legs = set(legs)
    return tuple(tuple((F(2,len(legs))-int(i==j) if i in legs and j in legs else int(i==j))
                       for j in range(4)) for i in range(4))


def state_wall(bases,rays):
    s = junction((0,1,2))
    v = tuple(row[0] for row in s)
    need(v == (F(-1,3), F(2,3), F(2,3), 0) and dense_mul(s,s) == I, "three-arm balance")
    target = outer(v)
    obs = [pairing(target,p) for p in rays]
    need(max(obs) == F(8,9) and target not in rays, "junction did not produce a fresh direction")
    # Alpha is a rational interior witness chosen from 1 < alpha < 1/max.
    # This is a constructed adversary, not an empirical constant.
    alpha = F(13,12)
    rho = scale(1/(4-alpha),combine((1,I),(-alpha,target)))
    scores = [pairing(rho,p) for p in rays]
    need(tr(rho) == 1 and min(scores) == F(4,315) and all(sum(pairing(rho,p) for p in b) == 1 for b in bases),
         "invalid native probabilities")
    need(pairing(rho,target) == F(-1,35), "wrong negative count after one junction")
    return {"min_native_probability":str(min(scores)), "max_native_probability":str(max(scores)),
            "max_native_overlap_with_missed_direction":str(max(obs)), "after_one_three_arm_junction":"-1/35"}


def axis_checks(ops):
    # Within any chosen three channels S is a half-turn about (1,1,1).
    # The available diagonal signs conjugate S to half-turns about other
    # sign vectors. Product of two is a rotation fixing their cross product,
    # with 2 cos(theta) = -14/9, not an integer. A root of unity plus
    # its inverse would be an algebraic integer, so this rotation's powers
    # are dense in its circle. Verify three independent circle axes on
    # each triple by exact constant-vector tests (not numeric angle fits).
    ds = [u for u in ops if all(not u[i][j] for i in range(4) for j in range(4) if i != j)]
    axes = {}
    for legs in combinations(range(4),3):
        s = junction(legs)
        found = set()
        for d in ds:
            # Opposite axes describe the same half-turn.
            x,y,z = (d[i][i] for i in legs)
            a = (z-y,x-z,y-x)
            if not any(a):
                continue
            # Signed-conjugated copies rotate about d'(1,1,1) and
            # d'd(1,1,1) in these three slots. Their axes span R^3.
            rot = dense_mul(s,dense_mul(d,dense_mul(s,d)))
            need(tr(rot)-2 == F(-14,9), "irrational-circle trace mismatch")
            for seed in ds:
                c = dense_mul(seed,dense_mul(rot,seed))
                v = [0]*4
                for i,t in zip(legs,a,strict=True):
                    v[i] = seed[i][i]*t
                need(all(sum(c[i][k]*v[k] for k in range(4)) == v[i] for i in range(4)), "wrong rotation axis")
                found.add(tuple(v[i] for i in legs))
        need(rank(found) == 3, "circle Lie directions do not span so(3)")
        axes[str(legs)] = len(found)
    # The closed subgroup thereby contains SO(3) on each triple (in the
    # ordinary topology of matrices). Coordinate-plane rotations from these
    # subgroups generate SO(4). Without any signed operation, each junction
    # instead preserves one common uniform line, even with wire permutations.
    need(all(all(sum(row) == 1 for row in junction(legs)) for legs in combinations(range(4),3)),
         "unsigned-control uniform mode")
    return {"three_dimensional_axis_spans":axes, "twice_cosine":"-14/9",
            "unsigned_only_escape":"all permutations and real junctions fix the uniform vector"}


def probe():
    ops, effects, bases, rays = frames()
    return {"native_effects_and_rays":[len(effects),len(rays)], "closure_weights":native_closure(ops,effects,rays),
            "state":state_wall(bases,rays), "rotations":axis_checks(ops),
            "scope":"linear waves, continuous real quadratic readout and real frame closure are bridges, not primitives"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), sort_keys=True))
