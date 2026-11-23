"""Search additive readouts rather than fitting a Born-like exponent.

Take d equivalent scalar ports over the rationals. The transition is
linear, commutes with all wire permutations, fixes uniform inputs, is
its own inverse and is not the identity. Off-diagonal matrix entries
therefore agree, as do diagonal entries, so it is aI+bJ. The uniform
line requires a+db=1, the difference space a^2=1. This forces
T=2J/d-I for d>=2. No orthogonal metric was used to impose these
requirements; linearity, signed scalar records, uniform-mode retention,
stationary memory-free operation and reciprocity WERE imposed.

Now ask for an additive per-port scalar f with sum f unchanged on this
contact. At d=4, feed (t+2u,t,t,t); output (t-u,t+u,t+u,t+u). Hence all
third forward differences vanish. On the integers f is quadratic plus
linear plus constant. On Q, restriction to every 1/q lattice gives
the same rational-coordinate polynomial after matching values at -1,0,1.
The coefficients can be REAL and no continuity or prior power law is
needed. Conversely constant, linear and squared functions are conserved
on every port by direct summation. The finite searches below are
independent checks, not a machine proof on all rationals. Imposing dark
vacuum and insensitive overall sign selects only the square, up to scale.
This does not explain intrinsic single events or why this calibratable
per-port separability or scalar wave law applies to nature.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import comb


def need(x, why):
    if not x:
        raise ArithmeticError(why)


def scatter(xs):
    a = F(2,len(xs))*sum(xs)
    return tuple(a-x for x in xs)


def rank(rows):
    pivots = {}
    for row in rows:
        v = list(map(F,row))
        for i,a in enumerate(v):
            if a:
                if i not in pivots:
                    pivots[i] = [b/a for b in v]
                    break
                for k,b in enumerate(pivots[i]):
                    v[k] -= a*b
    return len(pivots)


def census(d, values, transform):
    rows = set()
    eligible = moved = 0
    alphabet = set(values)
    for xs in combinations_with_replacement(values,d):
        out = transform(xs)
        if not set(out) <= alphabet:
            continue
        eligible += 1
        need(tuple(transform(out)) == xs, "not reversible on submitted set")
        diff = Counter(xs)
        diff.subtract(out)
        row = tuple(diff[t] for t in values)
        if any(row):
            moved += 1
            rows.add(row if next(t for t in row if t)>0 else tuple(-x for x in row))
    return rows,eligible,moved


def material():
    # Distinct inputs on a finite window, with nonintegral/out-of-window
    # successors left unsupported, NOT rounded, clipped or taken modulo.
    alphabet = tuple(range(-5,6))
    report = {}
    for d in (2,3,4):
        rows,seen,changed = census(d,alphabet,scatter)
        functions = [[1]*len(alphabet), list(alphabet), [x*x for x in alphabet]]
        if d==3:
            functions.append([int(x%2==1) for x in alphabet])
        need(all(sum(x*y for x,y in zip(r,f,strict=True))==0 for r in rows for f in functions),
             "expected invariant lost")
        dim = len(alphabet)-rank(rows)
        need(dim == {2:len(alphabet),3:4,4:3}[d], "wrong kernel dimension")
        if d>2:
            need(rank(functions)==dim, "basis not independent")
        report[d] = {"eligible_unordered_inputs":seen,"nontrivial_multiset_changes":changed,"nullity":dim}
    for p in (3,5,7,11):
        # Finite cyclic amplitude is a DIFFERENT model. f still real, not
        # a flux measured only modulo p. No nonconstant additive real f
        # survives a cyclic third-difference constraint.
        b = (2*pow(4,-1,p))%p
        def modular(s,b=b,p=p):
            return tuple((b*sum(s)-x)%p for x in s)
        rows,_,_ = census(4,tuple(range(p)),modular)
        need(p-rank(rows)==1, "spurious real readout on finite residue system")
    return report


def differences():
    for q in (1,2,3,5,7):
        for a,b in product(range(-4,5), repeat=2):
            t,u = F(a,q),F(b,q)
            src = (t+2*u,t,t,t)
            need(scatter(src) == (t-u,t+u,t+u,t+u), "missing constant third difference")
            for xs in (src, (t+3*u,t,t)):
                ys = scatter(xs)
                need(scatter(ys)==xs and sum(xs)==sum(ys) and sum(x*x for x in xs)==sum(y*y for y in ys),
                     "source operations do not conserve spanning functions")
    # For three integer lanes an alternating part is real: stable integer
    # moves preserve each input's parity. At half mesh the third difference
    # is already forced: (z²−1)^3 = (z+1)^2 (z−1)^3(z+1).
    # K=(-1,2,0,-2,1) is the three-arm translated contact at spacing 1/2.
    k = (-1,2,0,-2,1)
    result = [0]*7
    for i,x in enumerate(k):
        for j,y in enumerate((1,2,1)):
            result[i+j] += x*y
    need(result == [-1,0,3,0,-3,0,1], "three-port half-mesh implication")
    # A nonlinear reciprocal anonymous competitor equals -x on zero-sum
    # inputs and is identity elsewhere. Every even f, including |x|, then
    # survives. A simple even calibration plus reversibility is not enough.
    conditional = lambda z: tuple(-x for x in z) if not sum(z) else tuple(z)
    for z in product(range(-2,3),repeat=4):
        need(conditional(conditional(z))==z and sum(map(abs,conditional(z)))==sum(map(abs,z)), "nonlinear control")
    need(conditional((1,-1,0,0))!=(1,-1,0,0) and sum(map(abs,scatter((2,0,0,0))))==4, "ineffective control")
    return {"three_port_integer_parity_survives":True,"rational_half_mesh_removes_parity_as_an_additive_wall":True,
            "four_port_full_integer_lattice":"not a total integer map: one localized unit gives half units",
            "nonlinear_exchange":"all even functions can survive"}


def tolerance():
    # An absolute local imbalance epsilon bounds the third difference, not
    # the global error by the same epsilon independently of the amplitude.
    e = F(1,100)
    err = {n:F(0) for n in (-1,0,1)}
    for n in range(2,13):
        err[n] = 3*err[n-1]-3*err[n-2]+err[n-3]+e
        need(err[n] == comb(n+1,3)*e, "third difference accumulation")
    return {"calibrated_integer_sites":[-1,0,1], "unit_step_uniform_imbalance":str(e),
            "worst_error_at_site_12_in_raw_units":str(err[12]), "growth":"binomial(n+1,3) times local error"}


def probe():
    return {"integer_window":material(),"rational_and_nonlinear_controls":differences(),"robustness":tolerance(),
            "not_assumed_by_signed_conservation":"outcome actualization, detector noncontextuality, or physical amplitudes"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),sort_keys=True))
