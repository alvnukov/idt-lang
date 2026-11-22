"""Classical passive-network transfer on the supplied folded-five graph.

Give every vertex one real scalar displacement in a common orientation,
mass m>0 and every existing edge an identical positive spring k, energy
k/2 sum_edges (x_u-x_v)^2. Clamp r at zero. Drive a SINGLE nonneighbor t
with a prescribed harmonic force. Only the source, clamp and adjacency
enter the stiffness calculation: no local charge, negative spring, complex
quantum amplitude, or preassigned port weights. Installation, scalar motion,
linearity, phase-sensitive measurement, ordered pin, drive and mode selection
ARE extra resources. A force injects energy into a passive carrier.

D is the clamped, dimensionless stiffness (keep full degrees on its diagonal).
For uniform m,k the scalar equations are m x''+k D x=F(t); z=m omega^2/k.
The exact identities below resolve its
four normal-mode frequencies squared as 4,8,(7 +/- sqrt(41))/2. The top
eigenspace is four-dimensional, not a unique normal-mode shape. An isolated
force e_t selects P8 e_t, the pole residue, NOT an arbitrarily picked basis.
Derivation: insert x=v f(t), Dv=lambda v in the linear equations; each
modal coordinate obeys the scalar forced oscillator. No external theorem
about a physical apparatus or quantum measurement is used.

For undamped detuned forcing the harmonic particular solution is
(F0/k)(D-zI)^-1 e_t. Transients do not decay automatically. At z=8 an
undamped cosine force from rest gives a secular top term proportional to
t sin(omega*t) P8 e_t, not a bounded steady state. Alternatively add an
equal positive viscous drag c at every free site and wait for its steady
harmonic response. With convention exp(i omega t) and delta=c omega/k,
the normalized quadrature response is i delta(D-8I+i delta I)^-1 e_t.
Complex numbers here only encode the two real drive quadratures. Its limit
as delta -> 0+ is P8 e_t. The same spatial direction follows from the
signed two-sided undamped limit (8-z)(D-zI)^-1 e_t. A static positive
force or an unfiltered free impulse gives a different result.

Only AFTER solving the passive transfer do we compare with the previous
conditional integer charge table. The mode selects signed displacement ratios;
20 times the unit-force normalized residue equals the earlier charges. Six
integer names, an overall sign/unit, charge/matter semantics and physical
identification are not predicted. This is a finite synthetic mechanism.
"""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm

from scripts.probe_marked_carrier_charge import anonymous_fixture, validate_base
from scripts.probe_two_turn_charge_atlas import atlas


def need(test, why):
    if not test:
        raise AssertionError(why)


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mix(*terms):
    return [[sum(a*q[i][j] for a, q in terms) for j in range(len(terms[0][1]))]
            for i in range(len(terms[0][1]))]


def dot(v, w):
    return sum(x*y for x, y in zip(v, w, strict=True))


def mul(a, b):
    cols = list(zip(*b, strict=True))
    return [[dot(row, col) for col in cols] for row in a]


def mv(a, v):
    return [dot(row, v) for row in a]


def solve(a, b):
    """Exact Gaussian elimination; do not invoke a singular undamped steady state."""
    m = [[F(x) for x in row] + [F(y)] for row, y in zip(a, b, strict=True)]
    for j in range(len(m)):
        p = next((p for p in range(j, len(m)) if m[p][j]), None)
        if p is None:
            raise ValueError("singular compliance")
        m[j], m[p] = m[p], m[j]
        pivot = m[j][j]
        m[j] = [x/pivot for x in m[j]]
        for i in range(len(m)):
            if i != j and m[i][j]:
                c = m[i][j]
                m[i] = [x-c*y for x, y in zip(m[i], m[j], strict=True)]
    out = [row[-1] for row in m]
    need(mv(a, out) == b, "inverse residual")
    return out


def stiffness(g, r):
    sites = sorted(g.keys() - {r})
    return sites, [[len(g[u]) if u == v else -int(v in g[u]) for v in sites] for u in sites]


def modal(d):
    ident = eye(len(d))
    zero = mix((0, ident))
    poly = mix((1, mul(d, d)), (-7, d), (2, ident))
    p8 = mul(mix((1,d), (-4,ident)), poly)  # both are 40 times their projectors
    p4 = mul(mix((1,d), (-8,ident)), poly)
    for value, proj, multiplicity in ((4, p4, 9), (8, p8, 4)):
        need(mul(d, proj) == mix((value, proj)) and mul(proj, proj) == mix((40, proj))
             and sum(proj[j][j] for j in range(len(d))) == 40*multiplicity, "mode projector/rank")
    residual = mix((40, ident), (-1, p4), (-1, p8))
    need(mul(p4, p8) == zero and mul(poly, residual) == zero, "unresolved spectrum")
    # Two residual eigenvalues obey x^2-7x+2=0 and their sum is 7. Thus
    # each of the distinct roots occurs once; the top gap is > 5/4.
    need(sum(d[i][i] for i in range(len(d))) - 4*9 - 8*4 == 7 and F(13, 2)**2 > 41,
         "residual eigenvalues/gap")
    return p4, p8


def transfers(d, tt, p8):
    ident = eye(len(d))
    e = ident[tt]
    residue = [F(row[tt], 40) for row in p8]
    tail_weight = 1-dot(residue, residue)
    gap_lower = F(5, 4)
    results = []
    gained = 0
    for delta in (F(1, 8), F(1, 32), F(1, 64)):
        for sign in (-1, 1):
            z = 8+sign*delta
            x = solve(mix((1,d), (-z,ident)), e)
            pred = [(8-z)*y for y in x]
            err2 = sum((a-b)**2 for a, b in zip(pred, residue, strict=True))
            # On the orthogonal complement, |lambda-z| >= gap_lower-delta.
            bound = tail_weight*(delta/(gap_lower-delta))**2
            need(0 < err2 <= bound, "exact two-sided detuned bound")
            if delta <= F(1,32):
                need(bound < F(1,40)**2, "fixed-scale six-level readout not certified")
            if delta == F(1,64):
                # With only relative readings, e an upper bound on coordinate
                # error, p_t=3/10 and max |p_v|=p_t, the error of 6*x_v/x_t
                # is <=12e/(3/10-e). If e<3/250 this is <1/2, so the same
                # primitive integer targets are discernible at finite detuning.
                need(bound < F(3,250)**2 and pred[tt] > 0 and
                     all(abs(6*a/pred[tt]-20*b) < F(1,2) for a,b in zip(pred,residue,strict=True)),
                     "gain-independent finite detuning control")
                gained += 1
            results.append({"z": str(z), "squared_error": str(err2), "squared_error_bound": str(bound)})
    delta = F(1, 32)
    h = mix((1,d), (-8,ident))
    y = solve(mix((1, mul(h, h)), (delta**2, ident)), e)
    re = [delta**2*a for a in y]
    im = [delta*a for a in mv(h, y)]
    need([a-delta*b for a,b in zip(mv(h,re),im,strict=True)] == [0]*len(d) and
         [a+delta*b for a,b in zip(mv(h,im),re,strict=True)] == [delta*t for t in e],
         "complex compliance failed the two real quadrature equations")
    err2 = sum((a-b)**2+c*c for a,b,c in zip(re,residue,im,strict=True))
    bound = tail_weight*delta**2/(gap_lower**2+delta**2)
    need(0 < err2 <= bound < F(1,40)**2, "damped resonance six-level separation bound")
    dc = solve(d,e)
    need(min(dc) > 0 and min(residue) < 0, "static force mimics resonant signs")
    return {"undamped_particular": results, "certified_both_gain_free_ratios_at_detuning_1_over_64":gained == 2,
            "uniform_drag": {"delta": str(delta), "squared_error": str(err2),
            "squared_error_bound": str(bound)}, "static_free_site_range": [str(min(dc)), str(max(dc))]}


def changed_spring(g, r, t, sites, d, p8):
    # One positive extra spring in parallel with an existing edge: D' = D+bb^T.
    # P8 b != 0 => any vector in ker(D'-8I) is orthogonal to b (multiply
    # its equation by P8), hence that kernel is exactly old E8 intersect b^perp.
    # Conversely P8 b has Rayleigh quotient >8 for D', so its highest
    # frequency increases even for arbitrarily small positive stiffening.
    tt = sites.index(t)
    v = [F(row[tt], 40) for row in p8]
    found = {}
    for u, w in combinations(sorted(g), 2):
        if w not in g[u]:
            continue
        b = [int(s == u)-int(s == w) for s in sites]
        pb = [F(q, 40) for q in mv(p8, b)]
        weight = dot(pb, pb)
        if not weight:
            continue
        jump = dot(b, v)
        kind = "differential" if jump else "equal_displacement"
        if kind in found:
            continue
        update = [[a*c for c in b] for a in b]
        perturbed = mix((1, d), (1, update))
        remaining = [a-jump*c/weight for a,c in zip(v,pb,strict=True)]
        need(dot(b, pb) == weight and mv(perturbed, remaining) == [8*q for q in remaining] and
             dot(pb, mv(perturbed, pb)) > 8*weight and (remaining == v) == (jump == 0),
             "positive stiffness perturbation")
        dv = mv(perturbed, v)
        need(all(dv[i]*v[tt] == dv[tt]*v[i] for i in range(len(v))) == (jump == 0),
             "was the old measured pattern still an eigenvector?")
        found[kind] = {"on_clamp": r in (u,w), "on_drive": t in (u,w), "old_mode_jump": str(jump),
                       "remaining_rank_at_eight": 3, "old_pole_residue_unchanged": remaining == v,
                       "rayleigh_lower_bound_new_top": str(dot(pb, mv(perturbed,pb))/weight)}
    need(len(found) == 2, "missing stiffening controls")
    return found


def probe():
    g = anonymous_fixture()
    validate_base(g)
    order = sorted(g)
    fields = {}
    sample = {}
    for r in order:
        sites, d = stiffness(g,r)
        p4,p8 = modal(d)
        for shell in (g[r], set(sites)-g[r]):
            need(mv(p8,[int(v in shell) for v in sites]) == [0]*len(sites), "uniform shell drive has top overlap")
        for t in set(sites)-g[r]:
            tt = sites.index(t)
            response = dict(zip(sites, (F(row[tt],40) for row in p8), strict=True))
            response[r] = F(0)
            fields[r,t] = tuple(response[x] for x in order)
            if not sample and t == min(set(sites)-g[r]):
                # A delta-velocity impulse launches modes with amplitudes
                # proportional to P_lambda e_t, not the top projector alone.
                w4,w8 = F(p4[tt][tt],40), F(p8[tt][tt],40)
                rest, first_moment = 1-w4-w8, d[tt][tt]-4*w4-8*w8
                need(w4>0 and w8>0 and rest>0 and (2*first_moment-7*rest)**2 < 41*rest**2,
                     "one of the two remaining impulse weights vanishes")
                sample = {"residue_histogram": dict(sorted(Counter(str(x) for x in response.values()).items())),
                          "impulse_squared_projection_weights": {"four": str(w4), "eight": str(w8),
                          "remaining_pair_sum": str(rest), "remaining_pair_first_moment": str(first_moment)},
                          "frequency_controls": transfers(d, tt, p8), "stiffening_one_edge": changed_spring(
                              g, r, t, sites, d, p8)}
    # Independent comparison step: no prior integer table enters the network,
    # eigenprojector, drive location within each frame, or frequency calculation.
    vs, _, _, charges, _, _ = atlas(g)
    need(vs == order and fields.keys() == charges.keys(), "independent frame indexing mismatch")
    for key, word in fields.items():
        unit = lcm(*(y.denominator for y in word))
        integer = tuple(int(unit*y) for y in word)
        divisor = gcd(*integer)
        need(unit == 20 and divisor == 1 and integer == charges[key],
             "native least integer ratios fail the independent six-value comparison")
    return {"scope":"classical scalar positive equal-spring/equal-mass network; ordered clamp/drive and "
                    "phase-sensitive resonance selection supplied, no charge or physical confirmation",
            "frames_checked":len(fields), "signed_vertex_comparisons":len(fields)*len(order),
            "dimensionless_squared_frequencies":[["(7-sqrt(41))/2",1],["4",9],["(7+sqrt(41))/2",1],["8",4]],
            "top_physical_frequency":"sqrt(8*k/m)", "normalized_top_residue":"previous even-sheet q / 20",
            "uniform_shell_drives_with_zero_top_projection":2*len(order), "representative":sample}


if __name__ == "__main__":
    print(json.dumps(probe(),separators=(",",":")))
