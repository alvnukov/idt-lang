"""How much of an exclusive final output could already be permanently recorded?

Input: unconditional normalized rows p_c for later controlled continuations,
on ONE common preparation population. Before c is supplied, let a_i be the
mass of trials with an irrevocable, already readable fine-port promise i.
These promises must remain valid when c is externally forced and must not
change the reference dynamics. Thus a_i<=min_c p_c(i). Equality in total
is attainable in abstract record models: reserve the componentwise minima
and complete only the remainder after c. This is an existence statement
about causal probability tables, not an implementation of a passive meter.
Latent proposals, coarse facts, and genuinely disturbing earlier instruments
are different contracts. No conclusion about all hidden states follows.

On a tree the minima at each node run over its descendant leaves. They
increase componentwise along a path; reserve just their increments among
the still-undecided trials. All node optima can be attained simultaneously.
This does not require a uniform mixture of contexts. Interventional rows,
or independently assigned settings conditional on the supplied past, are
essential: observational conditioning on a leaked/adaptive future setting
is not equivalent. Count every starting trial, not just cases still running
when the setting was assigned. The construction uses a supplied common
uniform ticket independent of future settings; it does not derive one.

Here every row is a PRESCRIBED squared-amplitude target. Split one input
with S3 into three banks of weights (1,4,4)/9. In each bank apply S4,
optionally flip two signs, then recombine through the SAME S4. The late
control changes relative signs, not output labels. For each intact bank,
interference selects exit 0 or 1. An actual early measurement removing
those relative signs changes the experiment; see the backaction control.

Earlier IDT delayed-choice fixtures compare open/closed readouts of the
same preparation; these multi-context and tree capacity bounds ask a
different question. Experimental comparator only: Jacques et al.,
https://doi.org/10.1126/science.1136303 (authors: arXiv:quant-ph/0610241)
report closed-mode visibility 0.94, an open-mode which-way calibration above
0.99 with one path blocked, and separately anticorrelation 0.12 +/- 0.01. Neither those
numbers nor their entry/choice separation measures an early fine-port
fraction in the circuit below or calibrates our noise budgets.
"""

import json
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm


def need(ok,msg):
    if not ok:
        raise ArithmeticError(msg)


def junction(x,ports):
    need(len(ports)==len(set(ports)) and all(0<=j<len(x) for j in ports),"junction wiring")
    common = F(2,len(ports))*sum(x[j] for j in ports)
    return tuple(common-v if j in ports else v for j,v in enumerate(x))


BANKS = tuple(tuple(range(4*j,4*j+4)) for j in range(3))
W = (F(1,9),F(4,9),F(4,9))


def circuit_rows():
    start = (1,)+(0,)*11
    split = junction(start,(0,4,8))
    need(tuple(split[4*j] for j in range(3)) == (F(-1,3),F(2,3),F(2,3)), "initial S3")
    prefix = split
    for bank in BANKS:
        prefix = junction(prefix,bank)
    rows = {}
    for bits in product((0,1),repeat=3):
        x = prefix
        for b,bank in zip(bits,BANKS,strict=True):
            if b:
                x = tuple(-v if k in bank[:2] else v for k,v in enumerate(x))
            x = junction(x,bank)
        p = tuple(v*v for v in x)
        need(sum(p)==1 and
             all(p[4*j+k]==(W[j] if k==bits[j] else 0) for j in range(3) for k in range(4)),
             "rational native phase recombination did not give target row")
        rows[bits] = p
    return rows


def minimum(rows):
    rows = tuple(rows)
    need(rows and all(len(p)==len(rows[0]) and all(z>=0 for z in p) and sum(p)==1 for p in rows),
         "unconditional normalized common-alphabet rows required")
    return tuple(map(min,zip(*rows,strict=True)))


def distance(p,q):
    return sum(abs(a-b) for a,b in zip(p,q,strict=True))/2


def deficit(m,p):
    return sum(max(0,a-b) for a,b in zip(m,p,strict=True))


def attain_in_tv_ball(m,p):
    """Nearest distribution q>=m to p. Cost is the total positive deficit.

    Necessity: q must add each positive (m_i-p_i). Sufficiency: take
    that total from surplus cells. There is enough because sum(m)<=1.
    Thus the sharp general robust maximum is max sum(m) subject to m>=0,
    sum(m)<=1, deficit(m,p_c)<=epsilon_c for all c. Equivalently, these
    are finitely many linear inequalities (one per subset per row).
    """
    need(len(m)==len(p) and min(m)>=0 and sum(m)<=1 and min(p)>=0 and sum(p)==1,
         "invalid early-record mass or reference row")
    q = [max(a,b) for a,b in zip(m,p,strict=True)]
    cost = rem = deficit(m,p)
    for j in range(len(q)):
        take = min(rem,q[j]-m[j])
        q[j] -= take
        rem -= take
    need(rem==0 and sum(q)==1 and distance(q,p)==cost and all(x>=y for x,y in zip(q,m,strict=True)),
         "TV sharpness certificate")
    return tuple(q)


def proposal_error(m,p):
    """A DIFFERENT relaxation: exact final p, but fallible early proposals.

    This is not a passive permanent-label guarantee. The minimum joint
    mass of wrong proposals per ORIGINAL attempt is precisely deficit(m,p)
    (not a conditional rate just among the early proposals).
    """
    diag = [min(a,b) for a,b in zip(m,p,strict=True)]
    remaining = [b-c for b,c in zip(p,diag,strict=True)]
    wrong = F(0)
    for i,a in enumerate(m):
        excess = a-diag[i]
        for j in range(len(p)):
            take = min(remaining[j],excess)
            need(take==0 or j!=i, "misclassified early agreement")
            remaining[j] -= take
            excess -= take
            wrong += take
        need(excess==0, "insufficient final mass for early proposals")
    need(sum(remaining)==1-sum(m) and wrong==deficit(m,p), "early error coupling")
    return wrong


def tree_realization(leaves):
    """Single common ticket; no decisions use an unannounced branch bit."""
    den = lcm(*(F(v).denominator for p in leaves.values() for v in p))
    frontier = {(): (None,)*den}
    reached = {}
    while frontier:
        path,prev = frontier.popitem()
        suffixes = {h:p for h,p in leaves.items() if h[:len(path)]==path}
        m = minimum(suffixes.values())
        target = [int(v*den) for v in m]
        now = list(prev)
        for i,t in enumerate(target):
            need(t>=now.count(i),"would retract a previously observable label")
            for _ in range(t-now.count(i)):
                now[now.index(None)] = i
        need(all(before is None or before==after for before,after in zip(prev,now,strict=True))
             and [now.count(i) for i in range(len(m))]==target, "changed an irrevocable promise")
        reached[path] = F(den-now.count(None),den)
        if path in leaves:
            need(None not in now and m==leaves[path], "wrong leaf assignments")
        else:
            next_bits = {h[len(path)] for h in suffixes}
            for b in next_bits:
                frontier[(*path,b)] = tuple(now)
    return reached,den


def triangular_control(rows):
    keys = ((0,0,0),(0,1,1),(1,0,1))
    ps = [rows[k] for k in keys]
    pairs = [sum(minimum((p,q))) for p,q in combinations(ps,2)]
    need(pairs==list(W) and sum(minimum(ps))==0,"pairwise slack did not mask the three-way wall")
    coarse = [tuple(sum(p[i] for i in bank) for bank in BANKS) for p in ps]
    need(minimum(coarse)==W and sum(W)==1, "a permanent early bank label remains possible")
    # General upper bound here: each fine label is missing in at least
    # one ideal row, hence sum_c deficit(m,p_c)>=sum_i m_i. Under a TV
    # tolerance eps for each row this bounds the early mass by 3*eps.
    # For 0<=eps<=1/9 assign eps to each majority exit. Each context lacks
    # exactly one of those exits, hence the construction attains the bound.
    need(all(any(p[i]==0 for p in ps) for i in range(12)), "uncovered fine exit")
    majority = tuple(int(sum(k[j] for k in keys)>1) for j in range(3))
    need(all(sum(a!=b for a,b in zip(k,majority,strict=True))==1 for k in keys), "majority support")
    for eps in (F(0),F(1,100),F(1,18),F(1,9)):
        m = tuple(eps if i in tuple(4*j+b for j,b in enumerate(majority)) else F(0) for i in range(12))
        qs = [attain_in_tv_ball(m,p) for p in ps]
        need(all(deficit(m,p)==proposal_error(m,p)==eps for p in ps) and sum(minimum(qs))==3*eps,
             "multi-context noisy bound not attained")
    return {"late_settings":keys,"pairwise_common_mass":list(map(str,pairs)),
            "all_three_fine_capacity":"0","coarse_bank_capacity":"1",
            "sharp_fine_capacity_for_TV_epsilon_0_through_1_over_9":"3*epsilon"}


def two_stage_control(rows):
    leaves = {k[1:]:p for k,p in rows.items() if k[0]==0}
    found,den = tree_realization(leaves)
    need(found[()]==F(1,9) and found[0,]==found[1,]==F(5,9) and
         all(found[k]==1 for k in leaves), "simultaneous causal stopping schedule")
    # The opposite leaves disagree on 8/9 of all mass. The triangle
    # inequality limits any common mass after separate TV-eps changes
    # to 1/9+2*eps (and of course to 1). Attain it across ALL FOUR rows,
    # not just the opposite pair: shift h into the unused exit of EACH of
    # the two late banks. At h=2/9 all four modified rows coincide.
    need(distance(leaves[(0,0)],leaves[(1,1)])==F(8,9), "opposite-leaf separation")
    for eps in (F(0),F(1,100),F(1,9),F(4,9),F(1,2),F(1)):
        qs = []
        h = min(eps/2,F(2,9))
        for bits,p in leaves.items():
            q = list(p)
            for j,b in enumerate(bits,1):
                q[4*j+b] -= h
                q[4*j+1-b] += h
            need(distance(q,p)<=eps,"perturbed row beyond budget")
            qs.append(q)
        need(sum(minimum(qs))==min(1,F(1,9)+2*eps),"four-setting robust optimum")
    # No-click is a separate FINAL label under the per-attempt contract.
    # Under a supplied common independent efficiency eta only eta/9 can
    # be a permanent *click* at root, even if no-click promises may count.
    eta = F(3,4)
    expanded = [tuple(eta*v for v in p)+(1-eta,) for p in leaves.values()]
    mm = minimum(expanded)
    need(sum(mm[:-1])==eta/9 and mm[-1]==1-eta and sum(mm)==F(1,3), "loss accounting")
    return {"common_ticket_denominator":den,"fine_capacity_at_root":"1/9","after_first_choice":"5/9",
            "after_both_choices":"1","sharp_root_capacity_under_per_setting_TV":"min(1,1/9+2*epsilon)",
            "efficiency_3_over_4":{"per_attempt_click_capacity":str(sum(mm[:-1])),
                                   "capacity_if_no_click_counts_as_label":str(sum(mm))}}


def intervention_controls(rows):
    # Adversarial schedule: hidden tape contains the future setting AND
    # the draw. All outcomes can be written before the setting is exposed;
    # conditioning on that setting nevertheless reproduces the target row.
    # Forcing another setting cannot change an already exposed label.
    keys = ((0,0,0),(0,1,1),(1,0,1))
    hidden = [(k,i) for k in keys for i,z in enumerate(rows[k]) for _ in range(int(9*z))]
    for k in keys:
        observed = tuple(F(hidden.count((k,i)),9) for i in range(12))
        need(observed==rows[k],"leaked schedule fixture")
    forced = tuple(F(sum(z==i for _,z in hidden),len(hidden)) for i in range(12))
    need(all(forced!=rows[k] for k in keys),"intervention accidentally matched leaked observational rows")
    # If an actual intermediate arm measurement dephases each bank, the
    # second four-port junction sends any single incident mode to four
    # equal intensities. Its row is independent of the later sign toggle,
    # unlike the undisturbed calibration. Midcircuit path and final port
    # are not the same observable. Neither instrument is derived here.
    q = []
    for j,bank in enumerate(BANKS):
        cols = [junction(tuple(int(i==k) for i in range(12)),bank) for k in bank]
        q.extend(W[j]*sum(col[i]**2 for col in cols)/4 for i in bank)
    need(sum(q)==1 and all(q!=list(p) for p in rows.values()), "backaction control")
    # Hiding rejected trials can also manufacture disjoint accepted-only
    # labels: start from a fair A/B tag and accept exactly the tag matching
    # the current setting. This is not a permanent final reported label.
    full = ((F(1,2),F(0),F(1,2)), (F(0),F(1,2),F(1,2)))
    need(sum(minimum(full))==F(1,2) and not any(minimum(full)[:2]), "accepted-only loss control")
    return {"leaked_setting_observed_tables_match":True,"early_fraction_on_leaked_schedule":"1",
            "do_setting_rows_do_not_match":True,"dephased_bank_conditionals":["1/4"]*4,
            "accepted_only_fixture_common_final_label":"no-click only, mass 1/2"}


def probe():
    rows = circuit_rows()
    return {"scope":"sharp compatible fraction of passive, irrevocable final labels for submitted intervention rows",
            "triangular_family":triangular_control(rows),"late_choice_tree":two_stage_control(rows),
            "causal_and_detector_controls":intervention_controls(rows),
            "boundary":"No inaccessible early label or reversible provisional routing is excluded; "
                       "maximal abstract common mass is not an observed passive instrument."}


if __name__=="__main__":
    print(json.dumps(probe(),sort_keys=True))
