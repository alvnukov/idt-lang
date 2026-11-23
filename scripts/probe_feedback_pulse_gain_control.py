"""Two input ports and two output energy meters distinguish an empty short loop.

Hypothetical isolated pulses (successive loop returns DO NOT overlap before
squaring); stationary detectors may have different linear gains or timing
weights for positive energy samples, but each is unchanged between launches.
Dark offsets must be separately removed. No counted detector events, data or
claim that real meters have this response. Read signed fields instead, or
allow gain varying by BOTH input and output, and the guarantee is lost.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_feedback_ternary_from_pairs import star, tick


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def ratio(m):
    if any(v<=0 for row in m for v in row):
        return None
    return m[0][0]*m[1][1]/(m[0][1]*m[1][0])


def fields(kind, port, length):
    e=tuple(F(i==port) for i in range(3))
    blank=(F(0),)*3
    stock=F(0)
    rows=[]
    for n in range(length):
        x=e if n==0 else blank
        if kind=="loop":
            y,stock=tick(x,stock)
        elif kind=="direct":
            y=star(x)
        else:
            raise ValueError("unrecognized device")
        rows.append(y)
    return rows


def measured(kind, source_gain, detector_gain, timing):
    rows = [fields(kind,i,len(timing[0])) for i in (0,1)]
    return tuple(tuple(source_gain[i]*detector_gain[j]*sum(w*y[j]**2 for w,y in zip(timing[j],rows[i],strict=True))
                       for j in (0,1)) for i in (0,1))


def probe():
    full = (1,1,1,1)
    response = (full, (F(1,5),3,0,1), (2,0,1,0))
    setups=0
    for src,dst,weights in product(((1,1),(F(2,9),8)),((1,1),(7,F(1,8))),product(response,repeat=2)):
        for kind,expected in (("direct",F(1,16)),("loop",F(1))):
            m=measured(kind,src,dst,weights)
            need(ratio(m)==expected, "separable gain or detector timing leakage")
            setups+=1
    base=measured("direct",(1,1),(1,1),(full,full))
    nondesigned=tuple(tuple(v*(4 if i==j else 1) for j,v in enumerate(row)) for i,row in enumerate(base))
    need(ratio(nondesigned)==1, "uncontrolled input-dependent detector gains must counterfeit")
    late=((0,1,0,0),(0,1,0,0))
    need(ratio(measured("direct",(1,1),(1,1),late)) is None, "no division by a dark measurement")
    eb=sum(v*v for v in fields("loop",0,2)[1])
    need(eb==F(3,16) and sum(v*v for v in fields("direct",0,2)[1])==0, "blank tick control")
    # Bounded independent fractional errors remaining after separable gains:
    # each ratio can move by D=(1+eps)^2/(1-eps)^2, in either direction.
    for eps in (F(0),F(1,4),F(1,3),F(2,5)):
        low,high=1-eps,1+eps
        D=(high/low)**2
        for kind,target in (("direct",F(1,16)),("loop",F(1))):
            table=measured(kind,(1,1),(1,1),(full,full))
            possible=[ratio(tuple(tuple(v*factor[2*i+j] for j,v in enumerate(row))
                                  for i,row in enumerate(table))) for factor in product((low,high),repeat=4)]
            need(min(possible)==target/D and max(possible)==target*D, "endpoint nuisance bounds")
        need((D/16 < 1/D)==(eps<F(1,3)), "separation threshold")
    # Integrate signed signals (not separated energies) including exact tail:
    # both devices then give the amplitude S3 for either impulse and all ports.
    for i in (0,1):
        x=tuple(F(i==j) for j in range(3))
        y,t=tick(x,F(0))
        need(tuple(z+t/3 for z in y)==star(x), "coherent-integrator escape")
    return {"scope":"prospective sub-round-trip isolated wave energy experiment, no measured data",
            "first_blank_energy":{"direct":"0","loop":str(eb),"max_common_absolute_error_for_disjoint_rows":"strictly below 3/32"},
            "two_by_two_cross_ratio":{"direct":"1/16","loop":"1","positive_gain_and_weight_checks":setups},
            "remaining_per_cell_fractional_error":"the two intervals are disjoint iff epsilon<1/3 under this independent box model",
            "controls":"zero denominator is uninformative; input-dependent diagonal gain can counterfeit; coherent signed integration makes the two impulse sums identical"}


if __name__=="__main__":
    print(json.dumps(probe(),sort_keys=True))
