"""A static reflection looks exact on a vacancy star without being a wave.

Raw local operation: select one incident edge independently of occupation,
exchange its two bits. u are the incoming boundary means, h the initial hub
mean. Y is the actual outgoing boundary register, not a signed wave. A
*separate* meter may report u+c E[Y-u]. Its units are calibrated from an
echo equivalence on static preparations; no signed packet, microscopic
amplitude, Born distribution or detector law is inferred.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def exchange(u, hub, i):
    y = list(u)
    y[i], nxt = hub, y[i]
    return tuple(y), nxt


def dispatch(u, hub):
    d = len(u)
    actual = [exchange(u,hub,j) for j in range(d)]
    return tuple(sum((x[i] for x,h in actual),F())/d for i in range(d)), sum((h for x,h in actual),F())/d


def compare(u, outward, gain):
    return tuple(old+gain*(new-old) for old,new in zip(u,outward,strict=True))


def mean(u):
    return sum(u,F())/len(u)


def star(u):
    return tuple(2*mean(u)-x for x in u)


def static():
    checked, calibrated = 0, {}
    for d in range(2,9):
        for u in product((0,1), repeat=d):
            for h in (0,1):
                native,nxt = dispatch(u,h)
                need(nxt==mean(u), "hub receives one of the incoming bits")
                need(all(y-raw==F(h-raw,d) for y,raw in zip(native,u,strict=True)),
                     "actual mean directed boundary transfer")
                need(all(0<=y<=1 for y in native), "raw register outside probability range")
                checked += 1
            native,_ = dispatch(u,mean(u))
            measured = compare(u,native,2*d)
            need(measured==star(u) and star(measured)==u, "stationary echo and signed output")
        # The mean mode is fixed for every gain. On differences the eigenvalue
        # is 1-c/d, so echo only selects c=0 or 2d in this affine meter family.
        gains = [F(k,2) for k in range(-4*d,6*d+1) if (1-F(k,2*d))**2==1]
        need(gains==[0,2*d], "echo-calibrated gains")
        calibrated[d] = [int(v) for v in gains]
    # Interior nonnegative preparations admit an externally re-prepared echo.
    u = (F(3,4),F(1,2),F(1,2))
    v = compare(u,dispatch(u,mean(u))[0],6)
    need(all(0<=z<=1 for z in v) and compare(v,dispatch(v,mean(v))[0],6)==u, "interior static echo")
    return {"binary_hub_boundary_inputs":checked, "zero_or_nontrivial_echo_gains":calibrated,
            "interior_echo_intermediate":[str(z) for z in v]}


def timed():
    d = 3
    h = F(1,4)
    rows=[]
    for p in (F(3,4),F(1,4),F(3,4),F(1,4)):
        u = (p,)*d
        native,nxt = dispatch(u,h)
        meter = compare(u,native,2*d)
        # If one reads the *following* hub directly, a different arithmetic
        # instrument can always compute S(u), but it is not the outgoing wire.
        reread = tuple(2*nxt-z for z in u)
        need(meter==(2*h-p,)*d and reread==star(u)==u and native!=meter, "pulsed common mode")
        need((meter[0]-F(1,2))**2==9*(p-F(1,2))**2, "alternating small-signal gain")
        rows.append([str(p),str(native[0]),str(meter[0]),str(reread[0])])
        h = nxt
    # Strictly zero-mean variations about positive background are a null:
    # the previous hub is already at mean if all proposed vectors share it.
    for u in ((F(3,4),F(1,4),F(1,2)),(F(1,4),F(1,2),F(3,4))):
        need(compare(u,dispatch(u,F(1,2))[0],6)==star(u), "transverse modulation null")
    return rows


def cascade():
    # One localized bit, clean hubs (wires 4,5). Enumerate both actual edge
    # choices independently. The simulator here never reads a signed field.
    state=(1,0,0,0,0,0)
    raw=[]
    for i,j in product((0,1,2),(1,2,3)):
        v=list(state)
        v[i],v[4]=v[4],v[i]
        v[j],v[5]=v[5],v[j]
        raw.append(v)
    physical = tuple(sum((r[i] for r in raw),F())/9 for i in range(6))
    H = (*star(state[:3]),0)
    wave = (H[0], *star(H[1:]))
    need(physical==(F(2,3),0,0,0,F(1,3),0) and wave[3]==F(8,9), "raw interconnection")
    return {"actual_mean_wires_then_hubs":[str(v) for v in physical],
            "composed_rational_reflections":[str(v) for v in wave]}


def probe():
    return {"scope":"anonymous binary exchanges on a uniformly proposed edge and separately calibrated affine meter",
            "static":static(), "alternating_input_native_output_static_meter_posthub_reconstruction":timed(),
            "coupled_raw_cascade":cascade(),
            "missing":"Stationary means, reference-subtracted gain and re-preparations do not propagate a native signed reflected field."}


if __name__=="__main__":
    print(json.dumps(probe(),sort_keys=True))
