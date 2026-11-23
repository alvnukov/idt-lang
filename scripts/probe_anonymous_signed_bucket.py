"""An anonymous integer event mechanism for an equal-arm signed wave map.

An arrival has an incident arm i and sign +/-1. Reflect the opposite sign
on i, add twice the incoming sign to a bounded central stock, and on
overflow/underflow broadcast its sign to EVERY arm. Cancel opposite records
at the incident arm in this atomic burst. No division, port ordering, head,
sampling or angular amplitude is consulted by the unit update. An atomic
arrival, signed records, two stock units per input, a d-threshold counter,
fan-out, same-port cancellation and scheduling are supplied. Compare the
ordered-head device in probe_signed_rotor_junction.py: there the two copies
visit named successors and the outgoing signed sum is conserved EACH event;
here the stock can temporarily carry that sum.
The separate triangle_stock split-gain fixture tests an assigned function
of neutral triples under two branches. Here a neutral input sum simply
gives y=-x and unchanged stock; that fixture's branch/readout law is absent.

For input counts x, s=sum x, start stock r, and final r', telescoping gives
d*q+r'=2*s+r with 0<=r'<d and y=-x+q*1. Thus sum(y)+r'=s+r. The encoded
vector X=x+(r/d)*1 is sent exactly to Y=y+(r'/d)*1 = (2J/d-I)X. This
preserves its squared norm, not the raw sum of squares, absolute flux or
physical energy. The action on (x,r) is involutive: 2*sum(y)+r'=d*q+r.
Feeding the emitted records back is an inverse only after aggregation;
separate event times and cancellation need not reverse microscopically.

With positive inputs at a fixed arm, g=gcd(d,2), each phase repeats after
L=d/g, with 2/g broadcasts in that cycle. The emitted L1 cost is 3-4/d
per input after port-local cancellations. Triangle inequality makes this
sharp for this fixed-input exact cycle. An autonomous deterministic finite
machine with the same exact long-run mean cannot have fewer than L states:
on any eventual cycle the other arm has integer output with mean 2/d.
This lower bound does not count an external clock or a supplied random seed.

If instead EACH emitted event must have signed sum +1, with integer k
on every other arm by pointwise permutation symmetry, its cost is
c(k)=|1-(d-1)k|+(d-1)|k| >= 1+2(d-2)k for every integer k. Mean k=2/d
therefore costs >=5-8/d, sharp by time-sharing k=0,1. This comparison
forbids storing signed flux between events, NOT all timing memory; a
mixture with a distinguished hidden outlet need not obey pointwise symmetry.
No single-click detector or probabilistic interpretation is derived.
"""

import json
import sys
from fractions import Fraction as F
from itertools import permutations, product
from math import gcd
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_signed_rotor_junction import Ring


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def event(d,r,i,sg):
    """Thresholds only; d>=2 means at most one wrap per signed-unit input."""
    need(type(d) is int and d>=2 and type(r) is int and 0<=r<d and
         type(i) is int and 0<=i<d and type(sg) is int and sg in (-1,1), "invalid unit event")
    t = r+2*sg
    broadcast = 0
    if t>=d:
        t -= d
        broadcast = 1
    elif t<0:
        t += d
        broadcast = -1
    # Order of list slots represents simultaneous outputs, not traversal
    # priority. At a wrap the reflected and broadcast signs cancel at i.
    burst = tuple(broadcast-(sg if j==i else 0) for j in range(d))
    return t,burst


def recover(t,b):
    """Invert a correctly framed event, NOT a claim of passive time reversal."""
    d = len(b)
    live = [i for i,z in enumerate(b) if z]
    if d>2 and len(live)==1:
        i = live[0]
        sg = -b[i]
    else:
        need(d>=2 and len(live)==d-1 and len({b[i] for i in live})==1,
             "not one complete bucket broadcast")
        i, = set(range(d))-set(live)
        sg = b[live[0]]
    r = (t-2*sg)%d
    need(event(d,r,i,sg)==(t,b), "impossible prior stock or burst")
    return r,i,sg


def stream(d,r,records):
    x,y = [0]*d,[0]*d
    history = []
    for i,sg in records:
        x[i] += sg
        r,b = event(d,r,i,sg)
        history.append(b)
        for j,a in enumerate(b):
            y[j] += a
    return tuple(x),tuple(y),r,tuple(history)


def expand(x):
    return tuple((i,1 if a>0 else -1) for i,a in enumerate(x) for _ in range(abs(a)))


def aggregate(x,r):
    d = len(x)
    q,r1 = divmod(2*sum(x)+r,d)
    return tuple(q-a for a in x),r1


def exact_encoded(x,r):
    d = len(x)
    return tuple(F(d*a+r,d) for a in x)


def wave(x):
    return tuple(F(2*sum(x),len(x))-a for a in x)


def absolute_flux(b):
    return sum(map(abs,b))


def aggregate_audit():
    cases = 0
    for d in (2,3,4,5):
        for x in product(range(-1,2),repeat=d):
            for r in range(d):
                y,t = aggregate(x,r)
                need(aggregate(y,t)==(x,r) and sum(y)+t==sum(x)+r, "involution or stock conservation")
                a,b = exact_encoded(x,r),exact_encoded(y,t)
                need(wave(a)==b and sum(i*i for i in a)==sum(i*i for i in b),"encoded invariant")
                need(d*sum(i*i for i in a)==d*sum(i*i for i in x)+2*r*sum(x)+r*r,
                     "integer scaled invariant")
                if sum(x)==0:
                    need(t==r and y==tuple(-v for v in x), "neutral sector is pure negation")
                need(all(F(o)-h==F(r-t,d) for o,h in zip(y,wave(x),strict=True))
                     and abs(r-t)<=d-gcd(d,2), "common finite error bound")
                order = expand(x)
                for route in (order,tuple(reversed(order)),(*order,(0,1),(0,-1))):
                    obs = stream(d,r,route)
                    need(obs[:3] == (x,y,t),"arrival order or balanced pair changed aggregate")
                # These are *different* inverses: negate known inputs at
                # the final stock vs feeding back the signed output block.
                minus = tuple((i,-sg) for i,sg in reversed(order))
                need(stream(d,t,minus)[1:3] == (tuple(-v for v in y),r),"signed undo")
                need(stream(d,t,expand(y))[1:3] == (x,r), "packed inversion")
                cases += 1
    # A smaller comparison of long mixed streams at both parity classes.
    for d in (5,6,11,12):
        route = tuple(((7*k+2)%d,1 if k%5<3 else -1) for k in range(203))
        for r in range(d):
            x,y,t,_ = stream(d,r,route)
            need((y,t)==aggregate(x,r) and r%gcd(2,d)==t%gcd(2,d),"multiwrap signed stream")
    return cases


def references_and_symmetries():
    all_units, relabelings = 0,0
    for d in range(2,13):
        g = gcd(d,2)
        L = d//g
        symbols = []
        inverse = {}
        for r in range(d):
            seq = stream(d,r,((0,1),)*L)[3]
            symbols.append(seq)
            for i,sg in product(range(d),(-1,1)):
                t,b = event(d,r,i,sg)
                need((t,b) not in inverse,"framed event is not decodable from final stock and full burst")
                need(recover(t,b)==(r,i,sg), "constructive local inverse")
                inverse[t,b] = (r,i,sg)
                mirror,neg = event(d,d-1-r,i,-sg)
                need(mirror==d-1-t and neg == tuple(-v for v in b),"charge-sign phase mirror")
                back,undone = event(d,t,i,-sg)
                need((back,undone)==(r,tuple(-v for v in b)), "opposite-input event fails signed undo")
                if d<=4:
                    for p in permutations(range(d)):
                        rt,bt = event(d,r,p[i],sg)
                        need(rt==t and all(bt[p[j]]==b[j] for j in range(d)),"port covariance")
                        relabelings += 1
                all_units += 1
        need(len(set(symbols)) == L and all(symbols[r]==symbols[g*(r//g)] for r in range(d)),
             "observable phase count")
        # r=g*k+c: q=floor((k+(2/g)s)/L) independent of c in [0,g).
        # Thus any invisible parity tag remains invisible for ALL streams.
        for r in range(d):
            for sg in (-1,1):
                t,b = event(d,r,0,sg)
                t0,b0 = event(d,g*(r//g),0,sg)
                need(t//g==t0//g and b==b0 and t%g==r%g, "quotient transition")
    # The blank r=0 is port-anonymous, but not sign-symmetric for d>2.
    need(event(3,0,0,1) == (2,(-1,0,0)) and event(3,0,0,-1) == (1,(0,-1,-1)),
         "blank sign convention control")
    need(all(event(2,r,i,s) == (r,tuple(s if j!=i else 0 for j in range(2)))
             for r,i,s in product(range(2),range(2),(-1,1))),"degree-two swap control")
    return {"checked_unit_transitions":all_units,"permutation_intertwinings":relabelings,
            "minimal_observable_counter_phases":"d/gcd(d,2)","invisible_even_degree_tag":"r modulo 2",
            "sign_reversal_of_arbitrary_stream":"mirror initial stock d-1-r",
            "one_event_inverse_test":"given final stock and one framed burst on identifiable output arms"}


def resource_bounds():
    rows = []
    for d in range(2,14):
        g = gcd(d,2)
        L = d//g
        buffered, strict = 3-F(4,d),5-F(8,d)
        for r in range(d):
            for sg in (-1,1):
                x,y,t,h = stream(d,r,((0,sg),)*L)
                wraps = sum(any(b[1:]) for b in h)
                need(t==r and wraps==2//g and tuple(map(F,y))==wave(x),"closed signed reference")
                need(sum(absolute_flux(b) for b in h) == absolute_flux(y) == L*buffered,
                     "sharp closed emitted cost")
                need(L+d*wraps==3*L, "pre-cancellation raw multiplicity")
        # Integer k<=0: c(k)-[1+2(d-2)k]=-2(2d-3)k.
        # Integer k>=1: difference=2(k-1). An exact-cycle schedule with
        # 2/g occurrences of k=1 realizes equality at both endpoints.
        for k in range(-9,10):
            cost = abs(1-(d-1)*k)+(d-1)*abs(k)
            need(cost-(1+2*(d-2)*k) == (-2*(2*d-3)*k if k<=0 else 2*(k-1)),
                 "strict-flux symmetric affine bound")
        counts = (1,)*(2//g)+(0,)*(L-2//g)
        strict_bursts = [(1-(d-1)*k,*(k,)*(d-1)) for k in counts]
        need(all(sum(b)==1 for b in strict_bursts) and
             tuple(sum(s) for s in zip(*strict_bursts,strict=True)) == wave((L,*(0,)*(d-1))) and
             sum(map(absolute_flux,strict_bursts)) == L*strict, "sharp no-flux-storage control")
        # No uniform optimality for every mixed-port stream: totals with
        # different input directions can cancel across event boundaries.
        rows.append((d,L,str(buffered),str(strict)))
    _,y,_,h = stream(3,0,((0,1),(1,1),(2,1)))
    need(sum(map(absolute_flux,h)) > absolute_flux(y), "mixed-port triangle bound can be strict")
    return {"columns":["arms","observable_phases","minimum_buffered_L1","minimum_event_flux_one_pointwise_symmetric_L1"],
            "rows":rows,"before_same_arm_cancellation_records_per_fixed_positive_input":"3"}


def timing_and_readout_controls():
    # An unknown rotor head and an unknown bucket phase do not hide this
    # single-event difference. It requires ALL outgoing signs and a common
    # atomic time boundary, not just one threshold detector or unsigned hits.
    for d in range(3,13):
        ring = Ring.wire(tuple(range(d)))
        for i,sg in product(range(d),(-1,1)):
            rotor_flux = {sum(v for _,v in ring.burst(p,i,sg)[1]) for p in range(d)}
            bucket_flux = {sum(event(d,r,i,sg)[1]) for r in range(d)}
            need(rotor_flux == {sg} and bucket_flux == {-sg,(d-1)*sg} and
                 rotor_flux.isdisjoint(bucket_flux),"unknown-phase one-event intervention")
    # (1,+ at arm 0) -> stock zero and two positive outgoing records.
    # Feedback one at a time recovers the original signed count, not one
    # exclusive event in reverse. The intermediate opposite arm-1 records
    # live in DIFFERENT bursts, so per-burst cancellation cannot erase them.
    t,b = event(3,1,0,1)
    _,returned,r,replayed = stream(3,t,expand(b))
    need(b==(0,1,1) and returned==(1,0,0) and r==1 and
         replayed==((0,-1,0),(1,1,0)) and sum(map(absolute_flux,replayed))==3, "ordered feedback control")
    need(sum(a*a for a in b)==2 and sum(exact_encoded((1,0,0),1))==sum(exact_encoded(b,t)),
         "raw packet square changed despite encoded conservation")
    first,_ = aggregate((1,0,0),0)
    doubled,_ = aggregate((2,0,0),0)
    need(first==(-1,0,0) and doubled==(-1,1,1) and doubled!=tuple(2*v for v in first),
         "resetting the stock at each ingress should spoil raw superposition")
    # Same exact scatter wave, no required Born detector: the completely
    # symmetric counter that counts every surviving record independent of
    # sign predicts a DIFFERENT normalized profile from squared magnitudes.
    _,y,r,h = stream(3,0,((0,1),)*3)
    hits = tuple(sum(map(abs,c)) for c in zip(*h,strict=True))
    record_fraction = tuple(F(v,sum(hits)) for v in hits)
    squared = tuple(F(v*v,sum(z*z for z in y)) for v in y)
    need(r==0 and y==(-1,2,2) and record_fraction==(F(1,5),F(2,5),F(2,5))
         and squared==(F(1,9),F(4,9),F(4,9)),"two incompatible readouts")
    return {"framed_feedback_output":replayed,"signed_closed_counts":y,
            "record_fractions":list(map(str,record_fraction)),"squared_wave_fractions":list(map(str,squared)),
            "one_positive_complete_burst_d_gt_2":{"bucket_signed_sum":["-1","d-1"],"rotor_signed_sum":["1"]},
            "claim":"Neither a one-click event nor its probability is supplied by the signed stock."}


def probe():
    return {"scope":"atomic signed events and a bounded permutation-invariant central stock on d>=2 arms",
            "aggregate_cases":aggregate_audit(),"reference":references_and_symmetries(),
            "closed_cycle_costs":resource_bounds(),"countercontrols":timing_and_readout_controls(),
            "not_assumed":"No port ring, random phase, universal scheduler, raw-particle energy or Born detector."}


if __name__ == "__main__":
    print(json.dumps(probe(),sort_keys=True))
