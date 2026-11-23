"""Agreement on an additive square law does not imply a linear scatterer.

Compare equal reflection S_d with a reversible nonlinear alternative: use
S_d near the two-level locus and leave the input unchanged elsewhere. Equal
loads, individual localized inputs, every background used in the four-port
third-difference test, and every isolated square-leaf splitter pass under
BOTH devices. Signed sums and squared power are conserved by either rule.
A previously constructed three-port preparation followed by a four-port
command distinguishes them already at the level of wave power, without a
claim about click probabilities.
"""

from fractions import Fraction as F
from itertools import combinations, permutations, product

from scripts.probe_anonymous_contact_additive_readout import scatter

CUT = F(1,27)


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def variance(v):
    return sum(x*x for x in v)-F(sum(v)**2,len(v))


def distance(v):
    norm = variance(v)
    if not norm:
        return F(0)
    splits = []
    indices = tuple(range(len(v)))
    for size in range(1,len(v)):
        for parts in combinations(indices[1:],size-1):
            a = {0,*parts}
            splits.append(variance(tuple(v[i] for i in indices if i in a))+
                          variance(tuple(v[i] for i in indices if i not in a)))
    return min(splits)/norm


def rival(v):
    return scatter(v) if distance(v)<=CUT else tuple(v)


def probe():
    count = 0
    # S is a simultaneous shift and reversal about the mean. All
    # within- and total-group variances, hence their ratio, are invariant.
    # The buffer avoids an exact-equality switch on the calibrations;
    # the rival itself is still discontinuous at the threshold.
    for x in product(range(-2,3),repeat=4):
        y = rival(x)
        need(rival(y)==x and sum(y)==sum(x) and sum(a*a for a in y)==sum(a*a for a in x),
             "rival lost reciprocity or its invariants")
        need(distance(x)==distance(scatter(x))==distance(tuple(3-2*a for a in x)), "not affine-invariant")
        if len(set(x))<=2:
            need(distance(x)==0 and y==scatter(x), "missed known calibration")
        count += 1
    for t,u in product(range(-3,4),repeat=2):
        v=(t+2*u,t,t,t)
        need(rival(v)==scatter(v),"third difference is not forced for rival")
    x=(*scatter((1,0,0)),F(0))
    linear, nonlin = scatter(x),rival(x)
    need(nonlin==x and distance(x)==distance(linear)==F(2,27), "not separated from switching boundary")
    for p in permutations(range(4)):
        need(rival(tuple(x[i] for i in p))==tuple(nonlin[i] for i in p), "device carries a port name")
    a,b=[tuple(y*y for y in row) for row in (linear,nonlin)]
    need(a==(F(25,36),F(1,36),F(1,36),F(1,4)) and b==(F(1,9),F(4,9),F(4,9),0), "wrong wave powers")
    need(a[0]+a[3]-b[0]-b[3]==F(5,6) and linear[0]==F(5,6) and nonlin[0]==F(-1,3),
         "detector intervention without selective normalization")
    # The preparation itself starts at a two-level input, hence both
    # hypotheses realize it on the three-arm command without tuning.
    need(rival((1,0,0))==x[:3], "preparation already distinguishes the rivals")
    return {"four_arm_reversible_controls":count,"calibration_distance":"0","threshold":"1/27",
            "probe_distance":"2/27","linear_raw_power_ports_0_and_3":"17/18","rival_raw_power":"1/9",
            "absolute_power_contrast":"5/6","first_port_signed_field":["5/6","-1/3"],
            "scope":"specific nonlinear contender and prospective wave intervention; no physical data"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),sort_keys=True))
