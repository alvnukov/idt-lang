"""Can one estimate ONE common mixture of drifting binary cut tables?

At trial t, *before* choosing the pair a=(prefix,suffix), let H_t(a) be
its unconditional event probability given the pre-assignment history, and
let pi_t(a)>0 be the actual, predictable assignment probability. Require
conditional randomization independent of the device's latent state and
potential responses given that history, and consistency of the event on
the chosen pair. Only the prefix may reach the encoder, only the suffix
the decoder except through the counted message; e.g. an advance leak of
the suffix to the encoder invalidates that model. Log EVERY attempt or a
genuinely pre-assignment event-ready start. A joint accepted-and-event is
binary on that denominator; a later acceptance cannot select the trials.
Counts cannot establish these assumptions, nor reconstruct unknown pi.

For each a, Z_t=1{A_t=a AND event}/pi_t(a) has conditional mean H_t(a).
The target is Hbar_n(a)=sum_t H_t(a)/n over the SAME n histories for ALL
a. It can itself be random; the bound is over repeated random histories,
not conditional coverage given the particular observed schedule. At each
realized n, if all H_t have a D-level cut with input-independent shared
classical randomness, their common-weight mixture does too: sample t as
part of the shared seed, then use that t's device. No analogous transfer
of the unshared rank limit, no stationary law and no physical conclusion.

Anytime proof. Fix in advance a finite positive grid of J rational lambdas,
K cells, alpha, and an output grid. Write X=Z-H, b=1/pi. X has conditional
range width b, |X|<=b, variance H*(b-H)<=v, with v=b*b/4 if b<=2 else b-1.
For either sign, conditional log mgf is <=lambda^2*b^2/8: the log mgf's
second derivative is a tilted variance <= b^2/4, with value and slope zero
at zero. Also if lambda*b<3, expanding the exponential, k!>=2*3^(k-2)
for k>=2 and E|X|^k<=v*b^(k-2) give log mgf <=lambda^2*v/(2*(1-lambda*b/3)).
Take the smaller valid cost C_t. It is predictable even for adaptive pi.
Thus exp(+/-lambda*sum X-sum C_t) is a nonnegative supermartingale
starting at one. Stopping it at its first threshold crossing by time N
and then increasing N gives P(ever >=exp(L)) <= exp(-L). Union over
2*K*J fixed tests. Use L=(7/10)*ceil(log2(2*K*J/alpha)) >= ln(2*K*J/alpha)
since exp(7/10)>2 already by its first four Taylor terms. With probability
>=1-alpha simultaneously for every n>=1, a, and grid choice,
  |mean Z-Hbar_n(a)| <= min_lambda (L+sum C_t)/(lambda*n).
Projecting mean Z onto [0,1] cannot increase error; round the bounds outward.
The predictable variance *bound* is not a fitted variance. A finite fixed
grid remains valid indefinitely but need not give widths tending to zero.
Post-hoc choices of cells, endpoint conventions or a new lambda grid
are not free. No inference from missing trials, estimated propensities
or retrospectively selected reports. Coverage is not certainty.

Primary methodological comparison: Howard, Ramdas, McAuliffe & Sekhon,
Time-uniform Chernoff bounds via nonnegative supermartingales (2020),
https://arxiv.org/abs/1808.03204 . This finite-grid scalar construction
uses their nonnegative-supermartingale principle, not an optical data set.
Run: python3 -B -m scripts.probe_randomized_cut_coverage (also with -O).
"""

import json
from dataclasses import dataclass
from fractions import Fraction as F

from theory_experiments.binary_overlap_cut import BinaryOverlapCut, evaluate_binary_overlap_cut
from theory_experiments.primitive_screen import Limits

GRID = tuple(F(1, 2**k) for k in range(3, 15))
ROUND = 10**6


def need(test, why):
    if not test:
        raise ValueError(why)


@dataclass(frozen=True)
class Block:
    # Exact sufficient summaries for these bounds ONLY when the propensity
    # vector was the same at every included trial. Boundaries must retain
    # all attempts; disaggregated records are required for within-block reads.
    attempts: int
    pi: tuple
    assigned: tuple
    events: tuple


def log_upper(k, j, alpha):
    x = F(2*k*j)/alpha
    ceil_x = -(-x.numerator//x.denominator)
    return F(7,10)*(ceil_x-1).bit_length()


def cost(p, lam):
    b = 1/F(p)
    h = lam*lam*b*b/8
    if lam*b >= 3:
        return h
    v = b*b/4 if b <= 2 else b-1
    return min(h, lam*lam*v/(2*(1-lam*b/3)))


def interval(raw_estimate, radius):
    center = min(F(1), max(F(0),raw_estimate))
    lo,hi = max(F(0),center-radius), min(F(1),center+radius)
    return F((lo*ROUND).__floor__(),ROUND), F((hi*ROUND).__ceil__(),ROUND)


def coverage(blocks, cells, *, alpha=F(1,20), grid=GRID, basis="unconditional"):
    """All complete blocks supplied are the common prefix. No outcome imputation."""
    need(type(cells) is int and 1 <= cells <= 576 and type(blocks) in (list,tuple) and blocks,
         "expected a complete positive-length block log and bounded named cell set")
    need(type(alpha) is F and 0 < alpha < 1 and type(grid) is tuple and
         1 <= len(grid) <= 64 and all(type(l) is F and l > 0 for l in grid),
         "need a predeclared error level and positive rational grid")
    need(basis in ("unconditional","joint_accepted_event"), "accepted-only is not an all-attempts event")
    n=0
    totals=[F(0)]*cells
    budgets=[[F(0) for _ in grid] for _ in range(cells)]
    for block in blocks:
        need(type(block) is Block and type(block.attempts) is int and block.attempts > 0
             and all(type(v) is tuple and len(v)==cells for v in (block.pi,block.assigned,block.events)),
             "missing cell, denominator or attempt record")
        need(all(type(p) is F and 0 < p <= 1 for p in block.pi) and sum(block.pi)==1,
             "unknown/invalid propensity vector")
        need(all(type(a) is int and type(e) is int and 0 <= e <= a
                 for a,e in zip(block.assigned,block.events)) and sum(block.assigned)==block.attempts,
             "lost or invalid trial denominator")
        n+=block.attempts
        for a,p in enumerate(block.pi):
            totals[a]+=block.events[a]/p
            for j,l in enumerate(grid):
                budgets[a][j]+=block.attempts*cost(p,l)
    level=log_upper(cells,len(grid),alpha)
    means=tuple(s/n for s in totals)
    widths=tuple(min((level+c)/(l*n) for c,l in zip(bud,grid)) for bud in budgets)
    return means,widths,tuple(interval(x,r) for x,r in zip(means,widths))


def dimension(cells, cols, d, *, basis="unconditional"):
    rows=tuple(tuple(cells[i:i+cols]) for i in range(0,len(cells),cols))
    m=BinaryOverlapCut("coverage_control","ref",basis,"quantum",d,True,rows)
    (check,),_=evaluate_binary_overlap_cut(m,Limits())
    return check.status


def drift_control():
    # These counts are one possible synthetic realization (positive probability)
    # under independent assignments. NOT conditionally guaranteed after selecting
    # these counts or evidence that a real event-ready randomizer was unbiased.
    n=10000
    pi=(F(9,10),F(1,10))
    # One effect e_t, independent of preparation: unit response then zero response.
    first=Block(n,pi,(9000,1000),(9000,1000))
    last=Block(n,pi[::-1],(1000,9000),(0,0))
    means,_,box=coverage([first,last],2)
    naive=tuple(F(e,a) for e,a in zip(first.events,(10000,10000)))
    need(naive==pi and means==(F(1,2),F(1,2)) and
         all(lo < F(1,2) < hi for lo,hi in box), "drift correction broke")
    bad=dimension(tuple((p,p) for p in naive),1,1)
    naive_padded=dimension(tuple(interval(p,F(1,20)) for p in naive),1,1)
    sound=dimension(box,1,1)
    # If someone relabels these SAME counts as arising under a uniform
    # randomizer, the arithmetic cannot establish that this claim is false.
    # The result is then an invalid inference under the ACTUAL drifting law.
    false_pi=(F(1,2),)*2
    impostors=[Block(n,false_pi,b.assigned,b.events) for b in (first,last)]
    fake_means,_,fake_box=coverage(impostors,2)
    false_result=dimension(fake_box,1,1)
    need(fake_means==naive and bad==naive_padded==false_result=="counterexample" and
         sound=="inconclusive","lost concrete false-rejection control")
    return {"attempts":2*n,"announced_pi_by_phase":[list(map(str,pi)),list(map(str,pi[::-1]))],
            "synthetic_naive_per_visited_input":list(map(str,naive)), "naive_as_exact":bad,
            "common_truth_and_inverse_propensity_estimates":list(map(str,means)),
            "outward_common_boxes":[list(map(str,p)) for p in box],"one_level_verdict":sound,
            "naive_with_descriptive_padding_1_over_20":naive_padded,
            "falsely_declared_uniform_randomizer_invalid_verdict":false_result}


def adaptive_tree():
    # Independent exact four-way branch oracle (setting x binary outcome).
    # Past outcome affects the next randomizer AND the device response.
    leaves=0
    expected=[F(0),F(0)]
    target_means=set()
    def visit(t,last,weight,z,h):
        nonlocal leaves
        if t==3:
            leaves+=1
            target_means.add(h/3)
            for i in range(2):
                expected[i]+=weight*(z[i]-h)
            return weight
        p0=F(3,4) if last else F(1,4)
        hit=F(1,3) if last else F(2,3)
        mass=F(0)
        for i,p in enumerate((p0,1-p0)):
            for event in (0,1):
                znext=z.copy()
                znext[i]+=event/p
                mass+=visit(t+1,event,weight*p*(hit if event else 1-hit),znext,h+hit)
        return mass
    need(visit(0,0,F(1),[F(0),F(0)],F(0))==1 and expected==[0,0] and
         len(target_means)>1 and leaves==64,"predictable adaptive expectation mismatch")
    return {"exact_leaves":leaves,"path_dependent_targets":list(map(str,sorted(target_means))),
            "expected_ht_minus_target":[str(v) for v in expected]}


def anytime_exact_control():
    # Both actual H equal 1. Every one of the 2^64 ordered assignments has
    # equal probability. Count paths which have NEVER missed either cell at
    # ANY earlier tick; merging paths at (time,counts) keeps this flag.
    horizon=64
    alpha,lam=F(1,4),F(1,2)
    L=log_upper(2,1,alpha)
    live={0:1}
    for t in range(1,horizon+1):
        counts={}
        for x,ways in live.items():
            for nas in (x,x+1):
                counts[nas]=counts.get(nas,0)+ways
        remaining={}
        r=(L+t*cost(F(1,2),lam))/(t*lam)
        for x,num in counts.items():
            # The lower of the two estimates is 2*min(x,t-x)/t <= 1;
            # an outward-ceiled upper endpoint is 1 iff the unclipped upper
            # exceeds 1-1/ROUND. The higher estimate projects to 1.
            covered=F(2*min(x,t-x),t)+r>1-F(1,ROUND)
            if covered:
                remaining[x]=num
            if x in (min(counts),max(counts)) or t==horizon:
                b=Block(t,(F(1,2),F(1,2)),(x,t-x),(x,t-x))
                _,_,box=coverage([b],2,alpha=alpha,grid=(lam,))
                need(covered==all(hi==1 for _,hi in box),"integer-path oracle vs intervals")
        live=remaining
    miss=1-F(sum(live.values()),2**horizon)
    need(0<miss<alpha,"vacuous or invalid time-uniform coverage test")
    return {"ordered_paths":str(2**horizon),"ticks":horizon,"familywise_alpha":str(alpha),
            "exact_probability_either_cell_ever_misses":str(miss)}


def five_label():
    # Declared noisy truth and a possible compressed synthetic log, NOT run data
    # and NOT a coverage simulation. Each named cell has its assigned count,
    # including all non-events. Deterministic rounding just chooses this fixture.
    d,per,noise=5,400000,F(1,1000)
    truth=tuple(noise+(1-2*noise)*F(1,1+36*(i-j)**2) for i in range(d) for j in range(d))
    events=tuple((p*per).__floor__() for p in truth)
    b=Block(d*d*per,(F(1,d*d),)*(d*d),(per,)*(d*d),events)
    means,widths,box=coverage([b],d*d)
    need(all(lo<=p<=hi for p,(lo,hi) in zip(truth,box)), "known synthetic truth outside this box")
    verdict=dimension(box,d,4)
    need(verdict=="counterexample" and max(widths)<F(9,1000), "insufficient synthetic resolution")
    return {"attempts":b.attempts,"cells":d*d,"symmetric_binary_flip_rate":str(noise),
            "error_level":"1/20","radius_before_outward_rounding":str(max(widths)),
            "four_level_conditional_verdict":verdict,"sample_box_diagonal":list(map(str,box[0])),
            "sample_box_neighbor":list(map(str,box[1])),"observed_in_laboratory":False}


def invalid_controls():
    good=Block(2,(F(1,2),F(1,2)),(1,1),(1,0))
    for bad,basis in ((good,"accepted_only"),(Block(3,good.pi,good.assigned,good.events),"unconditional"),
                      (Block(2,(F(1),F(0)),good.assigned,good.events),"unconditional"),
                      (Block(2,(0.5,0.5),good.assigned,good.events),"unconditional")):
        try:
            coverage([bad],2,basis=basis)
        except ValueError:
            continue
        raise ArithmeticError("ineligible sampling contract was accepted")


def probe():
    invalid_controls()
    return {"scope":"synthetic known randomizers only; no verified real trial counts or propensities",
            "target":"all-input common time average; anytime simultaneous binary-event intervals",
            "drift_control":drift_control(),"adaptive_exact_control":adaptive_tree(),
            "anytime_exact_control":anytime_exact_control(),"five_label_control":five_label()}


if __name__=="__main__":
    print(json.dumps(probe(),separators=(",",":")))
