"""Robust dimension bounds from unconditional binary events across a cut.

Model: conditional on one input-independent shared CLASSICAL seed, i prepares
a normalized state rho_i on <=D levels and j selects an effect 0<=E_j<=I.
p_ij is the seed average of Tr(rho_i E_j). No extra prefix record, entangled
side channel, input-dependent seed law, or postselection. Classical messages
with <=D states are included. A used early output must be counted at the cut.
Intervals must cover the underlying probabilities SIMULTANEOUSLY. A table of
single-cell standard errors is not such a guarantee. Selection among the
supplied settings after obtaining a simultaneous rectangle is safe on its
coverage event. This program constructs no statistical interval from counts.

Derivation (finite-dimensional matrices; not a Lean or empirical result).
For each seed, S=sum_i rho_i has Tr S=d, hence d^2/D<=Tr S^2. Its diagonal
sum is <=d. For a pair i,j put A=sqrt(rho_i), B=sqrt(rho_j). Splitting AB
at E and I-E, triangle and ||XY||_F<=||X||_F ||Y||_F give
  sqrt(Tr rho_i rho_j) <= sqrt(p q)+sqrt((1-p)(1-q))
for p=Tr(rho_i E), q=Tr(rho_j E); factor E via its positive square root.
For E_j the right side is <=sqrt(p_ij)+sqrt(1-p_jj) at each seed.
Sum the squared bounds over ordered off-diagonals and integrate over seeds.
Cauchy-Schwarz on that product space gives
  d^2 <= D(d+O+L+2 sqrt(O L)),
where O sums off-diagonal probability upper bounds and L=(d-1) times the
sum of matched probability error upper bounds. Strict rational comparisons
are necessary for an exclusion, including at equality.

Stronger, even with arbitrary (not matched) suffixes: for BINARY outcomes
f(p,q)=(sqrt(pq)+sqrt((1-p)(1-q)))^2 is jointly concave. Write
a=sqrt(p(1-p)), b=sqrt(q(1-q)), u=1-2p, v=1-2q. In the interior its
Hessian has diagonal -b/(2a^3), -a/(2b^3), and off-diagonal
(4ab+uv)/(2ab). The vectors (2a,u),(2b,v) have norm one; hence the
determinant is nonnegative. Continuity handles the boundary. Jensen thus
upper-bounds the *averaged overlap* by f evaluated on the *averaged rates*;
this is not an assumption that the averages themselves have a D-level
factorization. For disjoint probability intervals f is maximized at their
nearest endpoints: put p=sin^2(t), q=sin^2(v), then f=cos^2(t-v).
Take the best suffix for each pair, sum over pairs, round radicals UP.
No assumption of joint concavity for arbitrary-outcome squared fidelity.

Primary comparison: Sikora, Varvitsiotis & Wei, Phys. Rev. A 94, 042125
(2016), https://arxiv.org/abs/1606.03878 . Their main theorem has the
minimum-over-settings squared affinity for a direct prepare-and-measure
factorization, arbitrary numbers of outcomes and arbitrary preparation
weights. Our uniform-weight binary formula is not a new general dimension
witness. The binary concavity argument above handles the shared classical
seed explicitly; the simultaneous boxes and false-exclusion controls here
are for this raw-stream contract. The paper is mathematical, not a
measurement or an independent validation of the target readout.

Run: python3 -B -m scripts.probe_robust_shared_cut_overlap (also with -O).
"""

import json
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt

from scripts.probe_streaming_observer_cut import rank, response_matrix


def need(test, why):
    if not test:
        raise ValueError(why)


def check_rectangle(box, dim):
    need(type(dim) is int and dim >= 1 and len(box) >= 2 and len(box[0]) > 0,
         "positive integer dimension and nonempty setting table required")
    need(all(len(row) == len(box[0]) for row in box), "ragged rectangle")
    for row in box:
        for lo, hi in row:
            need(all(type(x) in (int, F) for x in (lo, hi)) and 0 <= lo <= hi <= 1,
                 "invalid or inexact probability endpoints")


def box_around(table, radius):
    need(type(radius) in (int, F) and radius >= 0, "invalid radius")
    return [[(max(0, p-radius), min(1, p+radius)) for p in row] for row in table]


def aggregate(box, dim):
    check_rectangle(box, dim)
    d = len(box)
    need(len(box[0]) == d, "aggregate requires one matching setting per prefix")
    off = sum(box[i][j][1] for i in range(d) for j in range(d) if i != j)
    loss = (d-1)*sum(1-box[j][j][0] for j in range(d))
    gap = d*d-dim*(d+off+loss)
    excludes = gap > 0 and gap*gap > 4*dim*dim*off*loss
    return {"off_upper": str(off), "matched_loss_sum_scaled": str(loss),
            "gap_before_radical": str(gap), "excludes_at_most_D": excludes}


def sqrt_upper(x, bits=40):
    """A rational >= sqrt(x); exact for a perfect rational square."""
    x = F(x)
    need(x >= 0, "negative radicand")
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    if a*a == x.numerator and b*b == x.denominator:
        return F(a, b)
    scale = 1 << bits
    k = isqrt((x.numerator*scale*scale)//x.denominator)
    return F(k + (k*k*x.denominator < x.numerator*scale*scale), scale)


def affinity_upper(left, right):
    if left[1] < right[0]:
        p, q = left[1], right[0]
    elif right[1] < left[0]:
        p, q = left[0], right[1]
    else:
        return F(1)
    a, b = p*q, (1-p)*(1-q)
    return min(F(1), a+b+2*sqrt_upper(a*b))


def pair_bound(box, dim):
    check_rectangle(box, dim)
    d, upper = len(box), F(len(box))
    for i, j in combinations(range(d), 2):
        upper += 2*min(affinity_upper(a, b) for a, b in zip(box[i], box[j]))
    return {"total_overlap_upper": str(upper), "excludes_at_most_D": d*d > dim*upper}


def control_qubit():
    # Two antipodal poles and three equatorial trine vectors: unit Bloch
    # vectors, sum zero. Aligned projectors give (1+dot)/2 exactly. A shared
    # classical seed permutes all five names at both ends before each trial.
    def born(i, j):
        if i == j:
            return F(1)
        if max(i, j) < 2:
            return F(0)
        return F(1, 4) if min(i, j) >= 2 else F(1, 2)

    d = 5
    seeds = list(permutations(range(d)))
    mean = [[sum(born(s[i], s[j]) for s in seeds)/len(seeds)
             for j in range(d)] for i in range(d)]
    need(all(p == (1 if i == j else F(3, 8)) for i, row in enumerate(mean)
             for j, p in enumerate(row)), "wrong seed mixture")
    need(rank(mean) == 5, "shared reference did not break naive rank bound")
    exact = box_around(mean, 0)
    a, b = aggregate(exact, 2), pair_bound(exact, 2)
    need(a["gap_before_radical"] == "0" and b["total_overlap_upper"] == "25/2"
         and not a["excludes_at_most_D"] and not b["excludes_at_most_D"],
         "equality falsely excludes a shared qubit")
    delta = F(1, 25)  # flip binary readout unconditionally, not a lost shot
    noisy = [[delta+(1-2*delta)*p for p in row] for row in mean]
    box = box_around(noisy, F(1, 100))
    need(rank(noisy) == 5 and not aggregate(box, 2)["excludes_at_most_D"]
         and not pair_bound(box, 2)["excludes_at_most_D"], "noisy qubit excluded")
    return {"levels": 2, "shared_permutations": len(seeds), "mixed_table_rank": 5,
            "clean_case_saturates_both": True, "flip_rate": str(delta),
            "noisy_interval_radius": "1/100", "noisy_qubit_excluded": False}


def many_outcome_trap():
    # An actual one-bit machine, one setting, three preparations. Public
    # seed l chooses a label 0..2 independently. Send [i==l]; receiver emits
    # (l,bit), a SIX-outcome result. Each pair of output distributions
    # coincides on just one seed; square of affinity is 1/9, not 1/3.
    p = [[F(int(int(i == l) == b), 3) for l in range(3) for b in (0, 1)]
         for i in range(3)]
    need(all(sum(row) == 1 for row in p), "subnormalized classical control")
    total = sum(sum(sqrt_upper(a*b) for a, b in zip(x, y))**2 for x in p for y in p)
    naive = 9/total
    need(naive == F(27, 11) and naive > 2, "lost false-exclusion trap")
    return {"classical_message_states": 2, "outcomes": 6,
            "invalid_multivalued_shared_seed_dimension_lower": str(naive)}


def probe():
    # Equal-length raw +/- updates. This H is an imposed target, NOT data.
    raw = response_matrix(5, 3)
    box = box_around(raw, F(1, 200))
    a, b = aggregate(box, 4), pair_bound(box, 4)
    need(a["excludes_at_most_D"] and b["excludes_at_most_D"], "lost robust raw witness")
    wider = box_around(raw, F(39, 4000))
    wa, wb = aggregate(wider, 4), pair_bound(wider, 4)
    need(not wa["excludes_at_most_D"] and wb["excludes_at_most_D"],
         "lost strict gain on the very same raw target")
    # A separate five-label preparation code with explicitly supplied
    # bit-reading settings (not an implementation of raw H).
    # First three read individual bits; last two are constant. Every pair
    # is separated by some bit, but the matched diagonal is uninformative.
    bits = [[F((i >> j) & 1) if j < 3 else F(0) for j in range(5)] for i in range(5)]
    code = box_around(bits, F(1, 100))
    ca, cb = aggregate(code, 4), pair_bound(code, 4)
    need(not ca["excludes_at_most_D"] and cb["excludes_at_most_D"] and
         cb["total_overlap_upper"] == str(5+20*4*F(1,100)*F(99,100)),
         "different-suffix discrimination lost")
    broad = box_around(raw, 1)
    need(not aggregate(broad, 1)["excludes_at_most_D"] and
         not pair_bound(broad, 1)["excludes_at_most_D"], "uninformative intervals excluded")
    return {"scope": "synthetic unconditional probabilities, simultaneous boxes, shared classical seed",
            "five_raw_prefixes_spacing_3": {"tested_D": 4, "radius": "1/200",
                                            "aggregate": a, "best_suffix_per_pair": b,
                                            "wider_radius": "39/4000",
                                            "wider_aggregate": wa, "wider_best_suffix_per_pair": wb},
            "nonmatched_binary_code": {"tested_D": 4, "radius": "1/100",
                                       "aggregate": ca, "best_suffix_per_pair": cb},
            "shared_qubit_control": control_qubit(), "nonbinary_countercontrol": many_outcome_trap(),
            "empirical_intervals_computed": False}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",", ":")))
