"""Two idle modes discriminate the rational four-mode event law.

Four-mode input: an admissible ray with a unique odd coordinate predicts
certainty in that coordinate under the residue rule. Demand only for the
purposes of this test that (a) its calibrated small-subspace preparation
equivalences survive embedding, (b) a lossless change on the complement of
an observed output leaves that tagged unconditional probability unchanged,
and (c) the six output tags describe exclusive outcomes of the same input
population. These requirements are not derived from an unsigned graph.

There is NO assignment for the common tagged readout under all three
premises. The computed contradiction, a single 6-port event sum >=5, is
about this proposed extension, NOT an observation of Born statistics, or
an exclusion of contextual/memory-bearing small-subspace devices.
"""

from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm


def need(value, why):
    if not value:
        raise ArithmeticError(why)


def pulse(v, legs):
    """Equal-impedance scattering, with the complement exactly bypassed."""
    mean2 = 2*sum(v[j] for j in legs)/F(len(legs))
    return tuple(mean2-x if j in legs else x for j,x in enumerate(v))


def phase_pair(v, pair):
    return tuple(-x if j in pair else x for j,x in enumerate(v))


def profile(v):
    gain = lcm(*(x.denominator for x in v))
    nums = [int(gain*x) for x in v]
    g = gcd(*nums)
    nums = [x//g for x in nums]
    return tuple(i for i,x in enumerate(nums) if x % 2), nums


def probe():
    modes = tuple(range(6))
    a = tuple(F(i==0) for i in modes)
    prepared = pulse(pulse(a,(0,1,2)),(1,3,4,5))
    odd, witness = profile(prepared)
    need(witness==[-1,-1,2,1,1,1] and odd==(0,1,3,4,5) and sum(x*x for x in prepared)==1,
         "common input mismatch")
    options = []
    for j in odd:
        subset = tuple(i for i in odd if i != j)
        remote = tuple(i for i in modes if i!=j)
        for sign in ((),*combinations(remote,2)):
            comp = pulse(phase_pair(prepared,sign),subset)
            bits, vec = profile(comp)
            if bits==(j,) and sum(bool(x) for x in comp)<=3:
                break
        else:
            raise ArithmeticError("no complement-only compression")
        need(comp[j] == prepared[j] and sorted(abs(x) for x in vec if x)==[1,2,2],
             "different target or unsupported local reference state")
        # A reflection of one coordinate input on exactly three arms has
        # this magnitude pattern. Signed wires/port permutations fix its
        # pattern and orientation; no continuum of preparations is needed.
        need(j not in (*sign,*subset), "changed the tagged port itself")
        options.append({"tag":j, "flip_pair":sign,"other_four":subset, "compressed_numerators":vec,
                        "ordinary_probability":str(comp[j]**2), "four_mode_shadow_probability":1})
    pborn = tuple(x*x for x in prepared)
    need(sum(pborn)==1 and sum(pborn[j] for j in odd)==F(5,9), "standard normalization control")
    # If each of five transferred lower bounds is 1-epsilon_j, normalization
    # implies sum epsilon_j >= 4. This is a necessary robustness inequality,
    # not an experimentally achieved tolerance. It is sharp for this one-row
    # witness with five uniform probabilities 1/5 and the remaining one 0.
    relaxed = tuple(F(1,5) if i in odd else F(0) for i in modes)
    need(sum(relaxed)==1 and sum(1-relaxed[j] for j in odd)==4, "uniform slack control")
    # Postselect a DIFFERENT tag per setting from this distribution: every
    # selected conditional is 1, from disjoint one-fifth subpopulations. It
    # does not imply five unit unconditional probabilities for a common trial.
    need(all(relaxed[j]/relaxed[j] == 1 for j in odd), "conditioning control")
    return {"common_preparation":witness,"squared_norm_of_integer_vector":9,"transfers":options,
            "requested_unconditional_sum_over_five_tags":5,"allowed_maximum":1,
            "sum_of_five_standard_probabilities":str(sum(pborn[j] for j in odd)),
            "minimum_total_transfer_slack":4,"minimum_uniform_transfer_slack":"4/5",
            "separate_postselections":"all five conditionals can be one; common unconditional tags cannot",
            "missing":"physics of gate implementation, spectator independence, preparation equivalence and counts"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),sort_keys=True))
