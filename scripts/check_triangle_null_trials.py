"""Prospective finite-count calibration test, not measured IDT data.

Fix a number of independently routed trials BEFORE looking at outcomes. Always
exchange triangle rails 1,2. With probability 1/3 stop and score the first
minus port; otherwise exchange 0,1 on the selected full current and score its
minus port. Exactly one score per prepared trial. Late random routing must be
independent of the incoming current, ticket, first branch and earlier trials.
Do not read and rebuild a survivors-only state at the intermediate port.

On the canonical quadratic-stock triangle, any lit first plus output lies
on the median (2,-1,-1), and any lit first minus output on the edge (0,1,-1).
The second minus probabilities are 3/4 and 1/4 respectively. Thus even
given the first flag and the past the combined score is fair, IF the later
branch populations are sampled representatively conditional on that history.
The probability of k scores in N trials is then Binomial(N,1/2) by the
chain rule; the prepared current itself may drift between trials. This is
not device-independent randomness generation. Under the gain-one mod-three
competitor a lit preparation always takes minus at both exchanges. A plain
fair coin instead simulates the overall null, without simulating the device.

Supply the predeclared attempted count, number scored, and minus count.
If any attempt lacks a score the test declines inference. The exact upper
tail is directional (excess minus); it is not valid for optional stopping,
cherry-picked arms or pseudoreplicated descendants of one source ticket.
No code can verify sampling, herald completeness or pre-registration from
these three numbers. Zero physical detections are not the score zero.
"""

import argparse
import json
from fractions import Fraction as F
from math import comb

from scripts.probe_associative_stock_merge import q, split


def second_minus(current):
    a, b = split(current, 0, 1)
    return F(q(b), q(a)+q(b))


def null_report(attempted, scored, minus):
    if any(type(v) is not int for v in (attempted, scored, minus)):
        raise ValueError("integer counts required")
    if not 0 <= minus <= scored <= attempted <= 4096 or attempted == 0:
        raise ValueError("require 0 <= minus <= scored <= attempted, 1..4096 attempts")
    out = {"attempted": attempted, "scored": scored, "minus": minus,
           "empirical_status": "caller_supplied_counts_not_verified"}
    if scored != attempted:
        return dict(out, status="inconclusive_missing_score", upper_tail=None)
    tail = F(sum(comb(attempted, k) for k in range(minus, attempted+1)), 2**attempted)
    return dict(out, status="conditional_fixed_sample_tail", upper_tail=str(tail))


def population_controls():
    for a in range(-5, 6):
        for b in range(-5, 6):
            if a == b == 0:
                continue
            x = (a, b, -a-b)
            for flag, child in enumerate(split(x, 1, 2)):
                if q(child):
                    later = second_minus(child)
                    if F(flag, 3) + F(2, 3)*later != F(1, 2):
                        raise AssertionError("conditional null failed")
            lit = lambda z: (z[0]-z[1]) % 3 != 0
            if lit(x):
                first_plus, first_minus = split(x, 1, 2)
                next_plus, next_minus = split(first_minus, 0, 1)
                if lit(first_plus) or lit(next_plus) or not lit(next_minus):
                    raise AssertionError("residue-law directional control failed")
    # With a uniform late seed in {0,..,11} on a first plus, continuation has
    # correct marginal frequency 2/3 and second minus marginal 3/4. Reuse the
    # same seed for both and the score instead has frequency 8/12, not 1/2.
    if F(sum(seed < 8 and seed < 9 for seed in range(12)), 12) != F(2, 3):
        raise AssertionError("shared-randomness control collapsed")


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    for key in ("attempted", "scored", "minus"):
        p.add_argument(f"--{key}", type=int, required=True)
    args = p.parse_args()
    try:
        population_controls()
        report = null_report(args.attempted, args.scored, args.minus)
    except ValueError as err:
        p.error(str(err))
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
