"""How many fixed-gain dark-port checks separate small finite phase fields?

All comparisons use the SAME two three-port commands, one seeded input and
one output port, not a different mixer fit for each prime. Absolute contrast
cutoff is fixed before selecting depths. Finite candidate worlds and the
rational comparator share scalar addition, signed flux, the local linear
involution and quadratic conservation; zero in their respective arithmetic
is their submitted null observable. No measurement or squared click law.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from functools import cache
from math import isqrt

H, G = (0, 1, 2), (1, 2, 3)
SEED = (1, 0, 0, 0)
CUTOFF = F(1, 16)  # squared incident-normalized wave level, not a click rate


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def field_star(x, h, p=None):
    if p:
        t = 2*sum(x[i] for i in h)*pow(3, -1, p)
        out = tuple((t-y) % p if i in h else y for i,y in enumerate(x))
        need(sum(out) % p == sum(x) % p and sum(z*z for z in out) % p == sum(z*z for z in x) % p,
             "finite-ring conservation")
    else:
        t = F(2,3)*sum(x[i] for i in h)
        out = tuple(t-y if i in h else y for i,y in enumerate(x))
    return out


def orbit(p, n):
    x = SEED
    result = []
    for _ in range(n):
        for h in (H,G):
            y = field_star(x, h, p)
            need(field_star(y, h, p) == x, "echo")
            x = y
        result.append(x)
    return tuple(result)


def minimum_panel(rows, size):
    full = (1 << size)-1
    options = tuple(tuple(k for k,mask in rows.items() if mask & (1<<j)) for j in range(size))

    @cache
    def choose(remainder):
        if not remainder:
            return ()
        j = min((j for j in range(size) if remainder & (1<<j)), key=lambda j:len(options[j]))
        if not options[j]:
            raise ValueError("uncovered model")
        plans = (tuple(sorted((k,*choose(remainder & ~rows[k])))) for k in options[j])
        return min(plans,key=lambda group:(len(group),group))

    return choose(full)


def probe():
    ps = tuple(p for p in range(2, 98) if p != 3 and prime(p))
    depth = 96
    real = orbit(None,depth)
    lookup = {p:orbit(p,depth) for p in (*ps,101,103,107,109,113,127,1009)}
    returns, rows, cover, end = {}, {}, 0, None
    full = (1 << len(ps))-1
    for p, path in lookup.items():
        for k,(x,y) in enumerate(zip(real,path,strict=True),1):
            need(all((F(v).numerator*pow(F(v).denominator,-1,p))%p == w
                     for v,w in zip(x,y,strict=True)), "modular reduction not a comparator homomorphism")
            if p in ps and p not in returns and y == SEED:
                returns[p] = k
    for k,x in enumerate(real,1):
        v = x[3]
        rows[k] = sum(1<<j for j,p in enumerate(ps) if lookup[p][k-1][3] == 0 and v*v >= CUTOFF)
        cover |= rows[k]
        if cover == full and end is None:
            end = k
    need(end == 43 and len(returns)==len(ps), "fixed schedule first sufficient prefix")
    bounded = {k: mask for k,mask in rows.items() if k<=end and mask}
    best = minimum_panel(bounded,len(ps))
    seen = set()
    for k in best:
        seen.update(p for j,p in enumerate(ps) if bounded[k] & 1<<j)
    need(seen == set(ps) and len(set(best))==len(best), "insufficient panel")
    # Independent brute-force validation of the cover solver on a smaller design.
    from itertools import combinations
    smaller = {10:3, 20:6, 30:12, 40:9, 50:1, 60:4}
    brutish = min((t for n in range(1,7) for t in combinations(smaller,n)
                   if all(any(smaller[k] & 1<<j for k in t) for j in range(4))), key=lambda t:(len(t),t))
    need(minimum_panel(smaller,4)==brutish, "panel solver control")
    holdout = {p:[k for k in best if lookup[p][k-1][3] == 0] for p in (101,103,107,109,113,127,1009)}
    need(all(not holdout[p] for p in (101,103,107,109,113,127)) and holdout[1009]==[35],
         "untrained primes need not behave monotonically with their size")
    # One cut without gain calibration: port is dark mod 5 after four
    # commands, positive-field monitor is not; an exact null comparator is
    # still assumed. The return of both full states is a distinct criterion.
    need(lookup[5][1][3]==0 and real[1][3]==F(-40,81), "small dark-port control")
    need(real[0][3]==F(8,9) and lookup[2][0]==SEED, "characteristic-two control")
    return {"scope":"finite family of arithmetic candidates, stipulated faithful null readout, not physical exclusions",
            "design":"four wires, seed e0, H012 then G123 per block, read wire 3; threshold |field|>=1/4",
            "number_of_design_primes":len(ps), "first_sufficient_prefix_blocks":end,
            "fewest_reads_within_that_prefix":len(best), "chosen_blocks":best,
            "coverage_by_chosen_block":{k:[p for j,p in enumerate(ps) if bounded[k] & 1<<j] for k in best},
            "untrained_primes_and_distinguishing_blocks":holdout,
            "finite_state_first_exact_returns":returns,
            "four_commands_port_three":{"rational":"-40/81","F5":0},
            "unbounded_wall":"A finite union of nonzero reduced numerators has only finitely many prime divisors. All other primes except denominator primes preserve every zero/nonzero result, even without a contrast cut.",
            "resources":"Local intrinsic field addition and nonzero detection are assumed; F3 has no inverse of 3 and is not one of these models."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
