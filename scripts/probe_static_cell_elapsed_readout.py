"""Static-cell holdout: a common elapsed time and the cost of recognizing completion.

The primary target is still complement followed by an actual four-cycle on
the same four owned slots, measured on a hub return. Here the six inputs
may have made *different counts of returns* at the common time. All physical
edge traversal times are equal in this holdout. Waiting elsewhere and reading
remote stores or a non-hub projection would be a different contract.
"""

from functools import cache
from itertools import product
from math import gcd, lcm

from scripts.probe_static_cell_mixer_search import (
    GOALS,
    PAIRS,
    S,
    X,
    first_returns,
    need,
)


def meet(left,right):
    a,m = left
    b,n = right
    g = gcd(m,n)
    if (a-b) % g:
        return None
    n1 = n//g
    k = ((b-a)//g * pow(m//g,-1,n1)) % n1 if n1 > 1 else 0
    return a+m*k,m*n1


def epochs(f,h):
    out = []
    for start in range(len(f)):
        pos,elapsed = start,0
        at = {}
        while pos not in at:
            at[pos] = elapsed
            elapsed += h[pos]
            pos = f[pos]
        need(pos == start, "not a permutation/positive recurrent mesh")
        out.append({end:(r,elapsed) for end,r in at.items()})
    return out


def common(phases,goal,d,ignore_direction):
    times = {(0,1)}
    for i,w in enumerate(goal):
        row = phases[6*d+i]
        endpoints = (6*d+w,6*(1-d)+w) if ignore_direction else (6*d+w,)
        times = {v for old in times for j in endpoints if j in row
                 if (v := meet(old,row[j])) is not None}
        if not times:
            return None
    return min(a if a else m for a,m in times)


@cache
def classify(f,h):
    phases = epochs(f,h)
    return tuple(any(common(phases,goal,d,ignore) is not None for goal in GOALS)
                 for d,ignore in product(range(2),(False,True)))


def clock_bits():
    f,h = first_returns((X,S,X),PAIRS)
    e = epochs(f,h)
    plain = tuple(PAIRS.index(15^mask) for mask in PAIRS)
    need(common(e,plain,0,False) == 32, "lost positive simultaneous-time control")
    traces = []
    for i in range(6):
        row = []
        t = 0
        for _ in range(3):
            t += h[i]
            i = f[i]
            row.append(2*(i//6)+(PAIRS[i%6]&1))
        traces.append(tuple(row))
        need(t == 32, "inconsistent unequal-slot contact times")
    need(len(set(traces)) == 6 and any(word[0] == word[2] for word in traces),
         "lost distinct histories or missing single-symbol ambiguity")
    def correct(machine,seed):
        for i,word in enumerate(traces):
            q = seed[PAIRS[i]&1]
            for step,sym in enumerate(word):
                action = machine[4*q+sym]
                if (action == 2) != (step == 2):
                    return False
                q = 0 if action == 2 else action
        return True
    # Action: continue in state 0, continue in state 1, or emit now.
    # Even a single-run observer may initialize from the launch lane. No
    # state after emit is inspected. The other two binary initializations
    # are equivalent under relabeling; check them anyway.
    successes = [sum(correct(m,seed) for m in product(range(3),repeat=8))
                 for seed in product(range(2),repeat=2)]
    need(successes == [0]*4, "unexpected binary completion recognizer")
    for word in traces:
        q,flags = 0,[]
        for _ in word:
            q = (q+1)%3
            flags.append(q == 0)
        need(flags == [False,False,True] and q == 0, "ternary local return counter")


def main():
    for m,n in product(range(1,10),repeat=2):
        for a,b in product(range(m),range(n)):
            w = [t for t in range(lcm(m,n)) if t%m == a and t%n == b]
            need(meet((a,m),(b,n)) == ((w[0],lcm(m,n)) if w else None),
                 "elapsed-time intersections disagree with direct clock replay")
    clock_bits()
    totals = [0]*4
    for triple in product(range(40), repeat=3):
        flags = classify(*first_returns(triple,PAIRS))
        for j,hit in enumerate(flags):
            totals[j] += hit
    need(totals == [0]*4, "a static elapsed-time holdout hit needs review")
    print("64,000 static assemblies: no common positive elapsed hub time realizes "
          "the specified complement plus any four-cycle, even with unequal passage "
          "counts or ignored output direction. Pure X-S-X complement occurs at time 32. "
          "Local completion from returned side and lane alone needs three states "
          "in the tested reset interface; no two-state recognizer even with a lane-seeded start.")


if __name__ == "__main__":
    main()
