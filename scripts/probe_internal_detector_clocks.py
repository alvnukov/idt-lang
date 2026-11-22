"""Can a clock at the hub read a remote reversible cursor without a broadcast?

A known initial departure aligns a port register. At a hub scatter exchange
the ingress and egress rail names *in that register*. A clock is a second
pulse on a simple ring with one distinguished contact at this same hub.
Only when the reference pulse visits its contact is the register inspected.
Both pulses take one physical edge per update. This shared rate, a stable
channel interface, the observed active sector and a passive record of contact
events are inputs. No probability on initial phases is used. The external
all-hop rail label is used only as a diagnostic, not by the local observer.

Full joint periods, not individual clicks or arbitrary short windows, are
compared. A classification for integer neutral packets concerns this specific
family with equally subdivided logical edges, not physical clocks in general.
"""

from collections import Counter
from itertools import product
from math import gcd, lcm

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_reversible_excitation_detector import Apparatus


def exchange(label, left, right):
    return right if label == left else left if label == right else label


def hub_name(g, old, new, label):
    # No access to a mark or a remote cell. The two port labels are installed
    # at the junction; away from it the register is physically left alone.
    if old[1] == 0:
        return exchange(label, g.arc[old[:2]][0], g.arc[new[:2]][0])
    return label


def advance(g, state, label):
    after = g.step(state)
    return after, hub_name(g, state, after, label)


def retreat(g, state, label):
    before = g.inverse(state)
    return before, hub_name(g, before, state, label)


def active_trace(g, first, direction):
    start = state = g.launch(first, direction, 0)
    label, trace, crossings, changes = first, [], Counter(), Counter()
    while True:
        trace.append(label)
        need(label == g.arc[state[:2]][0], "hub register disagrees with hidden trajectory")
        new, nxt = advance(g, state, label)
        if state[1] == 0:
            crossings[label] += 1
            if label != nxt:
                changes[label] += 1
        need(retreat(g, new, nxt) == (state, label), "coupled apparatus inverse")
        state, label = new, nxt
        if (state, label) == (start, first):
            return tuple(trace), crossings, changes
        need(len(trace) < 100000, "active orbit did not close in fixture budget")


def ring(h):
    need(h >= 4 and h % 2 == 0, "reference requires a simple even cycle")
    return {k: ((k-1) % h, (k+1) % h) for k in range(h)}


def sample(trace, h, start, direction=1):
    rails = Counter()
    ref = ring(h)
    at, previous = start, (start-direction) % h
    initial = (at, previous)
    joint = lcm(len(trace), h)
    for tick in range(joint):
        if at == 0:
            rails[trace[tick % len(trace)]] += 1
        a, b = ref[at]
        need(previous in (a,b), "nonincident reference pulse")
        at, previous = (b if previous == a else a), at
    need((at, previous) == initial and rails.total() == joint//h, "lost clock contact")
    return rails


def blocks(currents):
    need(sum(currents) == 0 and any(currents), "active neutral packet required")
    return tuple(4*x*x for x in currents)


def preserves(block_lengths, h):
    # Each train samples a residue modulo gcd; equality requires that the
    # desired count per rail be integral, and a contiguous aligned block of
    # any such length has equal populations in every residue class.
    step = gcd(sum(block_lengths), h)
    return all(n % step == 0 for n in block_lengths)


def factors(n):
    distinct = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            distinct.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        distinct.append(n)
    return distinct


def universal_on_triangles(h):
    return h % 8 != 0 and all(p == 2 or p % 3 == 2 for p in factors(h))


def obstruction(h, rails):
    """Construct a neutral packet if the proposed universal clock is unsafe."""
    if h % 8 == 0:
        return (1,-1) + (0,)*(rails-2)
    for p in factors(h):
        if p == 2:
            continue
        if rails == 3:
            if p == 3 or p % 3 == 1:
                x = next(a for a in range(p) if (a*a+a+1) % p == 0)
                return (x,1,-x-1)
        else:
            # Q=(a+b)^2+(a+c)^2+(b+c)^2. Over an odd field these
            # coordinates are invertible. Find x^2+y^2+1=0, then lift.
            roots = {a*a % p:a for a in range(p)}
            x = next(a for a in range(p) if (-1-a*a) % p in roots)
            y = roots[(-1-x*x) % p]
            a = (x+y-1)*pow(2,-1,p) % p
            b, c = (x-a) % p, (y-a) % p
            return (a,b,c,-a-b-c) + (0,)*(rails-4)
    return None


def main():
    packets = ((2,1,-3), (1,1,-2), (2,-1,-1,0), (1,2,-1,-2), (1,-1))
    periods = (4,6,8,10,14,22)
    combinations = 0
    for currents in packets:
        g = Apparatus(tuple(map(abs,currents)))
        lengths = blocks(currents)
        for first,d in product(g.order, (-1,1)):
            trace, laps, handoffs = active_trace(g, first, d)
            all_hops = Counter(trace)
            need(all(all_hops[i] == n for i,n in enumerate(lengths)), "nonquadratic active tour")
            need(all(laps[i] == abs(currents[i]) for i in g.order), "hub visits are not time")
            need(all(handoffs[i] == 1 for i in g.order), "switches are not time")
            for h in periods:
                for phase in range(h):
                    got = sample(trace, h, phase, d)
                    equal = all(got[i]*len(trace) == n*got.total() for i,n in enumerate(lengths))
                    need(equal == preserves(lengths,h), "physical reference disagrees with gcd test")
                    combinations += 1

    g = Apparatus((2,1,3))
    for arc,mask,label in product(g.arc, range(1 << len(g.cells)), range(3)):
        state = (*arc,mask)
        after, new = advance(g,state,label)
        need(retreat(g,after,new) == (state,label), "noninvertible misaligned register")
        need((label == g.arc[arc][0]) == (new == g.arc[after[:2]][0]),
             "free initialization was smuggled in")
    table = {}
    for h in range(4,258,2):
        for k in (3,4,5):
            w = obstruction(h,k)
            classified = universal_on_triangles(h) if k == 3 else 4 % h == 0
            need((w is None) == classified and (w is None or not preserves(blocks(w),h)),
                 "clock classification or supplied witness failed")
            if k == 3 and h <= 32:
                table[h] = classified
        for a,b in product(range(-6,7),repeat=2):
            if (a or b) and universal_on_triangles(h):
                need(preserves(blocks((a,b,-a-b)),h), "false positive triangular clock")
    need([h for h,ok in table.items() if ok] == [4,10,20,22], "changed small-clock list")
    need(preserves(blocks((2,-1,-1,0)),10) and not preserves(blocks((1,2,-1,-2)),10),
         "unused channel should not itself cause aliasing")
    trace,_,_ = active_trace(Apparatus((1,2,1,2)),0,1)
    phases = {tuple(sampled[i] for i in range(4)) for k in range(10)
              for sampled in (sample(trace,10,k),)}
    need(len(phases) > 1 and all(sum(row) == 4 for row in phases), "alias hidden by phase averaging")
    print("internal detector clocks: passive hub latch reversible even when misaligned; "
          f"{combinations} physical full-period phase/preparation trials; "
          f"safe even triangle clocks <=32: {[h for h,ok in table.items() if ok]}; "
          f"four live rails at h=10: {sorted(phases)}. Conditional model only.")


if __name__ == "__main__":
    main()
